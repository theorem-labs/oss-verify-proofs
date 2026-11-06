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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Module CJ_band3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* [comment removed for export] *)
Ltac pose_head_blk_band A :=
  match goal with HL : ART ?AI _ _ ((A, ?n) :: _) _ _ _ _ _ _ |- _ =>
    let SC := fresh "NSC" in
    pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n A (Z.max n 1) HL (or_introl eq_refl) (Z.le_refl _) (Z.le_refl _)) as SC;
    unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC end.
(* [comment removed for export] *)
Ltac pose_arng_band ARNG := lazymatch type of ARNG with ablock_range ?A _ => pose_head_blk_band A end.
(* [comment removed for export] *)
Ltac pose_head_frm_band Fr :=
  match goal with HL : ART ?AI _ _ _ ((Fr, ?k) :: _) _ _ _ _ _ |- _ =>
    let SC := fresh "NFC" in
    pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr k Fr (fsz k) HL (or_introl eq_refl) (Z.le_refl _) (Z.le_refl _)) as SC;
    try (change (fsz 1) with 128 in SC); try (change (fsz 2) with 256 in SC);
    unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC end.
(* [comment removed for export] *)
Ltac pose_perm_blk_band HL HP :=
  let IN := fresh "BIN" in pose proof (perm_in_head _ _ _ HP) as IN; pose_blk_band HL IN.
End CJ_band3.

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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pvalue_pro.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM CJ_band3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_A2.CJ_pvalue_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_A2.CJ_pvalue_exit.
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

Section PVP.
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
  Hypothesis STK2 : stkmalloc_stmt' AI 2.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_value_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np B CH U P CA blen off depth bs D n lo m g
                      nx pv ty p1 vi p2 vd ky).
  Notation VSTx := (VST sp gp tp).
  Notation MID := (MIDV AI TI sp m g sp0 SPB LR LF np CH P CA bs lo).
  Notation SAVW_ := (SAVEDV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

  Ltac lits := pose proof (pvc_lits _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PVC)
                 as (HPU & (HD & DCA & CAD) & LEN & BLEN & CEIL & BOT & LO & (PLF & PF1 & PF2 & PF3) & (SP1 & SP2 & SP3 & SP4 & SP5 & SP6)
                     & OFF & DEP & TP & (U1 & U2 & U3 & U4) & (D1 & D2 & D3 & D4) & UD & PU & PD & SPR & TOPR & BOTE);
               unfold PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_STRING_STACK, DELETE_STACK, POBJ_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, ASTRFN_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.

  (* [comment removed for export] *)
  Definition PRO_SHV : list byte := map zb [-15; -15; -15; -15; -8; -14; -14; -14; -8; -8; -8; -8; -8; -8; -8; -8; -13; -13; -13; -13; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

  Variables (mo : Model) (TRS : list (list Z)) (errv : word).

  (* [comment removed for export] *)
  Definition PV_BODY : Prop :=
    forall (SA Fr : Z) m5 Fx fcx (jae jn lj : list byte) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      VGEOM sp LB LF P SA Fr -> MID SA Fr m5 mo g LB TRS B errv ->
      SHCW m5 Fr PRO_SHV -> rw_cells bsegs m5 Fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
      rw_cells bsegs m5 (Fr + 32) [CB 8 jae] -> rw_cells bsegs m5 (Fr + 64) [CB 64 jn] ->
      rw_cells bsegs m5 SA [CB 112 lj; C8 (Z_to_bv 64 Fr)] -> stk bsegs m5 (SA + 120) (SP + -104) ->
      rw_cells bsegs m5 (SP + -104) SAVW_ ->
      pbuf_at m5 P CA blen off depth -> rw_cells bsegs m5 U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) ->
      Fagree F Fx -> frm0 fcx ->
      LSCPS bsegs POST (VSTx SA Fr 0x82eec x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 U) s4 (Z_to_bv 64 P) s6 s8 s11 x28 x29 x30 x31 Fx fcx m5) mo g.
  Hypothesis BODY : PV_BODY.

  Theorem pv_pro : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
    ART AI sp0 SPB LB LF TRS B m mo g -> TINV TI np TRS ->
    bytes_at bsegs m CA bs -> rw_cells bsegs m AERRNO [C4 errv] -> mem_inv bsegs m -> stk bsegs m lo SP ->
    pbuf_sh m P -> chain_cells m CH -> lf_room 2 LF (1001 - depth) ->
    rw_cells bsegs m U (node_cells nx pv 0 ty p1 0 vi p2 vd ky) -> pbuf_at m P CA blen off depth -> frm0 fc ->
    LSCPS bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz U) (wz P) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (wz PARSE_VALUE) fc None m (seg_rom bsegs)) mo g.
  Proof.
    intros until fc. intros HL TV BY ERR MI ST PSH CC LFR ND PB FRM. lits. bandM. sepM.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof ERR as ERR'. unfold AERRNO, ATP in ERR'.
    pose proof (pbuf_at_bound _ _ _ _ _ _ PB) as PBB. pose proof (rw_cells_bound bsegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB. pose proof (art_uar_cells AI _ _ _ _ _ _ _ _ _ HL) as UAR.
    unfold PARSE_VALUE, wz. unfold pbuf_at, pbuf_cells, wz in PB. unfold node_cells, wz in ND.
    eapply lscps_step_evt.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -240, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    shbase_split SB. destruct UAR as [UAR1 UAR2].
    zstep. carve_frame 224%nat ST. zstep. fix_lit_store. do 13 zstep.
    zstep. zstep.
    rewrite land_align32 by lia.
    set (SA := (SP + -224) / 32 * 32) in *.
    assert (GSA : SP - 240 <= SA <= SP - 224 /\ SA mod 32 = 0) by (subst SA; Z.div_mod_to_equations; lia).
    clearbody SA.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?cs) => change (c1 :: c2 :: cs) with ([c1; c2] ++ cs) in FR end.
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FR. destruct FR as [FRLO SAVW].
    cbn [cells_size Cells.csize Nat.add] in SAVW. change (Z.of_nat 120) with 120 in SAVW. replace (SP + -224 + 120) with (SP + -104) in SAVW by lia.
    eapply stk_release in FRLO; [| exact ST| lia]. cbn [cells_size Cells.csize Nat.add] in FRLO. change (Z.of_nat 120) with 120 in FRLO.
    replace (SP + -224 + 120) with (SP + -104) in FRLO by lia. clear ST.
    destruct (stk_split bsegs m1 lo SA (SP + -104) FRLO ltac:(lia)) as [ST STP0]. clear FRLO.
    destruct (stk_split bsegs m1 SA (SA + 120) (SP + -104) STP0 ltac:(lia)) as [STL STP]. clear STP0.
    (nelim (stk_carve bsegs m1 SA (SA + 120) 120 STL ltac:(lia)) 3%nat; intros _ lj FRL). clear STL.
    change (Z.of_nat 120) with 120 in FRL. replace (SA + 120 - 120) with SA in FRL by lia.
    (* [comment removed for export] *)
    do 9 zstep.
    zstep. try rewrite (sx32_lit 1) by lia. if_false.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1' end.
    assert (HL1 : ART AI sp0 SPB LB LF TRS B m1' mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (PR1 : ppres sp0 LR LF SP P m m1').
    { eapply (ppres_frame_store AI); [exact HL| intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']| exact MU| exact WM| alia| lia| lia]. }
    assert (PSH1 : pbuf_sh m1' P) by (eapply pbuf_sh_munch; [exact PSH| exact MU| lia| lia| pbuf_dj (* [comment removed for export] *)]).
    assert (CC1 : chain_cells m1' CH).
    { eapply chain_cells_munch; [exact CC| exact CHOK| exact MU| lia| lia|]. intros lo' hi' [E|[]]. inversion E; subst. left. lia. }
    clear MU WM GOTSH SHOFF UAR1 UAR2 HL PSH CC.
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof STK2 as SM. unfold stkmalloc_stmt' in SM. eapply SM with (lo := lo); clear SM; rewrite ?unsigned_lit by lia;
        first [exact HL1 | exact ST | exact MI | exact ERR' | exact TP | eapply lf_room_alloc; [exact LFR| lia] | alia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 36%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 Fr fjunk fl -> MI2 ST2 ERR2 PR2 -> -> -> FAL FLO FHI FNEW FBLK HL2 FBODY FLP SHC)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x82e24)) with (Z_to_bv 64 0x82e24) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold AERRNO, ATP in ERR2. pose proof (FBLK D n ltac:(eapply Permutation_in; [exact HPU| right; exact HD])) as FDD.
    pose proof (FBLK U 64 ltac:(eapply perm_in_head; exact HPU)) as FUU.
    change (fsz 2) with 256 in *. change (Z.to_nat (256 - 8)) with 248%nat in FBODY. clear FLP.
    change (Z.to_nat (256 / 8)) with 32%nat in SHC. cbn [shcells map repeat] in SHC.
    rewrite <- SH_shiftr in SHC. pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    try rewrite alloc_ceiling_eq in FHI. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    pose_head_frm_band Fr.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FRL; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in SAVW; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_stk _ _ _ _ _ _ _ _ PR2) in STP; [| lia| lia].
    apply (cj_pres_bytes_at _ _ _ _ _ _ _ _ PR2) in BY; [| do 3 right; left; exists D, n; rewrite LEN; split; [eapply Permutation_in; [exact HPU| right; exact HD]| lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in ND; [| do 3 right; left; exists U, 64; cbn [cells_size Cells.csize Nat.add]; split; [eapply perm_in_head; exact HPU| lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PB; [| do 4 right; left; exists (P - 32), 1; split; [exact PLF| cbn [cells_size Cells.csize Nat.add]; change (fsz 1) with 128; lia]].
    assert (PR3 : ppres sp0 LR LF SP P m m2).
    { eapply ppres_trans; [exact PR1|]. eapply ppres_of_cj_pres; [exact PR2| lia| intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']]. }
    assert (PSH2 : pbuf_sh m2 P).
    { eapply pbuf_sh_ext; [exact PSH1|]. intros j Hj. destruct (PR2 j) as [E _]; [| | exact E].
      - pose proof (SH_bounds P ltac:(lia)). pose proof (SH_bounds (P + 55) ltac:(lia)). lia.
      - do 3 right. left. exists (P - 32), 1. split; [exact PLF|]. right. change (fsz 1) with 128.
        pose proof (SH_mono (P - 32) P ltac:(lia)). pose proof (SH_aligned_add (P - 32) 128 ltac:(Z.div_mod_to_equations; lia)).
        pose proof (SH_mono (P + 55) (P - 32 + 127) ltac:(lia)). pose proof (SH_aligned_add (P - 32) 127 ltac:(Z.div_mod_to_equations; lia)).
        change (127 / 8) with 15 in *. change (128 / 8) with 16 in *. lia. }
    assert (CC2 : chain_cells m2 CH).
    { eapply chain_cells_cj_pres; [exact CC1| exact CHOK| exact PR2| lia| lia| lia]. }
    clear PR2 PR1 HL1 MI ST ERR' PSH1 CC1.
    eapply lscps_step_evt. cbv beta delta [mkR].
    unfold wz. zstep. zstep. zstep. if_cases Kf; zify_cond Kf; [| exfalso; lia].
    (* [comment removed for export] *)
    pose proof (munch_refl [(SA, SA + 120); (Fr, Fr + 24); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 32)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    apply (rw_cells_split_CB bsegs m2 Fr [] 248 fjunk [] [8; 8; 8; 8; 8; 24; 64; 120]%nat) in FBODY; [| reflexivity].
    cbn [mk_CB_cells app] in FBODY.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. fix_lit_store. zstep. fix_lit_store. zstep. fix_lit_store.
    zstep. zstep.
    do 4 sbstep. zstep. do 4 sbstep. zstep. do 12 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (INF : In (Fr, 2) ((Fr, 2) :: LF)) by (left; reflexivity).
    assert (NE : Fr <> P - 32) by (intros E; apply FNEW; rewrite E; apply (in_map fst) in PLF; exact PLF).
    pose proof (art_frames_disjoint AI _ _ _ _ _ _ _ _ _ Fr 2 (P - 32) 1 HL2 INF ltac:(right; exact PLF) NE) as PFR.
    change (fsz 2) with 256 in PFR. change (fsz 1) with 128 in PFR.
    assert (GE : VGEOM sp LB LF P SA Fr).
    { split; [lia|]. split; [lia|]. split; [exact FAL|]. split; [unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia|]. split; [try rewrite alloc_ceiling_eq; lia|]. split; [exact FBLK|]. split; [exact FNEW| exact PFR]. }
    assert (HL3 : ART AI sp0 SPB LB ((Fr, 2) :: LF) TRS B m3 mo g).
    { eapply (art_frame AI); [exact HL2| exact MU| exact WM|]. constructor; [| constructor; [| constructor; [| constructor]]].
      - right; left. cbn. alia.
      - do 8 right. left. exists Fr, 2. cbn. split; [left; reflexivity|]. change (fsz 2) with 256. lia.
      - do 9 right. exists Fr, 2. cbn. split; [left; reflexivity|]. rewrite <- SH_shiftr. change (fsz 2) with 256. lia. }
    assert (INLR : forall b', In b' LR -> In b' LB) by (intros b' Hb'; eapply Permutation_in; [exact HPU| right; exact Hb']).
    assert (PR4 : ppres sp0 LR LF SP P m m3).
    { eapply ppres_trans; [exact PR3|]. eapply ppres_of_munch; [exact MU| exact WM|]. intros a Ha Hp. cbn.
      pose proof (pv_addr_not_frbody AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC Fr LB m2 mo g TRS B SA a GE HL2 INLR Ha Hp) as N1.
      pose proof (pv_addr_not_frsh AI ra sp tp s0 sp0 SPB LB LR LF U P CA blen off depth bs D n lo PVC Fr LB m2 mo g TRS B SA a GE HL2 INLR Ha Hp) as N2.
      rewrite SHFR. unfold SH, SHADOW_OFFSET in N2. destruct Hp as ([Hs|Hr] & _); [split; [lia| split; [lia| split; [lia| exact I]]]|].
      split; [| split; [lia| split; [lia| exact I]]].
      destruct Hr as [Hi|[(A & n0 & HinA & Hr)|[(G & k & HinG & Hr)|Hsh]]].
      + pose proof (aclient_image_lt a Hi). lia.
      + (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 (INLR _ HinA)) 4%nat; intros R1 _ _ R4). try rewrite alloc_ceiling_eq in R4. lia.
      + (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL2 ltac:(right; exact HinG)) 5%nat; intros Hk _ GLO GHI _). try rewrite alloc_ceiling_eq in GHI. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in GLO. bandM. sepM.
        destruct Hr as [Hb|Hshg]; [destruct Hk as [-> | ->]; cbn in Hb; lia|].
        pose proof (SH_bounds G ltac:(lia)). pose proof (SH_bounds (G + 255) ltac:(lia)). destruct Hk as [-> | ->]; cbn in Hshg; unfold SH, SHADOW_OFFSET in *; lia.
      + unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. lia. }
    assert (PSH3 : pbuf_sh m3 P).
    { eapply pbuf_sh_munch; [exact PSH2| exact MU| lia| lia|]. pbuf_dj. }   (* [comment removed for export] *)
    assert (CC3 : chain_cells m3 CH).
    { eapply chain_cells_munch; [exact CC2| exact CHOK| exact MU| lia| lia|]. intros lo' hi' Hin. cbn in Hin.
      destruct Hin as [E|[E|[E|[]]]]; inversion E; subst; left; unfold SH, SHADOW_OFFSET in *; lia. }
    clear MU WM HL2 PR3 PSH2 CC2.
    (* [comment removed for export] *)
    lazymatch type of FBODY with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
      change [c0; c1; c2; c3; c4; c5; c6; c7] with ([c0] ++ [c1; c2; c3] ++ [c4] ++ [c5] ++ [c6] ++ [c7]) in FBODY end.
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FBODY. destruct FBODY as [HDR FB2].
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FB2. destruct FB2 as [_ FB2].
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FB2. destruct FB2 as [AE FB2].
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FB2. destruct FB2 as [_ FB2].
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FB2. destruct FB2 as [NCS _].
    cbn [cells_size Cells.csize Nat.add] in AE, NCS. change (Z.of_nat 8) with 8 in AE, NCS. change (Z.of_nat 24) with 24 in AE, NCS.
    replace (Fr + 8 + 24) with (Fr + 32) in AE by lia. replace (Fr + 8 + 24 + 8 + 24) with (Fr + 64) in NCS by lia.
    apply evt_done.
    eapply (BODY SA Fr m3 F fc); [exact GE| | unfold SHCW, PRO_SHV; cbn [map]; exact SHC| exact HDR| exact AE| exact NCS| exact FRL| exact STP| exact SAVW
      | unfold pbuf_at; eqcells PB| eqcells ND| apply Fagree_refl| exact FRM].
    split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact PR4|]. split; [apply gmono_refl|]. split; [exact TV|]. split; [exact PSH3| exact CC3].
  Qed.
End PVP.


End CeilWrap.
End CJ_pvalue_pro.

(* [comment removed for export] *)
Module CJ_pwlopts_ctx.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
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
Lemma shc_pbuf_sh : forall m Fr v0 v1 v2 v3 v11 v12 v13 v14 v15,
  SHCW m Fr (map zb [v0; v1; v2; v3; 0; 0; 0; 0; 0; 0; 0; v11; v12; v13; v14; v15]) ->
  Fr mod 128 = 0 -> 0 <= Fr -> Fr + 128 <= 2^47 -> pbuf_sh m (Fr + 32).
Proof.
  intros m Fr v0 v1 v2 v3 v11 v12 v13 v14 v15 H HA H0 H47 a Ha.
  pose proof (SHCW_sh_bytes _ _ _ H) as SB.
  eapply (sh_bytes_shb m Fr _ (Z.to_nat ((a - Fr) / 8)) 0 a SB); [Z.div_mod_to_equations; lia| | Z.div_mod_to_equations; lia| lia].
  assert (E : (a - Fr) / 8 = 4 \/ (a - Fr) / 8 = 5 \/ (a - Fr) / 8 = 6 \/ (a - Fr) / 8 = 7 \/ (a - Fr) / 8 = 8 \/ (a - Fr) / 8 = 9 \/ (a - Fr) / 8 = 10)
    by (Z.div_mod_to_equations; lia).
  destruct E as [E|[E|[E|[E|[E|[E|E]]]]]]; rewrite E; reflexivity.
Qed.

Lemma shc_shadow_ok : forall m Fr v0 v1 v2 v3 v11 v12 v13 v14 v15,
  SHCW m Fr (map zb [v0; v1; v2; v3; 0; 0; 0; 0; 0; 0; 0; v11; v12; v13; v14; v15]) ->
  Fr mod 128 = 0 -> 0 <= Fr -> Fr + 128 <= 2^47 -> shadow_ok m (Fr + 32) 56.
Proof.
  intros m Fr v0 v1 v2 v3 v11 v12 v13 v14 v15 H HA H0 H47.
  pose proof (shc_pbuf_sh _ _ _ _ _ _ _ _ _ _ _ H HA H0 H47) as PS.
  split.
  - intros i Hi. exists 0. split; [apply PS; lia| left; reflexivity].
  - intros j Hj.
    unfold SHCW in H. rewrite SH_shiftr in H. destruct H as [[_ HB] _].
    cbn [cells_bytes cbytes map app] in HB. (nelim HB 3%nat; intros _ _ HB).
    assert (R : SH Fr <= j < SH Fr + 16).
    { unfold SH, SHADOW_OFFSET in *. Z.div_mod_to_equations. lia. }
    set (k := j - SH Fr).
    assert (Ej : j = SH (Fr + 8 * k)) by (rewrite SH_aligned_add by (Z.div_mod_to_equations; lia); subst k; Z.div_mod_to_equations; lia).
    specialize (HB (Z.to_nat k) ltac:(cbn; lia)).
    replace (SH Fr + Z.of_nat (Z.to_nat k)) with j in HB by lia. rewrite Ej in HB. rewrite Ej.
    lazymatch type of HB with mrd _ _ _ = ?rhs => destruct rhs as [b|] eqn:En; [| apply nth_error_None in En; cbn in En; lia] end.
    apply mrd_shadow in HB; [| lia]. rewrite HB. discriminate.
Qed.

(* [comment removed for export] *)
Section WL.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (mo : Model) (g : lghost) (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (np B : Z).
  Variables (CA blen : Z) (bs : list byte) (D n lo : Z) (errv : word).
  Hypothesis PRE : parse_doc_pre AI TI sp s0 ra tp fc m mo g sp0 SPB LB TRS np B D n lo blen errv.
  Hypothesis DCA : D <= CA.
  Hypothesis CAD : CA + blen <= D + n.
  Hypothesis LEN : Z.of_nat (length bs) = blen.
  Hypothesis BLEN : blen < 2^31.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_doc_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LB np B CA blen bs lo m g).

  Ltac lits := pose proof PRE as (HL0 & TV0 & IND & ERR0 & MI0 & ST0 & CEIL & BOT & LO & SP1 & SP2 & SP3 & SP4 & SP5 & AL & S0LE & RA1 & RA2 & FRM0 & TP & STW & STPV & STPO & STC & BPRE); (* [comment removed for export] *)
               pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL0 IND) as (D1 & D2 & D3 & D4); (* [comment removed for export] *)
               try rewrite alloc_ceiling_eq in D4, CEIL; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in D1; unfold PARSE_DOC_STACK, PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR;
               pose proof (ASTACK_TOP_le sp0) as TOPR; clear HL0 TV0 ERR0 MI0 ST0 FRM0.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold PARSE_DOC_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, DELETE_STACK, AMALLOC_STACK; lia | sclr_tac ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac blia := unfold pdoc_cost, pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.

  (* [comment removed for export] *)
  Definition SAVEDW : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition WST (SA Fr pc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 : word)
      (Fx : bvmap 5 word) (fcx : bv 32) (mm : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 Fr) (Z_to_bv 64 0) (Z_to_bv 64 CA) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 0x5dc040) x23 x24
            (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom bsegs).

  (* [comment removed for export] *)
  Definition MIDW (SA Fr : Z) (m1 : word -> option byte) (mo1 : Model) (g1 : lghost) (LB1 : list cblock) (TRS1 : list (list Z)) (B1 : Z) (errv1 : word) : Prop :=
    ART AI sp0 SPB LB1 [(Fr, 1)] TRS1 B1 m1 mo1 g1 /\ bytes_at bsegs m1 CA bs /\ rw_cells bsegs m1 AERRNO [C4 errv1]
    /\ mem_inv bsegs m1 /\ stk bsegs m1 lo SA /\ dpres sp0 LB [] SP m m1 /\ gmono g g1 /\ TINV TI np TRS1.

  (* [comment removed for export] *)
  Definition WGEOM (SA Fr : Z) : Prop :=
    SP - 144 <= SA <= SP - 128 /\ SA mod 32 = 0 /\ Fr mod 128 = 0
    /\ (AIMG_HI <= Fr /\ sclr Fr 128)      (* [comment removed for export] *)
    /\ Fr + 128 <= alloc_ceiling
    /\ (forall A n, In (A, n) LB -> A + n <= Fr \/ Fr + 128 <= A).

  (* [comment removed for export] *)
  Definition WRES (m1 : word -> option byte) (r : Z) (LBX : list cblock) : Prop :=
    (r = 0 /\ Permutation LBX LB)
    \/ (r <> 0 /\ exists (B2 : list cblock) (d : nat) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word),
          cj_chain CJ_PRINTABLE m1 d r B2 /\ (d <= 1001)%nat /\ Permutation LBX (B2 ++ LB)
          /\ Z.of_nat (length B2) <= blen + 1
          /\ rw_cells bsegs m1 r (node_cells 0 (wz 0) ch ty p1 vs vi p2 vd 0)).

  (* [comment removed for export] *)
  Lemma dpres_step : forall W m1 m2, dpres sp0 LB [] SP m m1 -> munch W m1 m2 -> wmono bsegs m1 m2 ->
    (forall a, 0 <= a < 2^64 -> doc_addr sp0 LB [] SP a -> outside W a) -> dpres sp0 LB [] SP m m2.
  Proof. intros W m1 m2 H MU WM HO. eapply dpres_trans; [exact H|]. eapply magree_of_munch; eauto. Qed.

  (* [comment removed for export] *)
  Lemma doc_addr_lits : forall a, doc_addr sp0 LB [] SP a ->
    (SP <= a /\ a < Z.max (sp0 + 4096) (2^47)) \/ (0 <= a < 0x5ff000) \/ (exists A n0, In (A, n0) LB /\ A <= a < A + n0)
    \/ (SH alloc_ceiling <= a < SH (2^47)).
  Proof.
    intros a (Hc & He & Hg0 & Hg1). destruct Hc as [Hs|[Hi|[Hb|[(Fr' & k & Hin & _)|Hsh]]]]. (* [comment removed for export] *)
    - left. exact Hs.
    - right; left. exact (aclient_image_lt a Hi).
    - right; right; left. exact Hb.
    - destruct Hin.
    - do 3 right. exact Hsh.
  Qed.

  (* [comment removed for export] *)
  Lemma pwlo_epi : forall (SA Fr r : Z) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx (b : list byte) (h0 : word) (cpre : list cell)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31,
    WGEOM SA Fr -> MIDW SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 ->
    SHCW m1 Fr b -> length b = 16%nat ->
    rw_cells bsegs m1 Fr [C8 h0] ->
    rw_cells bsegs m1 SA cpre -> SA + Z.of_nat (cells_size cpre) = SP - 104 ->
    rw_cells bsegs m1 (SP + -104) SAVEDW ->
    Fagree F Fx -> frm0 fcx -> B - pdoc_cost blen <= B1 ->
    WRES m1 r LBX ->
    LSCPS bsegs POST (WST SA Fr 0x82c64 x1 x5 x6 x7 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros (GSA & GAL & FAL & FLO & FHI & FBLK) (HL & BY & ERR & MI & ST & DP & GM & TV) SHC LB16 HDR FRL SZL SAVW FA FRM HB RES.
    lits. bandM. sepM. unfold WST. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold AERRNO, ATP in ERR. unfold SAVEDW in SAVW.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    (* [comment removed for export] *)
    destruct b as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 [|b11 [|b12 [|b13 [|b14 [|b15 [|? ?]]]]]]]]]]]]]]]]]; try (cbn in LB16; (cut_to LB16; lia)).
    unfold SHCW in SHC. cbn [map] in SHC. clear LB16.
    (* [comment removed for export] *)
    assert (INF : In (Fr, 1) [(Fr, 1)]) by (left; reflexivity).
    destruct (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL INF) as (_ & _ & _ & _ & _ & _ & (fl & FLP & FLB & FLK & FLT) & FD).
    change (fsz 1) with 128 in FLP, FLT, FD. replace (Fr + 128 - 8) with (Fr + 120) in FLP by lia.
    pose proof (rw_cells_bound bsegs _ _ _ FLB) as FLBB. cbn [cells_size Cells.csize Nat.add] in FLBB.
    pose proof (art_flag_high_holds AI _ _ _ _ _ _ _ _ _ Fr 1 fl HL INF ltac:(change (fsz 1) with 128; replace (Fr + 128 - 8) with (Fr + 120) by lia; exact FLP) ltac:(lia)) as FLHI.
    (* [comment removed for export] *)
    pose proof (ablk_img _ _ FLHI) as FLHIi. pose proof (ablk_top _ _ FLHI) as FLHIt. apply ablk_disj_band in FLHI. unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in FLHIi, FLHI.
    pose proof (FD D n ltac:(destruct RES as [(-> & HP)|(_ & B2 & d & ch & ty & p1 & vs & vi & p2 & vd & _ & _ & HP & _)];
                 (eapply Permutation_in; [apply Permutation_sym; exact HP|]); [exact IND| apply in_or_app; right; exact IND])) as FDD.
    pose proof (FLK D n ltac:(destruct RES as [(-> & HP)|(_ & B2 & d & ch & ty & p1 & vs & vi & p2 & vd & _ & _ & HP & _)];
                 (eapply Permutation_in; [apply Permutation_sym; exact HP|]); [exact IND| apply in_or_app; right; exact IND])) as FLKD.
    assert (INDX : In (D, n) LBX) by (destruct RES as [(-> & HP)|(_ & B2 & d & ch & ty & p1 & vs & vi & p2 & vd & _ & _ & HP & _)];
                 (eapply Permutation_in; [apply Permutation_sym; exact HP|]); [exact IND| apply in_or_app; right; exact IND]).
    (* [comment removed for export] *)
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INDX) 4%nat; intros _ _ DR3 _).
    pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ D n D (Z.max n 1) HL INDX ltac:(lia) ltac:(lia)) as DSC. unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in DSC.
    pose proof FLP as FLR. change (cells_at bsegs m1 (Fr + 120) [C8 (wz fl)]) with (ro_cells bsegs m1 (Fr + 120) [C8 (wz fl)]) in FLR.
    eapply lscps_step_evt. cbv beta delta [mkR].
    (* [comment removed for export] *)
    pose proof (munch_refl [(Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16); (Fr, Fr + 8)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
    zstep. sepM. do 7 sbstep.
    zstep. zstep. zstep. fix_lit_store.
    zstep. if_cases Kf; zify_cond Kf; [exfalso; lia|].
    zstep. do 16 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HL2 : ART AI sp0 SPB LBX [(Fr, 1)] TRS1 B1 m2 mo1 g1).
    { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor; [| constructor]].
      - do 9 right. exists Fr, 1. cbn. split; [left; reflexivity|]. rewrite <- SH_shiftr. change (fsz 1) with 128. lia.
      - do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia. }
    assert (DP2 : dpres sp0 LB [] SP m m2).
    { eapply dpres_step; [exact DP| exact MU| exact WM|]. intros a Ha Hd. apply doc_addr_lits in Hd. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to GSA GAL FLO FHI CEIL LO D1 SHFR Hs FLT FLHIi Hi; lia).
      - (* [comment removed for export] *)
        assert (INA : In (A, n0) LBX) by (destruct RES as [(-> & HP)|(_ & B2 & d & ch & ty & p1 & vs & vi & p2 & vd & _ & _ & HP & _)];
                 (eapply Permutation_in; [apply Permutation_sym; exact HP|]); [exact Hin| apply in_or_app; right; exact Hin]).
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INA) 4%nat; intros _ _ R3 _).
        pose proof (art_block_sclr AI _ _ _ _ _ _ _ _ _ A n0 A (Z.max n0 1) HL INA ltac:(lia) ltac:(lia)) as SC. unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in SC.
        unfold AIMG_HI in FLO. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2).
        sepM. destruct (FD A n0 INA); (lia_on GSA GAL FAL FLO FHI CEIL LO D1 SHFR Kf Hr SC H FLT FLHIi).
      - pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr 1 Fr 128 HL INF ltac:(lia) ltac:(change (fsz 1) with 128; lia)) as FSC. unfold sclr, KHIGHMEM_BEG, KLOWSHADOW_BEG in FSC.   (* [comment removed for export] *)
        unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    assert (RES2 : WRES m2 r LBX).
    { destruct RES as [L|(Hr & B2 & d & ch & ty & p1 & vs & vi & p2 & vd & CH & Hd & HP & HLB & ND)]; [left; exact L| right].
      split; [exact Hr|]. exists B2, d, ch, ty, p1, vs, vi, p2, vd. split; [| split; [exact Hd| split; [exact HP| split; [exact HLB|]]]].
      - eapply cj_chain_frame; [exact CH| exact MU| exact WM|]. intros A n0 Hin. cbn.
        assert (INA : In (A, n0) LBX) by (eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact Hin]).
        pose_blk_band HL INA. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2).   (* [comment removed for export] *)
        sepM. destruct (FD A n0 INA); (split; [lia| split; [lia| exact I]]).
      - eapply rw_cells_transport; [exact ND| exact MU| exact WM|]. rewrite node_cells_size. cbn.
        pose proof (cj_chain_head_block _ _ _ _ _ CH Hr) as HinR.
        assert (INA : In (r, 64) LBX) by (eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact HinR]).
        pose_blk_band HL INA. pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2).   (* [comment removed for export] *)
        destruct (FD r 64 INA); (split; [lia| split; [lia| exact I]]). }
    clear MU WM HL DP RES.
    (* [comment removed for export] *)
    zstep. unfold wz.
    assert (FLP2 : cells_at bsegs m2 (Fr + 120) [C8 (wz fl)]) by exact FLR.
    pose proof (munch_refl [(fl, fl + 1)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LBX [] TRS1 B1 m3 mo1 g1).
    { replace (@nil fframe) with (lf_remove Fr [(Fr, 1)]) by (cbn; rewrite Z.eqb_refl; reflexivity).
      eapply (art_ff_release AI); [exact HL2| exact INF| | exact MU| exact WM|].
      - change (fsz 1) with 128. replace (Fr + 128 - 8) with (Fr + 120) by lia. exact FLP2.
      - lazymatch goal with H : rw_cells bsegs m3 fl _ |- _ => exact H end. }
    assert (DP3 : dpres sp0 LB [] SP m m3).
    { eapply dpres_step; [exact DP2| exact MU| exact WM|]. intros a Ha Hd. apply doc_addr_lits in Hd. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to GSA FLO FHI CEIL LO D1 FLT Hs FLHIi Hi; lia).
      - destruct (FLK A n0 ltac:(destruct RES2 as [(-> & HP)|(_ & B2 & d & ch & ty & p1 & vs & vi & p2 & vd & _ & _ & HP & _)];
                 (eapply Permutation_in; [apply Permutation_sym; exact HP|]); [exact Hin| apply in_or_app; right; exact Hin])); lia.
      - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    assert (RES3 : WRES m3 r LBX).
    { destruct RES2 as [L|(Hr & B2 & d & ch & ty & p1 & vs & vi & p2 & vd & CH & Hd & HP & HLB & ND)]; [left; exact L| right].
      split; [exact Hr|]. exists B2, d, ch, ty, p1, vs, vi, p2, vd. split; [| split; [exact Hd| split; [exact HP| split; [exact HLB|]]]].
      - eapply cj_chain_frame; [exact CH| exact MU| exact WM|]. intros A n0 Hin. cbn.
        destruct (FLK A n0 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact Hin])); (split; [lia| exact I]).
      - eapply rw_cells_transport; [exact ND| exact MU| exact WM|]. rewrite node_cells_size. cbn.
        pose proof (cj_chain_head_block _ _ _ _ _ CH Hr) as HinR.
        destruct (FLK r 64 ltac:(eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact HinR])); (split; [lia| exact I]). }
    clear MU WM HL2 DP2 RES2.
    (* [comment removed for export] *)
    zstep. zstep. do 14 zstep. zstep.
    eapply stk_release in FRL; [| exact ST| lia]. rewrite SZL in FRL.
    replace (SP - 104) with (SP + -104) in FRL by lia.
    release_frame SAVW FRL (bv_unsigned sp).
    apply evt_done. apply lscps_done. unfold parse_doc_post.
    nexists 17%nat. exists m3, r, LBX, TRS1, B1, errv1.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact FA|]. split; [exact FRM|].
    split; [exact MI|]. split; [exact FRL|]. split; [unfold AERRNO, ATP; exact ERR|].
    split; [exact HL3|]. split; [exact TV|]. split; [exact GM|]. split; [exact HB|]. split; [exact BY|]. split; [exact DP3|].
    exact RES3.
  Qed.

  (* [comment removed for export] *)
  Lemma dpres_gerror_store : forall m1 m2 lo' hi',
    dpres sp0 LB [] SP m m1 -> munch [(lo', hi')] m1 m2 -> wmono bsegs m1 m2 ->
    ((AGERROR0 <= lo' /\ hi' <= AGERROR0 + 8) \/ (AGERROR1 <= lo' /\ hi' <= AGERROR1 + 8)) -> dpres sp0 LB [] SP m m2.
  Proof.
    intros m1 m2 lo' hi' DP MU WM HR. eapply dpres_trans; [exact DP|]. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha nelH_; (nelim nelH_ 4%nat; intros Hc He Hg0 Hg1). cbn. split; [|exact I]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma doc_fail : forall (SA Fr : Z) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx (b : list byte) (h0 : word) (cpre : list cell)
      (w0 w1 w2 w3 w4 w5 w6 e0 e1 : word)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31,
    WGEOM SA Fr -> MIDW SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 -> Permutation LBX LB ->
    SHCW m1 Fr b -> length b = 16%nat ->
    rw_cells bsegs m1 Fr [C8 h0] ->
    rw_cells bsegs m1 (Fr + 32) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6] ->
    rw_cells bsegs m1 AGERROR0 [C8 e0] -> rw_cells bsegs m1 AGERROR1 [C8 e1] ->
    rw_cells bsegs m1 SA cpre -> SA + Z.of_nat (cells_size cpre) = SP - 104 ->
    rw_cells bsegs m1 (SP + -104) SAVEDW ->
    Fagree F Fx -> frm0 fcx -> B - pdoc_cost blen <= B1 ->
    LSCPS bsegs POST (WST SA Fr 0x82c08 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD HP SHC LB16 HDR PBW GE0 GE1 FRL SZL SAVW FA FRM HB. lits. bandM. sepM. unfold WST.
    (nelimp GE 6%nat; intros GSA GAL FAL FLO FHI FBLK). (nelimp MD 8%nat; intros HL BY ERR MI ST DP GM TV).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold AERRNO, ATP in ERR. unfold AGERROR0 in GE0. unfold AGERROR1 in GE1. unfold SHCW in SHC.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    pose proof (FBLK D n IND) as FDD.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (JOIN : forall (y10 y11 : word) mm, mm = m1 ->
      evt bsegs (fun ms' => LSCPS bsegs POST ms' mo1 g1)
        (WST SA Fr 0x82c24 x1 x5 x6 x7 y10 y11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 Fx fcx mm)).
    { intros y10 y11 mm ->. unfold WST.
      zstep. if_true.
      pose proof (munch_refl [(6144064, 6144072)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (HL2 : ART AI sp0 SPB LBX [(Fr, 1)] TRS1 B1 m2 mo1 g1).
      { eapply (art_frame AI); [exact HL| exact MU| exact WM|]. constructor; [| constructor]. do 4 right. left. unfold AGERROR0. cbn. lia. }
      assert (DP2 : dpres sp0 LB [] SP m m2) by (eapply dpres_gerror_store; [exact DP| exact MU| exact WM| left; unfold AGERROR0; lia]).
      clear MU WM HL DP.
      pose proof (munch_refl [(6144072, 6144080)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      assert (HL3 : ART AI sp0 SPB LBX [(Fr, 1)] TRS1 B1 m3 mo1 g1).
      { eapply (art_frame AI); [exact HL2| exact MU| exact WM|]. constructor; [| constructor]. do 5 right. left. unfold AGERROR1. cbn. lia. }
      assert (DP3 : dpres sp0 LB [] SP m m3) by (eapply dpres_gerror_store; [exact DP2| exact MU| exact WM| right; unfold AGERROR1; lia]).
      clear MU WM HL2 DP2.
      zstep. apply evt_done.
      eapply (pwlo_epi SA Fr 0 m3 mo1 g1 LBX TRS1 B1 errv1 Fx fcx b h0 cpre);
        [exact GE| | unfold SHCW; exact SHC| exact LB16| exact HDR| exact FRL| exact SZL| exact SAVW| exact FA| exact FRM| exact HB| left; split; [reflexivity| exact HP]].
      split; [exact HL3|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|].
      split; [exact DP3|]. split; [exact GM| exact TV]. }
    unfold WST in JOIN.
    if_cases Kp; zify_cond Kp.
    - eapply JOIN. reflexivity.
    - zstep. zstep. zstep. zstep. eapply JOIN. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis DEL : cjson_delete_stmt AI TI.

  Lemma doc_fail_delete : forall (SA Fr item : Z) (T : Z -> Prop) (d : nat) (Bx : list cblock) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx
      (b : list byte) (h0 : word) (cpre : list cell) (w0 w1 w2 w3 w4 w5 w6 : word)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31,
    WGEOM SA Fr -> MIDW SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 ->
    cj_chain T m1 d item Bx -> Permutation (Bx ++ LB) LBX -> (d <= 1001)%nat ->
    SHCW m1 Fr b -> length b = 16%nat ->
    rw_cells bsegs m1 Fr [C8 h0] ->
    rw_cells bsegs m1 (Fr + 32) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6] ->
    rw_cells bsegs m1 SA cpre -> SA + Z.of_nat (cells_size cpre) = SP - 104 ->
    rw_cells bsegs m1 (SP + -104) SAVEDW ->
    Fagree F Fx -> frm0 fcx -> B - pdoc_cost blen + cost_free * Z.of_nat (length Bx) <= B1 ->
    LSCPS bsegs POST (WST SA Fr 0x82c00 x1 x5 x6 x7 (Z_to_bv 64 item) x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD CH HP Hd SHC LB16 HDR PBW FRL SZL SAVW FA FRM HB. lits. bandM. sepM. unfold WST.
    (nelimp GE 6%nat; intros GSA GAL FAL FLO FHI FBLK). (nelimp MD 8%nat; intros HL BY ERR MI ST DP GM TV).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. unfold AERRNO, ATP in ERR. unfold SHCW in SHC.
    assert (B0 : 0 <= B - pdoc_cost blen) by (clear -BPRE; lia).
    apply Forall_app in STC. destruct STC as [_ SDEL].
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. change (Z_to_bv 64 534036) with (wz DELETE_ENTRY).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof (DEL d) as DS. unfold delete_spec_at in DS.
      eapply DS with (lo := lo); clear DS; rewrite ?unsigned_lit by lia;
        first [ exact HL | exact CH | exact HP | exact ST | unfold AERRNO, ATP; exact ERR | exact MI | exact TP | exact TV | exact SDEL | reflexivity
              | rewrite cost_free_eq in *; (cut_to CEIL LO SP2 D1 GSA FLO SP5 SP4 GAL BOT HB B0; lia) | alia | Z.div_mod_to_equations; lia ]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 27%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 TRS2 -> MI2 ST2 ERR2 HL2 HP2 TV2 GM2 PR2)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x82c04)) with (Z_to_bv 64 0x82c04) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (INF : In (Fr, 1) [(Fr, 1)]) by (left; reflexivity).
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FRL; [| left; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in SAVW; [| left; unfold SAVEDW; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in HDR; [| do 4 right; left; exists Fr, 1; split; [exact INF| cbn; change (fsz 1) with 128; lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in PBW; [| do 4 right; left; exists Fr, 1; split; [exact INF| cbn; change (fsz 1) with 128; lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in SHC; [| do 5 right; left; exists Fr, 1; split; [exact INF| rewrite cells_size_mapC1, LB16, SH_shiftr; change (fsz 1) with 128; cbn; lia]].
    apply (cj_pres_bytes_at _ _ _ _ _ _ _ _ PR2) in BY; [| do 3 right; left; exists D, n; rewrite LEN; split; [exact IND| lia]].
    assert (DP2 : dpres sp0 LB [] SP m m2).
    { eapply dpres_trans; [exact DP|]. intros a Ha nelH_; (nelim nelH_ 4%nat; intros Hc He Hg0 Hg1). apply PR2; [exact Ha|].
      destruct Hc as [Hs|[Hi|[Hb|[(Fr' & k & [] & _)|Hsh]]]]; [left; lia| right; left; exact Hi| right; right; left; exact Hb| do 4 right; exact Hsh]. }
    (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL2) 4%nat; intros _ [e0 GE0] [e1 GE1] _).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases Kv; zify_cond Kv; [exfalso; lia|].
    apply evt_done.
    eapply (doc_fail SA Fr m2 mo2 g2 LR2 TRS2 (B1 - cost_free * Z.of_nat (length Bx)) errv1 Fx fcx b h0 cpre w0 w1 w2 w3 w4 w5 w6 e0 e1);
      [exact GE| | exact HP2| unfold SHCW; exact SHC| exact LB16| exact HDR| exact PBW| exact GE0| exact GE1| exact FRL| exact SZL| exact SAVW| exact FA| exact FRM| lia].
    split; [exact HL2|]. split; [exact BY|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact DP2|]. split; [eapply gmono_trans; [exact GM| exact GM2]| exact TV2].
  Qed.

  (* [comment removed for export] *)
  Lemma doc_success : forall (SA Fr item : Z) m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx (b : list byte) (h0 : word) (cpre : list cell)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31,
    WGEOM SA Fr -> MIDW SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 ->
    SHCW m1 Fr b -> length b = 16%nat ->
    rw_cells bsegs m1 Fr [C8 h0] ->
    rw_cells bsegs m1 SA cpre -> SA + Z.of_nat (cells_size cpre) = SP - 104 ->
    rw_cells bsegs m1 (SP + -104) SAVEDW ->
    Fagree F Fx -> frm0 fcx -> B - pdoc_cost blen <= B1 ->
    WRES m1 item LBX -> item <> 0 ->
    LSCPS bsegs POST (WST SA Fr 0x82b98 x1 x5 x6 x7 (Z_to_bv 64 item) x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC LB16 HDR FRL SZL SAVW FA FRM HB RES INZ. lits. bandM. sepM. unfold WST.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_true. apply evt_done.
    eapply pwlo_epi; [exact GE| exact MD| exact SHC| exact LB16| exact HDR| exact FRL| exact SZL| exact SAVW| exact FA| exact FRM| exact HB| exact RES].
  Qed.

  (* [comment removed for export] *)
  Definition PRO_SHB : list byte :=
    [Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15);
     Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0;
     Z_to_bv 8 (-13); Z_to_bv 8 (-13); Z_to_bv 8 (-13); Z_to_bv 8 (-13); Z_to_bv 8 (-13)].

  Lemma PRO_SHB_zb : PRO_SHB = map zb [-15; -15; -15; -15; 0; 0; 0; 0; 0; 0; 0; -13; -13; -13; -13; -13].
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition PWLO_BODY : Prop :=
    forall (SA Fr item : Z) m5 mo5 g5 TRS5 errv5 Fx fcx (h0 : word) (cpre : list cell)
           x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31,
      WGEOM SA Fr -> MIDW SA Fr m5 mo5 g5 ((item, 64) :: LB) TRS5 (B - 448) errv5 ->
      SHCW m5 Fr PRO_SHB -> rw_cells bsegs m5 Fr [C8 h0] -> rw_cells bsegs m5 (Fr + 32) (pbuf_cells CA blen 0 0) ->
      rw_cells bsegs m5 SA cpre -> SA + Z.of_nat (cells_size cpre) = SP - 104 ->
      rw_cells bsegs m5 (SP + -104) SAVEDW ->
      rw_cells bsegs m5 item (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) -> item <> 0 ->
      Fagree F Fx -> frm0 fcx ->
      LSCPS bsegs POST (WST SA Fr 0x829fc x1 x5 x6 x7 (Z_to_bv 64 item) x11 x12 x13 x14 x15 x16 x17 x23 (Z_to_bv 64 item) x28 x29 x30 x31 Fx fcx m5) mo5 g5.
End WL.


End CeilWrap.
End CJ_pwlopts_ctx.

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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
Import CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_ctx.CJ_fp_lemmas.
Import CJ_pwlopts_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma shadow_ok_join : forall m a n1 n2, shadow_ok m a n1 -> shadow_ok m (a + n1) n2 -> 0 < n1 -> 0 < n2 -> shadow_ok m a (n1 + n2).
Proof.
  intros m a n1 n2 [P1 V1] [P2 V2] H1 H2. split.
  - intros i Hi. destruct (Z_lt_le_dec i n1) as [L|L].
    + apply P1. lia.
    + (nelim (P2 (i - n1) ltac:(lia)) 3%nat; intros v Hv Cv). exists v. replace (a + n1 + (i - n1)) with (a + i) in Hv, Cv by lia. split; [exact Hv| exact Cv].
  - intros j Hj. replace (a + (n1 + n2) - 1) with (a + n1 + n2 - 1) in Hj by lia.
    destruct (Z_lt_le_dec j (SH (a + n1 - 1) / 8 * 8 + 8)) as [L|L].
    + apply V1. lia.
    + apply V2. unfold SH, SHADOW_OFFSET in *. Z.div_mod_to_equations. lia.
Qed.

Section WLA.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (mo : Model) (g : lghost) (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (np B : Z).
  Variables (CA blen : Z) (bs : list byte) (D n lo : Z) (errv : word).
  Hypothesis PRE : parse_doc_pre AI TI sp s0 ra tp fc m mo g sp0 SPB LB TRS np B D n lo blen errv.
  Hypothesis DCA : D <= CA.
  Hypothesis CAD : CA + blen <= D + n.
  Hypothesis BY : bytes_at bsegs m CA bs.
  Hypothesis LEN : Z.of_nat (length bs) = blen.
  Hypothesis BLEN : blen < 2^31.
  Hypothesis STK1 : stkmalloc_stmt' AI 1.
  Hypothesis MEMSET : asan_memset_spec.
  Hypothesis MEMCPY : asan_memcpy_spec.
  Hypothesis BODY : PWLO_BODY AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB np B CA blen bs lo.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_doc_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LB np B CA blen bs lo m g).
  Notation DOC_FAIL := (doc_fail AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo g sp0 SPB LB TRS np B CA blen bs D n lo errv PRE DCA CAD LEN).

  Ltac lits := pose proof PRE as (HL & TV & IND & ERR & MI & ST & CEIL & BOT & LO & SP1 & SP2 & SP3 & SP4 & SP5 & AL & S0LE & RA1 & RA2 & FRM & TP & STW & STPV & STPO & STC & BPRE); (* [comment removed for export] *)
               pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL IND) as (D1 & D2 & D3 & D4); (* [comment removed for export] *)
               try rewrite alloc_ceiling_eq in D4, CEIL; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in D1; unfold PARSE_DOC_STACK, PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R;
               pose proof (ASTACK_TOP_le sp0) as TOPR.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_DOC_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, DELETE_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac blia := unfold pdoc_cost, pv_cost_pre, PV_FRATE, PV_RATE, cost_free in *; lia.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  Theorem pwlo_pro : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    LSCPS bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz blen) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (wz PARSE_WLOPTS) fc None m (seg_rom bsegs)) mo g.
  Proof.
    intros. lits. bandM. sepM.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof ERR as ERR'. unfold AERRNO, ATP in ERR'.
    pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB. pose proof (art_uar_cells AI _ _ _ _ _ _ _ _ _ HL) as UAR.
    unfold PARSE_WLOPTS, wz.
    eapply lscps_step_evt.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SP + -144, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    shbase_split SB. destruct UAR as [UAR1 UAR2].
    zstep. carve_frame 128%nat ST. zstep. fix_lit_store. sepM. do 13 zstep.
    zstep. zstep.
    rewrite land_align32 by lia.
    set (SA := (SP + -128) / 32 * 32) in *.
    assert (GSA : SP - 144 <= SA <= SP - 128 /\ SA mod 32 = 0) by (subst SA; Z.div_mod_to_equations; lia).
    clearbody SA.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?cs) => change (c1 :: c2 :: cs) with ([c1; c2] ++ cs) in FR end.
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FR. destruct FR as [FRLO SAVW].
    cbn [cells_size Cells.csize Nat.add] in SAVW. change (Z.of_nat 24) with 24 in SAVW. replace (SP + -128 + 24) with (SP + -104) in SAVW by lia.
    eapply stk_release in FRLO; [| exact ST| lia]. cbn [cells_size Cells.csize Nat.add] in FRLO. change (Z.of_nat 24) with 24 in FRLO.
    replace (SP + -128 + 24) with (SP + -104) in FRLO by lia. clear ST.
    destruct (stk_split bsegs m1 lo SA (SP + -104) FRLO ltac:(lia)) as [ST STP0]. clear FRLO.
    destruct (stk_split bsegs m1 SA (SA + 24) (SP + -104) STP0 ltac:(lia)) as [STL STP]. clear STP0.
    (nelim (stk_carve bsegs m1 SA (SA + 24) 24 STL ltac:(lia)) 3%nat; intros _ lj FRL). clear STL.
    change (Z.of_nat 24) with 24 in FRL. replace (SA + 24 - 24) with SA in FRL by lia.
    (* [comment removed for export] *)
    do 11 zstep.
    zstep. rewrite (sx32_lit 1) by lia. if_false.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1' end.
    assert (HL1 : ART AI sp0 SPB LB [] TRS B m1' mo g) by (eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| alia]).
    assert (DP1 : dpres sp0 LB [] SP m m1').
    { eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha Hd. apply (doc_addr_lits sp sp0 LB a) in Hd. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try lia.
      - (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4. lia.
      - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    clear MU WM GOTSH SHOFF UAR1 UAR2 HL.
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof STK1 as SM. unfold stkmalloc_stmt' in SM. eapply SM with (lo := lo); clear SM; rewrite ?unsigned_lit by lia;
        first [exact HL1 | exact ST | exact MI | exact ERR' | exact TP | cbn [lf_count]; rewrite (proj1 fcap_vals); lia | alia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 36%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 Fr fjunk fl -> MI2 ST2 ERR2 PR2 -> -> -> FAL FLO FHI FNEW FBLK HL2 FBODY FLP SHC)
.
    rewrite ?unsigned_lit in ST2, PR2 by lia.
    replace (ret_pc (Z_to_bv 64 0x828d8)) with (Z_to_bv 64 0x828d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold AERRNO, ATP in ERR2. pose proof (FBLK D n IND) as FDD.
    change (fsz 1) with 128 in *. change (Z.to_nat (128 - 8)) with 120%nat in FBODY. clear FLP.
    change (shcells (repeat 0 (Z.to_nat (128 / 8)))) with (shcells [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]) in SHC. cbn [shcells map] in SHC.
    rewrite <- SH_shiftr in SHC. pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (LJ : length fjunk = 120%nat) by (destruct FBODY as [[Hwf _] _]; cbn in Hwf; lia).
    try rewrite alloc_ceiling_eq in FHI. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM.
    (* [comment removed for export] *)
    pose proof (art_frame_sclr AI _ _ _ _ _ _ _ _ _ Fr 1 Fr 128 HL2 ltac:(left; reflexivity) ltac:(lia) ltac:(change (fsz 1) with 128; lia)) as FSC.
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FSC. bandM. sepM. pose_blk_band HL2 IND.
    (* [comment removed for export] *)
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FRL; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in SAVW; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_stk _ _ _ _ _ _ _ _ PR2) in STP; [| lia| lia].
    apply (cj_pres_bytes_at _ _ _ _ _ _ _ _ PR2) in BY; [| do 3 right; left; exists D, n; rewrite LEN; split; [exact IND| lia]].
    assert (DP2 : dpres sp0 LB [] SP m m2).
    { eapply dpres_trans; [exact DP1|]. intros a Ha nelH_; (nelim nelH_ 4%nat; intros Hc He Hg0 Hg1). apply PR2; [exact Ha|].
      destruct Hc as [Hs|[Hi|[Hb|[(Fr' & k & [] & _)|Hsh]]]]; [left; lia| right; left; exact Hi| right; right; left; exact Hb| do 4 right; exact Hsh]. }
    clear PR2 DP1 HL1 MI ST ERR'.
    eapply lscps_step_evt. cbv beta delta [mkR].
    unfold wz. zstep. zstep. zstep. if_cases Kf; zify_cond Kf; [| exfalso; lia].
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs m2 Fr [] 120 fjunk [] [24; 8; 56; 32]%nat) in FBODY; [| reflexivity].
    cbn [mk_CB_cells app] in FBODY.
    pose proof (munch_refl [(SA, SA + 24); (Fr, Fr + 24); (Z.shiftr Fr 3 + 2147450880, Z.shiftr Fr 3 + 2147450880 + 16)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. fix_lit_store. zstep. fix_lit_store. zstep. fix_lit_store.
    zstep. zstep.
    do 4 sbstep. zstep. do 12 sbstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HL3 : ART AI sp0 SPB LB [(Fr, 1)] TRS B m3 mo g).
    { eapply (art_frame AI); [exact HL2| exact MU| exact WM|]. constructor; [| constructor; [| constructor; [| constructor]]].
      - right; left. cbn. alia.
      - do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia.
      - do 9 right. exists Fr, 1. cbn. split; [left; reflexivity|]. rewrite <- SH_shiftr. change (fsz 1) with 128. lia. }
    assert (DP3 : dpres sp0 LB [] SP m m3).
    { eapply (dpres_step sp m sp0 LB); [exact DP2| exact MU| exact WM|]. intros a Ha Hd. apply (doc_addr_lits sp sp0 LB a) in Hd. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO FHI SHFR Hs Hi; lia).
      - pose_blk_band HL2 Hin; pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2); destruct (FBLK A n0 Hin); (lia_on CEIL LO D1 GSA FAL FLO FHI SHFR Kf Hr BR0 BSC0 H).   (* [comment removed for export] *)
      - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    clear MU WM HL2 DP2.
    (* [comment removed for export] *)
    lazymatch type of FBODY with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] => change [c0; c1; c2; c3; c4; c5] with ([c0] ++ [c1; c2; c3] ++ [c4] ++ [c5]) in FBODY end.
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FBODY. destruct FBODY as [HDR FB2].
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FB2. destruct FB2 as [_ FB2].
    apply (proj1 (rw_cells_split_app _ _ _ _)) in FB2. destruct FB2 as [PB56 _].
    cbn [cells_size Cells.csize Nat.add] in PB56. change (Z.of_nat 8) with 8 in PB56. change (Z.of_nat 24) with 24 in PB56.
    replace (Fr + 8 + 24) with (Fr + 32) in PB56 by lia.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
      sepM. eapply MSX with (lo := lo) (d := Fr + 32) (c := 0) (n := 56); clear MSX; rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- icpt_cells _ => eapply art_icpt_cells; exact HL3 end | exact MI2 | exact ST2 | exact PB56 | reflexivity
              | lazymatch goal with |- app_range _ _ => app_rng0 end
              | apply wr_range_ok_high; lia
              | intros _; apply (shc_shadow_ok m3 Fr (-15) (-15) (-15) (-15) (-13) (-13) (-13) (-13) (-13)); [unfold SHCW; cbn [map]; exact SHC| exact FAL| lia| lia]
              | unfold AINTRIN_STACK; (cut_on [CEIL LO D1 GSA FLO FHI] (cut_on [CEIL LO GSA FHI] alia))
              | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m4 -> MU4 WM4 MI4 ZP ST4).
    rewrite ?unsigned_lit in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
    replace (ret_pc (Z_to_bv 64 0x8299c)) with (Z_to_bv 64 0x8299c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc FRL MU4 WM4. trc SAVW MU4 WM4. trc STP MU4 WM4. trc BY MU4 WM4. trc ERR2 MU4 WM4. trc HDR MU4 WM4.
    eapply rw_cells_transport in SHC; [| exact MU4| exact WM4| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia].
    assert (HL4 : ART AI sp0 SPB LB [(Fr, 1)] TRS B m4 mo g).
    { eapply (art_frame AI); [exact HL3| exact MU4| exact WM4|]. constructor; [| constructor; [| constructor]].
      - do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia.
      - right; left. cbn. alia. }
    assert (DP4 : dpres sp0 LB [] SP m m4).
    { eapply (dpres_step sp m sp0 LB); [exact DP3| exact MU4| exact WM4|]. intros a Ha Hd. apply (doc_addr_lits sp sp0 LB a) in Hd. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO FHI Hs Hi; lia).
      - pose_blk_band HL3 Hin; pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2); destruct (FBLK A n0 Hin); lia.   (* [comment removed for export] *)
      - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    clear MU4 WM4 HL3 DP3 MI2 ST2 PB56.
    (* [comment removed for export] *)
    (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL4) 4%nat; intros _ [e0 GE0] [e1 GE1] _). unfold AGERROR0 in GE0. unfold AGERROR1 in GE1.
    (nelimp (art_global_shadow AI _ _ _ _ _ _ _ _ _ HL4) 4%nat; intros _ _ SOG0 SOG1). unfold AGERROR0 in SOG0. unfold AGERROR1 in SOG1.
    assert (GE16 : rw_cells bsegs m4 6144064 ([C8 e0] ++ [C8 e1])) by (apply (proj2 (rw_cells_split_app _ _ _ _)); split; [exact GE0| cbn; exact GE1]).
    destruct (rw_cells_forget bsegs m4 _ _ GE16) as [gj GEB]. cbn [cells_size Cells.csize Nat.add app] in GEB. clear GE16 GE0 GE1.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
      sepM. eapply MSX with (lo := lo) (d := 6144064) (c := 0) (n := 16) (junk := gj); clear MSX; rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- icpt_cells _ => eapply art_icpt_cells; exact HL4 end | exact MI4 | exact ST4 | exact GEB | reflexivity
              | left; unfold lowmem_range, KLOWSHADOW_BEG; lia
              | unfold wr_range_ok, icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil
              | intros _; change 16 with (8 + 8); apply shadow_ok_join; [exact SOG0| exact SOG1| lia| lia]
              | unfold AINTRIN_STACK; alia
              | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 21%nat; intros g0' g1' g2' ga1 ga2 ga3 ga4 ga5 ga6 ga7 g3' g4' g5' g6' m6 -> MU6 WM6 MI6 ZG ST6).
    rewrite ?unsigned_lit in MU6, ST6 by lia. unfold AINTRIN_STACK in MU6.
    replace (ret_pc (Z_to_bv 64 0x829b4)) with (Z_to_bv 64 0x829b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc FRL MU6 WM6. trc SAVW MU6 WM6. trc STP MU6 WM6. trc BY MU6 WM6. trc ERR2 MU6 WM6. trc HDR MU6 WM6.
    eapply rw_cells_transport in ZP; [| exact MU6| exact WM6| dj].
    eapply rw_cells_transport in SHC; [| exact MU6| exact WM6| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia].
    assert (HL6 : ART AI sp0 SPB LB [(Fr, 1)] TRS B m6 mo g).
    { eapply (art_frame AI) with (W := [(6144064, 6144072); (6144072, 6144080); (SA - 2304, SA)]); [exact HL4| | exact WM6|].
      - eapply munch_weaken; [| exact MU6]. intros x Hx. cbn in Hx |- *. lia.
      - constructor; [| constructor; [| constructor; [| constructor]]].
        + do 4 right. left. unfold AGERROR0. cbn. lia.
        + do 5 right. left. unfold AGERROR1. cbn. lia.
        + right; left. cbn. alia. }
    assert (DP6 : dpres sp0 LB [] SP m m6).
    { eapply (dpres_step sp m sp0 LB); [exact DP4| exact MU6| exact WM6|]. intros a Ha Hd. (nelimp Hd 4%nat; intros _ _ Hg0 Hg1). apply (doc_addr_lits sp sp0 LB a) in Hd.
      unfold AGERROR0 in Hg0. unfold AGERROR1 in Hg1. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO Hs Hi Hg0 Hg1; lia).
      - destruct (FBLK A n0 Hin); (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL4 Hin) 4%nat; intros R1 _ _ R4); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1; try rewrite alloc_ceiling_eq in R4; lia.
      - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    apply (rw_cells_recell m6 6144064 _ [C8 (wz 0); C8 (wz 0)]) in ZG; [| cbn; repeat split| reflexivity].
    change [C8 (wz 0); C8 (wz 0)] with ([C8 (wz 0)] ++ [C8 (wz 0)]) in ZG. apply (proj1 (rw_cells_split_app _ _ _ _)) in ZG. destruct ZG as [GE0 GE1].
    cbn [cells_size Cells.csize Nat.add] in GE1. change (6144064 + Z.of_nat 8) with 6144072 in GE1. unfold wz in GE0, GE1.
    clear MU6 WM6 HL4 DP4 MI4 ST4 GEB SOG0 SOG1.
    (* [comment removed for export] *)
    zstep. if_cases Kv; zify_cond Kv; [exfalso; lia|].
    assert (GE : WGEOM sp LB SA Fr).
    { split; [lia|]. split; [lia|]. split; [exact FAL|]. split; [alia|]. split; [alia| exact FBLK]. }
    zstep. if_cases Kb; zify_cond Kb.
    { (* [comment removed for export] *)
      zstep. if_cases Kv'; zify_cond Kv'; [exfalso; lia|].
      (nelim (frame_join m6 SA _ (SP + -104) FRL ltac:(cbn [cells_size Cells.csize Nat.add]; change (Z.of_nat 56) with 56; exact STP) ltac:(cbn [cells_size Cells.csize Nat.add]; change (Z.of_nat 56) with 56; lia)) 3%nat; intros cpre FRX SZX)
.
      apply (rw_cells_recell m6 (Fr + 32) _ [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]) in ZP; [| cbn; repeat split| reflexivity].
      apply evt_done.
      eapply (DOC_FAIL SA Fr m6 mo g LB TRS B errv F fc PRO_SHB _ cpre);
        [ exact GE | | apply Permutation_refl | unfold SHCW, PRO_SHB; cbn [map]; exact SHC | reflexivity | exact HDR | exact ZP | exact GE0 | exact GE1
        | exact FRX | lia | exact SAVW | apply Fagree_refl | exact FRM | blia ].
      split; [exact HL6|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI6|]. split; [exact ST6|].
      split; [exact DP6|]. split; [apply gmono_refl| exact TV]. }
    (* [comment removed for export] *)
    apply (rw_cells_recell m6 (Fr + 32) _ [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 (repeat (Z_to_bv 8 0) 24)]) in ZP; [| cbn; repeat split| reflexivity].
    unfold wz in ZP.
    pose proof (munch_refl [(Fr + 32, Fr + 48)] m6) as MU. pose proof (wmono_refl bsegs m6) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    assert (HL7 : ART AI sp0 SPB LB [(Fr, 1)] TRS B m7 mo g).
    { eapply (art_frame AI); [exact HL6| exact MU| exact WM|]. constructor; [| constructor].
      do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia. }
    assert (DP7 : dpres sp0 LB [] SP m m7).
    { eapply (dpres_step sp m sp0 LB); [exact DP6| exact MU| exact WM|]. intros a Ha Hd. apply (doc_addr_lits sp sp0 LB a) in Hd. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO FHI Hs Hi; lia).
      - pose_blk_band HL6 Hin; pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2); destruct (FBLK A n0 Hin); lia.   (* [comment removed for export] *)
      - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    clear MU WM HL6 DP6.
    lazymatch type of ZP with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4] => change [c0; c1; c2; c3; c4] with ([c0; c1; c2; c3] ++ [c4]) in ZP end.
    apply (proj1 (rw_cells_split_app _ _ _ _)) in ZP. destruct ZP as [PBW HK24].
    cbn [cells_size Cells.csize Nat.add] in HK24. change (Z.of_nat 32) with 32 in HK24. replace (Fr + 32 + 32) with (Fr + 64) in HK24 by lia.
    pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HL7) as ([_ HKB] & _). unfold AHOOKS in HKB.
    (nelimp (art_global_shadow AI _ _ _ _ _ _ _ _ _ HL7) 3%nat; intros _ HKS _). unfold AHOOKS in HKS.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { pose proof MEMCPY as MCX. unfold asan_memcpy_spec, memcpy_contract in MCX.
      sepM. eapply MCX with (lo := lo) (d := Fr + 64) (s := 679104) (n := 24); clear MCX; rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- icpt_cells _ => eapply art_icpt_cells; exact HL7 end | exact MI6 | exact ST6 | exact HKB | exact HK24 | reflexivity
              | left; unfold lowmem_range, KLOWSHADOW_BEG; (cut_to FLO CEIL FHI; lia)
              | lazymatch goal with |- app_range _ _ => app_rng0 end
              | apply wr_range_ok_high; lia
              | intros _; exact HKS
              | intros _; eapply shadow_ok_sub; [apply (shc_shadow_ok m7 Fr (-15) (-15) (-15) (-15) (-13) (-13) (-13) (-13) (-13)); [unfold SHCW; cbn [map]; exact SHC| exact FAL| lia| lia] | lia| lia| lia]
              | unfold AINTRIN_STACK; alia
              | lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 22%nat; intros v0 v1 v2 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 m8 -> MU8 WM8 MI8 HKC _ ST8).
    rewrite ?unsigned_lit in MU8, ST8 by lia. unfold AINTRIN_STACK in MU8.
    replace (ret_pc (Z_to_bv 64 0x829dc)) with (Z_to_bv 64 0x829dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    trc FRL MU8 WM8. trc SAVW MU8 WM8. trc STP MU8 WM8. trc BY MU8 WM8. trc ERR2 MU8 WM8. trc HDR MU8 WM8. trc PBW MU8 WM8. trc GE0 MU8 WM8. trc GE1 MU8 WM8.
    eapply rw_cells_transport in SHC; [| exact MU8| exact WM8| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia].
    assert (HL8 : ART AI sp0 SPB LB [(Fr, 1)] TRS B m8 mo g).
    { eapply (art_frame AI); [exact HL7| exact MU8| exact WM8|]. constructor; [| constructor; [| constructor]].
      - do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia.
      - right; left. cbn. alia. }
    assert (DP8 : dpres sp0 LB [] SP m m8).
    { eapply (dpres_step sp m sp0 LB); [exact DP7| exact MU8| exact WM8|]. intros a Ha Hd. apply (doc_addr_lits sp sp0 LB a) in Hd. cbn.
      destruct Hd as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO FHI Hs Hi; lia).
      - pose_blk_band HL7 Hin; pose proof (frame1_sh_band Fr FAL ltac:(lia) FHI) as (FB1 & FB2); destruct (FBLK A n0 Hin); lia.   (* [comment removed for export] *)
      - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
    clear MU8 WM8 HL7 DP7 MI6 ST6 HKB HKS HK24.
    apply (rw_cells_recell m8 (Fr + 64) _ [C8 (wz AMALLOC); C8 (wz AFREE); C8 (wz AREALLOC)]) in HKC; [| cbn; repeat split| reflexivity].
    assert (PB8 : rw_cells bsegs m8 (Fr + 32) (pbuf_cells CA blen 0 0)).
    { unfold pbuf_cells. change [C8 (wz CA); C8 (wz blen); C8 (wz 0); C8 (wz 0); C8 (wz AMALLOC); C8 (wz AFREE); C8 (wz AREALLOC)]
        with ([C8 (wz CA); C8 (wz blen); C8 (wz 0); C8 (wz 0)] ++ [C8 (wz AMALLOC); C8 (wz AFREE); C8 (wz AREALLOC)]).
      apply (proj2 (rw_cells_split_app _ _ _ _)). split; [exact PBW|]. cbn [cells_size Cells.csize Nat.add]. change (Z.of_nat 32) with 32.
      replace (Fr + 32 + 32) with (Fr + 64) by lia. exact HKC. }
    clear PBW HKC.
    (* [comment removed for export] *)
    pose proof (art_cjst AI _ _ _ _ _ _ _ _ _ HL8) as (HKB & _). change (cells_at bsegs m8 AHOOKS) with (ro_cells bsegs m8 AHOOKS) in HKB. unfold AHOOKS in HKB.
    assert (CC : chain_cells m8 [(SP, bv_unsigned ra, bv_unsigned s0)]).
    { apply chain_cells_frame1.
      lazymatch type of SAVW with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
        pose proof (proj2 (proj1 (rw_cells_split_app m8 (SP + -104) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] rest) SAVW)) as S2 end.
      cbn [cells_size Cells.csize Nat.add] in S2. change (Z.of_nat 88) with 88 in S2. replace (SP + -104 + 88) with (SP + -16) in S2 by lia. exact S2. }
    zstep. zstep. zstep.
    replace (ret_pc (wz AMALLOC)) with (wz AMALLOC) by (unfold wz, AMALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { sepM. eapply (art_malloc_ok AI) with (lo := lo) (n := 64) (tl := [bv_unsigned ra]); rewrite ?unsigned_lit by (lia_on CEIL LO SP4 SP5 TOPR GSA);
        first [ exact HL8 | exact ST8 | exact ERR2 | exact MI8 | exact TP | reflexivity | (cut_on [CEIL LO SP2 GSA BOT SP4] (cut_on [CEIL LO SP2 GSA BOT SP4] alia))
              | rewrite cost_malloc_64; blia
              | split; [lia| unfold PC0_MALLOC; lia]
              | change [bv_unsigned ra] with (chain_trace 2 [(SP, bv_unsigned ra, bv_unsigned s0)]);
                apply uwt_hook_fp; [unfold is_pc0; left; reflexivity| exact CC| cbn; repeat split; first [(cut_to AL SP4 RA1 RAR S0R S0LE; lia) | exact RA2 | exact I] | lia]
              | eapply (tinv_room TI); [exact TV| exact STW]
              | Z.div_mod_to_equations; lia ]. }
    cbv beta. intros ms2 mo9 g9 PO'.
    (nelim PO' 26%nat; intros w0' w1' w2' b0' b1' b2' b3' b4' b5' b6' b7' w3' w4' w5' w6' m9 errv9 TRS9 -> MI9 ST9 ERR9 PR9 GM9 TP9 RES)
.
    rewrite ?unsigned_lit in ST9, PR9, TP9 by lia. rewrite cost_malloc_64 in RES.
    replace (ret_pc (Z_to_bv 64 0x829e8)) with (Z_to_bv 64 0x829e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (INF : In (Fr, 1) [(Fr, 1)]) by (left; reflexivity).
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in FRL; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in SAVW; [| left; cbn [cells_size Cells.csize Nat.add]; lia].
    apply (cj_pres_stk _ _ _ _ _ _ _ _ PR9) in STP; [| lia| lia].
    apply (cj_pres_bytes_at _ _ _ _ _ _ _ _ PR9) in BY; [| do 3 right; left; exists D, n; rewrite LEN; split; [exact IND| lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in HDR; [| do 4 right; left; exists Fr, 1; split; [exact INF| cbn; change (fsz 1) with 128; lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in PB8; [| do 4 right; left; exists Fr, 1; split; [exact INF| rewrite pbuf_cells_size; change (fsz 1) with 128; lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in SHC; [| do 5 right; left; exists Fr, 1; split; [exact INF| rewrite SH_shiftr; change (fsz 1) with 128; cbn; lia]].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in GE0; [| right; left; unfold AGERROR0; cbn; lia].
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR9) in GE1; [| right; right; left; unfold AGERROR1; cbn; lia].
    assert (DP9 : dpres sp0 LB [] SP m m9).
    { eapply dpres_trans; [exact DP8|]. intros a Ha nelH_; (nelim nelH_ 4%nat; intros Hc He Hg0 Hg1). apply PR9; [exact Ha|].
      destruct Hc as [Hs|[Hi|[Hb|[(Fr' & k & [] & _)|Hsh]]]]; [left; lia| right; left; exact Hi| right; right; left; exact Hb| do 4 right; exact Hsh]. }
    assert (TV9 : TINV TI np TRS9) by (eapply (tinv_put_or TI); [exact TV| exact STW| exact TP9]).
    unfold AERRNO, ATP in ERR9.
    clear PR9 DP8 HL8 MI8 ST8 ERR2 HKB CC TP9.
    destruct RES as [[-> HL9] | (A & jk & -> & ARNG & ANEW & AFR & HL9 & BLK & FILL)].
    - (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR].
      unfold wz. zstep. if_true.
      (nelim (frame_join m9 SA _ (SP + -104) FRL ltac:(cbn [cells_size Cells.csize Nat.add]; change (Z.of_nat 56) with 56; exact STP) ltac:(cbn [cells_size Cells.csize Nat.add]; change (Z.of_nat 56) with 56; lia)) 3%nat; intros cpre FRX SZX)
.
      apply evt_done.
      eapply (DOC_FAIL SA Fr m9 mo9 g9 LB TRS9 (B - 448) errv9 F fc PRO_SHB _ cpre);
        [ exact GE | | apply Permutation_refl | unfold SHCW, PRO_SHB; cbn [map]; exact SHC | reflexivity | exact HDR | unfold pbuf_cells in PB8; exact PB8 | exact GE0 | exact GE1
        | exact FRX | lia | exact SAVW | apply Fagree_refl | exact FRM | blia ].
      split; [exact HL9|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR9|]. split; [exact MI9|]. split; [exact ST9|].
      split; [exact DP9|]. split; [exact GM9| exact TV9].
    - (* [comment removed for export] *)
      clear GE0 GE1 FILL.
      (nelimp ARNG 4%nat; intros A1 A2 A3 A4). try rewrite alloc_ceiling_eq in A4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM.
      pose_arng_band ARNG.   (* [comment removed for export] *)
      pose proof (AFR Fr 1 INF) as AFF. change (fsz 1) with 128 in AFF.
      assert (APART : forall A' n', In (A', n') LB -> A' <> A /\ (A' + n' <= A \/ A + 64 <= A')).
      { intros A' n' Hin. eapply (lheap_perm_apart AI); [exact HL9| apply Permutation_refl| exact Hin]. }
      destruct (APART D n IND) as [_ AD].
      eapply lscps_step_evt. cbv beta delta [mkR].
      unfold wz. zstep. if_cases Kz; zify_cond Kz; [exfalso; lia|].
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { pose proof MEMSET as MSX. unfold asan_memset_spec, memset_contract in MSX.
        sepM. eapply MSX with (lo := lo) (d := A) (c := 0) (n := 64) (junk := jk); clear MSX; rewrite ?unsigned_lit by lia;
          first [ lazymatch goal with |- icpt_cells _ => eapply art_icpt_cells; exact HL9 end | exact MI9 | exact ST9 | exact BLK | reflexivity
                | lazymatch goal with |- app_range _ _ => app_rng0 end
                | apply wr_range_ok_high; lia
                | intros _; eapply art_block_shadow_ok; [exact HL9| left; reflexivity]
                | unfold AINTRIN_STACK; (cut_on [CEIL LO D1 GSA FLO A1 A4] (cut_on [CEIL LO GSA D1 FLO A1 A4] alia))
                | lia ]. }
      cbv beta. intros ms' PO.
      (nelim PO 21%nat; intros u0' u1' u2' ub1 ub2 ub3 ub4 ub5 ub6 ub7 u3' u4' u5' u6' m10 -> MU10 WM10 MI10 ZB ST10).
      rewrite ?unsigned_lit in MU10, ST10 by lia. unfold AINTRIN_STACK in MU10.
      replace (ret_pc (Z_to_bv 64 0x829fc)) with (Z_to_bv 64 0x829fc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (zero_node_cells' _ _ ZB) as NDA. clear ZB.
      trc FRL MU10 WM10. trc SAVW MU10 WM10. trc STP MU10 WM10. trc BY MU10 WM10. trc ERR9 MU10 WM10. trc HDR MU10 WM10.
      eapply rw_cells_transport in PB8; [| exact MU10| exact WM10| rewrite pbuf_cells_size; dj].
      eapply rw_cells_transport in SHC; [| exact MU10| exact WM10| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; (lia_on CEIL LO BYB GSA FAL FLO FHI SHFR BR Kf Kv A1 A4 NSC AFF Kz H H0 H14)].
      assert (HL10 : ART AI sp0 SPB ((A, 64) :: LB) [(Fr, 1)] TRS9 (B - 448) m10 mo9 g9).
      { eapply (art_frame AI); [exact HL9| exact MU10| exact WM10|]. constructor; [| constructor; [| constructor]].
        - do 7 right. left. exists A, 64. cbn. split; [left; reflexivity| lia].
        - right; left. cbn. alia. }
      assert (DP10 : dpres sp0 LB [] SP m m10).
      { eapply (dpres_step sp m sp0 LB); [exact DP9| exact MU10| exact WM10|]. intros a Ha Hd. apply (doc_addr_lits sp sp0 LB a) in Hd. cbn.
        destruct Hd as [Hs|[Hi|[(A' & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO A1 A4 Hs Hi; lia).
        - destruct (APART A' n0 Hin) as [_ DJ]. sepM. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL9 ltac:(right; exact Hin)) 4%nat; intros R1 _ _ R4); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1; try rewrite alloc_ceiling_eq in R4; (lia_on CEIL LO D1 GSA FLO A1 A4 Kz Hr DJ R4).
        - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. (lia_on CEIL LO BYB GSA FLO Kf Kv A1 NSC Kz Hsh H H0 H4 H5). }
      clear MU10 WM10 HL9 DP9 MI9 ST9 BLK.
      (* [comment removed for export] *)
      (nelim (frame_join m10 SA _ (SP + -104) FRL ltac:(cbn [cells_size Cells.csize Nat.add]; change (Z.of_nat 24) with 24; exact STP) ltac:(cbn [cells_size Cells.csize Nat.add]; change (Z.of_nat 24) with 24; lia)) 3%nat; intros cpre FRX SZX)
.
      apply evt_done.
      eapply (BODY SA Fr A m10 mo9 g9 TRS9 errv9 F fc _ cpre);
        [ exact GE | | unfold SHCW, PRO_SHB; cbn [map]; exact SHC | exact HDR | exact PB8 | exact FRX | lia | exact SAVW
        | exact NDA | lia | apply Fagree_refl | exact FRM ].
      split; [exact HL10|]. split; [exact BY|]. split; [unfold AERRNO, ATP; exact ERR9|]. split; [exact MI10|]. split; [exact ST10|].
      split; [exact DP10|]. split; [exact GM9| exact TV9].
  Qed.
End WLA.


End CeilWrap.
