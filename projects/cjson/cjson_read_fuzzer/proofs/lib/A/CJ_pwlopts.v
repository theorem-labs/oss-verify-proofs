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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pwlopts_B.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_skipws OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_pwlopts_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma fin_stop_l : forall bs blen i b, Z.of_nat (length bs) = blen -> 0 <= i < blen ->
  nth_error bs (Z.to_nat i) = Some b -> 32 < bv_unsigned b -> fin blen bs i = i.
Proof.
  intros bs blen i b LEN Hi Hn Hb. unfold fin.
  replace (ws_count (skipn (Z.to_nat i) bs)) with O.
  2:{ destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E; [reflexivity|]. cbn.
      assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
      rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst.
      destruct (Z.leb_spec (bv_unsigned c) 32); [lia| reflexivity]. }
  cbn [Z.of_nat]. rewrite Z.add_0_r. destruct (Z.eqb_spec i blen); lia.
Qed.

Lemma fin_ws_l : forall bs blen i b, Z.of_nat (length bs) = blen -> 0 <= i < blen ->
  nth_error bs (Z.to_nat i) = Some b -> bv_unsigned b <= 32 ->
  fin blen bs i = (if i + 1 =? blen then blen - 1 else fin blen bs (i + 1)).
Proof.
  intros bs blen i b LEN Hi Hn Hb. unfold fin.
  destruct (skipn (Z.to_nat i) bs) as [|c rest] eqn:E.
  { exfalso. assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = None) by (rewrite E; reflexivity).
    rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. discriminate. }
  assert (Hc : nth_error (skipn (Z.to_nat i) bs) 0 = Some c) by (rewrite E; reflexivity).
  rewrite nth_error_skipn, Nat.add_0_r, Hn in Hc. inversion Hc; subst c.
  assert (Er : rest = skipn (Z.to_nat (i + 1)) bs).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite <- skipn_skipn with (x := 1%nat) (y := Z.to_nat i).
    hnf. rewrite E. reflexivity. }
  cbn [ws_count]. destruct (Z.leb_spec (bv_unsigned b) 32); [|lia]. rewrite <- Er.
  destruct (Z.eqb_spec (i + 1) blen) as [E1|NE1].
  - pose proof (ws_count_le rest) as HL.
    assert (length rest = 0)%nat. { rewrite Er, length_skipn. lia. }
    replace (ws_count rest) with O by lia.
    lazymatch goal with |- (if ?x =? ?y then _ else _) = _ => replace x with y by lia end. rewrite Z.eqb_refl. reflexivity.
  - replace (i + Z.of_nat (S (ws_count rest))) with (i + 1 + Z.of_nat (ws_count rest)) by lia. reflexivity.
Qed.

Lemma fin_range : forall bs blen i, Z.of_nat (length bs) = blen -> 0 <= i < blen -> i <= fin blen bs i < blen.
Proof.
  intros bs blen i LEN Hi. unfold fin.
  pose proof (ws_count_le (skipn (Z.to_nat i) bs)) as HL. rewrite length_skipn in HL.
  destruct (Z.eqb_spec (i + Z.of_nat (ws_count (skipn (Z.to_nat i) bs))) blen); lia.
Qed.

Section WLB.
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
  Hypothesis DEL : cjson_delete_stmt AI TI.
  Hypothesis PV : parse_value_stmt AI TI.

  Notation SP := (bv_unsigned sp).
  Notation POST := (parse_doc_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LB np B CA blen bs lo m g).
  Notation WSTx := (WST sp gp tp CA).
  Notation MID := (MIDW AI TI sp m g sp0 SPB LB np CA bs lo).
  Notation SAVW_ := (SAVEDW ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation DOC_FAIL_DELETE := (doc_fail_delete AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo g sp0 SPB LB TRS np B CA blen bs D n lo errv PRE DCA CAD LEN DEL).
  Notation DOC_SUCCESS := (doc_success AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo g sp0 SPB LB TRS np B CA blen bs D n lo errv PRE DCA CAD LEN).

  Ltac lits := pose proof PRE as (HL0 & TV0 & IND & ERR0 & MI0 & ST0 & CEIL & BOT & LO & SP1 & SP2 & SP3 & SP4 & SP5 & AL & S0LE & RA1 & RA2 & FRM0 & TP & STW & STPV & STPO & STC & BPRE); (* [comment removed for export] *)
               pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL0 IND) as (D1 & D2 & D3 & D4); (* [comment removed for export] *)
               try rewrite alloc_ceiling_eq in D4, CEIL; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in D1; unfold PARSE_DOC_STACK, PARSE_STACK in LO;
               pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR;
               pose proof (bv_unsigned_in_range 64 ra) as RAR; change (bv_modulus 64) with (2^64) in RAR;
               pose proof (bv_unsigned_in_range 64 s0) as S0R; change (bv_modulus 64) with (2^64) in S0R;
               pose proof (ASTACK_TOP_le sp0) as TOPR; clear HL0 TV0 ERR0 MI0 ST0.
  Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_END; rewrite ?alloc_ceiling_eq; unfold PARSE_DOC_STACK, PARSE_STACK, ASTKMALLOC_STACK, AINTRIN_STACK, DELETE_STACK, AMALLOC_STACK; lia | sclr_tac2 ].
  Ltac zfeq := repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).
  Ltac eqcells H :=
    lazymatch goal with |- rw_cells _ _ _ ?cs =>
      lazymatch type of H with rw_cells _ _ _ ?cs' =>
        replace cs with cs'; [exact H| unfold pbuf_cells, node_cells, wz; zfeq] end end.
  Ltac blia := unfold pdoc_cost, pv_cost_pre, PV_FRATE, PV_RATE in *; rewrite ?cost_free_eq in *; rewrite ?length_app in *; cbn [length] in *; unfold cblock in *; lia.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length];
             first [lia | split; [lia| exact I] | split; [lia| split; [lia| exact I]]].
  Ltac trc H MU WM := first [ eapply rw_cells_transport in H; [| exact MU| exact WM| dj]
                            | eapply bytes_at_transport in H; [| exact MU| dj]
                            | eapply stk_transport_disjoint in H; [| exact MU| exact WM| dj] ].

  (* [comment removed for export] *)
  Definition ws_memW (Fr : Z) (m0 m2 : word -> option byte) (r : Z) : Prop :=
    rw_cells asegs m2 (Fr + 32) (pbuf_cells CA blen r 0) /\ bytes_at asegs m2 CA bs /\ mem_inv asegs m2
    /\ munch [(Fr + 48, Fr + 56)] m0 m2 /\ wmono asegs m0 m2.

  (* [comment removed for export] *)
  Lemma wsA : forall (SA Fr : Z) (m0 : word -> option byte), WGEOM sp LB SA Fr -> text_sh m0 CA blen ->
    forall (cnt : nat) (i : Z) (m1 : word -> option byte) Fx fcx x1 x5 x6 x7 x10 x12 x16 x17 x23 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells asegs m1 (Fr + 32) (pbuf_cells CA blen i 0) -> bytes_at asegs m1 CA bs -> mem_inv asegs m1 ->
    munch [(Fr + 48, Fr + 56)] m0 m1 -> wmono asegs m0 m1 ->
    evt asegs (fun ms' => exists x10' x11' x14' x16' x17' m2,
                 ms' = WSTx SA Fr 0x82c60 x1 x5 x6 x7 x10' x11' x12 (Z_to_bv 64 CA) x14' (Z_to_bv 64 32) x16' x17' x23 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_memW Fr m0 m2 (fin blen bs i))
        (WSTx SA Fr 0x82a54 x1 x5 x6 x7 x10 (Z_to_bv 64 blen) x12 (Z_to_bv 64 CA) (Z_to_bv 64 i) (Z_to_bv 64 32) x16 x17 x23 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros SA Fr m0 (GSA & GAL & FAL & FLO & FHI & FBLK) TSH. induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof (FBLK D n IND) as FDD.
    unfold pbuf_cells, wz in PB. unfold WST.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read asegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD.
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep.
    pose proof (TSH (CA + i) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply evt_done. nexists 6%nat. split; [reflexivity|].
      rewrite (fin_stop_l bs blen i b LEN) by first [lia | exact Hn].
      split; [unfold pbuf_cells, wz; exact PB|]. split; [exact BY|]. split; [exact MI|]. split; [exact MU| exact WM].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + rewrite (fin_ws_l bs blen i b LEN) by first [lia | exact Hn]. destruct (Z.eqb_spec (i + 1) blen); [exfalso; lia|].
        replace (CA + i + 1) with (CA + (i + 1)) by lia.
        eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [lia| lia| unfold pbuf_cells, wz; eassumption| exact BY| exact MI| exact MU| exact WM].
      + zstep. zstep. zstep.
        rewrite (fin_ws_l bs blen i b LEN) by first [lia | exact Hn]. destruct (Z.eqb_spec (i + 1) blen); [| exfalso; lia].
        apply evt_done. nexists 6%nat. split; [reflexivity|].
        split; [unfold pbuf_cells, wz; replace (blen - 1) with (blen + -1) by lia; eassumption|].
        split; [exact BY|]. split; [exact MI|]. split; [exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma wsB : forall (SA Fr : Z) (m0 : word -> option byte), WGEOM sp LB SA Fr -> text_sh m0 CA blen ->
    forall (cnt : nat) (i : Z) (m1 : word -> option byte) Fx fcx x1 x5 x6 x7 x10 x15 x16 x17 x23 x28 x29 x30 x31,
    Z.of_nat cnt = blen - i -> 0 <= i < blen ->
    rw_cells asegs m1 (Fr + 32) (pbuf_cells CA blen i 0) -> bytes_at asegs m1 CA bs -> mem_inv asegs m1 ->
    munch [(Fr + 48, Fr + 56)] m0 m1 -> wmono asegs m0 m1 ->
    evt asegs (fun ms' => exists x10' x12' x13' x15' x16' m2,
                 ms' = WSTx SA Fr 0x82aa0 x1 x5 x6 x7 x10' (Z_to_bv 64 CA) x12' x13' (Z_to_bv 64 32) x15' x16' x17 x23 x28 x29 x30 x31 Fx fcx m2
                 /\ ws_memW Fr m0 m2 (fin blen bs i))
        (WSTx SA Fr 0x82990 x1 x5 x6 x7 x10 (Z_to_bv 64 CA) (Z_to_bv 64 blen) (Z_to_bv 64 i) (Z_to_bv 64 32) x15 x16 x17 x23 x28 x29 x30 x31 Fx fcx m1).
  Proof.
    intros SA Fr m0 (GSA & GAL & FAL & FLO & FHI & FBLK) TSH. induction cnt as [cnt IH] using lt_wf_ind.
    intros until x31. intros Hc Hi PB BY MI MU WM. lits. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof (FBLK D n IND) as FDD.
    unfold pbuf_cells, wz in PB. unfold WST.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
    pose proof (u8ro_read asegs _ CA bs i b _ BY Hn ltac:(lia) eq_refl) as RD.
    pose proof (byte_range b) as Rb.
    zstep. zstep. zstep.
    pose proof (TSH (CA + i) ltac:(lia)) as CK. sepM. asan_chk CK.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply evt_done. nexists 6%nat. split; [reflexivity|].
      rewrite (fin_stop_l bs blen i b LEN) by first [lia | exact Hn].
      split; [unfold pbuf_cells, wz; exact PB|]. split; [exact BY|]. split; [exact MI|]. split; [exact MU| exact WM].
    - zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + rewrite (fin_ws_l bs blen i b LEN) by first [lia | exact Hn]. destruct (Z.eqb_spec (i + 1) blen); [exfalso; lia|].
        replace (CA + i + 1) with (CA + (i + 1)) by lia.
        eapply (IH (cnt - 1)%nat ltac:(lia) (i + 1)); [lia| lia| unfold pbuf_cells, wz; eassumption| exact BY| exact MI| exact MU| exact WM].
      + zstep. zstep. zstep.
        rewrite (fin_ws_l bs blen i b LEN) by first [lia | exact Hn]. destruct (Z.eqb_spec (i + 1) blen); [| exfalso; lia].
        apply evt_done. nexists 6%nat. split; [reflexivity|].
        split; [unfold pbuf_cells, wz; replace (blen - 1) with (blen + -1) by lia; eassumption|].
        split; [exact BY|]. split; [exact MI|]. split; [exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma locals_join : forall mm SA csa (rnt : word) csb,
    rw_cells asegs mm SA csa -> Z.of_nat (cells_size csa) = 24 -> rw_cells asegs mm (SA + 24) [C8 rnt] -> rw_cells asegs mm (SA + 32) csb ->
    rw_cells asegs mm SA (csa ++ [C8 rnt] ++ csb) /\ SA + Z.of_nat (cells_size (csa ++ [C8 rnt] ++ csb)) = SA + 32 + Z.of_nat (cells_size csb).
  Proof.
    intros mm SA csa rnt csb H1 S1 H2 H3. split.
    - apply (proj2 (rw_cells_split_app _ _ _ _)). split; [exact H1|]. rewrite S1.
      apply (proj2 (rw_cells_split_app _ _ _ _)). split; [exact H2|]. cbn [cells_size Cells.csize Nat.add].
      replace (SA + 24 + Z.of_nat 8) with (SA + 32) by lia. exact H3.
    - rewrite !cells_size_app. cbn [cells_size Cells.csize Nat.add]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma null_check : forall (SA Fr item off1 : Z) (rnt : word) (Bx : list cblock) (d : nat) (ch ty vs : Z) (vi vd : word)
      m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx (h0 : word) (csa csb : list cell) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    WGEOM sp LB SA Fr -> MID SA Fr m1 mo1 g1 LBX TRS1 B1 errv1 ->
    cj_chain CJ_PRINTABLE m1 d item Bx -> Permutation (Bx ++ LB) LBX -> (d <= 1001)%nat -> Z.of_nat (length Bx) <= blen + 1 ->
    item <> 0 -> rw_cells asegs m1 item (node_cells 0 (wz 0) ch ty (wz 0) vs vi (wz 0) vd 0) ->
    SHCW m1 Fr PRO_SHB -> rw_cells asegs m1 Fr [C8 h0] ->
    rw_cells asegs m1 (Fr + 32) (pbuf_cells CA blen off1 0) -> 0 <= off1 <= blen ->
    rw_cells asegs m1 SA csa -> Z.of_nat (cells_size csa) = 24 -> rw_cells asegs m1 (SA + 24) [C8 rnt] ->
    rw_cells asegs m1 (SA + 32) csb -> SA + 32 + Z.of_nat (cells_size csb) = SP - 104 ->
    rw_cells asegs m1 (SP + -104) SAVW_ ->
    Fagree F Fx -> frm0 fcx -> B - pdoc_cost blen + cost_free * Z.of_nat (length Bx) <= B1 ->
    LSCPS asegs POST (WSTx SA Fr 0x82970 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 item) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD CH HP Hd HLB NZ ND SHC HDR PB Ho CSA SZA RNT CSB SZB SAVW FA FRM HB. lits. bandM. sepM.
    (nelimp GE 6%nat; intros GSA GAL FAL FLO FHI FBLK). (nelimp MD 8%nat; intros HL BY ERR MI ST DP GM TV).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof (FBLK D n IND) as FDD.
    pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INF : In (Fr, 1) [(Fr, 1)]) by (left; reflexivity).
    (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL INF) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    assert (INDX : In (D, n) LBX) by (eapply Permutation_in; [exact HP| apply in_or_app; right; exact IND]).
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL INDX DCA CAD) as TSH.
    assert (B0 : 0 <= cost_free * Z.of_nat (length Bx)) by (rewrite cost_free_eq; lia).
    destruct (locals_join m1 SA csa rnt csb CSA SZA RNT CSB) as [FRL SZL]. rewrite SZB in SZL.
    pose proof PB as PB'. unfold pbuf_cells, wz in PB. unfold SHCW, PRO_SHB in SHC. cbn [map] in SHC. unfold WST.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. if_cases Krnt; zify_cond Krnt.
    { (* [comment removed for export] *)
      apply evt_done. eapply (DOC_SUCCESS SA Fr item m1 mo1 g1 LBX TRS1 B1 errv1 Fx fcx PRO_SHB h0 (csa ++ [C8 rnt] ++ csb));
        [exact GE| exact MD| unfold SHCW, PRO_SHB; cbn [map]; exact SHC| reflexivity| exact HDR| exact FRL| lia| exact SAVW| exact FA| exact FRM| lia| | exact NZ].
      right. split; [exact NZ|]. exists Bx, d, ch, ty, (wz 0), vs, vi, (wz 0), vd. split; [exact CH|]. split; [exact Hd|].
      split; [apply Permutation_sym; exact HP|]. split; [exact HLB| exact ND]. }
    zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    zstep. zstep.
    (* [comment removed for export] *)
    assert (JOIN : forall x10' x12' x13' x14' x15' x16' m2 o2,
      rw_cells asegs m2 (Fr + 32) (pbuf_cells CA blen o2 0) -> bytes_at asegs m2 CA bs -> mem_inv asegs m2 ->
      munch [(Fr + 48, Fr + 56)] m1 m2 -> wmono asegs m1 m2 -> off1 <= o2 <= blen ->
      evt asegs (fun ms' => LSCPS asegs POST ms' mo1 g1)
        (WSTx SA Fr 0x82aa0 x1 x5 x6 x7 x10' (Z_to_bv 64 CA) x12' x13' x14' x15' x16' x17 (Z_to_bv 64 item) x28 x29 x30 x31 Fx fcx m2)).
    { intros x10' x12' x13' x14' x15' x16' m2 o2 PB2 BY2 MI2 MU2 WM2 Ho2. unfold WST.
      pose proof HDR as HDR2. trc HDR2 MU2 WM2. pose proof SHC as SHC2. eapply rw_cells_transport in SHC2; [| exact MU2| exact WM2| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia].
      pose proof FRL as FRL2. eapply rw_cells_transport in FRL2; [| exact MU2| exact WM2| rewrite !cells_size_app; cbn [disjoint_from cells_size Cells.csize Nat.add length]; lia].
      pose proof SAVW as SAVW2. trc SAVW2 MU2 WM2. pose proof ERR as ERR2. trc ERR2 MU2 WM2. pose proof ST as ST2. trc ST2 MU2 WM2.
      pose proof ND as ND2. unfold node_cells, wz in ND2. eapply rw_cells_transport in ND2; [| exact MU2| exact WM2|].
      2:{ cbn [disjoint_from cells_size Cells.csize Nat.add length]. destruct (FD item 64 ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; eapply cj_chain_head_block; [exact CH| exact NZ]])); lia. }
      assert (HL2 : ART AI sp0 SPB LBX [(Fr, 1)] TRS1 B1 m2 mo1 g1).
      { eapply (art_frame AI); [exact HL| exact MU2| exact WM2|]. constructor; [| constructor].
        do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia. }
      assert (DP2 : dpres sp0 LB [] SP m m2).
      { eapply (dpres_step sp m sp0 LB); [exact DP| exact MU2| exact WM2|]. intros a Ha Hda. apply (doc_addr_lits sp sp0 LB a) in Hda. cbn.
        destruct Hda as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO FHI Hs Hi; lia).
        - destruct (FBLK A n0 Hin); (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| apply in_or_app; right; exact Hin])) 4%nat; intros R1 _ _ R4); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1; try rewrite alloc_ceiling_eq in R4; lia.
        - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
      assert (CH2 : cj_chain CJ_PRINTABLE m2 d item Bx).
      { eapply cj_chain_frame; [exact CH| exact MU2| exact WM2|]. intros A n0 Hin. cbn.
        destruct (FD A n0 ltac:(eapply Permutation_in; [exact HP| apply in_or_app; left; exact Hin])); (split; [lia| exact I]). }
      assert (MD2 : MID SA Fr m2 mo1 g1 LBX TRS1 B1 errv1).
      { split; [exact HL2|]. split; [exact BY2|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
        split; [exact DP2|]. split; [exact GM| exact TV]. }
      pose proof PB2 as PB2'. unfold pbuf_cells, wz in PB2.
      zstep. zstep. zstep. if_cases Kend; zify_cond Kend.
      { (* [comment removed for export] *)
        apply evt_done. eapply (DOC_FAIL_DELETE SA Fr item CJ_PRINTABLE d Bx m2 mo1 g1 LBX TRS1 B1 errv1 Fx fcx PRO_SHB h0 (csa ++ [C8 rnt] ++ csb));
          [exact GE| exact MD2| exact CH2| exact HP| exact Hd| unfold SHCW, PRO_SHB; cbn [map]; exact SHC2| reflexivity| exact HDR2| exact PB2| exact FRL2| lia| exact SAVW2| exact FA| exact FRM| lia]. }
      zstep.
      destruct (nth_error bs (Z.to_nat o2)) as [b|] eqn:Hn; [| apply nth_error_None in Hn; lia].
      pose proof (u8ro_read asegs _ CA bs o2 b _ BY2 Hn ltac:(lia) eq_refl) as RD. pose proof (byte_range b) as Rb.
      zstep. zstep.
      pose proof (TSH (CA + o2) ltac:(lia)) as CK. sepM. sepM. asan_chk CK.
      zstep. zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        apply evt_done. eapply (DOC_SUCCESS SA Fr item m2 mo1 g1 LBX TRS1 B1 errv1 Fx fcx PRO_SHB h0 (csa ++ [C8 rnt] ++ csb));
          [exact GE| exact MD2| unfold SHCW, PRO_SHB; cbn [map]; exact SHC2| reflexivity| exact HDR2| exact FRL2| lia| exact SAVW2| exact FA| exact FRM| (lia_on HB CEIL LO D1 GSA FLO B0)| | exact NZ].
        right. split; [exact NZ|]. exists Bx, d, ch, ty, (wz 0), vs, vi, (wz 0), vd. split; [exact CH2|]. split; [exact Hd|].
        split; [apply Permutation_sym; exact HP|]. split; [exact HLB| unfold node_cells, wz; exact ND2]. }
      apply evt_done. eapply (DOC_FAIL_DELETE SA Fr item CJ_PRINTABLE d Bx m2 mo1 g1 LBX TRS1 B1 errv1 Fx fcx PRO_SHB h0 (csa ++ [C8 rnt] ++ csb));
        [exact GE| exact MD2| exact CH2| exact HP| exact Hd| unfold SHCW, PRO_SHB; cbn [map]; exact SHC2| reflexivity| exact HDR2| exact PB2| exact FRL2| lia| exact SAVW2| exact FA| exact FRM| lia]. }
    zstep. if_cases Kskip; zify_cond Kskip.
    - eapply (JOIN _ _ _ _ _ _ m1 off1); [exact PB'| exact BY| exact MI| apply munch_refl| apply wmono_refl| lia].
    - zstep.
      pose proof (fin_range bs blen off1 LEN ltac:(lia)) as FRG.
      eapply evt_cut.
      { eapply (wsA SA Fr m1 GE TSH (Z.to_nat (blen - off1)) off1 m1) || eapply (wsB SA Fr m1 GE TSH (Z.to_nat (blen - off1)) off1 m1);
          [lia| lia| exact PB'| exact BY| exact MI| apply munch_refl| apply wmono_refl]. }
      intros ms' nelH_; (nelim nelH_ 12%nat; intros x10' x12' x13' x15' x16' m2 -> PB2 BY2 MI2 MU2 WM2).
      eapply (JOIN _ _ _ _ _ _ m2 (fin blen bs off1)); [exact PB2| exact BY2| exact MI2| exact MU2| exact WM2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma call_pv : forall (SA Fr item off0 : Z) (rnt : word) m1 mo1 g1 TRS1 B1 errv1 Fx fcx (h0 : word) (csa csb : list cell)
      x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    WGEOM sp LB SA Fr -> MID SA Fr m1 mo1 g1 ((item, 64) :: LB) TRS1 B1 errv1 ->
    SHCW m1 Fr PRO_SHB -> rw_cells asegs m1 Fr [C8 h0] ->
    rw_cells asegs m1 (Fr + 32) (pbuf_cells CA blen off0 0) -> 0 <= off0 <= blen ->
    rw_cells asegs m1 SA csa -> Z.of_nat (cells_size csa) = 24 -> rw_cells asegs m1 (SA + 24) [C8 rnt] ->
    rw_cells asegs m1 (SA + 32) csb -> SA + 32 + Z.of_nat (cells_size csb) = SP - 104 ->
    rw_cells asegs m1 (SP + -104) SAVW_ ->
    rw_cells asegs m1 item (node_cells 0 (wz 0) 0 0 (wz 0) 0 (wz 0) (wz 0) (wz 0) 0) -> item <> 0 ->
    Fagree F Fx -> frm0 fcx -> B - 448 <= B1 ->
    LSCPS asegs POST (WSTx SA Fr 0x82964 x1 x5 x6 x7 x10 (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 item) x13 x14 x15 x16 x17 (Z_to_bv 64 item) x28 x29 x30 x31 Fx fcx m1) mo1 g1.
  Proof.
    intros until x31. intros GE MD SHC HDR PB Ho CSA SZA RNT CSB SZB SAVW ND NZ FA FRM HB. lits. bandM. sepM.
    (nelimp GE 6%nat; intros GSA GAL FAL FLO FHI FBLK). (nelimp MD 8%nat; intros HL BY ERR MI ST DP GM TV).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof (FBLK D n IND) as FDD.
    pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INF : In (Fr, 1) [(Fr, 1)]) by (left; reflexivity).
    (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL INF) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 4%nat; intros I1 I2 I3 I4). try rewrite alloc_ceiling_eq in I4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in I1. bandM. sepM.
    assert (CC : chain_cells m1 [(SP, bv_unsigned ra, bv_unsigned s0)]).
    { apply chain_cells_frame1. unfold SAVEDW in SAVW.
      lazymatch type of SAVW with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
        pose proof (proj2 (proj1 (rw_cells_split_app m1 (SP + -104) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] rest) SAVW)) as S2 end.
      cbn [cells_size Cells.csize Nat.add] in S2. change (Z.of_nat 88) with 88 in S2. replace (SP + -104 + 88) with (SP + -16) in S2 by lia. exact S2. }
    assert (PSH : pbuf_sh m1 (Fr + 32)).
    { apply (shc_pbuf_sh m1 Fr (-15) (-15) (-15) (-15) (-13) (-13) (-13) (-13) (-13)); [unfold SHCW, PRO_SHB in SHC |- *; cbn [map] in SHC |- *; exact SHC| exact FAL| lia| lia]. }
    assert (PI : parse_inv AI TI m1 mo1 g1 sp0 SPB ((item, 64) :: LB) [] LB [(Fr, 1)] TRS1 np B1 item (Fr + 32) CA blen bs D n lo SA errv1).
    { split; [exact HL|]. split; [apply Permutation_refl|]. split; [exact IND|]. split; [lia|]. split; [lia|]. split; [exact BY|].
      split; [exact LEN|]. split; [exact BLEN|]. split; [unfold AERRNO, ATP; exact ERR|]. split; [exact MI|]. split; [exact ST|]. split; [alia|].
      split; [exact TV|]. split; [replace (Fr + 32 - 32) with Fr by lia; exact INF|]. split; [exact PSH|].
      repeat split; try assumption; try (cut_on [CEIL LO D1 GSA FLO NDB SP2 SP4 GAL] alia). }
    unfold WST. eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. change (Z_to_bv 64 535724) with (wz PARSE_VALUE).
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { pose proof (PV (Z.to_nat blen)) as PVS. unfold parse_value_at in PVS.
      sepM. eapply PVS with (U := item) (P := Fr + 32) (off := off0) (depth := 0) (nx := 0) (ty := 0) (ky := 0) (CH := [(SP, bv_unsigned ra, bv_unsigned s0)]);
        clear PVS; rewrite ?unsigned_lit by (lia_on CEIL LO SP4 SP5 TOPR GSA);
        first [ exact PI | unfold pbuf_at; exact PB | eqcells ND | exact FRM | exact TP | reflexivity | exact CC
              | unfold lf_room; replace (lf_count 2 [(Fr, 1)]) with 0 by reflexivity; pose proof fcap_vals; (cut_to Ho GAL H; lia)
              | apply not_pc0_high; lia
              | intros bb; specialize (STPV bb); unfold tr_pv_pwlo in STPV; unfold pv_trace; cbn [map fr_ra fst snd]; exact STPV
              | exact STPO | exact STC
              | lazymatch goal with |- chain_ok _ _ _ => cbn; split; [lia|]; split; [Z.div_mod_to_equations; lia|]; split; [lia|]; split; [lia|]; split; [exact RA2|]; split; [lia|]; split; [lia| exact I] end
              | lazymatch goal with |- chain_link _ _ _ => cbn; split; [reflexivity| lia] end
              | clear -HB BPRE Ho BLEN LEN; blia
              | alia
              | lia ]. }
    cbv beta. intros ms5 mo5 g5 PO'.
    (nelim PO' 36%nat; intros t0' t1' t2' a0' a1_ a2_ a3_ a4_ a5_ a6_ a7' t3' t4' t5' t6' F5 fc5 m5 r off5 depth5 LB5 X5 TRS5 B5 errv5 -> -> FA5 FRM5 PI5 PR5 GM5 _ PB5 RES)
.
    rewrite ?unsigned_lit in PI5, PR5 by lia.
    replace (ret_pc (Z_to_bv 64 0x8296c)) with (Z_to_bv 64 0x8296c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim PI5 16%nat; intros HL5 HP5 _ _ _ BY5 _ _ ERR5 MI5 ST5 _ TV5 _ PSH5 _).
    cbn [app] in HP5.
    (* [comment removed for export] *)
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR5) in CSA; [| lia| lia| alia| alia].
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR5) in RNT; [| lia| cbn; lia| alia| alia].
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR5) in CSB; [| lia| lia| alia| alia].
    apply (ppres_rw_cells_stack _ _ _ _ _ _ _ _ _ PR5) in SAVW; [| lia| unfold SAVEDW; cbn; lia| alia| alia].
    assert (HDR5 : rw_cells asegs m5 Fr [C8 h0]).
    { eapply rw_cells_magree; [exact PR5| exact HDR|]. cbn. intros a Ha. split; [| unfold AERRNO, ATP; lia].
      do 3 right. left. exists Fr, 1. split; [exact INF|]. left. change (fsz 1) with 128. lia. }
    assert (SHC5 : SHCW m5 Fr PRO_SHB).
    { unfold SHCW in SHC |- *. eapply rw_cells_magree; [exact PR5| exact SHC|]. rewrite cells_size_mapC1. cbn [length PRO_SHB]. intros a Ha.
      split; [| unfold AERRNO, ATP; lia]. do 3 right. left. exists Fr, 1. split; [exact INF|]. right. rewrite <- SH_shiftr. change (fsz 1) with 128. lia. }
    assert (DP5 : dpres sp0 LB [] SP m m5).
    { eapply dpres_trans; [exact DP|]. intros a Ha nelH_; (nelim nelH_ 4%nat; intros Hc He Hg0 Hg1). apply PR5; [exact Ha|]. split; [| split; [exact He|]].
      - destruct Hc as [Hs|[Hi|[Hb|[(Fr' & k & [] & _)|Hsh]]]]; [left; lia| right; left; exact Hi| right; right; left; exact Hb| do 4 right; exact Hsh].
      - destruct Hc as [Hs|[Hi|[(A & n0 & Hin & Hr)|[(Fr' & k & [] & _)|Hsh]]]]; try (cut_to CEIL LO D1 GSA FLO FHI NDB Hs; lia).
        + pose proof (aclient_image_lt a Hi). lia.
        + destruct (FBLK A n0 Hin); (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact Hin)) 4%nat; intros R1 _ _ R4); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1; try rewrite alloc_ceiling_eq in R4; lia.
        + unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. (lia_on NZ BMf NDB Hsh H H0 H4 H5). }
    assert (MD5 : MID SA Fr m5 mo5 g5 LB5 TRS5 B5 errv5).
    { split; [exact HL5|]. split; [exact BY5|]. split; [exact ERR5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact DP5|].
      split; [eapply gmono_trans; [exact GM| exact GM5]| exact TV5]. }
    pose proof PB5 as PB5'. unfold pbuf_at, pbuf_cells, wz in PB5'.
    eapply lscps_step_evt. cbv beta delta [mkR]. unfold wz.
    destruct RES as [(-> & -> & ND5 & HB5) | (-> & -> & Ho5 & HB5 & HX & ch & ty' & vs & vi' & vd' & dc & Bv & Bc & -> & ND5 & HT & SV & CH & Hdc)].
    - (* [comment removed for export] *)
      assert (CH1 : cj_chain CJ_ANY m5 1 item ((item, 64) :: [] ++ [] ++ [])).
      { eapply cj_chain_one; [exact NZ| exact ND5| lia| exact I| apply cj_str_null| apply cj_str_null| apply cj_chain_nil]. }
      cbn [app] in CH1, HP5.
      zstep. if_true. apply evt_done.
      eapply (DOC_FAIL_DELETE SA Fr item CJ_ANY 1%nat [(item, 64)] m5 mo5 g5 LB5 TRS5 B5 errv5 F5 fc5 PRO_SHB h0 (csa ++ [C8 rnt] ++ csb));
        [exact GE| exact MD5| exact CH1| cbn [app]; exact HP5| lia| exact SHC5| reflexivity| exact HDR5| exact PB5'| | | exact SAVW| eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5
        | cbn [length]; clear -HB HB5 BPRE Ho BLEN LEN; blia].
      + apply (proj1 (locals_join m5 SA csa rnt csb CSA SZA RNT CSB)).
      + pose proof (proj2 (locals_join m5 SA csa rnt csb CSA SZA RNT CSB)). lia.
    - (* [comment removed for export] *)
      assert (CHR : cj_chain CJ_PRINTABLE m5 (S dc) item ((item, 64) :: Bv ++ [] ++ Bc)).
      { eapply cj_chain_one; [exact NZ| exact ND5| apply CJ_PRINTABLE_range; exact HT| exact HT| exact SV| apply cj_str_null| exact CH]. }
      cbn [app] in CHR.
      zstep. if_false. apply evt_done.
      eapply (null_check SA Fr item off5 rnt ((item, 64) :: Bv ++ Bc) (S dc) ch ty' vs vi' vd' m5 mo5 g5 LB5 TRS5 B5 errv5 F5 fc5 h0 csa csb);
        [exact GE| exact MD5| exact CHR| exact HP5| lia| cbn [length]; clear -HX Ho5 Ho; unfold cblock in *; lia| exact NZ| eqcells ND5| exact SHC5| exact HDR5| exact PB5| lia
        | exact CSA| exact SZA| exact RNT| exact CSB| exact SZB| exact SAVW| eapply Fagree_trans; [exact FA| exact FA5]| exact FRM5
        | cbn [length]; clear -HB HB5 HX BPRE Ho Ho5 BLEN LEN; blia].
  Qed.

  (* [comment removed for export] *)
  Theorem pwlo_body : PWLO_BODY AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m g sp0 SPB LB np B CA blen bs lo.
  Proof.
    unfold PWLO_BODY. intros until x31. intros GE MD SHC HDR PB CSA SZA RNT CSB SZB SAVW ND NZ FA FRM. lits. bandM. sepM.
    (nelimp GE 6%nat; intros GSA GAL FAL FLO FHI FBLK). (nelimp MD 8%nat; intros HL BY ERR MI ST DP GM TV).
    unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in FLO. bandM. sepM. try rewrite alloc_ceiling_eq in FHI. unfold AERRNO, ATP in ERR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. pose proof (FBLK D n IND) as FDD.
    pose proof (rw_cells_bound asegs _ _ _ ND) as NDB. rewrite node_cells_size in NDB.
    pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR. change (2^3) with 8 in SHFR.
    assert (INF : In (Fr, 1) [(Fr, 1)]) by (left; reflexivity).
    (nelim (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL INF) 8%nat; intros _ _ _ _ _ _ _ FD). change (fsz 1) with 128 in FD.
    pose proof (FD item 64 ltac:(left; reflexivity)) as IFd.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) 4%nat; intros I1 I2 I3 I4). try rewrite alloc_ceiling_eq in I4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in I1. bandM. sepM.
    pose proof (art_text_sh AI _ _ _ _ _ _ _ _ _ D n CA blen HL ltac:(right; exact IND) DCA CAD) as TSH.
    unfold SHCW, PRO_SHB in SHC. cbn [map] in SHC. unfold node_cells, wz in ND.
    (* [comment removed for export] *)
    assert (JA : forall y10 y11 y12 y13 mm o0,
      rw_cells asegs mm (Fr + 32) (pbuf_cells CA blen o0 0) -> 0 <= o0 <= blen -> mem_inv asegs mm ->
      munch [(Fr + 48, Fr + 56)] m5 mm -> wmono asegs m5 mm ->
      evt asegs (fun ms' => LSCPS asegs POST ms' mo5 g5)
        (WSTx SA Fr 0x82a38 x1 x5 x6 x7 y10 y11 y12 y13 x14 x15 x16 x17 (Z_to_bv 64 item) x28 x29 x30 x31 Fx fcx mm)).
    { intros y10 y11 y12 y13 mm o0 PBm Ho MIm MUm WMm. unfold WST.
      pose proof BY as BYm. trc BYm MUm WMm.
      pose proof PBm as PBm'. unfold pbuf_cells, wz in PBm.
      (* [comment removed for export] *)
      assert (CALL : forall x10' x11' x14' x15' x16' x17' m2 o1, ws_memW Fr m5 m2 o1 -> 0 <= o1 <= blen ->
        evt asegs (fun ms' => LSCPS asegs POST ms' mo5 g5)
          (WSTx SA Fr 0x82c60 x1 x5 x6 x7 x10' x11' (Z_to_bv 64 item) (Z_to_bv 64 CA) x14' x15' x16' x17' (Z_to_bv 64 item) x28 x29 x30 x31 Fx fcx m2)).
      { intros x10' x11' x14' x15' x16' x17' m2 o1 (PB2 & BY2 & MI2 & MU2 & WM2) Ho1. unfold WST.
        pose proof HDR as HDR2. trc HDR2 MU2 WM2.
        pose proof SHC as SHC2. eapply rw_cells_transport in SHC2; [| exact MU2| exact WM2| cbn [disjoint_from cells_size Cells.csize Nat.add length]; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia].
        pose proof CSA as CSA2. trc CSA2 MU2 WM2. pose proof RNT as RNT2. trc RNT2 MU2 WM2. pose proof CSB as CSB2. trc CSB2 MU2 WM2.
        pose proof SAVW as SAVW2. unfold SAVEDW in SAVW2. trc SAVW2 MU2 WM2. pose proof ERR as ERR2. trc ERR2 MU2 WM2. pose proof ST as ST2. trc ST2 MU2 WM2.
        pose proof ND as ND2. trc ND2 MU2 WM2.
        assert (HL2 : ART AI sp0 SPB ((item, 64) :: LB) [(Fr, 1)] TRS5 (B - 448) m2 mo5 g5).
        { eapply (art_frame AI); [exact HL| exact MU2| exact WM2|]. constructor; [| constructor].
          do 8 right. left. exists Fr, 1. cbn. split; [left; reflexivity|]. change (fsz 1) with 128. lia. }
        assert (DP2 : dpres sp0 LB [] SP m m2).
        { eapply (dpres_step sp m sp0 LB); [exact DP| exact MU2| exact WM2|]. intros a Ha Hda. apply (doc_addr_lits sp sp0 LB a) in Hda. cbn.
          destruct Hda as [Hs|[Hi|[(A & n0 & Hin & Hr)|Hsh]]]; try (cut_to CEIL LO D1 GSA FLO FHI NDB Hs Hi; lia).
          - destruct (FBLK A n0 Hin); (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; exact Hin)) 4%nat; intros R1 _ _ R4); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1; try rewrite alloc_ceiling_eq in R4; lia.
          - unfold SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia. }
        zstep. zstep. apply evt_done.
        eapply (call_pv SA Fr item o1 rnt m2 mo5 g5 TRS5 (B - 448) errv5 Fx fcx h0 csa csb);
          [exact GE| | unfold SHCW, PRO_SHB; cbn [map]; exact SHC2| exact HDR2| exact PB2| exact Ho1| exact CSA2| exact SZA| exact RNT2| exact CSB2| exact SZB
          | unfold SAVEDW; exact SAVW2| unfold node_cells, wz; exact ND2| exact NZ| exact FA| exact FRM| lia].
        split; [exact HL2|]. split; [exact BY2|]. split; [unfold AERRNO, ATP; exact ERR2|]. split; [exact MI2|]. split; [exact ST2|].
        split; [exact DP2|]. split; [exact GM| exact TV]. }
      unfold WST in CALL.
      zstep. zstep. zstep. if_cases KC'; zify_cond KC'; [exfalso; lia|].
      zstep. zstep. zstep. if_cases Kge; zify_cond Kge.
      - eapply (CALL _ _ _ _ _ _ mm o0); [| lia]. split; [exact PBm'|]. split; [exact BYm|]. split; [exact MIm|]. split; [exact MUm| exact WMm].
      - zstep. pose proof (fin_range bs blen o0 LEN ltac:(lia)) as FRG.
        eapply evt_cut; [eapply (wsA SA Fr m5 GE TSH (Z.to_nat (blen - o0)) o0 mm); [lia| lia| exact PBm'| exact BYm| exact MIm| exact MUm| exact WMm]|].
        intros ms' nelH_; (nelim nelH_ 8%nat; intros x10' x11' x14' x16' x17' m2 -> WSM).
        eapply (CALL _ _ _ _ _ _ m2 (fin blen bs o0)); [exact WSM| lia]. }
    unfold WST in JA. pose proof PB as PB'. unfold pbuf_cells, wz in PB. unfold WST.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. if_cases KC; zify_cond KC; [exfalso; lia|].
    zstep. zstep. if_true.
    zstep. zstep. zstep. if_cases K5; zify_cond K5.
    { (* [comment removed for export] *) eapply (JA _ _ _ _ m5 0); [exact PB'| lia| exact MI| apply munch_refl| apply wmono_refl]. }
    (* [comment removed for export] *)
    destruct (nth_error bs 0) as [b0|] eqn:Hn0; [| apply nth_error_None in Hn0; lia].
    pose proof (u8ro_read asegs _ CA bs 0 b0 _ BY Hn0 ltac:(lia) eq_refl) as RD0. pose proof (byte_range b0) as Rb0.
    zstep. zstep. pose proof (TSH CA ltac:(lia)) as CK0. sepM. asan_chk CK0.
    zstep. clear RD0. zstep. zstep. if_cases KB0; zify_cond KB0.
    { eapply (JA _ _ _ _ m5 0); [exact PB'| lia| exact MI| apply munch_refl| apply wmono_refl]. }
    (* [comment removed for export] *)
    zstep.
    destruct (nth_error bs 1) as [b1|] eqn:Hn1; [| apply nth_error_None in Hn1; lia].
    pose proof (u8ro_read asegs _ CA bs 1 b1 _ BY Hn1 ltac:(lia) eq_refl) as RD1. pose proof (byte_range b1) as Rb1.
    zstep. zstep. pose proof (TSH (CA + 1) ltac:(lia)) as CK1. sepM. asan_chk CK1.
    zstep. clear RD1. zstep. zstep. if_cases KB1; zify_cond KB1.
    { eapply (JA _ _ _ _ m5 0); [exact PB'| lia| exact MI| apply munch_refl| apply wmono_refl]. }
    (* [comment removed for export] *)
    zstep.
    destruct (nth_error bs 2) as [b2|] eqn:Hn2; [| apply nth_error_None in Hn2; lia].
    pose proof (u8ro_read asegs _ CA bs 2 b2 _ BY Hn2 ltac:(lia) eq_refl) as RD2. pose proof (byte_range b2) as Rb2.
    zstep. zstep. pose proof (TSH (CA + 2) ltac:(lia)) as CK2. sepM. asan_chk CK2.
    zstep. clear RD2. zstep. zstep. if_cases KB2; zify_cond KB2.
    { eapply (JA _ _ _ _ m5 0); [exact PB'| lia| exact MI| apply munch_refl| apply wmono_refl]. }
    (* [comment removed for export] *)
    zstep. clear PB'.
    pose proof (munch_refl [(Fr + 48, Fr + 56)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    zstep. fix_lit_store.
    eapply (JA _ _ _ _ _ 3); [unfold pbuf_cells, wz; exact PB| lia| exact MI| exact MU| exact WM].
  Qed.
End WLB.


End CeilWrap.
End CJ_pwlopts_B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_pwlopts_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pwlopts_A.
Import CJ_pwlopts_B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Theorem parse_wlopts_spec : forall (AI : art_iface) (TI : trs_iface),
  asan_memset_spec -> asan_memcpy_spec ->
  cjson_delete_stmt AI TI -> parse_value_stmt AI TI ->
  parse_wlopts_stmt AI TI.
Proof.
  intros AI TI MEMSET MEMCPY DEL PV. pose proof (stkmalloc_stmt'_holds AI 1 ltac:(left; reflexivity)) as STK1. unfold parse_wlopts_stmt.
  intros until errv. intros PRE DCA CAD BY LEN BLEN -> -> ->.
  eapply (pwlo_pro AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo g sp0 SPB LB TRS np B CA blen bs D n lo errv
            PRE DCA CAD BY LEN BLEN STK1 MEMSET MEMCPY).
  apply (pwlo_body AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo g sp0 SPB LB TRS np B CA blen bs D n lo errv
           PRE DCA CAD LEN BLEN DEL PV).
Qed.


End CeilWrap.
