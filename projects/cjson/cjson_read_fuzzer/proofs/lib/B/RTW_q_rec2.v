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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_ms.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_q_merge1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_ms OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AQMERGE : Z := 0x33ebc.

(* [comment removed for export] *)
Lemma mg_copy_spec : forall (cnt : nat)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (cA nA cntc cntn i : Z) (sl : Z -> Z),
  Z.of_nat cnt = cntn - i -> 0 <= i < cntn -> 0 <= cntc -> cntc + cntn <= QBATCH_CAP ->
  mem_inv bsegs m ->
  t2 = wz (nA + 24 + 8 * i) -> t3 = wz (cA + 24 + 8 * (cntc + i)) -> t4 = wz (nA + 24 + 8 * cntn) ->
  AIMG_HI <= cA -> cA + QBATCH_SIZE <= alloc_ceiling -> AIMG_HI <= nA -> nA + QBATCH_SIZE <= alloc_ceiling ->
  (cA + QBATCH_SIZE <= nA \/ nA + QBATCH_SIZE <= cA) ->
  (forall j, 0 <= j < cntn -> 0 <= sl j < 2^64) ->
  (forall j, 0 <= j < cntn -> rw_cells bsegs m0 (nA + 24 + 8 * j) [C8 (wz (sl j))]) ->
  munch [(cA + 24 + 8 * cntc, cA + 24 + 8 * (cntc + cntn))] m0 m -> wmono bsegs m0 m ->
  (forall j, 0 <= j < i -> rw_cells bsegs m (cA + 24 + 8 * (cntc + j)) [C8 (wz (sl j))]) ->
  vis m cA (cA + QBATCH_SIZE) ->
  evt bsegs (fun ms' => exists (t5' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 (wz (nA + 24 + 8 * cntn)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    (wz (cA + 24 + 8 * (cntc + cntn))) t4 t5' t6)
               F (wz 0x33f40) fc None m' (seg_rom bsegs)
      /\ munch [(cA + 24 + 8 * cntc, cA + 24 + 8 * (cntc + cntn))] m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
      /\ (forall j, 0 <= j < cntn -> rw_cells bsegs m' (cA + 24 + 8 * (cntc + j)) [C8 (wz (sl j))])
      /\ vis m' cA (cA + QBATCH_SIZE))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33f2c) fc None m (seg_rom bsegs)).
Proof.
  induction cnt as [|cnt IH]; intros until sl;
    intros Hcnt Hi Hc CAP MI -> -> -> HC1 HC2 HN1 HN2 DJ SLR SRC MU WM DONE V; [lia|].
  unfold QBATCH_SIZE, QBATCH_CAP, AIMG_HI in *. idtac.
  (* [comment removed for export] *)
  assert (SRCi : rw_cells bsegs m (nA + 24 + 8 * i) [C8 (wz (sl i))]).
  { eapply rw_cells_transport; [exact (SRC i ltac:(lia))| exact MU| exact WM| cbn; lia]. }
  destruct (vis_cell m cA (cA + 8192) (cA + 24 + 8 * (cntc + i)) 8 V ltac:(lia) ltac:(cbn; lia)) as [jd DST].
  pose proof (SLR i ltac:(lia)) as SLi.
  pose proof (munch_refl [(cA + 24 + 8 * (cntc + i), cA + 24 + 8 * (cntc + i) + 8)] m) as MU1. pose proof (wmono_refl bsegs m) as WM1.
  set (src := nA + 24 + 8 * i) in *. set (dst := cA + 24 + 8 * (cntc + i)) in *.
  cbv beta delta [wz] in *. leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mS := mx) in * end.
  assert (DONE' : forall j, 0 <= j < i + 1 -> rw_cells bsegs mS (cA + 24 + 8 * (cntc + j)) [C8 (Z_to_bv 64 (sl j))]).
  { intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
    - fold dst. assumption.
    - eapply rw_cells_transport; [exact (DONE j ltac:(lia))| exact MU1| exact WM1| cbn; subst dst; lia]. }
  lstep; if_cases KE; zify_cond KE.
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 (src + 8)) with (Z_to_bv 64 (nA + 24 + 8 * (i + 1)) : word) by (subst src; f_equal; lia).
    replace (Z_to_bv 64 (dst + 8)) with (Z_to_bv 64 (cA + 24 + 8 * (cntc + (i + 1))) : word) by (subst dst; f_equal; lia).
    eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 mS cA nA cntc cntn (i + 1) sl);
      try reflexivity; try eassumption; unfold AIMG_HI, QBATCH_SIZE, QBATCH_CAP in *; idtac; try lia.
  - (* [comment removed for export] *)
    assert (i + 1 = cntn) by (subst src; lia).
    replace (Z_to_bv 64 (src + 8)) with (Z_to_bv 64 (nA + 24 + 8 * cntn) : word) by (subst src; f_equal; lia).
    replace (Z_to_bv 64 (dst + 8)) with (Z_to_bv 64 (cA + 24 + 8 * (cntc + cntn)) : word) by (subst dst; f_equal; lia).
    replace (i + 1) with cntn in DONE' by lia.
    apply evt_done. eexists. exists mS. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact DONE'| exact V].
Qed.

(* [comment removed for export] *)
Lemma mg_bodyA_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cA nA cntc cntn szc szn nn : Z) (sl : Z -> Z),
  mem_inv bsegs m ->
  a4 = wz cA -> t0 = wz nA -> a5 = wz 1021 ->
  0 <= cntc -> 0 <= cntn -> cntc + cntn <= QBATCH_CAP -> 8192 <= szc < 2^62 -> 0 <= szn < 2^62 -> 0 <= nn < 2^64 ->
  AIMG_HI <= cA -> cA + QBATCH_SIZE <= alloc_ceiling -> AIMG_HI <= nA -> nA + QBATCH_SIZE <= alloc_ceiling ->
  (cA + QBATCH_SIZE <= nA \/ nA + QBATCH_SIZE <= cA) ->
  (forall j, 0 <= j < cntn -> 0 <= sl j < 2^64) ->
  (forall j, 0 <= j < cntn -> rw_cells bsegs m (nA + 24 + 8 * j) [C8 (wz (sl j))]) ->
  rw_cells bsegs m cA [C8 (wz nA); C8 (wz szc); C8 (wz cntc)] ->
  rw_cells bsegs m nA [C8 (wz nn); C8 (wz szn); C8 (wz cntn)] ->
  vis m cA (cA + QBATCH_SIZE) ->
  evt bsegs (fun ms' => exists (t2' t3' t4' t5' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 (wz (cntc + cntn)) t2' s0 s1 a0 a1 a2 (wz szc) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6)
               F (wz 0x33f40) fc None m' (seg_rom bsegs)
      /\ munch [(cA + 24 + 8 * cntc, cA + 24 + 8 * (cntc + cntn))] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ (forall j, 0 <= j < cntn -> rw_cells bsegs m' (cA + 24 + 8 * (cntc + j)) [C8 (wz (sl j))])
      /\ rw_cells bsegs m' cA [C8 (wz nA); C8 (wz szc); C8 (wz cntc)]
      /\ rw_cells bsegs m' nA [C8 (wz nn); C8 (wz szn); C8 (wz cntn)]
      /\ vis m' cA (cA + QBATCH_SIZE))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33ef4) fc None m (seg_rom bsegs)).
Proof.
  intros until sl. intros MI -> -> -> Hc Hn CAP Hszc Hszn Hnn HC1 HC2 HN1 HN2 DJ SLR SRC CC NC V.
  pose proof (munch_refl [(cA + 24 + 8 * cntc, cA + 24 + 8 * (cntc + cntn))] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold QBATCH_SIZE, QBATCH_CAP, AIMG_HI in *. idtac. cbv beta delta [wz] in *. leaf_prep.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  rewrite (Z.shiftr_div_pow2 szc 13) by lia. change (2 ^ 13) with 8192.
  assert (1 <= szc / 8192) by (apply Z.div_le_lower_bound; lia).
  lstep; if_lia. (* [comment removed for export] *)
  destruct (Z.eq_dec cntn 0) as [E0|NE0].
  - subst cntn. lstep; if_lia. (* [comment removed for export] *)
    try replace (0 + cntc) with cntc by lia. rewrite (Z.add_0_r cntc) in MU.
    apply evt_done. nexists 4%nat. exists m. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [intros j Hj; lia|].
    split; [exact CC|]. split; [exact NC| exact V].
  - lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) rewrite (Z.shiftl_mul_pow2 cntc 3) by lia. change (2 ^ 3) with 8.
    lstep. (* [comment removed for export] *) rewrite (Z.shiftl_mul_pow2 cntn 3) by lia.
    lstep. lstep. lstep. (* [comment removed for export] *)
    replace (cA + cntc * 8 + 24) with (cA + 24 + 8 * (cntc + 0)) by lia.
    replace (nA + 24 + cntn * 8) with (nA + 24 + 8 * cntn) by lia.
    replace (Z_to_bv 64 (nA + 24)) with (Z_to_bv 64 (nA + 24 + 8 * 0) : word) by (f_equal; lia).
    eapply evt_cut.
    { eapply (mg_copy_spec (Z.to_nat cntn) ra sp gp tp _ _ _ s0 s1 a0 a1 a2 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ t6 F fc m m cA nA cntc cntn 0 sl);
        try reflexivity; try eassumption; unfold AIMG_HI, QBATCH_SIZE, QBATCH_CAP; idtac; try lia; try (intros j Hj; lia). }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 8%nat; intros t5' m' -> MU' WM' MI' DONE V').
    replace (cntn + cntc) with (cntc + cntn) by lia.
    assert (CC' : rw_cells bsegs m' cA [C8 (Z_to_bv 64 nA); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cntc)]).
    { eapply rw_cells_transport; [exact CC| exact MU'| exact WM'| cbn; lia]. }
    assert (NC' : rw_cells bsegs m' nA [C8 (Z_to_bv 64 nn); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cntn)]).
    { eapply rw_cells_transport; [exact NC| exact MU'| exact WM'| cbn; lia]. }
    apply evt_done. nexists 4%nat. exists m'. split; [reflexivity|].
    repeat (split; [eassumption|]). exact V'.
Qed.

(* [comment removed for export] *)
Lemma mg_bodyBE_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cA nA cntc cntn szc szn nn ng gf gl B ext tf tlA tb tmpA : Z),
  mem_inv bsegs m ->
  a0 = wz (A_QUAR + 160) -> a1 = wz tmpA -> a2 = wz ext -> a3 = wz szc -> a4 = wz cA -> a6 = wz (-8192) -> a7 = wz 8192 ->
  t0 = wz nA -> t1 = wz (cntc + cntn) ->
  0 <= cntc + cntn < 2^62 -> 8192 <= szc -> 8192 <= szn -> szc + szn < 2^62 -> 0 <= nn < 2^64 -> 1 <= ng < 2^62 ->
  0 <= gl < 2^64 -> 0 <= ext -> ext + 8192 < 2^62 -> 0 <= tb -> tb + 8192 < 2^62 ->
  AIMG_HI <= cA -> cA + QBATCH_SIZE <= alloc_ceiling -> AIMG_HI <= nA -> nA + QBATCH_SIZE <= alloc_ceiling ->
  (cA + QBATCH_SIZE <= nA \/ nA + QBATCH_SIZE <= cA) ->
  alloc_ceiling <= tmpA -> tmpA + 32 <= 2^64 ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz B)] ->
  rw_cells bsegs m cA [C8 (wz nA); C8 (wz szc); C8 (wz cntc)] ->
  rw_cells bsegs m nA [C8 (wz nn); C8 (wz szn); C8 (wz cntn)] ->
  rw_cells bsegs m tmpA [C8 (wz 0); C8 (wz tf); C8 (wz tlA); C8 (wz tb)] ->
  evt bsegs (fun ms' => exists (a3' t1' t2' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp (wz nn) t1' t2' s0 s1 a0 a1 (wz (ext + 8192)) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6)
               F (wz 0x33fd4) fc None m' (seg_rom bsegs)
      /\ munch [(cA, cA + 24); (nA, nA + 24); (A_QUAR + 160, A_QUAR + 192); (tmpA, tmpA + 32)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (A_QUAR + 160) [C8 (wz (ng - 1)); C8 (wz gf); C8 (wz (if gl =? nA then cA else gl)); C8 (wz B)]
      /\ rw_cells bsegs m' cA [C8 (wz nn); C8 (wz (szc + szn - 8192)); C8 (wz (cntc + cntn))]
      /\ rw_cells bsegs m' nA [C8 (wz 0); C8 (wz 8192); C8 (wz 0)]
      /\ rw_cells bsegs m' tmpA [C8 (wz 1); C8 (wz nA); C8 (wz nA); C8 (wz (tb + 8192))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33f40) fc None m (seg_rom bsegs)).
Proof.
  intros until tmpA. intros MI -> -> -> -> -> -> -> -> -> Hcc Hszc Hszn Hss Hnn Hng Hgl Hext Hext2 Htb Htb2 HC1 HC2 HN1 HN2 DJ HT1 HT2 QH CC NC TM.
  pose proof (munch_refl [(cA, cA + 24); (nA, nA + 24); (A_QUAR + 160, A_QUAR + 192); (tmpA, tmpA + 32)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold QBATCH_SIZE, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in *.
  replace (681520 + 160) with 681680 in * by reflexivity. replace (681520 + 192) with 681712 in MU by reflexivity.
  leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try replace (Z_to_bv 64 (szc + szn + -8192)) with (Z_to_bv 64 (szc + szn - 8192) : word) by (f_equal; lia).
  try replace (Z_to_bv 64 (szc + szn + 18446744073709543424)) with (Z_to_bv 64 (szc + szn - 8192) : word)
    by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  destruct (Z.eq_dec gl nA) as [EG|NG].
  - subst gl. lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. rewrite Z.eqb_refl.
    replace (ng + -1) with (ng - 1) in * by lia.
    finish; eassumption.
  - lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia.
    replace (gl =? nA) with false by (symmetry; apply Z.eqb_neq; exact NG).
    replace (ng + -1) with (ng - 1) in * by lia.
    finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma mg_bodyBN_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cA nA cntc cntn szc szn nn ng gf gl B ext tsz tf tlA tb tmpA : Z),
  mem_inv bsegs m ->
  a0 = wz (A_QUAR + 160) -> a1 = wz tmpA -> a2 = wz ext -> a3 = wz szc -> a4 = wz cA -> a6 = wz (-8192) -> a7 = wz 8192 ->
  t0 = wz nA -> t1 = wz (cntc + cntn) ->
  0 <= cntc + cntn < 2^62 -> 8192 <= szc -> 8192 <= szn -> szc + szn < 2^62 -> 0 <= nn < 2^64 -> 1 <= ng < 2^62 ->
  0 <= gl < 2^64 -> 0 <= ext -> ext + 8192 < 2^62 -> 0 <= tb -> tb + 8192 < 2^62 -> 1 <= tsz < 2^62 -> 0 <= tf < 2^64 ->
  AIMG_HI <= cA -> cA + QBATCH_SIZE <= alloc_ceiling -> AIMG_HI <= nA -> nA + QBATCH_SIZE <= alloc_ceiling ->
  AIMG_HI <= tlA -> tlA + QBATCH_SIZE <= alloc_ceiling ->
  (cA + QBATCH_SIZE <= nA \/ nA + QBATCH_SIZE <= cA) -> (cA + QBATCH_SIZE <= tlA \/ tlA + QBATCH_SIZE <= cA) ->
  (nA + QBATCH_SIZE <= tlA \/ tlA + QBATCH_SIZE <= nA) ->
  alloc_ceiling <= tmpA -> tmpA + 32 <= 2^64 ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz B)] ->
  rw_cells bsegs m cA [C8 (wz nA); C8 (wz szc); C8 (wz cntc)] ->
  rw_cells bsegs m nA [C8 (wz nn); C8 (wz szn); C8 (wz cntn)] ->
  rw_cells bsegs m tmpA [C8 (wz tsz); C8 (wz tf); C8 (wz tlA); C8 (wz tb)] ->
  rw_cells bsegs m tlA [C8 (wz 0)] ->
  evt bsegs (fun ms' => exists (a3' t1' t2' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp (wz nn) t1' t2' s0 s1 a0 a1 (wz (ext + 8192)) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6)
               F (wz 0x33fd4) fc None m' (seg_rom bsegs)
      /\ munch [(cA, cA + 24); (nA, nA + 24); (A_QUAR + 160, A_QUAR + 192); (tmpA, tmpA + 32); (tlA, tlA + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (A_QUAR + 160) [C8 (wz (ng - 1)); C8 (wz gf); C8 (wz (if gl =? nA then cA else gl)); C8 (wz B)]
      /\ rw_cells bsegs m' cA [C8 (wz nn); C8 (wz (szc + szn - 8192)); C8 (wz (cntc + cntn))]
      /\ rw_cells bsegs m' nA [C8 (wz 0); C8 (wz 8192); C8 (wz 0)]
      /\ rw_cells bsegs m' tmpA [C8 (wz (tsz + 1)); C8 (wz tf); C8 (wz nA); C8 (wz (tb + 8192))]
      /\ rw_cells bsegs m' tlA [C8 (wz nA)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33f40) fc None m (seg_rom bsegs)).
Proof.
  intros until tmpA. intros MI -> -> -> -> -> -> -> -> -> Hcc Hszc Hszn Hss Hnn Hng Hgl Hext Hext2 Htb Htb2 Htsz Htf HC1 HC2 HN1 HN2 HL1 HL2 DJ DJ2 DJ3 HT1 HT2 QH CC NC TM TL.
  pose proof (munch_refl [(cA, cA + 24); (nA, nA + 24); (A_QUAR + 160, A_QUAR + 192); (tmpA, tmpA + 32); (tlA, tlA + 8)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold QBATCH_SIZE, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in *.
  replace (681520 + 160) with 681680 in * by reflexivity. replace (681520 + 192) with 681712 in MU by reflexivity.
  leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try replace (Z_to_bv 64 (szc + szn + -8192)) with (Z_to_bv 64 (szc + szn - 8192) : word) by (f_equal; lia).
  try replace (Z_to_bv 64 (szc + szn + 18446744073709543424)) with (Z_to_bv 64 (szc + szn - 8192) : word)
    by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  destruct (Z.eq_dec gl nA) as [EG|NG].
  - subst gl. lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. rewrite Z.eqb_refl.
    replace (ng + -1) with (ng - 1) in * by lia.
    finish; eassumption.
  - lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia.
    replace (gl =? nA) with false by (symmetry; apply Z.eqb_neq; exact NG).
    replace (ng + -1) with (ng - 1) in * by lia.
    finish; eassumption.
Qed.

(* [comment removed for export] *)
Definition mg_frame (j0 : list byte) (vra : word) : list cell := [CB 8 j0; C8 vra].

(* [comment removed for export] *)
Lemma mg_entry2_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (szc cntc : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ng gf gl B nn lo : Z),
  mem_inv bsegs m ->
  a0 = wz (A_QUAR + 160) ->
  0 < gf < 2^64 -> 0 < nn < 2^64 -> AIMG_HI <= gf -> gf + QBATCH_SIZE <= alloc_ceiling ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz B)] ->
  rw_cells bsegs m gf [C8 (wz nn); C8 szc; C8 cntc] ->
  evt bsegs (fun ms' => exists (j0 : list byte) (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 16)) gp tp (wz nn) t1 t2 s0 s1 a0 a1 (wz 0) a3 (wz gf) (wz 1021) (wz (-8192)) (wz 8192)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33ef4) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp - 16)
      /\ rw_cells bsegs m' (bv_unsigned sp - 16) (mg_frame j0 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQMERGE) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI -> Hgf Hnn HG1 HG2 ST HCL LO QH GC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold AQMERGE, mg_frame, QBATCH_SIZE, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in *.
  replace (681520 + 160) with 681680 in * by reflexivity.
  leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma mg_entry1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (szc cntc : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ng gf gl B lo : Z),
  mem_inv bsegs m ->
  a0 = wz (A_QUAR + 160) ->
  0 < gf < 2^64 -> 0 <= B < 2^63 -> AIMG_HI <= gf -> gf + QBATCH_SIZE <= alloc_ceiling ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp -> bv_unsigned sp <= 2^64 ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz B)] ->
  rw_cells bsegs m gf [C8 (wz 0); C8 szc; C8 cntc] ->
  evt bsegs (fun ms' => exists (a1' a4' t0' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 a1' a2 a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (A_QUAR + 184, A_QUAR + 192)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz B)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQMERGE) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI -> Hgf HB HG1 HG2 ST HCL LO SPH QH GC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (681704, 681712)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold AQMERGE, QBATCH_SIZE, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in *.
  replace (681520 + 160) with 681680 in * by reflexivity.
  leaf_prep.
  carve_frame 16%nat ST.
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned. try replace (B - 0) with B in * by lia.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame H ST (bv_unsigned sp) end.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma mg_skip_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (lc szc szn : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cA nA cntc cntn nn : Z),
  mem_inv bsegs m ->
  a4 = wz cA -> t0 = wz nA -> a5 = wz 1021 ->
  0 <= cntc <= QBATCH_CAP -> 0 <= cntn <= QBATCH_CAP -> QBATCH_CAP < cntc + cntn -> 0 <= nn < 2^64 ->
  AIMG_HI <= cA -> cA + QBATCH_SIZE <= alloc_ceiling -> AIMG_HI <= nA -> nA + QBATCH_SIZE <= alloc_ceiling ->
  rw_cells bsegs m cA [C8 lc; C8 szc; C8 (wz cntc)] ->
  rw_cells bsegs m nA [C8 (wz nn); C8 szn; C8 (wz cntn)] ->
  evt bsegs (fun ms' => exists (t1' t3' t4' : word),
      ms' = MS (mkR ra sp gp tp (wz nn) t1' t2 s0 s1 a0 a1 a2 a3 (wz nA) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
               F (wz (if nn =? 0 then 0x33fd8 else 0x33ef4)) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33ef4) fc None m (seg_rom bsegs)).
Proof.
  intros until nn. intros MI -> -> -> Hc Hn CAP Hnn HC1 HC2 HN1 HN2 CC NC.
  unfold QBATCH_SIZE, QBATCH_CAP, AIMG_HI in *. idtac. cbv beta delta [wz] in *. leaf_prep.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  destruct (Z.eq_dec nn 0) as [->|NE].
  - lstep; if_lia. cbn [Z.eqb]. finish.
  - lstep; if_lia. replace (nn =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE). finish.
Qed.

(* [comment removed for export] *)
Lemma mg_exit_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ng gf gl B ext lo : Z),
  mem_inv bsegs m ->
  a0 = wz (A_QUAR + 160) -> a2 = wz ext ->
  0 <= ext <= B -> B < 2^63 ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (mg_frame j0 vra) ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz B)] ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 16)) gp tp t0 t1 t2 s0 s1 a0 (wz (B - ext)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(A_QUAR + 184, A_QUAR + 192)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + 16)
      /\ rw_cells bsegs m' (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz (B - ext))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33fd8) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI -> -> Hext HB ST HCL LO SPH FR QH.
  pose proof (munch_refl [(681704, 681712)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold mg_frame in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in *.
  replace (681520 + 160) with 681680 in * by reflexivity.
  leaf_prep.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 16).
  finish; eassumption.
Qed.


End CeilWrap.
End RTW_q_merge1.

(* [comment removed for export] *)
Module RTW_q_recw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AQREC : Z := 0x33cd8.

(* [comment removed for export] *)
Definition rec_frame (tn tf tl tb : Z) (vs4 vs3 vs2 vs1 vs0 vra : word) : list cell :=
  [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz tb); C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra].

(* [comment removed for export] *)
Lemma rec_pro_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ng gf gl gb lo : Z) (b2 b3 : byte),
  let U := bv_unsigned b2 + 256 * bv_unsigned b3 in
  mem_inv bsegs m ->
  a0 = wz A_QUAR ->
  0 <= ng -> 8192 * ng <= gb -> gb < 2^62 -> 0 <= gf < 2^64 -> 0 <= gl < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 80 <= bv_unsigned sp ->
  rw_cells bsegs m (A_QUAR + 152) [C4 (wz (lkw 0 1 U))] ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)] ->
  evt bsegs (fun ms' => exists (t0' t1' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 80)) gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 (wz (8192 * ng)) (wz gb) (wz ng) a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33d48) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp - 80)
      /\ rw_cells bsegs m' (bv_unsigned sp - 80) (rec_frame 0 0 0 0 s4 s3 s2 s1 s0 ra)
      /\ rw_cells bsegs m' (A_QUAR + 152) [C4 (wz (lkw 1 1 U))]
      /\ rw_cells bsegs m' (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQREC) fc None m (seg_rom bsegs)).
Proof.
  intros until b3. intros U MI -> Hng Hgb Hgb2 Hgf Hgl ST HCL LO QL QH.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  assert (HU : 0 <= U < 65536) by (subst U; lia). assert (EU : U = bv_unsigned b2 + 256 * bv_unsigned b3) by reflexivity. clearbody U.
  unfold AQREC, rec_frame in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QL, QH.
  replace (681520 + 152) with 681672 in QL by reflexivity. replace (681520 + 160) with 681680 in QH by reflexivity.
  replace (681520 + 152) with 681672 in MU by reflexivity. replace (681520 + 156) with 681676 in MU by reflexivity.
  pose proof (lkw_range 0 1 U ltac:(lia) ltac:(lia) HU) as LR.
  leaf_prep.
  carve_frame 80%nat ST.
  do 7 lstep. (* [comment removed for export] *)
  do 4 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  pose proof (sx32_word_facts (lkw 0 1 U) LR) as XF. cbv zeta in XF.
  remember (sx32 (Z_to_bv 64 (lkw 0 1 U))) as xv eqn:Exv. (nelim XF 3%nat; intros XR XM _).
  (nelimp (lane0_facts (bv_unsigned xv) 1 U XR XM ltac:(lia) HU) 5%nat; intros L1 L2 L3 L4 L5).
  lstep. lstep. lstep. (* [comment removed for export] *) rewrite L1.
  lstep. (* [comment removed for export] *) rewrite L2.
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite L3.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (Z.shiftl_mul_pow2 ng 13) by lia. change (2 ^ 13) with 8192.
  lstep; if_lia. (* [comment removed for export] *)
  match type of QL with rw_cells _ ?my _ _ => assert (QL' : rw_cells bsegs my 681672 [C4 (Z_to_bv 64 (lkw 1 1 U))]) end.
  { match type of QL with rw_cells _ ?mx _ _ =>
      apply (qlock_w3 mx 681672 _ 1 1 b2 b3) in QL; [| lia| lia| apply cas_le4; [lia| lia| lia| rewrite <- EU; exact L5]] end.
    apply qlock_w1 in QL; [| lia| lia]. rewrite <- EU in QL. exact QL. }
  try rewrite unsigned_lit in * by lia.
  replace (ng * 8192) with (8192 * ng) by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rec_nomerge_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ng gb : Z),
  a4 = wz (8192 * ng) -> a5 = wz gb -> a6 = wz ng ->
  0 <= ng -> 8192 * ng <= gb -> gb < 2^55 ->
  (8192 * ng = gb \/ ng * 1638400 <= gb * 100) ->
  evt bsegs (fun ms' => exists (a4' a5' a7' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33d94) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33d48) fc None m (seg_rom bsegs)).
Proof.
  intros until gb. intros -> -> -> Hng Hle Hgb COND.
  leaf_prep.
  destruct (Z.eq_dec (8192 * ng) gb) as [E|NE].
  - lstep; if_lia. (* [comment removed for export] *) finish.
  - lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    finish.
Qed.

(* [comment removed for export] *)
Lemma rec_tomerge_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ng gb : Z),
  a0 = wz A_QUAR -> a4 = wz (8192 * ng) -> a5 = wz gb -> a6 = wz ng ->
  0 <= ng -> 8192 * ng < gb -> gb < 2^55 -> gb * 100 < ng * 1638400 ->
  evt bsegs (fun ms' => exists (a4' a5' a7' : word),
      ms' = MS (mkR (wz 0x33d80) sp gp tp t0 t1 t2 (wz (A_QUAR + 160)) a1 (wz (A_QUAR + 160)) sp a2 a3 a4' a5' a6 a7'
                    a0 a3 a2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33ebc) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33d48) fc None m (seg_rom bsegs)).
Proof.
  intros until gb. intros -> -> -> -> Hng Hlt Hgb COND.
  rewrite A_QUAR_val. leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  do 7 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite Z_to_bv_bv_unsigned. finish.
Qed.

(* [comment removed for export] *)
Lemma rec_aftermerge_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ng gf gl gb : Z),
  mem_inv bsegs m ->
  s0 = wz (A_QUAR + 160) ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)] ->
  evt bsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 s2 s1 s4 s3 a4 a5 (wz ng) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33d94) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33d80) fc None m (seg_rom bsegs)).
Proof.
  intros until gb. intros MI -> QH.
  rewrite A_QUAR_val in *. cbv beta delta [wz] in QH. replace (681520 + 160) with 681680 in QH by reflexivity. leaf_prep.
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
Lemma rec_nopop_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tn tf tl tb ng gf gl gb mn : Z),
  mem_inv bsegs m ->
  a0 = wz A_QUAR -> a1 = wz mn ->
  0 <= gb < 2^63 -> 0 <= mn < 2^63 -> gb <= mn -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl tb vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)] ->
  evt bsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz tn) (wz tl) a6 (wz gb) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33e30) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33d94) fc None m (seg_rom bsegs)).
Proof.
  intros until mn. intros MI -> -> Hgb Hmn Hle SPH FR QH.
  unfold rec_frame in *. rewrite A_QUAR_val in *. cbv beta delta [wz] in QH. replace (681520 + 160) with 681680 in QH by reflexivity. leaf_prep.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
Lemma rec_popentry_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tn tf tl tb ng gf gl gb mn : Z),
  mem_inv bsegs m ->
  a0 = wz A_QUAR -> a1 = wz mn ->
  0 <= gb < 2^63 -> 0 <= mn < 2^63 -> mn < gb -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl tb vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz gf); C8 (wz gl); C8 (wz gb)] ->
  evt bsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp (wz gf) t1 t2 s0 s1 a0 a1 a2 a3 (wz tn) (wz tl) a6 (wz gb) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33dd4) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33d94) fc None m (seg_rom bsegs)).
Proof.
  intros until mn. intros MI -> -> Hgb Hmn Hlt SPH FR QH.
  unfold rec_frame in *. rewrite A_QUAR_val in *. cbv beta delta [wz] in QH. replace (681520 + 160) with 681680 in QH by reflexivity. leaf_prep.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
Lemma rec_pop1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (cnt : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ng bA gl gb bnx bsz : Z),
  mem_inv bsegs m ->
  a0 = wz A_QUAR -> a6 = wz ng -> t0 = wz bA ->
  1 <= ng < 2^62 -> 0 <= gl < 2^64 -> 0 <= bnx < 2^64 -> 0 <= bsz <= gb -> gb < 2^62 ->
  AIMG_HI <= bA -> bA + 24 <= alloc_ceiling ->
  rw_cells bsegs m (A_QUAR + 160) [C8 (wz ng); C8 (wz bA); C8 (wz gl); C8 (wz gb)] ->
  rw_cells bsegs m bA [C8 (wz bnx); C8 (wz bsz); C8 cnt] ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp (wz bA) (wz bA) (wz gb) s0 s1 a0 a1 a2 a3 a4 a5 (wz (ng - 1)) (wz bnx)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33e08) fc None m' (seg_rom bsegs)
      /\ munch [(A_QUAR + 160, A_QUAR + 192); (bA, bA + 8)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (A_QUAR + 160) [C8 (wz (ng - 1)); C8 (wz bnx); C8 (wz (if bnx =? 0 then 0 else gl)); C8 (wz (gb - bsz))]
      /\ rw_cells bsegs m' bA [C8 (wz 0); C8 (wz bsz); C8 cnt])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33dd4) fc None m (seg_rom bsegs)).
Proof.
  intros until bsz. intros MI -> -> -> Hng Hgl Hbnx Hbsz Hgb HB1 HB2 QH LB.
  pose proof (munch_refl [(A_QUAR + 160, A_QUAR + 192); (bA, bA + 8)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QH, LB.
  replace (681520 + 160) with 681680 in QH by reflexivity.
  replace (681520 + 160) with 681680 in MU by reflexivity. replace (681520 + 192) with 681712 in MU by reflexivity.
  leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  destruct (Z.eq_dec bnx 0) as [E0|NE0].
  - subst bnx. lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. cbn [Z.eqb].
    replace (ng + -1) with (ng - 1) in * by lia.
    finish; eassumption.
  - lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia.
    replace (bnx =? 0) with false by (symmetry; apply Z.eqb_neq; exact NE0).
    replace (ng + -1) with (ng - 1) in * by lia.
    finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rec_pop2F_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra cnt : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tn tf tl tb bA gb' bsz lnk : Z),
  mem_inv bsegs m ->
  a0 = wz A_QUAR -> a4 = wz 0 -> t1 = wz bA ->
  0 <= bsz -> 0 <= tb -> tb + bsz < 2^62 -> 0 <= gb' < 2^63 ->
  AIMG_HI <= bA -> bA + 24 <= alloc_ceiling -> alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl tb vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m (A_QUAR + 184) [C8 (wz gb')] ->
  rw_cells bsegs m bA [C8 (wz lnk); C8 (wz bsz); C8 cnt] ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp a7 t1 (wz gb') s0 s1 a0 a1 a2 a3 (wz 1) (wz bA) a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33dd0) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp, bv_unsigned sp + 32)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (bv_unsigned sp) (rec_frame tn bA tl (tb + bsz) vs4 vs3 vs2 vs1 vs0 vra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33e08) fc None m (seg_rom bsegs)).
Proof.
  intros until lnk. intros MI -> -> -> Hbsz Htb Htb2 Hgb HB1 HB2 HSP SPH FR QB LB.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold rec_frame, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QB, LB.
  replace (681520 + 184) with 681704 in QB by reflexivity.
  leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rec_pop2N_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra cnt : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tn tf tl tb bA gb' bsz lnk tsz tlA : Z),
  mem_inv bsegs m ->
  a0 = wz A_QUAR -> a4 = wz tsz -> a5 = wz tlA -> t1 = wz bA ->
  0 <= bsz -> 0 <= tb -> tb + bsz < 2^62 -> 0 <= gb' < 2^63 -> 1 <= tsz < 2^62 ->
  AIMG_HI <= bA -> bA + 24 <= alloc_ceiling -> AIMG_HI <= tlA -> tlA + 8 <= alloc_ceiling -> (bA + 24 <= tlA \/ tlA + 8 <= bA) ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl tb vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m (A_QUAR + 184) [C8 (wz gb')] ->
  rw_cells bsegs m bA [C8 (wz lnk); C8 (wz bsz); C8 cnt] ->
  rw_cells bsegs m tlA [C8 (wz 0)] ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp a7 t1 (wz gb') s0 s1 a0 a1 a2 a3 (wz (tsz + 1)) (wz bA) a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33dd0) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp, bv_unsigned sp + 32); (tlA, tlA + 8)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (bv_unsigned sp) (rec_frame tn tf tl (tb + bsz) vs4 vs3 vs2 vs1 vs0 vra)
      /\ rw_cells bsegs m' tlA [C8 (wz bA)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33e08) fc None m (seg_rom bsegs)).
Proof.
  intros until tlA. intros MI -> -> -> -> Hbsz Htb Htb2 Hgb Htsz HB1 HB2 HT1 HT2 DJ HSP SPH FR QB LB TL.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 32); (tlA, tlA + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold rec_frame, AIMG_HI in *. rewrite A_QUAR_val in *. idtac. cbv beta delta [wz] in QB, LB, TL.
  replace (681520 + 184) with 681704 in QB by reflexivity.
  leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rec_popmore_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mn gb : Z),
  a1 = wz mn -> t2 = wz gb -> 0 <= mn < 2^63 -> 0 <= gb < 2^63 -> mn < gb ->
  evt bsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33dd4) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33dd0) fc None m (seg_rom bsegs)).
Proof.
  intros until gb. intros -> -> Hmn Hgb Hlt. leaf_prep. lstep; if_lia. finish.
Qed.

(* [comment removed for export] *)
Lemma rec_popdone_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tn tf tl tb mn gb tsz bA : Z),
  mem_inv bsegs m ->
  a1 = wz mn -> t2 = wz gb -> a4 = wz tsz -> t1 = wz bA -> 0 <= mn < 2^63 -> 0 <= gb < 2^63 -> gb <= mn ->
  0 <= tsz < 2^63 -> 0 <= bA < 2^64 ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl tb vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33e30) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp, bv_unsigned sp + 32)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (bv_unsigned sp) (rec_frame tsz tf bA tb vs4 vs3 vs2 vs1 vs0 vra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33dd0) fc None m (seg_rom bsegs)).
Proof.
  intros until bA. intros MI -> -> -> -> Hmn Hgb Hle Htsz HbA HSP SPH FR.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold rec_frame in *. idtac. leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rec_unlock_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b2 b3 : byte),
  let U := bv_unsigned b2 + 256 * bv_unsigned b3 in
  mem_inv bsegs m ->
  a0 = wz A_QUAR ->
  rw_cells bsegs m (A_QUAR + 152) [C4 (wz (lkw 1 1 U))] ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR (wz 0x33e48) sp gp tp t0 t1 t2 s0 s1 a0 sp a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x34040) fc None m' (seg_rom bsegs)
      /\ munch [(A_QUAR + 152, A_QUAR + 156)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (A_QUAR + 152) [C4 (wz (lkw 0 0 U))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33e30) fc None m (seg_rom bsegs)).
Proof.
  intros until b3. intros U MI -> QL.
  pose proof (munch_refl [(681672, 681676)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  assert (HU : 0 <= U < 65536) by (subst U; lia). assert (EU : U = bv_unsigned b2 + 256 * bv_unsigned b3) by reflexivity. clearbody U.
  rewrite A_QUAR_val in *. cbv beta delta [wz] in QL. replace (681520 + 152) with 681672 in QL by reflexivity.
  leaf_prep.
  apply (qlock_w3 m 681672 _ 1 1 b2 b3) in QL; [| lia| lia| rewrite EU; apply lkw_bytes; lia].
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    match goal with H : rw_cells _ mx 681672 _ |- _ => apply qlock_w1 in H; [| lia| lia]; rewrite <- EU in H end end.
  try rewrite Z_to_bv_bv_unsigned.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rec_epi_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tn tf tl tb lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl tb vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (fun ms' =>
      ms' = MS (mkR vra (wz (bv_unsigned sp + 80)) gp tp t0 t1 t2 vs0 vs1 a0 a1 a2 a3 a4 a5 a6 a7 vs2 vs3 vs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m (seg_rom bsegs)
      /\ stk bsegs m lo (bv_unsigned sp + 80))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33e48) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST HCL LO SPH FR.
  unfold rec_frame in *. idtac. leaf_prep.
  do 6 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 80).
  finish; eassumption.
Qed.


End CeilWrap.
End RTW_q_recw.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_apz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_q_merge2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_car OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_zone2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_ms OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_drain2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_bz RTW_q_recw RTW_q_merge1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac qlia := unfold QBATCH_CAP, QBATCH_SIZE, AIMG_HI, KHIGHMEM_BEG, CEIL in *; idtac; lia.
(* [comment removed for export] *)
Local Ltac zsubst := repeat match goal with x := _ |- _ => subst x end.
Local Ltac memb0 := zsubst; repeat match goal with H : _ |- _ => clear H end;
  rewrite ?in_app_iff; cbn [In]; rewrite ?in_app_iff; cbn [In]; tauto.
Local Ltac memb H := zsubst; move H at top; repeat match goal with H' : _ |- _ => lazymatch H' with H => fail | _ => clear H' end end;
  rewrite ?in_app_iff in H; rewrite ?in_app_iff; cbn [In] in H |- *; rewrite ?in_app_iff in H; rewrite ?in_app_iff; cbn [In] in H |- *; tauto.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qb_size_lb' : forall b, 8192 <= qb_size b.
Proof. intros b. pose proof (qb_size_lb b). unfold QBATCH_SIZE in *. lia. Qed.

Lemma nthz_app_l : forall {X} (l1 l2 : list X) i d, 0 <= i < zlen l1 -> nthz (l1 ++ l2) i d = nthz l1 i d.
Proof.
  intros X l1 l2 i d Hi. unfold nthz. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  apply app_nth1. unfold zlen in Hi. lia.
Qed.
Lemma nthz_app_r : forall {X} (l1 l2 : list X) i d, zlen l1 <= i -> nthz (l1 ++ l2) i d = nthz l2 (i - zlen l1) d.
Proof.
  intros X l1 l2 i d Hi. unfold nthz, zlen in *. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i - Z.of_nat (length l1) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite app_nth2 by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma QBCx_keep_g : forall K W m m' x, RTWF K -> munch W m m' -> wmono bsegs m m' ->
  In (qb_addr x) (qbatch_addrs K) -> 0 <= qb_count x <= QBATCH_CAP -> QBCx m x ->
  Forall (fun iv => CEIL <= fst iv \/ snd iv <= AIMG_HI \/ (st_t K <= fst iv /\ snd iv <= st_t K + 4096)
                    \/ (qb_addr x <= fst iv /\ snd iv <= qb_addr x + 8)
                    \/ (exists a, In a (qbatch_addrs K) /\ a <> qb_addr x /\ a <= fst iv /\ snd iv <= a + QBATCH_SIZE)) W ->
  QBCx m' x.
Proof.
  intros K W m m' x WF MU WM Ha CNT (HC & V & SL & SHD) HW.
  (nelimp (batch_facts_a K x WF Ha) 4%nat; intros B1 B2 B3 B4). pose proof (t_range K WF) as [T1 T2].
  assert (AL8 : qb_addr x mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact B3]).
  pose proof (rt_SH_bounds (qb_addr x) ltac:(unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SB1.
  pose proof (rt_SH_bounds (qb_addr x + 8192) ltac:(unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SB2.
  pose proof (rt_SH_aligned_add (qb_addr x) 8192 AL8) as SA. change (8192 / 8) with 1024 in SA.
  assert (OBJ : forall a sz, qb_addr x + 8 <= a -> a + sz <= qb_addr x + 8192 -> disjoint_from W a sz).
  { intros a sz H1 H2. apply (disjoint_from_forallq _ W a sz HW). intros lo hi X. cbn [fst snd] in X.
    destruct X as [X|[X|[X|[X|(a2 & Ha2 & NE2 & X)]]]]; try (unfold QBATCH_SIZE, CEIL, AIMG_HI, KHIGHMEM_BEG in *; lia).
    pose proof (batch_disj K a2 (qb_addr x) WF Ha2 Ha NE2). unfold QBATCH_SIZE in *. lia. }
  assert (SHW : disjoint_from W (SH (qb_addr x)) 1024).
  { apply (disjoint_from_forallq _ W _ _ HW). intros lo hi X. cbn [fst snd] in X.
    destruct X as [X|[X|[X|[X|(a2 & Ha2 & NE2 & X)]]]]; try (unfold QBATCH_SIZE, CEIL, AIMG_HI, KHIGHMEM_BEG in *; first [lia | clear - X T1 SB1 SB2 SA; blia]).
    apply in_map_iff in Ha2 as (b2 & <- & Hb2). pose proof (batch_facts K WF b2 Hb2) as (C1 & _). unfold KHIGHMEM_BEG, AIMG_HI in *. lia. }
  split; [| split; [| split]].
  - eapply (rwT W m m' MU WM); [exact HC| cbn; apply OBJ; lia].
  - eapply visT; [exact WM| exact V| unfold AIMG_HI, KHIGHMEM_BEG in *; lia].
  - intros i Hi. eapply (rwT W m m' MU WM); [exact (SL i Hi)| cbn; apply OBJ; unfold QBATCH_CAP in *; lia].
  - eapply (rwT W m m' MU WM); [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia.
    change (8192 / 8) with 1024. exact SHW.
Qed.

(* [comment removed for export] *)
Lemma far_keep3 : forall K v1 v2 v3 W1 W2 W3 m m', RTWF K ->
  In (qb_addr v1) (qbatch_addrs K) -> In (qb_addr v2) (qbatch_addrs K) -> In (qb_addr v3) (qbatch_addrs K) ->
  Forall (ucz_ok K 24 (bk K v1)) W1 -> Forall (ucz_ok K 24 (bk K v2)) W2 -> Forall (ucz_ok K 24 (bk K v3)) W3 ->
  munch (W1 ++ W2 ++ W3) m m' -> wmono bsegs m m' ->
     (coreC K m -> coreC K m')
  /\ (R_alloc4 K m -> R_alloc4 K m')
  /\ (R_threadx K m -> R_threadx K m')
  /\ (R_live K m -> R_live K m')
  /\ (R_quar K m -> R_quar K m')
  /\ (forall x nxt, In (qb_addr x) (qbatch_addrs K) -> 0 <= qb_count x <= QBATCH_CAP ->
        qb_addr x <> qb_addr v1 -> qb_addr x <> qb_addr v2 -> qb_addr x <> qb_addr v3 -> QBC m x nxt -> QBC m' x nxt).
Proof.
  intros K v1 v2 v3 W1 W2 W3 m m' WF H1 H2 H3 F1 F2 F3 MU WM.
  (nelim (munch_split W1 (W2 ++ W3) m m' MU WM) 5%nat; intros m1 MU1 WM1 MU23 WM23).
  (nelim (munch_split W2 W3 m1 m' MU23 WM23) 5%nat; intros m2 MU2 WM2 MU3 WM3).
  (nelim (bzone_a K WF v1 H1 W1 F1 m m1 MU1 WM1) 8%nat; intros A1 A2 A3 A4 A5 _ _ A8).
  (nelim (bzone_a K WF v2 H2 W2 F2 m1 m2 MU2 WM2) 8%nat; intros B1 B2 B3 B4 B5 _ _ B8).
  (nelim (bzone_a K WF v3 H3 W3 F3 m2 m' MU3 WM3) 8%nat; intros C1 C2 C3 C4 C5 _ _ C8).
  split; [intros X; exact (C1 (B1 (A1 X)))|]. split; [intros X; exact (C2 (B2 (A2 X)))|].
  split; [intros X; exact (C3 (B3 (A3 X)))|]. split; [intros X; exact (C4 (B4 (A4 X)))|].
  split; [intros X; exact (C5 (B5 (A5 X)))|].
  intros x nxt Hx CNT N1 N2 N3 QB. apply (C8 x nxt Hx CNT N3). apply (B8 x nxt Hx CNT N2). apply (A8 x nxt Hx CNT N1). exact QB.
Qed.

Lemma qlist_far : forall m m' q, (forall x nxt, In x q -> QBC m x nxt -> QBC m' x nxt) -> R_qlist m q -> R_qlist m' q.
Proof.
  intros m m' q FAR RL. apply (proj2 (R_qlist_iff m' q)). intros q1 x q2 E. apply FAR; [rewrite E; apply in_or_app; right; left; reflexivity|].
  exact (proj1 (R_qlist_iff m q) RL q1 x q2 E).
Qed.
Lemma qc_first_absorb : forall q c n r r', qc_first (q ++ qb_absorb c n :: r) = qc_first (q ++ c :: r').
Proof. intros q c n r r'. destruct q; reflexivity. Qed.

Lemma ainv_merge : forall K qt cur pre c n post tmp, ainv K qt cur (pre ++ c :: n :: post) tmp -> qb_count c + qb_count n <= QBATCH_CAP ->
  ainv K qt cur (pre ++ qb_absorb c n :: post) (tmp ++ [mkQB (qb_addr n) []]).
Proof.
  intros K qt cur pre c n post tmp (P & C & E & B) CAP.
  assert (PA : Permutation (map qb_addr (qt ++ (pre ++ qb_absorb c n :: post) ++ (tmp ++ [mkQB (qb_addr n) []]) ++ map fst cur))
                            (map qb_addr (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur))).
  { rewrite !map_app. cbn [map qb_addr qb_absorb]. apply Permutation_app_head. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
    apply perm_skip. rewrite (app_assoc (map qb_addr post) (map qb_addr tmp) (qb_addr n :: map qb_addr (map fst cur))).
    rewrite (app_assoc (map qb_addr post) (map qb_addr tmp) (map qb_addr (map fst cur))).
    apply Permutation_sym. apply Permutation_middle. }
  split; [eapply Permutation_trans; [exact PA| exact P]|].
  split.
  - intros x Hx. rewrite !in_app_iff in Hx. cbn [In] in Hx.
    destruct Hx as [Hx|[[Hx|[<-|Hx]]|[[Hx|[<-|[]]]|Hx]]]; try (apply C; rewrite !in_app_iff; cbn [In]; tauto).
    + rewrite qb_count_absorb. exact CAP.
    + unfold qb_count. cbn. unfold QBATCH_CAP. lia.
  - split.
    + eapply Permutation_trans; [| exact E]. apply Permutation_app_tail.
      rewrite !flat_map_app. cbn [flat_map qb_elems qb_absorb]. rewrite !app_nil_r, <- !app_assoc. apply Permutation_refl.
    + rewrite !qc_bytes_app, !qc_bytes_cons, qb_size_absorb in *. cbn [qc_bytes fold_right] in *.
      unfold qb_size at 3. cbn [qb_elems fold_right]. pose proof (qb_size_lb' c). pose proof (qb_size_lb' n). unfold QBATCH_SIZE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MERGE.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variables (qt : list qbatch) (cur : list (qbatch * Z)).
Variables (lo SP : Z).
Local Notation minv := (ainv K qt cur).

Definition mg_post (ra sp gp tp s0 s1 a0 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (vs4 vs3 vs2 vs1 vs0 vra : word) (j0 : list byte) (vraM : word) (m : word -> option byte)
    (qg' tmp' : list qbatch) (B ext' cA nxt : Z) : machine_state -> Prop :=
  fun ms' => exists (a3' t1' t2' t3' t4' t5' : word) (m' : word -> option byte) (Wd : list (Z * Z)),
      ms' = MS (mkR ra sp gp tp (wz nxt) t1' t2' s0 s1 a0 a1 (wz ext') a3' (wz cA) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
               F (wz 0x33fd4) fc None m' (seg_rom bsegs)
      /\ minv qg' tmp' /\ QXb K m' 1 1 qt qg' tmp' cur B /\ B = qc_bytes qg' + ext'
      /\ rw_cells bsegs m' (bv_unsigned sp + 16) (rec_frame (zlen tmp') (qc_first tmp') (qc_last tmp') (qc_bytes tmp') vs4 vs3 vs2 vs1 vs0 vra)
      /\ rw_cells bsegs m' (bv_unsigned sp) (mg_frame j0 vraM)
      /\ mem_inv bsegs m' /\ munch Wd m m' /\ Forall (dwin K lo SP) Wd /\ wmono bsegs m m'.

Theorem mg_step :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (j0 : list byte) (vraM : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (pre post tmp : list qbatch) (c n : qbatch) (B ext : Z),
  minv (pre ++ c :: n :: post) tmp ->
  QXb K m 1 1 qt (pre ++ c :: n :: post) tmp cur B -> mem_inv bsegs m ->
  qb_count c + qb_count n <= QBATCH_CAP ->
  B = qc_bytes (pre ++ c :: n :: post) + ext -> 0 <= ext -> B < 2^61 ->
  a0 = wz (A_QUAR + 160) -> a1 = wz (bv_unsigned sp + 16) -> a2 = wz ext -> a4 = wz (qb_addr c) -> a5 = wz 1021 -> a6 = wz (-8192) -> a7 = wz 8192 ->
  t0 = wz (qb_addr n) ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 96 <= SP -> SP <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp + 16) (rec_frame (zlen tmp) (qc_first tmp) (qc_last tmp) (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m (bv_unsigned sp) (mg_frame j0 vraM) ->
  evt bsegs (mg_post ra sp gp tp s0 s1 a0 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc vs4 vs3 vs2 vs1 vs0 vra j0 vraM m
               (pre ++ qb_absorb c n :: post) (tmp ++ [mkQB (qb_addr n) []]) B (ext + 8192) (qb_addr c) (qc_first post))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33ef4) fc None m (seg_rom bsegs)).
Proof.
  intros until ext. intros PI X MI CAP HB Hext HB2 Ha0 Ha1 Ha2 Ha4 Ha5 Ha6 Ha7 Ht0 HCL LO SPB SPH FR FRM.
  (nelimp X 14%nat; intros CO A4 XA XL XH XS TX TCq LV QR RL1 RL2 RL3 RC).
  pose proof (t_range K WF) as [T1 T2]. idtac.
  set (qg := pre ++ c :: n :: post) in *.
  (* [comment removed for export] *)
  assert (INc : In c (qt ++ qg ++ tmp ++ map fst cur)) by (subst qg; memb0).
  assert (INn : In n (qt ++ qg ++ tmp ++ map fst cur)) by (subst qg; memb0).
  pose proof (ainv_addr K qt cur _ _ c PI INc) as Hc. pose proof (ainv_addr K qt cur _ _ n PI INn) as Hn.
  pose proof (ainv_cnt K qt cur _ _ c PI INc) as Cc. pose proof (ainv_cnt K qt cur _ _ n PI INn) as Cn.
  (nelimp (batch_facts_a K c WF Hc) 4%nat; intros Gc1 Gc2 Gc3 Gc4). (nelimp (batch_facts_a K n WF Hn) 4%nat; intros Gn1 Gn2 Gn3 Gn4).
  pose proof (ainv_nodup K WF qt cur _ _ PI) as ND.
  assert (NDc : forall x, In x ((qt ++ pre) ++ (n :: post) ++ tmp ++ map fst cur) -> qb_addr x <> qb_addr c).
  { intros x Hx. apply (nodup_map_mid qb_addr (qt ++ pre) ((n :: post) ++ tmp ++ map fst cur) c x); [| exact Hx].
    subst qg. repeat rewrite <- app_assoc in ND. cbn [app] in ND. repeat rewrite <- app_assoc. cbn [app]. exact ND. }
  assert (NDn : forall x, In x ((qt ++ pre ++ [c]) ++ post ++ tmp ++ map fst cur) -> qb_addr x <> qb_addr n).
  { intros x Hx. apply (nodup_map_mid qb_addr (qt ++ pre ++ [c]) (post ++ tmp ++ map fst cur) n x); [| exact Hx].
    subst qg. repeat rewrite <- app_assoc in ND. cbn [app] in ND. repeat rewrite <- app_assoc. cbn [app]. exact ND. }
  assert (NEcn : qb_addr c <> qb_addr n) by (intros E; apply (NDn c); [memb0| exact E]).
  pose proof (batch_disj K (qb_addr c) (qb_addr n) WF Hc Hn NEcn) as DJcn.
  (nelimp PI 4%nat; intros _ _ _ BB).
  assert (ELK : forall e, In e (flat_map qb_elems (qt ++ qg ++ tmp)) -> In e (qelems K)) by (intros e He; exact (ainv_elems K qt cur _ _ e PI He)). subst qg. rewrite !qc_bytes_app, !qc_bytes_cons in BB. rewrite qc_bytes_app, !qc_bytes_cons in HB.
  pose proof (qc_bytes_nonneg pre) as B0. pose proof (qc_bytes_nonneg post) as B1. pose proof (qc_bytes_nonneg tmp) as B2.
  pose proof (qb_size_lb' c) as S1. pose proof (qb_size_lb' n) as S2.
  (* [comment removed for export] *)
  pose proof (proj1 (R_qlist_iff m _) RL2 pre c (n :: post) eq_refl) as QBc. cbn [qc_first] in QBc.
  pose proof (proj1 (R_qlist_iff m _) RL2 (pre ++ [c]) n post ltac:(rewrite <- app_assoc; reflexivity)) as QBn.
  (nelimp QBc 4%nat; intros CC Vc SLc SHc). (nelimp QBn 4%nat; intros NC Vn SLn SHn).
  set (sl := fun j => b_chunk_beg (fst (nthz (qb_elems n) j (0, 0)))).
  assert (SLR : forall j, 0 <= j < qb_count n -> 0 <= sl j < 2^64).
  { intros j Hj. subst sl. cbv beta.
    assert (INel : In (nthz (qb_elems n) j (0, 0)) (qb_elems n)).
    { unfold nthz. replace (j <? 0) with false by (symmetry; apply Z.ltb_ge; lia). apply nth_In. unfold qb_count in Hj. lia. }
    assert (IN : In (nthz (qb_elems n) j (0, 0)) (qelems K)).
    { apply ELK. clear - INel. rewrite !flat_map_app. cbn [flat_map]. rewrite !in_app_iff. tauto. }
    destruct (nthz (qb_elems n) j (0, 0)) as [A nn] eqn:EE. cbn [fst].
    (nelimp (block_geom K WF A nn ltac:(unfold all_blocks; rewrite !in_app_iff; right; left; exact IN)) 7%nat; intros _ _ K1 K2 K3 K4 _).
    unfold b_chunk_beg, usz, KHIGHMEM_BEG, AIMG_HI in *. blia. }
  assert (AF : forall l, (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) -> 0 <= qc_first l < 2^64).
  { intros l Hl. destruct l as [|x l]; [cbn; lia|]. cbn [qc_first]. pose proof (batch_facts_a K x WF (Hl x ltac:(left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  assert (SUBpost : forall x, In x post -> In (qb_addr x) (qbatch_addrs K)) by (intros x Hx; apply (ainv_addr K qt cur _ _ x PI); memb Hx).
  pose proof (AF post SUBpost) as Fpost.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (mg_bodyA_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (qb_addr c) (qb_addr n) (qb_count c) (qb_count n) (qb_size c) (qb_size n) (qc_first post) sl);
      [exact MI| exact Ha4| exact Ht0| exact Ha5| lia| lia| exact CAP| lia| lia| exact Fpost
      | unfold AIMG_HI, KHIGHMEM_BEG in *; lia| idtac; unfold CEIL in *; lia| unfold AIMG_HI, KHIGHMEM_BEG in *; lia| idtac; unfold CEIL in *; lia
      | exact DJcn| exact SLR| exact SLn| exact CC| exact NC| exact Vc]. }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 13%nat; intros t2' t3' t4' t5' m1 -> MU1 WM1 MI1 DONE CC1 NC1 Vc1).
  (* [comment removed for export] *)
  destruct (bk_used_a K c WF Hc) as [UKc Ec]. destruct (bk_used_a K n WF Hn) as [UKn En].
  match type of MU1 with munch ?Wx _ _ => set (W1 := Wx) in MU1 end.
  assert (HW1 : Forall (ucz_ok K 24 (bk K c)) W1).
  { subst W1. unfold ucz_ok. change (csize 24) with 8192. rewrite <- Ec.
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold QBATCH_CAP in *. lia. }
  (nelimp (bzone_a K WF c Hc W1 HW1 m m1 MU1 WM1) 8%nat; intros Zc Za Zt Zl Zq Zrl Zcu Zqb).
  assert (D1 : forall a sz, a + sz <= qb_addr c + 24 + 8 * qb_count c \/ qb_addr c + QBATCH_SIZE <= a -> disjoint_from W1 a sz).
  { intros a sz Ha. subst W1. cbn. unfold QBATCH_SIZE, QBATCH_CAP in *. split; [lia| exact I]. }
  pose proof (rt_SH_bounds (qb_addr c) ltac:(clear - Gc1 Gc2; unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SBc.
  pose proof (rt_SH_bounds (qb_addr n) ltac:(clear - Gn1 Gn2; unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SBn.
  assert (ALL : forall x, In x (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur) ->
                In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP).
  { intros x Hx. split; [exact (ainv_addr K qt cur _ _ x PI Hx)| exact (ainv_cnt K qt cur _ _ x PI Hx)]. }
  pose proof (Zc CO) as CO1. pose proof (Za A4) as A41. pose proof (Zt TX) as TX1. pose proof (Zl LV) as LV1. pose proof (Zq QR) as QR1.
  assert (XA1 : QA m1) by (apply (UZ_QA W1 m m1 MU1 WM1 XA); apply D1; left; unfold A_QUAR, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *; lia).
  assert (XS1 : QS m1) by (apply (UZ_QS W1 m m1 MU1 WM1 XS); apply D1; left; unfold A_QUAR, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *; lia).
  assert (XL1 : QLK m1 1 1) by (apply (UZ_QLK W1 m m1 MU1 WM1 1 1 XL); apply D1; left; unfold A_QUAR, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *; lia).
  assert (XH1 : QH4 m1 (zlen (pre ++ c :: n :: post)) (qc_first (pre ++ c :: n :: post)) (qc_last (pre ++ c :: n :: post)) B)
    by (apply (UZ_QH4 W1 m m1 MU1 WM1 _ _ _ _ XH); apply D1; left; unfold A_QUAR, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *; lia).
  assert (TC1 : TC K m1 qt) by (apply (UZ_TC K W1 m m1 MU1 WM1 qt TCq); apply D1; unfold qcache_t, T_QCACHE, QBATCH_SIZE in *; lia).
  assert (RLt1 : R_qlist m1 qt).
  { apply (Zrl qt RL1). intros x Hx. destruct (ALL x ltac:(memb Hx)) as [U1 U2]. split; [exact U1| split; [exact U2| apply NDc; memb Hx]]. }
  pose proof (proj1 (R_qlist_app m pre (c :: n :: post)) RL2) as [RLpre RLcn].
  pose proof (proj2 (proj1 (R_qlist_cons m n post) (proj2 (proj1 (R_qlist_cons m c (n :: post)) RLcn)))) as RLpost.
  assert (RLpost1 : R_qlist m1 post).
  { apply (Zrl post RLpost). intros x Hx. destruct (ALL x ltac:(memb Hx)) as [U1 U2]. split; [exact U1| split; [exact U2| apply NDc; memb Hx]]. }
  assert (RL31 : R_qlist m1 tmp).
  { apply (Zrl tmp RL3). intros x Hx. destruct (ALL x ltac:(memb Hx)) as [U1 U2]. split; [exact U1| split; [exact U2| apply NDc; memb Hx]]. }
  assert (RC1 : QCUR m1 cur).
  { apply (Zcu cur RC). intros bd Hbd. pose proof (in_map fst cur bd Hbd) as Hb1. destruct (ALL (fst bd) ltac:(memb Hb1)) as [U1 U2]. split; [exact U1| split; [exact U2| apply NDc; memb Hb1]]. }
  assert (PRE1 : forall q1 x q2, pre = q1 ++ x :: q2 -> QBC m1 x (qc_first (q2 ++ c :: n :: post))).
  { intros q1 x q2 E. destruct (ALL x ltac:(rewrite E; memb0)) as [U1 U2].
    apply (Zqb x _ U1 U2); [apply NDc; rewrite E; memb0| exact (RLpre q1 x q2 E)]. }
  assert (QBn1 : QBC m1 n (qc_first post)) by (apply (Zqb n _ Hn Cn); [intros E; apply NEcn; symmetry; exact E| exact QBn]).
  (nelimp QBn1 4%nat; intros _ Vn1 SLn1 SHn1).
  assert (SLc1 : forall i, 0 <= i < qb_count c -> rw_cells bsegs m1 (qb_addr c + 24 + 8 * i) [W8 (b_chunk_beg (fst (nthz (qb_elems c) i (0, 0))))]).
  { intros i Hi. eapply (rwT W1 m m1 MU1 WM1); [exact (SLc i Hi)| cbn; apply D1; left; lia]. }
  assert (SHc1 : rw_cells bsegs m1 (SH (qb_addr c)) (zcells (sh_avail 24))).
  { eapply (rwT W1 m m1 MU1 WM1); [exact SHc|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. change (8192 / 8) with 1024.
    apply D1. left. clear - Gc1 Cc. unfold SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI in *. Z.div_mod_to_equations. lia. }
  assert (FR1 : rw_cells bsegs m1 (bv_unsigned sp + 16) (rec_frame (zlen tmp) (qc_first tmp) (qc_last tmp) (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra)).
  { eapply (rwT W1 m m1 MU1 WM1); [exact FR| cbn; apply D1; right; unfold QBATCH_SIZE, CEIL in *; lia]. }
  assert (FRM1 : rw_cells bsegs m1 (bv_unsigned sp) (mg_frame j0 vraM)).
  { eapply (rwT W1 m m1 MU1 WM1); [exact FRM| cbn; apply D1; right; unfold QBATCH_SIZE, CEIL in *; lia]. }
  clear Zc Za Zt Zl Zq Zrl Zcu Zqb CO A4 TX LV QR XA XS XL XH TCq RL1 RL2 RL3 RC FR FRM RLcn RLpost QBn QBc CC NC Vc SLc SHc Vn SLn SHn RLpre.
  (* [comment removed for export] *)
  unfold rec_frame in FR1.
  apply (proj1 (rw_cells_app m1 (bv_unsigned sp + 16) [C8 (wz (zlen tmp)); C8 (wz (qc_first tmp)); C8 (wz (qc_last tmp)); C8 (wz (qc_bytes tmp))] _)) in FR1 as [TMP1 SAV1].
  cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.add Pos.succ] in SAV1.
  (* [comment removed for export] *)
  assert (NG : 1 <= zlen (pre ++ c :: n :: post) < 2^62).
  { rewrite zlen_app, !zlen_cons. pose proof (zlen_nonneg pre). pose proof (zlen_nonneg post).
    pose proof (qc_bytes_lb pre). pose proof (qc_bytes_lb post). unfold QBATCH_SIZE in *. lia. }
  assert (SUBall : forall l, (forall x, In x l -> In x (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur)) -> forall x, In x l -> In (qb_addr x) (qbatch_addrs K)).
  { intros l Hl x Hx. exact (proj1 (ALL x (Hl x Hx))). }
  assert (AL : forall l, (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) -> 0 <= qc_last l < 2^64).
  { intros l Hl. destruct (snoc_or_nil' l) as [->|(q & x & ->)]; [cbn; lia|]. rewrite qc_last_snoc.
    pose proof (batch_facts_a K x WF (Hl x ltac:(apply in_or_app; right; left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  assert (SUBqg : forall x, In x (pre ++ c :: n :: post) -> In x (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur))
    by (intros x Hx; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (SUBtm : forall x, In x tmp -> In x (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur))
    by (intros x Hx; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hx).
  pose proof (AL (pre ++ c :: n :: post) (SUBall _ SUBqg)) as GL.
  pose proof (AF tmp (SUBall _ SUBtm)) as TF.
  unfold QH4 in XH1.
  (* [comment removed for export] *)
  assert (EQH : zlen (pre ++ c :: n :: post) - 1 = zlen (pre ++ qb_absorb c n :: post)
                /\ qc_first (pre ++ c :: n :: post) = qc_first (pre ++ qb_absorb c n :: post)
                /\ (if qc_last (pre ++ c :: n :: post) =? qb_addr n then qb_addr c else qc_last (pre ++ c :: n :: post)) = qc_last (pre ++ qb_absorb c n :: post)).
  { split; [rewrite !zlen_app, !zlen_cons; lia|]. split; [symmetry; apply qc_first_absorb|].
    destruct (snoc_or_nil' post) as [->|(pq & pL & EP)].
    - replace (pre ++ [c; n]) with ((pre ++ [c]) ++ [n]) by (rewrite <- app_assoc; reflexivity). rewrite !qc_last_snoc, Z.eqb_refl. reflexivity.
    - rewrite EP. replace (pre ++ c :: n :: pq ++ [pL]) with ((pre ++ c :: n :: pq) ++ [pL]) by (rewrite <- app_assoc; reflexivity).
      replace (pre ++ qb_absorb c n :: pq ++ [pL]) with ((pre ++ qb_absorb c n :: pq) ++ [pL]) by (rewrite <- app_assoc; reflexivity).
      rewrite !qc_last_snoc. replace (qb_addr pL =? qb_addr n) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. apply NDn. rewrite EP. memb0. }
  (nelim EQH 3%nat; intros EQ1 EQ2 EQ3).
  assert (CAP' : 0 <= qb_count (qb_absorb c n) <= QBATCH_CAP) by (rewrite qb_count_absorb; lia).
  pose proof (ainv_merge K qt cur pre c n post tmp PI CAP) as PI'.
  (* [comment removed for export] *)
  assert (SLOTS : forall mm W, munch W m1 mm -> wmono bsegs m1 mm -> (forall a sz, qb_addr c + 24 <= a -> a + sz <= qb_addr c + 8192 -> disjoint_from W a sz) ->
            forall i, 0 <= i < qb_count (qb_absorb c n) ->
              rw_cells bsegs mm (qb_addr (qb_absorb c n) + 24 + 8 * i) [W8 (b_chunk_beg (fst (nthz (qb_elems (qb_absorb c n)) i (0, 0))))]).
  { intros mm W MUx WMx DX i Hi. rewrite qb_count_absorb in Hi. cbn [qb_addr qb_elems qb_absorb].
    destruct (Z_lt_le_dec i (qb_count c)) as [LT|GE].
    - rewrite nthz_app_l by (unfold qb_count, zlen in *; lia). eapply (rwT W m1 mm MUx WMx); [exact (SLc1 i ltac:(lia))| cbn; apply DX; unfold QBATCH_CAP in *; lia].
    - rewrite nthz_app_r by (unfold qb_count, zlen in *; lia). replace (zlen (qb_elems c)) with (qb_count c) by reflexivity.
      replace (qb_addr c + 24 + 8 * i) with (qb_addr c + 24 + 8 * (qb_count c + (i - qb_count c))) by lia.
      eapply (rwT W m1 mm MUx WMx); [exact (DONE (i - qb_count c) ltac:(lia))| cbn; apply DX; unfold QBATCH_CAP in *; lia]. }
  destruct (snoc_or_nil' tmp) as [ET|(tq & tL & ET)].
  - (* [comment removed for export] *)
    subst tmp.
    eapply evt_cut.
    { eapply (mg_bodyBE_spec ra sp gp tp _ _ _ s0 s1 a0 a1 a2 _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ t6 F fc m1
                (qb_addr c) (qb_addr n) (qb_count c) (qb_count n) (qb_size c) (qb_size n) (qc_first post)
                (zlen (pre ++ c :: n :: post)) (qc_first (pre ++ c :: n :: post)) (qc_last (pre ++ c :: n :: post)) B ext
                (qc_first []) (qc_last []) (qc_bytes []) (bv_unsigned sp + 16));
        [exact MI1| exact Ha0| exact Ha1| exact Ha2| reflexivity| exact Ha4| exact Ha6| exact Ha7| exact Ht0| reflexivity
        | qlia| qlia| qlia| qlia| exact Fpost| qlia| exact GL| exact Hext| qlia| cbn; qlia| cbn; qlia
        | qlia| qlia| qlia| qlia| exact DJcn| qlia| qlia| exact XH1| exact CC1| exact NC1| exact TMP1]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 12%nat; intros a3' t1'' t2'' m2 -> MU2 WM2 MI2 XH2 CC2 NC2 TMP2).
    rewrite EQ1, EQ2, EQ3 in XH2.
    apply evt_done. unfold mg_post.
    nexists 6%nat. exists m2, (W1 ++ [(qb_addr c, qb_addr c + 24); (qb_addr n, qb_addr n + 24); (A_QUAR + 160, A_QUAR + 192); (bv_unsigned sp + 16, bv_unsigned sp + 16 + 32)]).
    rewrite Ha4. split; [reflexivity|]. split; [exact PI'|].
    (* [comment removed for export] *)
    assert (HWc : Forall (ucz_ok K 24 (bk K c)) [(qb_addr c, qb_addr c + 24)]).
    { unfold ucz_ok. change (csize 24) with 8192. rewrite <- Ec. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
    assert (HWn : Forall (ucz_ok K 24 (bk K n)) [(qb_addr n, qb_addr n + 24); (A_QUAR + 160, A_QUAR + 192); (bv_unsigned sp + 16, bv_unsigned sp + 16 + 32)]).
    { unfold ucz_ok. change (csize 24) with 8192. rewrite <- En. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL in *; lia. }
    (nelimp (far_keep3 K c n n _ _ [] m1 m2 WF Hc Hn Hn HWc HWn ltac:(apply Forall_nil) MU2 WM2) 6%nat; intros Yc Ya Yt Yl Yq Yqb).
    assert (D2 : forall a sz, (a + sz <= AIMG_HI /\ (a + sz <= A_QUAR + 160 \/ A_QUAR + 192 <= a)) \/ (st_t K <= a /\ a + sz <= st_t K + 4096)
                               \/ (qb_addr c + 24 <= a /\ a + sz <= qb_addr c + 8192) \/ (qb_addr n + 24 <= a /\ a + sz <= qb_addr n + 8192)
                               \/ (a + sz <= KHIGHMEM_BEG /\ AIMG_HI <= a) \/ (CEIL <= a /\ a + sz <= bv_unsigned sp + 16) -> disjoint_from
                 [(qb_addr c, qb_addr c + 24); (qb_addr n, qb_addr n + 24); (A_QUAR + 160, A_QUAR + 192); (bv_unsigned sp + 16, bv_unsigned sp + 16 + 32)] a sz).
    { intros a sz Ha. cbn. unfold A_QUAR, A_ALLOC, AIMG_HI, KHIGHMEM_BEG, QBATCH_SIZE, CEIL in *. repeat split; blia. }
    assert (FARQ : forall x nxt, In x (qt ++ (pre ++ c :: n :: post) ++ map fst cur) ->
              qb_addr x <> qb_addr c -> qb_addr x <> qb_addr n -> QBC m1 x nxt -> QBC m2 x nxt).
    { intros x nxt Hx N1 N2 Q. destruct (ALL x ltac:(memb Hx)) as [U1 U2].
      exact (Yqb x nxt U1 U2 N1 N2 N2 Q). }
    split.
    { (* [comment removed for export] *)
      split; [exact (Yc CO1)|]. split; [exact (Ya A41)|].
      split; [apply (UZ_QA _ m1 m2 MU2 WM2 XA1); apply D2; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [apply (UZ_QLK _ m1 m2 MU2 WM2 1 1 XL1); apply D2; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [exact XH2|].
      split; [apply (UZ_QS _ m1 m2 MU2 WM2 XS1); apply D2; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [exact (Yt TX1)|].
      split; [apply (UZ_TC K _ m1 m2 MU2 WM2 qt TC1); apply D2; right; left; unfold qcache_t, T_QCACHE; lia|].
      split; [exact (Yl LV1)|]. split; [exact (Yq QR1)|].
      split.
      { apply (qlist_far m1 m2 qt); [| exact RLt1]. intros x nxt Hx Q.
        apply (FARQ x nxt); [memb Hx| apply NDc; memb Hx| apply NDn; memb Hx| exact Q]. }
      split.
      { apply (proj2 (R_qlist_app m2 pre (qb_absorb c n :: post))). split.
        - intros q1 x q2 E. rewrite (qc_first_absorb q2 c n post (n :: post)).
          apply (FARQ x); [rewrite E; memb0| apply NDc; rewrite E; memb0| apply NDn; rewrite E; memb0| exact (PRE1 q1 x q2 E)].
        - apply R_qlist_cons. split.
          + split; [cbn [qb_addr qb_absorb]; rewrite qb_size_absorb, qb_count_absorb; unfold QBATCH_SIZE; exact CC2|].
            split; [cbn [qb_addr qb_absorb]; eapply visT; [exact WM2| exact Vc1| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]|].
            split; [apply (SLOTS m2 _ MU2 WM2); intros a sz H1 H2; apply D2; right; right; left; lia|].
            cbn [qb_addr qb_absorb]. eapply (rwT _ m1 m2 MU2 WM2); [exact SHc1|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. change (8192/8) with 1024.
            apply D2. right; right; right; right; left. clear - Gc1 Gc2. unfold SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, CEIL in *. Z.div_mod_to_equations. lia.
          + apply (qlist_far m1 m2 post); [| exact RLpost1]. intros x nxt Hx Q.
            apply (FARQ x nxt); [memb Hx| apply NDc; memb Hx| apply NDn; memb Hx| exact Q]. }
      split.
      { cbn [app]. apply R_qlist_one. split; [cbn [qb_addr]; exact NC2|].
        split; [cbn [qb_addr]; eapply visT; [exact WM2| exact Vn1| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]|].
        split; [intros i Hi; unfold qb_count in Hi; cbn in Hi; lia|].
        cbn [qb_addr]. eapply (rwT _ m1 m2 MU2 WM2); [exact SHn1|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. change (8192/8) with 1024.
        apply D2. right; right; right; right; left. clear - Gn1 Gn2. unfold SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, CEIL in *. Z.div_mod_to_equations. lia. }
      intros bd Hbd. pose proof (in_map fst cur bd Hbd) as Hb1. destruct (RC1 bd Hbd) as [[nx HL] HS].
      destruct (FARQ (fst bd) nx ltac:(memb Hb1) ltac:(apply NDc; memb Hb1) ltac:(apply NDn; memb Hb1) (conj HL HS)) as [HL' HS'].
      split; [exists nx; exact HL'| exact HS']. }
    split; [rewrite qc_bytes_app, qc_bytes_cons, qb_size_absorb; unfold QBATCH_SIZE; lia|].
    split.
    { cbn [app zlen length Z.of_nat Pos.of_succ_nat qc_first qc_last last qc_bytes fold_right qb_addr]. unfold rec_frame.
      apply (proj2 (rw_cells_app m2 (bv_unsigned sp + 16) [C8 (wz 1); C8 (wz (qb_addr n)); C8 (wz (qb_addr n)); C8 (wz (qb_size {| qb_addr := qb_addr n; qb_elems := [] |} + 0))] _)).
      split; [unfold qb_size; cbn [qb_elems fold_right]; cbn [qc_bytes fold_right] in TMP2; replace (0 + 8192) with (QBATCH_SIZE + 0 + 0) in TMP2 by reflexivity; exact TMP2|].
      eapply (rwT _ m1 m2 MU2 WM2); [exact SAV1| cbn; unfold A_QUAR, A_ALLOC, QBATCH_SIZE, CEIL in *; repeat split; lia]. }
    split; [eapply (rwT _ m1 m2 MU2 WM2); [exact FRM1| cbn; unfold mg_frame; cbn; unfold A_QUAR, A_ALLOC, QBATCH_SIZE, CEIL in *; repeat split; lia]|].
    split; [exact MI2|]. split; [eapply munch_cat; [exact MU1| exact MU2]|].
    split; [| eapply wmono_trans; [exact WM1| exact WM2]].
    (nelim (qall_of_addr K c Hc) 3%nat; intros c0 Hc0 Ec0). (nelim (qall_of_addr K n Hn) 3%nat; intros n0 Hn0 En0).
    subst W1. unfold dwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + do 3 right. exists c0. split; [exact Hc0|]. rewrite Ec0. unfold QBATCH_SIZE, QBATCH_CAP in *. lia.
    + do 3 right. exists c0. split; [exact Hc0|]. rewrite Ec0. unfold QBATCH_SIZE in *. lia.
    + do 3 right. exists n0. split; [exact Hn0|]. rewrite En0. unfold QBATCH_SIZE in *. lia.
    + right. left. lia.
    + left. lia.
  - (* [comment removed for export] *)
    assert (TNE : tmp <> []) by (rewrite ET; destruct tq; discriminate).
    assert (INt : In tL (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur)) by (rewrite ET; memb0).
    destruct (ALL tL INt) as [Ht Ct]. (nelimp (batch_facts_a K tL WF Ht) 4%nat; intros Gt1 Gt2 Gt3 Gt4).
    assert (NDt : forall x, In x ((qt ++ (pre ++ c :: n :: post) ++ tq) ++ map fst cur) -> qb_addr x <> qb_addr tL).
    { intros x Hx. apply (nodup_map_mid qb_addr (qt ++ (pre ++ c :: n :: post) ++ tq) (map fst cur) tL x); [| exact Hx].
      rewrite ET in ND. repeat rewrite <- app_assoc in ND. cbn [app] in ND. repeat rewrite <- app_assoc. cbn [app]. exact ND. }
    assert (NEct : qb_addr c <> qb_addr tL) by (apply NDt; memb0).
    assert (NEnt : qb_addr n <> qb_addr tL) by (apply NDt; memb0).
    pose proof (batch_disj K (qb_addr c) (qb_addr tL) WF Hc Ht NEct) as DJct.
    pose proof (batch_disj K (qb_addr n) (qb_addr tL) WF Hn Ht NEnt) as DJnt.
    pose proof (proj1 (R_qlist_iff m1 tmp) RL31 tq tL [] ET) as TQB. cbn [qc_first] in TQB. apply QBC_split in TQB as [TLNK1 TBX1].
    replace (qc_last tmp) with (qb_addr tL) in TMP1 by (rewrite ET, qc_last_snoc; reflexivity).
    pose proof (zlen_pos_ne tmp TNE) as ZT. pose proof (qc_bytes_lb tmp) as LBT.
    eapply evt_cut.
    { eapply (mg_bodyBN_spec ra sp gp tp _ _ _ s0 s1 a0 a1 a2 _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ t6 F fc m1
                (qb_addr c) (qb_addr n) (qb_count c) (qb_count n) (qb_size c) (qb_size n) (qc_first post)
                (zlen (pre ++ c :: n :: post)) (qc_first (pre ++ c :: n :: post)) (qc_last (pre ++ c :: n :: post)) B ext
                (zlen tmp) (qc_first tmp) (qb_addr tL) (qc_bytes tmp) (bv_unsigned sp + 16));
        [exact MI1| exact Ha0| exact Ha1| exact Ha2| reflexivity| exact Ha4| exact Ha6| exact Ha7| exact Ht0| reflexivity
        | qlia| qlia| qlia| qlia| exact Fpost| qlia| exact GL| exact Hext| qlia| qlia| qlia| qlia| exact TF
        | qlia| qlia| qlia| qlia| qlia| qlia| exact DJcn| qlia| qlia| qlia| qlia
        | exact XH1| exact CC1| exact NC1| exact TMP1| exact TLNK1]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 13%nat; intros a3' t1'' t2'' m2 -> MU2 WM2 MI2 XH2 CC2 NC2 TMP2 TL2).
    rewrite EQ1, EQ2, EQ3 in XH2.
    apply evt_done. unfold mg_post.
    nexists 6%nat. exists m2, (W1 ++ [(qb_addr c, qb_addr c + 24); (qb_addr n, qb_addr n + 24); (A_QUAR + 160, A_QUAR + 192); (bv_unsigned sp + 16, bv_unsigned sp + 16 + 32); (qb_addr tL, qb_addr tL + 8)]).
    rewrite Ha4. split; [reflexivity|]. split; [exact PI'|].
    (* [comment removed for export] *)
    assert (HWc : Forall (ucz_ok K 24 (bk K c)) [(qb_addr c, qb_addr c + 24)]).
    { unfold ucz_ok. change (csize 24) with 8192. rewrite <- Ec. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
    assert (HWn : Forall (ucz_ok K 24 (bk K n)) [(qb_addr n, qb_addr n + 24); (A_QUAR + 160, A_QUAR + 192); (bv_unsigned sp + 16, bv_unsigned sp + 16 + 32)]).
    { unfold ucz_ok. change (csize 24) with 8192. rewrite <- En. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL in *; lia. }
    destruct (bk_used_a K tL WF Ht) as [UKt Et].
    assert (HWt : Forall (ucz_ok K 24 (bk K tL)) [(qb_addr tL, qb_addr tL + 8)]).
    { unfold ucz_ok. change (csize 24) with 8192. rewrite <- Et. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
    (nelimp (far_keep3 K c n tL _ _ _ m1 m2 WF Hc Hn Ht HWc HWn HWt MU2 WM2) 6%nat; intros Yc Ya Yt Yl Yq Yqb).
    assert (D2 : forall a sz, (a + sz <= AIMG_HI /\ (a + sz <= A_QUAR + 160 \/ A_QUAR + 192 <= a)) \/ (st_t K <= a /\ a + sz <= st_t K + 4096)
                               \/ (qb_addr c + 24 <= a /\ a + sz <= qb_addr c + 8192) \/ (qb_addr n + 24 <= a /\ a + sz <= qb_addr n + 8192)
                               \/ (a + sz <= KHIGHMEM_BEG /\ AIMG_HI <= a) \/ (CEIL <= a /\ a + sz <= bv_unsigned sp + 16) -> disjoint_from
                 [(qb_addr c, qb_addr c + 24); (qb_addr n, qb_addr n + 24); (A_QUAR + 160, A_QUAR + 192); (bv_unsigned sp + 16, bv_unsigned sp + 16 + 32); (qb_addr tL, qb_addr tL + 8)] a sz).
    { intros a sz Ha. cbn. unfold A_QUAR, A_ALLOC, AIMG_HI, KHIGHMEM_BEG, QBATCH_SIZE, CEIL in *. repeat split; (cut_on [T2 Gc1 Gc2 Gc4 Gn1 Gn2 Gn4 DJcn Gt1 Gt2 Gt4 DJct DJnt Ha T1 HCL LO] blia). }
    assert (SUBtq : forall y, In y (qt ++ (pre ++ c :: n :: post) ++ tq ++ map fst cur) -> In y (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur)).
    { intros y Hy. rewrite ET. memb Hy. }
    assert (FARQ : forall x nxt, In x (qt ++ (pre ++ c :: n :: post) ++ tq ++ map fst cur) ->
              qb_addr x <> qb_addr c -> qb_addr x <> qb_addr n -> qb_addr x <> qb_addr tL -> QBC m1 x nxt -> QBC m2 x nxt).
    { intros x nxt Hx N1 N2 N3 Q. destruct (ALL x (SUBtq x Hx)) as [U1 U2].
      exact (Yqb x nxt U1 U2 N1 N2 N3 Q). }
    split.
    { (* [comment removed for export] *)
      split; [exact (Yc CO1)|]. split; [exact (Ya A41)|].
      split; [apply (UZ_QA _ m1 m2 MU2 WM2 XA1); apply D2; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [apply (UZ_QLK _ m1 m2 MU2 WM2 1 1 XL1); apply D2; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [exact XH2|].
      split; [apply (UZ_QS _ m1 m2 MU2 WM2 XS1); apply D2; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [exact (Yt TX1)|].
      split; [apply (UZ_TC K _ m1 m2 MU2 WM2 qt TC1); apply D2; right; left; unfold qcache_t, T_QCACHE; lia|].
      split; [exact (Yl LV1)|]. split; [exact (Yq QR1)|].
      split.
      { apply (qlist_far m1 m2 qt); [| exact RLt1]. intros x nxt Hx Q.
        apply (FARQ x nxt); [memb Hx| apply NDc; memb Hx| apply NDn; memb Hx| apply NDt; memb Hx| exact Q]. }
      split.
      { apply (proj2 (R_qlist_app m2 pre (qb_absorb c n :: post))). split.
        - intros q1 x q2 E. rewrite (qc_first_absorb q2 c n post (n :: post)).
          apply (FARQ x); [rewrite E; memb0| apply NDc; rewrite E; memb0| apply NDn; rewrite E; memb0| apply NDt; rewrite E; memb0| exact (PRE1 q1 x q2 E)].
        - apply R_qlist_cons. split.
          + split; [cbn [qb_addr qb_absorb]; rewrite qb_size_absorb, qb_count_absorb; unfold QBATCH_SIZE; exact CC2|].
            split; [cbn [qb_addr qb_absorb]; eapply visT; [exact WM2| exact Vc1| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]|].
            split; [apply (SLOTS m2 _ MU2 WM2); intros a sz H1 H2; apply D2; right; right; left; lia|].
            cbn [qb_addr qb_absorb]. eapply (rwT _ m1 m2 MU2 WM2); [exact SHc1|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. change (8192/8) with 1024.
            apply D2. right; right; right; right; left. clear - Gc1 Gc2. unfold SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, CEIL in *. Z.div_mod_to_equations. lia.
          + apply (qlist_far m1 m2 post); [| exact RLpost1]. intros x nxt Hx Q.
            apply (FARQ x nxt); [memb Hx| apply NDc; memb Hx| apply NDn; memb Hx| apply NDt; memb Hx| exact Q]. }
      split.
      { rewrite ET, <- app_assoc. apply (proj2 (R_qlist_app m2 tq ([tL] ++ [{| qb_addr := qb_addr n; qb_elems := [] |}]))). split.
        - intros q1 x q2 E. cbn [app]. rewrite (qc_first_app_cons q2 tL [{| qb_addr := qb_addr n; qb_elems := [] |}] []).
          apply (FARQ x); [rewrite E; memb0| apply NDc; rewrite ET, E; memb0| apply NDn; rewrite ET, E; memb0| apply NDt; rewrite E; memb0|].
          exact (proj1 (R_qlist_iff m1 tmp) RL31 q1 x (q2 ++ [tL]) ltac:(rewrite ET, E, <- app_assoc; reflexivity)).
        - cbn [app]. apply R_qlist_cons. split.
          + cbn [qc_first qb_addr]. apply QBC_split. split; [exact TL2|].
            apply (QBCx_keep_g K _ m1 m2 tL WF MU2 WM2 Ht Ct TBX1).
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
            * do 4 right. exists (qb_addr c). split; [exact Hc|]. split; [exact NEct|]. unfold QBATCH_SIZE. lia.
            * do 4 right. exists (qb_addr n). split; [exact Hn|]. split; [exact NEnt|]. unfold QBATCH_SIZE. lia.
            * right. left. unfold A_QUAR, A_ALLOC, AIMG_HI. lia.
            * left. unfold CEIL in *. lia.
            * do 3 right. left. lia.
          + apply R_qlist_one. split; [cbn [qb_addr]; exact NC2|].
            split; [cbn [qb_addr]; eapply visT; [exact WM2| exact Vn1| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]|].
            split; [intros i Hi; unfold qb_count in Hi; cbn in Hi; lia|].
            cbn [qb_addr]. eapply (rwT _ m1 m2 MU2 WM2); [exact SHn1|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. change (8192/8) with 1024.
            apply D2. right; right; right; right; left. clear - Gn1 Gn2. unfold SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, CEIL in *. Z.div_mod_to_equations. lia. }
      intros bd Hbd. pose proof (in_map fst cur bd Hbd) as Hb1. destruct (RC1 bd Hbd) as [[nx HL] HS].
      destruct (FARQ (fst bd) nx ltac:(memb Hb1) ltac:(apply NDc; memb Hb1) ltac:(apply NDn; memb Hb1) ltac:(apply NDt; memb Hb1) (conj HL HS)) as [HL' HS'].
      split; [exists nx; exact HL'| exact HS']. }
    split; [rewrite qc_bytes_app, qc_bytes_cons, qb_size_absorb; unfold QBATCH_SIZE; lia|].
    split.
    { rewrite (zlen_app tmp), (qc_first_app_l tmp _ TNE), qc_last_snoc, (qc_bytes_app tmp). cbn [zlen length Z.of_nat Pos.of_succ_nat qb_addr qc_bytes fold_right].
      unfold rec_frame.
      apply (proj2 (rw_cells_app m2 (bv_unsigned sp + 16) [C8 (wz (zlen tmp + 1)); C8 (wz (qc_first tmp)); C8 (wz (qb_addr n)); C8 (wz (qc_bytes tmp + (qb_size {| qb_addr := qb_addr n; qb_elems := [] |} + 0)))] _)).
      split; [unfold qb_size; cbn [qb_elems fold_right]; replace (qc_bytes tmp + (QBATCH_SIZE + 0 + 0)) with (qc_bytes tmp + 8192) by (unfold QBATCH_SIZE; lia); exact TMP2|].
      eapply (rwT _ m1 m2 MU2 WM2); [exact SAV1| cbn; unfold A_QUAR, A_ALLOC, QBATCH_SIZE, CEIL in *; repeat split; lia]. }
    split; [eapply (rwT _ m1 m2 MU2 WM2); [exact FRM1| cbn; unfold mg_frame; cbn; unfold A_QUAR, A_ALLOC, QBATCH_SIZE, CEIL in *; repeat split; lia]|].
    split; [exact MI2|]. split; [eapply munch_cat; [exact MU1| exact MU2]|].
    split; [| eapply wmono_trans; [exact WM1| exact WM2]].
    (nelim (qall_of_addr K c Hc) 3%nat; intros c0 Hc0 Ec0). (nelim (qall_of_addr K n Hn) 3%nat; intros n0 Hn0 En0). (nelim (qall_of_addr K tL Ht) 3%nat; intros t0' Ht0' Et0).
    subst W1. unfold dwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + do 3 right. exists c0. split; [exact Hc0|]. rewrite Ec0. unfold QBATCH_SIZE, QBATCH_CAP in *. lia.
    + do 3 right. exists c0. split; [exact Hc0|]. rewrite Ec0. unfold QBATCH_SIZE in *. lia.
    + do 3 right. exists n0. split; [exact Hn0|]. rewrite En0. unfold QBATCH_SIZE in *. lia.
    + right. left. lia.
    + left. lia.
    + do 3 right. exists t0'. split; [exact Ht0'|]. rewrite Et0. unfold QBATCH_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
End MERGE.


End CeilWrap.
End RTW_q_merge2.

(* [comment removed for export] *)
Module RTW_q_merge3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_car OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_zone2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_ms OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_drain2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_bz RTW_q_recw RTW_q_merge1 RTW_q_merge2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac qlia := unfold QBATCH_CAP, QBATCH_SIZE, AIMG_HI, KHIGHMEM_BEG, CEIL in *; idtac; lia.
(* [comment removed for export] *)
Local Ltac zsubst := repeat match goal with x := _ |- _ => subst x end.
Local Ltac memb0 := zsubst; repeat match goal with H : _ |- _ => clear H end;
  rewrite ?in_app_iff; cbn [In]; rewrite ?in_app_iff; cbn [In]; tauto.
Local Ltac memb H := zsubst; move H at top; repeat match goal with H' : _ |- _ => lazymatch H' with H => fail | _ => clear H' end end;
  rewrite ?in_app_iff in H; rewrite ?in_app_iff; cbn [In] in H |- *; rewrite ?in_app_iff in H; rewrite ?in_app_iff; cbn [In] in H |- *; tauto.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MERGE.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variables (qt : list qbatch) (cur : list (qbatch * Z)).
Variables (lo SP : Z).
Local Notation minv := (ainv K qt cur).

Definition mgl_post (ra sp gp tp s0 s1 a0 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (vs4 vs3 vs2 vs1 vs0 vra : word) (j0 : list byte) (vraM : word) (m : word -> option byte) (qg tmp : list qbatch) (B : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a3' a4' t3' t4' t5' : word) (m' : word -> option byte) (Wd : list (Z * Z)) (qg' tmp' : list qbatch) (ext' : Z),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 (wz ext') a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
               F (wz 0x33fd8) fc None m' (seg_rom bsegs)
      /\ minv qg' tmp' /\ QXb K m' 1 1 qt qg' tmp' cur B /\ B = qc_bytes qg' + ext' /\ 0 <= ext' /\ qg' <> []
      /\ qc_first qg' = qc_first qg
      /\ rw_cells bsegs m' (bv_unsigned sp + 16) (rec_frame (zlen tmp') (qc_first tmp') (qc_last tmp') (qc_bytes tmp') vs4 vs3 vs2 vs1 vs0 vra)
      /\ rw_cells bsegs m' (bv_unsigned sp) (mg_frame j0 vraM)
      /\ mem_inv bsegs m' /\ munch Wd m m' /\ Forall (dwin K lo SP) Wd /\ wmono bsegs m m'.

Theorem mg_loop : forall (k : nat)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (j0 : list byte) (vraM : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (pre rest tmp : list qbatch) (c : qbatch) (B ext : Z),
  (length rest <= k)%nat -> rest <> [] ->
  minv (pre ++ c :: rest) tmp ->
  QXb K m 1 1 qt (pre ++ c :: rest) tmp cur B -> mem_inv bsegs m ->
  B = qc_bytes (pre ++ c :: rest) + ext -> 0 <= ext -> B < 2^61 ->
  a0 = wz (A_QUAR + 160) -> a1 = wz (bv_unsigned sp + 16) -> a2 = wz ext -> a4 = wz (qb_addr c) -> a5 = wz 1021 -> a6 = wz (-8192) -> a7 = wz 8192 ->
  t0 = wz (qc_first rest) ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 96 <= SP -> SP <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp + 16) (rec_frame (zlen tmp) (qc_first tmp) (qc_last tmp) (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m (bv_unsigned sp) (mg_frame j0 vraM) ->
  evt bsegs (mgl_post ra sp gp tp s0 s1 a0 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc vs4 vs3 vs2 vs1 vs0 vra j0 vraM m (pre ++ c :: rest) tmp B)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33ef4) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until ext; intros Hlen RNE PI X MI HB Hext HB2 Ha0 Ha1 Ha2 Ha4 Ha5 Ha6 Ha7 Ht0 HCL LO SPB SPH FR FRM.
  { destruct rest; [congruence| cbn in Hlen; lia]. }
  destruct rest as [|n post]; [congruence|]. cbn in Hlen. cbn [qc_first] in Ht0.
  pose proof (t_range K WF) as [T1 T2]. pose proof HCL as HCL0. idtac.
  assert (INc : In c (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur)) by memb0.
  assert (INn : In n (qt ++ (pre ++ c :: n :: post) ++ tmp ++ map fst cur)) by memb0.
  pose proof (ainv_addr K qt cur _ _ c PI INc) as Hc. pose proof (ainv_addr K qt cur _ _ n PI INn) as Hn.
  pose proof (ainv_cnt K qt cur _ _ c PI INc) as Cc. pose proof (ainv_cnt K qt cur _ _ n PI INn) as Cn.
  (nelimp (batch_facts_a K c WF Hc) 4%nat; intros Gc1 Gc2 Gc3 Gc4). (nelimp (batch_facts_a K n WF Hn) 4%nat; intros Gn1 Gn2 Gn3 Gn4).
  assert (SUBpost : forall x, In x post -> In (qb_addr x) (qbatch_addrs K)) by (intros x Hx; apply (ainv_addr K qt cur _ _ x PI); memb Hx).
  assert (Fpost : 0 <= qc_first post < 2^64).
  { destruct post as [|x l]; [cbn; lia|]. cbn [qc_first]. pose proof (batch_facts_a K x WF (SUBpost x ltac:(left; reflexivity))). qlia. }
  destruct (Z_le_gt_dec (qb_count c + qb_count n) QBATCH_CAP) as [FIT|NOFIT].
  - (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (mg_step K WF qt cur lo SP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 vs4 vs3 vs2 vs1 vs0 vra j0 vraM F fc m pre post tmp c n B ext);
        try eassumption. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 18%nat; intros a3' t1' t2' t3' t4' t5' m1 Wd1 -> PI1 X1 HB1 FR1 FRM1 MI1 MU1 HW1 WM1).
    pose proof (qc_bytes_nonneg (pre ++ qb_absorb c n :: post)) as BP.
    destruct post as [|n2 post'].
    + (* [comment removed for export] *)
      cbn [qc_first]. cbv beta delta [wz]. leaf_prep.
      lstep; if_lia. (* [comment removed for export] *)
      apply evt_done. unfold mgl_post.
      nexists 8%nat. exists m1, Wd1, (pre ++ [qb_absorb c n]), (tmp ++ [{| qb_addr := qb_addr n; qb_elems := [] |}]), (ext + 8192).
      split; [reflexivity|]. split; [exact PI1|]. split; [exact X1|]. split; [exact HB1|]. split; [lia|].
      split; [destruct pre; discriminate|]. split; [apply qc_first_absorb|].
      split; [exact FR1|]. split; [exact FRM1|]. split; [exact MI1|]. split; [exact MU1|]. split; [exact HW1| exact WM1].
    + (* [comment removed for export] *)
      cbn [qc_first]. pose proof (batch_facts_a K n2 WF (SUBpost n2 ltac:(left; reflexivity))) as (G21 & _). unfold KHIGHMEM_BEG, AIMG_HI in G21.
      cbv beta delta [wz]. leaf_prep.
      lstep; if_lia. (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (IH ra _ gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ t6 vs4 vs3 vs2 vs1 vs0 vra j0 vraM F fc m1
                  pre (n2 :: post') (tmp ++ [{| qb_addr := qb_addr n; qb_elems := [] |}]) (qb_absorb c n) B (ext + 8192));
          try reflexivity; try eassumption; try lia; try discriminate. }
      cbv beta. intros ms2 nelH_; (nelim nelH_ 26%nat; intros u0 u1 u2 u3 u4 u5 u6 u7 m2 Wd2 qg' tmp' ext' -> PI2 X2 HB2' Hext2 NE2 QF2 FR2 FRM2 MI2 MU2 HW2 WM2).
      apply evt_done. unfold mgl_post.
      nexists 8%nat. exists m2, (Wd1 ++ Wd2), qg', tmp', ext'.
      split; [reflexivity|]. split; [exact PI2|]. split; [exact X2|]. split; [exact HB2'|]. split; [exact Hext2|]. split; [exact NE2|].
      split; [rewrite QF2; apply qc_first_absorb|].
      split; [exact FR2|]. split; [exact FRM2|]. split; [exact MI2|].
      split; [eapply munch_cat; [exact MU1| exact MU2]|].
      split; [apply Forall_app; split; [exact HW1| exact HW2]| eapply wmono_trans; [exact WM1| exact WM2]].
  - (* [comment removed for export] *)
    (nelimp X 14%nat; intros CO A4 XA XL XH XS TX TCq LV QR RL1 RL2 RL3 RC).
    pose proof (proj1 (R_qlist_iff m _) RL2 pre c (n :: post) eq_refl) as (CC & _). cbn [qc_first] in CC.
    pose proof (proj1 (R_qlist_iff m _) RL2 (pre ++ [c]) n post ltac:(rewrite <- app_assoc; reflexivity)) as (NC & _).
    eapply evt_cut.
    { eapply (mg_skip_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ _ F fc m
                (qb_addr c) (qb_addr n) (qb_count c) (qb_count n) (qc_first post));
        [exact MI| exact Ha4| exact Ht0| exact Ha5| exact Cc| exact Cn| lia| exact Fpost| qlia| qlia| qlia| qlia| exact CC| exact NC]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 4%nat; intros t1' t3' t4' ->).
    destruct post as [|n2 post'].
    + (* [comment removed for export] *)
      cbn [qc_first Z.eqb]. apply evt_done. unfold mgl_post.
      nexists 8%nat. exists m, [], (pre ++ c :: [n]), tmp, ext.
      split; [rewrite Ha2; reflexivity|]. split; [exact PI|]. split; [exact X|]. split; [exact HB|]. split; [exact Hext|].
      split; [destruct pre; discriminate|]. split; [reflexivity|].
      split; [exact FR|]. split; [exact FRM|]. split; [exact MI|]. split; [apply munch_refl|]. split; [apply Forall_nil| apply wmono_refl].
    + cbn [qc_first]. pose proof (batch_facts_a K n2 WF (SUBpost n2 ltac:(left; reflexivity))) as (G21 & _).
      replace (qb_addr n2 =? 0) with false by (symmetry; apply Z.eqb_neq; unfold KHIGHMEM_BEG, AIMG_HI in G21; lia).
      eapply evt_cut.
      { eapply (IH ra sp gp tp _ _ t2 s0 s1 a0 a1 a2 a3 _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 vs4 vs3 vs2 vs1 vs0 vra j0 vraM F fc m
                  (pre ++ [c]) (n2 :: post') tmp n B ext);
          try reflexivity; try eassumption; try lia; try discriminate; rewrite <- ?app_assoc; cbn [app]; try eassumption; try reflexivity. }
      cbv beta. intros ms2 nelH_; (nelim nelH_ 26%nat; intros u0 u1 u2 u3 u4 u5 u6 u7 m2 Wd2 qg' tmp' ext' -> PI2 X2 HB2' Hext2 NE2 QF2 FR2 FRM2 MI2 MU2 HW2 WM2).
      apply evt_done. unfold mgl_post.
      nexists 8%nat. exists m2, Wd2, qg', tmp', ext'.
      split; [reflexivity|]. split; [exact PI2|]. split; [exact X2|]. split; [exact HB2'|]. split; [exact Hext2|]. split; [exact NE2|].
      split; [rewrite QF2, <- app_assoc; cbn [app]; destruct pre; reflexivity|].
      split; [exact FR2|]. split; [exact FRM2|]. split; [exact MI2|]. split; [exact MU2|]. split; [exact HW2| exact WM2].
Qed.

(* [comment removed for export] *)
Definition mgf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (vs4 vs3 vs2 vs1 vs0 vra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (Wd : list (Z * Z)) (qg' tmp' : list qbatch),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ minv qg' tmp' /\ QX K m' 1 1 qt qg' tmp' cur /\ qg' <> []
      /\ rw_cells bsegs m' (bv_unsigned sp) (rec_frame (zlen tmp') (qc_first tmp') (qc_last tmp') (qc_bytes tmp') vs4 vs3 vs2 vs1 vs0 vra)
      /\ mem_inv bsegs m' /\ munch Wd m m' /\ Forall (dwin K lo SP) Wd /\ wmono bsegs m m'.

Theorem mg_full :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (qg tmp : list qbatch),
  minv qg tmp -> qg <> [] ->
  QX K m 1 1 qt qg tmp cur -> mem_inv bsegs m ->
  a0 = wz (A_QUAR + 160) -> a1 = sp -> 4096 <= bv_unsigned ra ->
  alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp -> bv_unsigned sp + 80 <= SP -> SP <= 2^64 ->
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame (zlen tmp) (qc_first tmp) (qc_last tmp) (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (mgf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vs4 vs3 vs2 vs1 vs0 vra m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQMERGE) fc None m (seg_rom bsegs)).
Proof.
  intros until tmp. intros PI QNE X MI Ha0 -> Hra HCL LO SPB SPH ST FR.
  (nelimp X 14%nat; intros CO A4 XA XL XH XS TX TCq LV QR RL1 RL2 RL3 RC). unfold QH4 in XH.
  pose proof (t_range K WF) as [T1 T2]. pose proof HCL as HCL0. idtac.
  destruct qg as [|b1 qg1]; [congruence|].
  assert (IN1 : In b1 (qt ++ (b1 :: qg1) ++ tmp ++ map fst cur)) by memb0.
  pose proof (ainv_addr K qt cur _ _ b1 PI IN1) as H1. pose proof (ainv_cnt K qt cur _ _ b1 PI IN1) as C1.
  (nelimp (batch_facts_a K b1 WF H1) 4%nat; intros G1 G2 G3 G4).
  pose proof (proj1 (proj1 (R_qlist_cons m b1 qg1) RL2)) as (B1C & _).
  (nelimp PI 4%nat; intros _ _ _ BB). rewrite qc_bytes_cons in BB. pose proof (qc_bytes_nonneg qg1) as B0. pose proof (qc_bytes_nonneg tmp) as BT0. pose proof (qb_size_lb' b1) as S1.
  destruct qg1 as [|b2 rest].
  - (* [comment removed for export] *)
    cbn [qc_first] in B1C.
    eapply evt_cut.
    { eapply (mg_entry1_spec ra sp gp tp t0 t1 t2 s0 s1 a0 sp a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ F fc m
                (zlen [b1]) (qb_addr b1) (qc_last [b1]) (qc_bytes [b1]) lo);
        [exact MI| exact Ha0| qlia| cbn [qc_bytes fold_right]; lia| qlia| qlia| exact ST| qlia| lia| lia| exact XH| exact B1C]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 10%nat; intros a1' a4' t0' m1 -> MU1 WM1 MI1 ST1 XH1).
    apply evt_done. unfold mgf_post.
    nexists 15%nat. exists m1, [(bv_unsigned sp - 16, bv_unsigned sp); (A_QUAR + 184, A_QUAR + 192)], [b1], tmp.
    split; [reflexivity|]. split; [exact PI|].
    destruct (bk_used_a K b1 WF H1) as [UK1 E1].
    assert (HW1 : Forall (ucz_ok K 24 (bk K b1)) [(bv_unsigned sp - 16, bv_unsigned sp); (A_QUAR + 184, A_QUAR + 192)]).
    { unfold ucz_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL in *; lia. }
    (nelimp (bzone_a K WF b1 H1 _ HW1 m m1 MU1 WM1) 8%nat; intros Zc Za Zt Zl Zq Zrl Zcu Zqb).
    assert (D1 : forall a sz, (a + sz <= A_QUAR + 184 \/ (A_QUAR + 192 <= a /\ a + sz <= CEIL)) -> disjoint_from [(bv_unsigned sp - 16, bv_unsigned sp); (A_QUAR + 184, A_QUAR + 192)] a sz).
    { intros a sz Ha. cbn. unfold A_QUAR, A_ALLOC, CEIL in *. repeat split; lia. }
    pose proof (ainv_nodup K WF qt cur _ _ PI) as ND.
    assert (NE1 : forall x, In x (qt ++ (tmp ++ map fst cur)) -> qb_addr x <> qb_addr b1).
    { intros x Hx. exact (nodup_map_mid qb_addr qt (tmp ++ map fst cur) b1 x ND Hx). }
    assert (ALL : forall x, In x (qt ++ [b1] ++ tmp ++ map fst cur) -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP).
    { intros x Hx. split; [exact (ainv_addr K qt cur _ _ x PI Hx)| exact (ainv_cnt K qt cur _ _ x PI Hx)]. }
    split.
    { split; [exact (Zc CO)|]. split; [exact (Za A4)|].
      split; [apply (UZ_QA _ m m1 MU1 WM1 XA); apply D1; unfold A_QUAR, A_ALLOC; lia|].
      split; [apply (UZ_QLK _ m m1 MU1 WM1 1 1 XL); apply D1; unfold A_QUAR, A_ALLOC; lia|].
      split; [exact XH1|].
      split; [apply (UZ_QS _ m m1 MU1 WM1 XS); apply D1; unfold A_QUAR, A_ALLOC, AIMG_HI, CEIL; lia|].
      split; [exact (Zt TX)|].
      split; [apply (UZ_TC K _ m m1 MU1 WM1 qt TCq); apply D1; unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, CEIL, KHIGHMEM_BEG, AIMG_HI in *; blia|].
      split; [exact (Zl LV)|]. split; [exact (Zq QR)|].
      split; [apply (Zrl qt RL1); intros x Hx; destruct (ALL x ltac:(memb Hx)) as [U1 U2]; split; [exact U1| split; [exact U2| apply NE1; memb Hx]]|].
      split.
      { apply R_qlist_one. pose proof (proj1 (R_qlist_one m b1) RL2) as Q1. apply QBC_split in Q1 as [Q1 Q2]. apply QBC_split. split.
        - eapply (rwT _ m m1 MU1 WM1); [exact Q1| cbn; apply D1; right; unfold A_QUAR, A_ALLOC, QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *; lia].
        - apply (QBCx_keep_a K _ m m1 b1 WF MU1 WM1 H1 C1 Q2). repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold A_QUAR, A_ALLOC, AIMG_HI, CEIL in *; lia. }
      split; [apply (Zrl tmp RL3); intros x Hx; destruct (ALL x ltac:(memb Hx)) as [U1 U2]; split; [exact U1| split; [exact U2| apply NE1; memb Hx]]|].
      apply (Zcu cur RC). intros bd Hbd. pose proof (in_map fst cur bd Hbd) as Hb1. destruct (ALL (fst bd) ltac:(memb Hb1)) as [U1 U2]. split; [exact U1| split; [exact U2| apply NE1; memb Hb1]]. }
    split; [discriminate|].
    split; [eapply (rwT _ m m1 MU1 WM1); [exact FR| cbn; unfold rec_frame; cbn; unfold A_QUAR, A_ALLOC, CEIL in *; repeat split; lia]|].
    split; [exact MI1|]. split; [exact MU1|]. split; [| exact WM1].
    unfold dwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [left; lia| right; left; lia].
  - (* [comment removed for export] *)
    cbn [qc_first] in B1C.
    assert (IN2 : In b2 (qt ++ (b1 :: b2 :: rest) ++ tmp ++ map fst cur)) by memb0.
    pose proof (ainv_addr K qt cur _ _ b2 PI IN2) as H2. (nelimp (batch_facts_a K b2 WF H2) 3%nat; intros G21 G22 _).
    eapply evt_cut.
    { eapply (mg_entry2_spec ra sp gp tp t0 t1 t2 s0 s1 a0 sp a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ F fc m
                (zlen (b1 :: b2 :: rest)) (qb_addr b1) (qc_last (b1 :: b2 :: rest)) (qc_bytes (b1 :: b2 :: rest)) (qb_addr b2) lo);
        [exact MI| exact Ha0| qlia| qlia| qlia| qlia| exact ST| qlia| lia| exact XH| exact B1C]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 8%nat; intros j0 m1 -> MU1 WM1 MI1 ST1 FRM1).
    (* [comment removed for export] *)
    destruct (bk_used_a K b1 WF H1) as [UK1 E1].
    assert (HW1 : Forall (ucz_ok K 24 (bk K b1)) [(bv_unsigned sp - 16, bv_unsigned sp)]).
    { unfold ucz_ok. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold CEIL in *. lia. }
    (nelimp (bzone_a K WF b1 H1 _ HW1 m m1 MU1 WM1) 8%nat; intros Zc Za Zt Zl Zq Zrl Zcu Zqb).
    assert (D1 : forall a sz, a + sz <= CEIL -> disjoint_from [(bv_unsigned sp - 16, bv_unsigned sp)] a sz).
    { intros a sz Ha. cbn. unfold CEIL in *. split; [lia| exact I]. }
    assert (ALL : forall x, In x (qt ++ (b1 :: b2 :: rest) ++ tmp ++ map fst cur) -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP).
    { intros x Hx. split; [exact (ainv_addr K qt cur _ _ x PI Hx)| exact (ainv_cnt K qt cur _ _ x PI Hx)]. }
    assert (X1 : QXb K m1 1 1 qt (b1 :: b2 :: rest) tmp cur (qc_bytes (b1 :: b2 :: rest))).
    { split; [exact (Zc CO)|]. split; [exact (Za A4)|].
      split; [apply (UZ_QA _ m m1 MU1 WM1 XA); apply D1; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QLK _ m m1 MU1 WM1 1 1 XL); apply D1; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QH4 _ m m1 MU1 WM1 _ _ _ _ XH); apply D1; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QS _ m m1 MU1 WM1 XS); apply D1; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [exact (Zt TX)|].
      split; [apply (UZ_TC K _ m m1 MU1 WM1 qt TCq); apply D1; unfold qcache_t, T_QCACHE, CEIL in *; lia|].
      split; [exact (Zl LV)|]. split; [exact (Zq QR)|].
      assert (FAR : forall q, (forall x, In x q -> In x (qt ++ (b1 :: b2 :: rest) ++ tmp ++ map fst cur)) -> R_qlist m q -> R_qlist m1 q).
      { intros q SUB RL. apply (qlist_far m m1 q); [| exact RL]. intros x nxt Hx Q. destruct (ALL x (SUB x Hx)) as [U1 U2].
        destruct (Z.eq_dec (qb_addr x) (qb_addr b1)) as [E|NE].
        - apply QBC_split in Q as [L R]. apply QBC_split. split.
          + eapply (rwT _ m m1 MU1 WM1); [exact L| cbn; apply D1; rewrite E; unfold QBATCH_SIZE, CEIL in *; lia].
          + apply (QBCx_keep_a K _ m m1 x WF MU1 WM1 U1 U2 R). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold CEIL in *. lia.
        - exact (Zqb x nxt U1 U2 NE Q). }
      split; [apply FAR; [intros x Hx; memb Hx| exact RL1]|].
      split; [apply FAR; [intros x Hx; memb Hx| exact RL2]|].
      split; [apply FAR; [intros x Hx; memb Hx| exact RL3]|].
      intros bd Hbd. pose proof (in_map fst cur bd Hbd) as Hb1. destruct (RC bd Hbd) as [[nx HL] HS].
      destruct (ALL (fst bd) ltac:(memb Hb1)) as [U1 U2].
      assert (NE : qb_addr (fst bd) <> qb_addr b1).
      { apply (nodup_map_mid qb_addr qt ((b2 :: rest) ++ tmp ++ map fst cur) b1 (fst bd) (ainv_nodup K WF qt cur _ _ PI)). memb Hb1. }
      destruct (Zqb (fst bd) nx U1 U2 NE (conj HL HS)) as [HL' HS']. split; [exists nx; exact HL'| exact HS']. }
    assert (FR1 : rw_cells bsegs m1 (bv_unsigned sp) (rec_frame (zlen tmp) (qc_first tmp) (qc_last tmp) (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra)).
    { eapply (rwT _ m m1 MU1 WM1); [exact FR| cbn; unfold rec_frame; cbn; split; [lia| exact I]]. }
    replace (bv_unsigned sp - 16) with (bv_unsigned (wz (bv_unsigned sp - 16) : word)) in FRM1, ST1 by (cbv delta [wz]; rewrite unsigned_lit by lia; reflexivity).
    eapply evt_cut.
    { eapply (mg_loop (length (b2 :: rest)) _ (wz (bv_unsigned sp - 16)) gp tp _ t1 t2 s0 s1 a0 sp _ a3 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                vs4 vs3 vs2 vs1 vs0 vra j0 ra F fc m1 [] (b2 :: rest) tmp b1 (qc_bytes (b1 :: b2 :: rest)) 0);
        try reflexivity; try eassumption; try lia; try discriminate.
      - cbn [app]. lia.
      - rewrite qc_bytes_cons. lia.
      - cbv delta [wz]. rewrite unsigned_lit by lia. replace (bv_unsigned sp - 16 + 16) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
      - cbv delta [wz]. rewrite unsigned_lit by lia. lia.
      - cbv delta [wz]. rewrite unsigned_lit by lia. lia.
      - cbv delta [wz]. rewrite unsigned_lit by lia. replace (bv_unsigned sp - 16 + 16) with (bv_unsigned sp) by lia. exact FR1. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 26%nat; intros u0 u1 u2 u3 u4 u5 u6 u7 m2 Wd2 qg' tmp' ext' -> PI2 X2 HB2 Hext2 NE2 QF2 FR2 FRM2 MI2 MU2 HW2 WM2).
    cbv delta [wz] in FR2. rewrite unsigned_lit in FR2 by lia. replace (bv_unsigned sp - 16 + 16) with (bv_unsigned sp) in FR2 by lia.
    (nelimp X2 14%nat; intros CO2 A42 XA2 XL2 XH2 XS2 TX2 TC2 LV2 QR2 RL12 RL22 RL32 RC2). unfold QH4 in XH2.
    (nelimp PI2 4%nat; intros _ _ _ BB2). pose proof (qc_bytes_nonneg qg') as BQ2.
    assert (B63 : qc_bytes (b1 :: b2 :: rest) < 2^63) by (rewrite qc_bytes_cons; lia).
    eapply evt_cut.
    { eapply (mg_exit_spec _ (wz (bv_unsigned sp - 16)) gp tp _ _ _ s0 s1 a0 sp _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ t6 j0 ra F fc m2
                (zlen qg') (qc_first qg') (qc_last qg') (qc_bytes (b1 :: b2 :: rest)) ext' lo);
        [exact MI2| exact Ha0| reflexivity| lia| exact B63| | exact HCL0| cbv delta [wz]; rewrite unsigned_lit by lia; lia| cbv delta [wz]; rewrite unsigned_lit by lia; lia| exact FRM2| exact XH2].
      eapply stk_wmono_noseg; [exact ST1| exact WM2| unfold AIMG_HI, CEIL in *; lia]. }
    cbv beta. intros ms3 nelH_; (nelim nelH_ 7%nat; intros m3 -> MU3 WM3 MI3 ST3 XH3).
    cbv delta [wz] in ST3 |- *. rewrite unsigned_lit in ST3 by lia. rewrite ?unsigned_lit by lia. replace (bv_unsigned sp - 16 + 16) with (bv_unsigned sp) in * by lia.
    rewrite Z_to_bv_bv_unsigned.
    apply evt_done. unfold mgf_post.
    nexists 15%nat. exists m3, ([(bv_unsigned sp - 16, bv_unsigned sp)] ++ Wd2 ++ [(A_QUAR + 184, A_QUAR + 192)]), qg', tmp'.
    split; [reflexivity|]. split; [exact PI2|].
    (* [comment removed for export] *)
    destruct qg' as [|c1 qr]; [congruence|].
    assert (INc1 : In c1 (qt ++ (c1 :: qr) ++ tmp' ++ map fst cur)) by memb0.
    pose proof (ainv_addr K qt cur _ _ c1 PI2 INc1) as Hc1. pose proof (ainv_cnt K qt cur _ _ c1 PI2 INc1) as Cc1.
    destruct (bk_used_a K c1 WF Hc1) as [UKc Ec]. (nelimp (batch_facts_a K c1 WF Hc1) 4%nat; intros Gc1 Gc2 Gc3 Gc4).
    assert (HW3 : Forall (ucz_ok K 24 (bk K c1)) [(A_QUAR + 184, A_QUAR + 192)]).
    { unfold ucz_ok. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
    (nelimp (bzone_a K WF c1 Hc1 _ HW3 m2 m3 MU3 WM3) 8%nat; intros Yc Ya Yt Yl Yq Yrl Ycu Yqb).
    assert (D3 : forall a sz, (a + sz <= A_QUAR + 184 \/ A_QUAR + 192 <= a) -> disjoint_from [(A_QUAR + 184, A_QUAR + 192)] a sz).
    { intros a sz Ha. cbn. split; [lia| exact I]. }
    pose proof (ainv_nodup K WF qt cur _ _ PI2) as ND2.
    assert (NEc : forall x, In x (qt ++ (qr ++ tmp' ++ map fst cur)) -> qb_addr x <> qb_addr c1).
    { intros x Hx. exact (nodup_map_mid qb_addr qt (qr ++ tmp' ++ map fst cur) c1 x ND2 Hx). }
    assert (ALL2 : forall x, In x (qt ++ (c1 :: qr) ++ tmp' ++ map fst cur) -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP).
    { intros x Hx. split; [exact (ainv_addr K qt cur _ _ x PI2 Hx)| exact (ainv_cnt K qt cur _ _ x PI2 Hx)]. }
    split.
    { split; [exact (Yc CO2)|]. split; [exact (Ya A42)|].
      split; [apply (UZ_QA _ m2 m3 MU3 WM3 XA2); apply D3; unfold A_QUAR, A_ALLOC; lia|].
      split; [apply (UZ_QLK _ m2 m3 MU3 WM3 1 1 XL2); apply D3; unfold A_QUAR, A_ALLOC; lia|].
      split; [unfold QH4; replace (qc_bytes (b1 :: b2 :: rest) - ext') with (qc_bytes (c1 :: qr)) in XH3 by lia; exact XH3|].
      split; [apply (UZ_QS _ m2 m3 MU3 WM3 XS2); apply D3; unfold A_QUAR, A_ALLOC; lia|].
      split; [exact (Yt TX2)|].
      split; [apply (UZ_TC K _ m2 m3 MU3 WM3 qt TC2); apply D3; unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *; blia|].
      split; [exact (Yl LV2)|]. split; [exact (Yq QR2)|].
      split; [apply (Yrl qt RL12); intros x Hx; destruct (ALL2 x ltac:(memb Hx)) as [U1 U2]; split; [exact U1| split; [exact U2| apply NEc; memb Hx]]|].
      split.
      { apply R_qlist_cons. pose proof (proj1 (R_qlist_cons m2 c1 qr) RL22) as [Q1 Q2]. split.
        - apply QBC_split in Q1 as [L R]. apply QBC_split. split.
          + eapply (rwT _ m2 m3 MU3 WM3); [exact L| cbn; apply D3; unfold A_QUAR, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *; lia].
          + apply (QBCx_keep_a K _ m2 m3 c1 WF MU3 WM3 Hc1 Cc1 R). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold A_QUAR, A_ALLOC, AIMG_HI. lia.
        - apply (Yrl qr Q2). intros x Hx. destruct (ALL2 x ltac:(memb Hx)) as [U1 U2]. split; [exact U1| split; [exact U2| apply NEc; memb Hx]]. }
      split; [apply (Yrl tmp' RL32); intros x Hx; destruct (ALL2 x ltac:(memb Hx)) as [U1 U2]; split; [exact U1| split; [exact U2| apply NEc; memb Hx]]|].
      apply (Ycu cur RC2). intros bd Hbd. pose proof (in_map fst cur bd Hbd) as Hb1. destruct (ALL2 (fst bd) ltac:(memb Hb1)) as [U1 U2]. split; [exact U1| split; [exact U2| apply NEc; memb Hb1]]. }
    split; [discriminate|].
    split; [eapply (rwT _ m2 m3 MU3 WM3); [exact FR2| cbn; unfold rec_frame; cbn; unfold A_QUAR, A_ALLOC, CEIL in *; split; [lia| exact I]]|].
    split; [exact MI3|].
    split; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]|].
    split; [| eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]].
    apply Forall_app. split; [apply Forall_cons; [| apply Forall_nil]; unfold dwin; cbn [fst snd]; left; lia|].
    apply Forall_app. split; [exact HW2|]. apply Forall_cons; [| apply Forall_nil]. unfold dwin. cbn [fst snd]. right. left. lia.
Qed.
End MERGE.


End CeilWrap.
End RTW_q_merge3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_lib2 RTW_m_lib4 RTW_m_tpz RTW_m_apz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_q_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_enq2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_q_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_car.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_zone2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_drain2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_bz.
Import RTW_q_recw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section POPS.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variables (qt : list qbatch) (cur : list (qbatch * Z)).
Variables (mn lo SP : Z).         (* [comment removed for export] *)
Hypothesis Hmn : 0 <= mn < 2^62.

(* [comment removed for export] *)
Local Notation pinv := (ainv K qt cur).
Lemma pin_Ka : forall qg tmp b, pinv qg tmp -> In b (qt ++ qg ++ tmp ++ map fst cur) -> In (qb_addr b) (qbatch_addrs K).
Proof. intros. eapply ainv_addr; eassumption. Qed.
Lemma pin_Kc : forall qg tmp b, pinv qg tmp -> In b (qt ++ qg ++ tmp ++ map fst cur) -> 0 <= qb_count b <= QBATCH_CAP.
Proof. intros. eapply ainv_cnt; eassumption. Qed.

Definition pop_post (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (tn tl : Z) (vs4 vs3 vs2 vs1 vs0 vra : word) (m : word -> option byte) (rest tmp' : list qbatch) (b : qbatch) : machine_state -> Prop :=
  fun ms' => exists (m' : word -> option byte) (Wd : list (Z * Z)),
      ms' = MS (mkR ra sp gp tp (wz (qc_first rest)) (wz (qb_addr b)) (wz (qc_bytes rest)) s0 s1 a0 a1 a2 a3
                    (wz (zlen tmp')) (wz (qb_addr b)) (wz (zlen rest)) (wz (qc_first rest))
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33dd0) fc None m' (seg_rom bsegs)
      /\ QX K m' 1 1 qt rest tmp' cur
      /\ rw_cells bsegs m' (bv_unsigned sp) (rec_frame tn (qc_first tmp') tl (qc_bytes tmp') vs4 vs3 vs2 vs1 vs0 vra)
      /\ mem_inv bsegs m' /\ munch Wd m m' /\ Forall (dwin K lo SP) Wd /\ wmono bsegs m m'.

(* [comment removed for export] *)
Theorem pop_step :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (b : qbatch) (rest tmp : list qbatch) (tn tf tl : Z),
  pinv (b :: rest) tmp ->
  QX K m 1 1 qt (b :: rest) tmp cur -> mem_inv bsegs m ->
  a0 = wz A_QUAR -> a4 = wz (zlen tmp) -> (tmp <> [] -> a5 = wz (qc_last tmp)) -> a6 = wz (zlen (b :: rest)) -> t0 = wz (qb_addr b) ->
  (tmp <> [] -> tf = qc_first tmp) ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 80 <= SP -> SP <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (pop_post ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc tn tl vs4 vs3 vs2 vs1 vs0 vra m rest (tmp ++ [b]) b)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33dd4) fc None m (seg_rom bsegs)).
Proof.
  intros until tl. intros PI X MI Ha0 Ha4 Ha5 Ha6 Ht0 Htf HCL LO SPB SPH FR.
  (nelimp X 14%nat; intros CO A4 XA XL XH XS TX TCq LV QR RL1 RL2 RL3 RC).
  unfold QH4 in XH.
  pose proof (t_range K WF) as [T1 T2]. idtac.
  assert (Hb : In (qb_addr b) (qbatch_addrs K)) by (apply (pin_Ka _ _ b PI); rewrite !in_app_iff; cbn; (cut_on [Hmn] tauto)).
  assert (Cb : 0 <= qb_count b <= QBATCH_CAP) by (apply (pin_Kc _ _ b PI); rewrite !in_app_iff; cbn; (cut_on [Hmn] tauto)).
  (nelimp (batch_facts_a K b WF Hb) 4%nat; intros G1 G2 G3 G4).
  assert (SUBR : forall x, In x rest -> In (qb_addr x) (qbatch_addrs K)) by (intros x Hx; apply (pin_Ka _ _ x PI); rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 Hx] tauto)).
  assert (SUBT : forall x, In x tmp -> In (qb_addr x) (qbatch_addrs K)) by (intros x Hx; apply (pin_Ka _ _ x PI); rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 Hx] tauto)).
  assert (CNR : forall x, In x rest -> 0 <= qb_count x <= QBATCH_CAP) by (intros x Hx; apply (pin_Kc _ _ x PI); rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 Hx] tauto)).
  assert (CNT : forall x, In x tmp -> 0 <= qb_count x <= QBATCH_CAP) by (intros x Hx; apply (pin_Kc _ _ x PI); rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 Hx] tauto)).
  assert (CNQ : forall x, In x qt -> 0 <= qb_count x <= QBATCH_CAP) by (intros x Hx; apply (pin_Kc _ _ x PI); rewrite !in_app_iff; cbn; tauto).
  assert (CNC : forall bd, In bd cur -> 0 <= qb_count (fst bd) <= QBATCH_CAP) by (intros bd Hbd; apply (pin_Kc _ _ _ PI); rewrite !in_app_iff; pose proof (in_map fst cur bd Hbd); cbn; (cut_on [Hmn Cb G4 H] tauto)).
  assert (SUBQ : forall x, In x qt -> In (qb_addr x) (qbatch_addrs K)) by (intros x Hx; apply (pin_Ka _ _ x PI); rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 Hx] tauto)).
  assert (SUBC : forall bd, In bd cur -> In (qb_addr (fst bd)) (qbatch_addrs K)) by (intros bd Hbd; apply (pin_Ka _ _ _ PI); rewrite !in_app_iff; pose proof (in_map fst cur bd Hbd); cbn; (cut_on [Hmn Cb G4 H] tauto)).
  assert (AF : forall l, (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) -> 0 <= qc_first l < 2^64).
  { intros l Hl. destruct l as [|x l]; [cbn; lia|]. cbn [qc_first]. pose proof (batch_facts_a K x WF (Hl x ltac:(left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  assert (AL : forall l, (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) -> 0 <= qc_last l < 2^64).
  { intros l Hl. destruct (snoc_or_nil' l) as [->|(q & x & ->)]; [cbn; lia|]. rewrite qc_last_snoc.
    pose proof (batch_facts_a K x WF (Hl x ltac:(apply in_or_app; right; left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  pose proof (AF rest SUBR) as F1. pose proof (AL (b :: rest) ltac:(intros x [<-|Hx]; [exact Hb| exact (SUBR x Hx)])) as F2.
  pose proof PI as [_ BB]. rewrite qc_bytes_cons in BB. pose proof (qc_bytes_nonneg rest) as BR. pose proof (qc_bytes_nonneg tmp) as BT.
  pose proof (qb_size_lb b) as SB. unfold QBATCH_SIZE in SB.
  pose proof (zlen_nonneg rest) as ZR. pose proof (qc_bytes_lb rest) as LBR. unfold QBATCH_SIZE in LBR.
  (* [comment removed for export] *)
  pose proof RL2 as RL2'. cbn [R_qlist] in RL2'. (nelim RL2' 3%nat; intros LNKc SLT RLr).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rec_pop1_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              (wz (qb_count b)) F fc m (zlen (b :: rest)) (qb_addr b) (qc_last (b :: rest)) (qc_bytes (b :: rest)) (qc_first rest) (qb_size b));
      [exact MI| exact Ha0| exact Ha6| exact Ht0| rewrite zlen_cons; lia| lia| lia| rewrite qc_bytes_cons; lia| rewrite qc_bytes_cons; lia
      | unfold AIMG_HI, KHIGHMEM_BEG in *; lia| idtac; unfold QBATCH_SIZE, CEIL in *; lia| exact XH| exact LNKc]. }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 7%nat; intros m1 -> MU1 WM1 MI1 XH1 LNK1).
  (* [comment removed for export] *)
  destruct (bk_used_a K b WF Hb) as [UKb Eb].
  match type of MU1 with munch ?Wx _ _ => set (W1 := Wx) in MU1 end.
  assert (HW1 : Forall (ucz_ok K 24 (bk K b)) W1).
  { subst W1. unfold ucz_ok. change (csize 24) with 8192. rewrite <- Eb.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold QBATCH_SIZE, CEIL in *; lia. }
  (nelimp (bzone_a K WF b Hb W1 HW1 m m1 MU1 WM1) 8%nat; intros Zc Za Zt Zl Zq Zrl Zcu Zqb).
  pose proof (ainv_nodup K WF qt cur _ _ PI) as ND. change (qt ++ (b :: rest) ++ tmp ++ map fst cur) with (qt ++ b :: (rest ++ tmp ++ map fst cur)) in ND.
  assert (NEb : forall x, In x (qt ++ (rest ++ tmp ++ map fst cur)) -> qb_addr x <> qb_addr b).
  { intros x Hx. exact (nodup_map_mid qb_addr qt (rest ++ tmp ++ map fst cur) b x ND Hx). }
  assert (D1 : forall a n, (a + n <= AIMG_HI /\ (a + n <= A_QUAR + 160 \/ A_QUAR + 192 <= a)) \/ CEIL <= a \/ (st_t K <= a /\ a + n <= st_t K + 4096) -> disjoint_from W1 a n).
  { intros a n Ha. subst W1. cbn. unfold AIMG_HI, A_QUAR, A_ALLOC, QBATCH_SIZE, CEIL, KHIGHMEM_BEG in *. repeat split; blia. }
  pose proof (Zc CO) as CO1. pose proof (Za A4) as A41. pose proof (Zt TX) as TX1. pose proof (Zl LV) as LV1. pose proof (Zq QR) as QR1.
  assert (XA1 : QA m1) by (apply (UZ_QA W1 m m1 MU1 WM1 XA); apply D1; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia).
  assert (XS1 : QS m1) by (apply (UZ_QS W1 m m1 MU1 WM1 XS); apply D1; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia).
  assert (XL1 : QLK m1 1 1) by (apply (UZ_QLK W1 m m1 MU1 WM1 1 1 XL); apply D1; left; unfold A_QUAR, A_ALLOC, AIMG_HI; lia).
  assert (TC1 : TC K m1 qt) by (apply (UZ_TC K W1 m m1 MU1 WM1 qt TCq); apply D1; right; right; unfold qcache_t, T_QCACHE; lia).
  assert (RLt1 : R_qlist m1 qt) by (apply (Zrl qt RL1); intros x Hx; split; [apply SUBQ; exact Hx| split; [apply CNQ; exact Hx| apply NEb; rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 F1 F2 BB Hx] tauto)]]).
  assert (RLr1 : R_qlist m1 rest) by (apply (Zrl rest RLr); intros x Hx; split; [apply SUBR; exact Hx| split; [apply CNR; exact Hx| apply NEb; rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 F1 F2 BB Hx] tauto)]]).
  assert (RL31 : R_qlist m1 tmp) by (apply (Zrl tmp RL3); intros x Hx; split; [apply SUBT; exact Hx| split; [apply CNT; exact Hx| apply NEb; rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 F1 F2 BB Hx] tauto)]]).
  assert (RC1 : QCUR m1 cur) by (apply (Zcu cur RC); intros bd Hbd; split; [apply SUBC; exact Hbd| split; [apply CNC; exact Hbd| apply NEb; rewrite !in_app_iff; pose proof (in_map fst cur bd Hbd); cbn; (cut_on [Hmn Cb G4 F1 F2 BB H] tauto)]]).
  assert (BX1 : QBCx m1 b).
  { apply (QBCx_keep_a K W1 m m1 b WF MU1 WM1 Hb Cb); [split; [| exact SLT]|].
    - apply (proj1 (rw_cells_app m (qb_addr b) [W8 (qc_first rest)] [W8 (qb_size b); W8 (qb_count b)])) in LNKc as [_ X2]. exact X2.
    - subst W1. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold A_QUAR, A_ALLOC, AIMG_HI in *; lia. }
  assert (FR1 : rw_cells bsegs m1 (bv_unsigned sp) (rec_frame tn tf tl (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra))
    by (eapply (rwT W1 m m1 MU1 WM1); [exact FR| cbn; apply D1; right; left; unfold CEIL; lia]).
  clear Zc Za Zt Zl Zq Zcu CO A4 TX LV QR XA XS XL TCq RL1 RL2 RL3 RC FR.
  (* [comment removed for export] *)
  assert (EQH : zlen (b :: rest) - 1 = zlen rest /\ qc_bytes (b :: rest) - qb_size b = qc_bytes rest
                /\ (if qc_first rest =? 0 then 0 else qc_last (b :: rest)) = qc_last rest).
  { rewrite zlen_cons, qc_bytes_cons. split; [lia|]. split; [lia|].
    destruct rest as [|x r]; [reflexivity|]. cbn [qc_first].
    pose proof (batch_facts_a K x WF (SUBR x ltac:(left; reflexivity))) as (X1 & _).
    replace (qb_addr x =? 0) with false by (symmetry; apply Z.eqb_neq; unfold KHIGHMEM_BEG, AIMG_HI in X1; lia).
    exact (qc_last_app_r [b] (x :: r) ltac:(discriminate)). }
  (nelim EQH 3%nat; intros E1 E2 E3). rewrite E1, E2, E3 in XH1. rewrite E1.
  pose proof (proj1 (rw_cells_app m1 (A_QUAR + 160) [W8 (zlen rest); W8 (qc_first rest); W8 (qc_last rest)] [W8 (qc_bytes rest)]) XH1) as [_ QB1].
  replace (A_QUAR + 160 + Z.of_nat (cells_size [W8 (zlen rest); W8 (qc_first rest); W8 (qc_last rest)])) with (A_QUAR + 184) in QB1 by reflexivity.
  destruct (snoc_or_nil' tmp) as [ET|(tq & tL & ET)].
  - (* [comment removed for export] *)
    subst tmp. cbv beta delta [wz] in Ha4. cbn [zlen length Z.of_nat] in Ha4.
    eapply evt_cut.
    { eapply (rec_pop2F_spec ra sp gp tp _ _ _ s0 s1 a0 a1 a2 a3 a4 a5 _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                vs4 vs3 vs2 vs1 vs0 vra (wz (qb_count b)) F fc m1 tn tf tl (qc_bytes []) (qb_addr b) (qc_bytes rest) (qb_size b) 0);
        [exact MI1| exact Ha0| exact Ha4| reflexivity| lia| cbn; lia| cbn [qc_bytes fold_right]; lia| lia
        | unfold AIMG_HI, KHIGHMEM_BEG in *; lia| idtac; unfold QBATCH_SIZE, CEIL in *; lia| idtac; lia| lia
        | exact FR1| exact QB1| exact LNK1]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 6%nat; intros m2 -> MU2 WM2 MI2 FR2).
    apply evt_done. unfold pop_post.
    exists m2, (W1 ++ [(bv_unsigned sp, bv_unsigned sp + 32)]).
    cbn [zlen length Z.of_nat Pos.of_succ_nat app qc_first]. split; [reflexivity|].
    match type of MU2 with munch ?Wx _ _ => set (W2 := Wx) in MU2 end.
    assert (HW2 : Forall (ucz_ok K 24 (bk K b)) W2).
    { subst W2. unfold ucz_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL in *; lia. }
    (nelimp (bzone_a K WF b Hb W2 HW2 m1 m2 MU2 WM2) 8%nat; intros Yc Ya Yt Yl Yq Yrl Ycu Yqb).
    assert (D2 : forall a n, a + n <= CEIL -> disjoint_from W2 a n).
    { intros a n Ha. subst W2. cbn. unfold CEIL in *. repeat split; lia. }
    split.
    { split; [exact (Yc CO1)|]. split; [exact (Ya A41)|].
      split; [apply (UZ_QA W2 m1 m2 MU2 WM2 XA1); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QLK W2 m1 m2 MU2 WM2 1 1 XL1); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QH4 W2 m1 m2 MU2 WM2 _ _ _ _ XH1); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QS W2 m1 m2 MU2 WM2 XS1); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [exact (Yt TX1)|].
      split; [apply (UZ_TC K W2 m1 m2 MU2 WM2 qt TC1); apply D2; unfold qcache_t, T_QCACHE, CEIL in *; lia|].
      split; [exact (Yl LV1)|]. split; [exact (Yq QR1)|].
      split; [apply (Yrl qt RLt1); intros x Hx; split; [apply SUBQ; exact Hx| split; [apply CNQ; exact Hx| apply NEb; rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 F1 F2 BB Hx] tauto)]]|].
      split; [apply (Yrl rest RLr1); intros x Hx; split; [apply SUBR; exact Hx| split; [apply CNR; exact Hx| apply NEb; rewrite !in_app_iff; cbn; (cut_on [Hmn Cb G4 F1 F2 BB Hx] tauto)]]|].
      split.
      { apply R_qlist_one. apply QBC_split. split.
        - apply (proj1 (rw_cells_app m2 (qb_addr b) [W8 0] [W8 (qb_size b); W8 (qb_count b)])).
          eapply (rwT W2 m1 m2 MU2 WM2); [exact LNK1| cbn; apply D2; unfold QBATCH_SIZE in *; lia].
        - apply (QBCx_keep_a K W2 m1 m2 b WF MU2 WM2 Hb Cb BX1). subst W2. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL in *; lia. }
      apply (Ycu cur RC1). intros bd Hbd. split; [apply SUBC; exact Hbd| split; [apply CNC; exact Hbd| apply NEb; rewrite !in_app_iff; pose proof (in_map fst cur bd Hbd); cbn; (cut_on [Hmn Cb G4 F1 F2 BB H] tauto)]]. }
    split; [replace (qc_bytes [b]) with (qc_bytes [] + qb_size b) by (cbn [qc_bytes fold_right]; lia); exact FR2|].
    split; [exact MI2|].
    split; [eapply munch_cat; [exact MU1| exact MU2]|].
    split; [| eapply wmono_trans; [exact WM1| exact WM2]].
    subst W1. unfold dwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + right. left. lia.
    + right. right. right. (nelim (qall_of_addr K b Hb) 3%nat; intros b0 Hb0 Eb0). exists b0. split; [exact Hb0|]. rewrite Eb0. unfold QBATCH_SIZE. lia.
    + left. lia.
  - (* [comment removed for export] *)
    assert (TNE : tmp <> []) by (rewrite ET; destruct tq; discriminate).
    specialize (Ha5 TNE). specialize (Htf TNE). rewrite ET, qc_last_snoc in Ha5.
    assert (HtL : In (qb_addr tL) (qbatch_addrs K)) by (apply SUBT; rewrite ET, in_app_iff; right; left; reflexivity).
    assert (CtL : 0 <= qb_count tL <= QBATCH_CAP) by (apply CNT; rewrite ET, in_app_iff; right; left; reflexivity).
    (nelimp (batch_facts_a K tL WF HtL) 4%nat; intros L1 L2 L3 L4).
    assert (NEtb : qb_addr tL <> qb_addr b) by (apply NEb; rewrite ET, !in_app_iff; cbn; (cut_on [Hmn Cb G4 F1 F2 BB CtL L4] tauto)).
    (* [comment removed for export] *)
    pose proof (proj1 (R_qlist_iff m1 tmp) RL31 tq tL [] ET) as TQB. cbn [qc_first] in TQB. apply QBC_split in TQB as [TLNK TBX].
    pose proof (zlen_pos_ne tmp TNE) as ZT. pose proof (qc_bytes_lb tmp) as LBT. unfold QBATCH_SIZE in LBT.
    (* [comment removed for export] *)
    assert (DJ : qb_addr b + 24 <= qb_addr tL \/ qb_addr tL + 8 <= qb_addr b).
    { pose proof (batch_disj K (qb_addr tL) (qb_addr b) WF HtL Hb NEtb). unfold QBATCH_SIZE in *. lia. }
    eapply evt_cut.
    { eapply (rec_pop2N_spec ra sp gp tp _ _ _ s0 s1 a0 a1 a2 a3 a4 a5 _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                vs4 vs3 vs2 vs1 vs0 vra (wz (qb_count b)) F fc m1 tn tf tl (qc_bytes tmp) (qb_addr b) (qc_bytes rest) (qb_size b) 0 (zlen tmp) (qb_addr tL));
        [exact MI1| exact Ha0| exact Ha4| exact Ha5| reflexivity| lia| lia| lia| lia| lia
        | unfold AIMG_HI, KHIGHMEM_BEG in *; lia| idtac; unfold QBATCH_SIZE, CEIL in *; lia
        | unfold AIMG_HI, KHIGHMEM_BEG in *; lia| idtac; unfold QBATCH_SIZE, CEIL in *; lia| exact DJ
        | idtac; lia| lia| exact FR1| exact QB1| exact LNK1| exact TLNK]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 7%nat; intros m2 -> MU2 WM2 MI2 FR2 TLNK2).
    apply evt_done. unfold pop_post.
    exists m2, (W1 ++ [(bv_unsigned sp, bv_unsigned sp + 32); (qb_addr tL, qb_addr tL + 8)]).
    rewrite zlen_app, zlen_cons, zlen_nil, Z.add_0_r. split; [reflexivity|].
    match type of MU2 with munch ?Wx _ _ => set (W2 := Wx) in MU2 end.
    destruct (bk_used_a K tL WF HtL) as [UKt Et].
    assert (HW2 : Forall (ucz_ok K 24 (bk K tL)) W2).
    { subst W2. unfold ucz_ok. change (csize 24) with 8192. rewrite <- Et.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold QBATCH_SIZE, CEIL in *; lia. }
    (nelimp (bzone_a K WF tL HtL W2 HW2 m1 m2 MU2 WM2) 8%nat; intros Yc Ya Yt Yl Yq Yrl Ycu Yqb).
    assert (D2 : forall a n, a + n <= AIMG_HI \/ (CEIL <= a /\ a + n <= bv_unsigned sp) \/ (st_t K <= a /\ a + n <= st_t K + 4096) -> disjoint_from W2 a n).
    { intros a n Ha. subst W2. cbn. unfold AIMG_HI, QBATCH_SIZE, CEIL, KHIGHMEM_BEG in *. repeat split; lia. }
    pose proof ND as ND2. rewrite ET in ND2.
    replace (qt ++ b :: rest ++ (tq ++ [tL]) ++ map fst cur) with ((qt ++ b :: rest ++ tq) ++ tL :: map fst cur) in ND2
      by (rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; reflexivity).
    assert (NEt : forall x, In x ((qt ++ b :: rest ++ tq) ++ map fst cur) -> qb_addr x <> qb_addr tL).
    { intros x Hx. exact (nodup_map_mid qb_addr (qt ++ b :: rest ++ tq) (map fst cur) tL x ND2 Hx). }
    split.
    { split; [exact (Yc CO1)|]. split; [exact (Ya A41)|].
      split; [apply (UZ_QA W2 m1 m2 MU2 WM2 XA1); apply D2; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [apply (UZ_QLK W2 m1 m2 MU2 WM2 1 1 XL1); apply D2; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [apply (UZ_QH4 W2 m1 m2 MU2 WM2 _ _ _ _ XH1); apply D2; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [apply (UZ_QS W2 m1 m2 MU2 WM2 XS1); apply D2; unfold A_QUAR, A_ALLOC, AIMG_HI; lia|].
      split; [exact (Yt TX1)|].
      split; [apply (UZ_TC K W2 m1 m2 MU2 WM2 qt TC1); apply D2; unfold qcache_t, T_QCACHE; lia|].
      split; [exact (Yl LV1)|]. split; [exact (Yq QR1)|].
      split; [apply (Yrl qt RLt1); intros x Hx; split; [apply SUBQ; exact Hx| split; [apply CNQ; exact Hx| apply NEt; rewrite !in_app_iff; cbn [In]; rewrite ?in_app_iff; (cut_on [Hmn Cb G4 F1 F2 BB CtL L4 DJ Hx] tauto)]]|].
      split; [apply (Yrl rest RLr1); intros x Hx; split; [apply SUBR; exact Hx| split; [apply CNR; exact Hx| apply NEt; rewrite !in_app_iff; cbn [In]; rewrite ?in_app_iff; (cut_on [Hmn Cb G4 F1 F2 BB CtL L4 DJ Hx] tauto)]]|].
      split.
      { rewrite ET, <- app_assoc. apply (proj2 (R_qlist_app m2 tq ([tL] ++ [b]))). split.
        - intros q1 x q2 E. cbn [app]. rewrite (qc_first_app_cons q2 tL [b] []).
          apply (Yqb x); [apply SUBT; rewrite ET, E, !in_app_iff; cbn [In]; (cut_on [Hmn Cb G4 F1 F2 BB CtL L4 DJ] tauto)| apply CNT; rewrite ET, E, !in_app_iff; cbn [In]; (cut_on [Hmn Cb G4 F1 F2 BB CtL L4 DJ] tauto)| apply NEt; rewrite E, !in_app_iff; cbn [In]; rewrite ?in_app_iff; cbn [In]; (cut_on [Hmn Cb G4 F1 F2 BB CtL L4 DJ] tauto)|].
          exact (proj1 (R_qlist_iff m1 tmp) RL31 q1 x (q2 ++ [tL]) ltac:(rewrite ET, E, <- app_assoc; reflexivity)).
        - cbn [app]. apply R_qlist_cons. split.
          + cbn [qc_first]. apply QBC_split. split; [exact TLNK2|].
            apply (QBCx_keep_a K W2 m1 m2 tL WF MU2 WM2 HtL CtL TBX). subst W2. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL in *; lia.
          + apply R_qlist_one. apply (Yqb b 0 Hb Cb); [intros E; apply NEtb; symmetry; exact E|].
            apply QBC_split. split; [| exact BX1].
            apply (proj1 (rw_cells_app m1 (qb_addr b) [W8 0] [W8 (qb_size b); W8 (qb_count b)])) in LNK1 as [X1 _]. exact X1. }
      apply (Ycu cur RC1). intros bd Hbd. split; [apply SUBC; exact Hbd| split; [apply CNC; exact Hbd| apply NEt; rewrite !in_app_iff; pose proof (in_map fst cur bd Hbd); cbn [In]; rewrite ?in_app_iff; (cut_on [Hmn Cb G4 F1 F2 BB CtL L4 DJ H] (cut_on [Hmn Cb G4 F1 F2 BB CtL L4 DJ H] tauto))]]. }
    split; [rewrite (qc_first_app_l tmp [b] TNE), qc_bytes_app, <- Htf; cbn [qc_bytes fold_right]; rewrite Z.add_0_r; exact FR2|].
    split; [exact MI2|].
    split; [eapply munch_cat; [exact MU1| exact MU2]|].
    split; [| eapply wmono_trans; [exact WM1| exact WM2]].
    subst W1. unfold dwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + right. left. lia.
    + right. right. right. (nelim (qall_of_addr K b Hb) 3%nat; intros b0 Hb0 Eb0). exists b0. split; [exact Hb0|]. rewrite Eb0. unfold QBATCH_SIZE. lia.
    + left. lia.
    + right. right. right. (nelim (qall_of_addr K tL HtL) 3%nat; intros b0 Hb0 Eb0). exists b0. split; [exact Hb0|]. rewrite Eb0. unfold QBATCH_SIZE. lia.
Qed.

Definition loop_post (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (vs4 vs3 vs2 vs1 vs0 vra : word) (m : word -> option byte) (qg tmp : list qbatch) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' : word) (m' : word -> option byte) (Wd : list (Z * Z)) (popped qgF : list qbatch),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33e30) fc None m' (seg_rom bsegs)
      /\ qg = popped ++ qgF /\ qc_bytes qgF <= mn
      /\ pinv qgF (tmp ++ popped) /\ QX K m' 1 1 qt qgF (tmp ++ popped) cur
      /\ rw_cells bsegs m' (bv_unsigned sp)
           (rec_frame (zlen (tmp ++ popped)) (qc_first (tmp ++ popped)) (qc_last (tmp ++ popped)) (qc_bytes (tmp ++ popped)) vs4 vs3 vs2 vs1 vs0 vra)
      /\ mem_inv bsegs m' /\ munch Wd m m' /\ Forall (dwin K lo SP) Wd /\ wmono bsegs m m'.

Theorem pop_loop : forall (n : nat)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (qg tmp : list qbatch) (tn tf tl : Z),
  (length qg <= n)%nat ->
  pinv qg tmp ->
  QX K m 1 1 qt qg tmp cur -> mem_inv bsegs m ->
  mn < qc_bytes qg ->
  a0 = wz A_QUAR -> a1 = wz mn -> a4 = wz (zlen tmp) -> (tmp <> [] -> a5 = wz (qc_last tmp)) -> a6 = wz (zlen qg) -> t0 = wz (qc_first qg) ->
  (tmp <> [] -> tf = qc_first tmp) ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 80 <= SP -> SP <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (rec_frame tn tf tl (qc_bytes tmp) vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (loop_post ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc vs4 vs3 vs2 vs1 vs0 vra m qg tmp)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x33dd4) fc None m (seg_rom bsegs)).
Proof.
  induction n as [|n IH]; intros until tl; intros Hlen PI X MI HB Ha0 Ha1 Ha4 Ha5 Ha6 Ht0 Htf HCL LO SPB SPH FR.
  { destruct qg; cbn in Hlen; [cbn in HB; lia| lia]. }
  destruct qg as [|b rest]; [cbn in HB; lia|]. cbn in Hlen.
  eapply evt_cut.
  { eapply (pop_step ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 vs4 vs3 vs2 vs1 vs0 vra F fc m b rest tmp tn tf tl);
      try eassumption. }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 Wd1 -> X1 FR1 MI1 MU1 HW1 WM1).
  pose proof (ainv_pop K qt cur b rest tmp PI) as PI1.
  (nelimp PI1 4%nat; intros _ _ _ BB1). pose proof (qc_bytes_nonneg rest) as BR. pose proof (qc_bytes_nonneg (tmp ++ [b])) as BT.
  assert (Hb : In (qb_addr b) (qbatch_addrs K)) by (apply (pin_Ka _ _ b PI); rewrite !in_app_iff; cbn; (cut_on [Hmn] tauto)).
  assert (Cb : 0 <= qb_count b <= QBATCH_CAP) by (apply (pin_Kc _ _ b PI); rewrite !in_app_iff; cbn; (cut_on [Hmn] tauto)).
  (nelimp (batch_facts_a K b WF Hb) 4%nat; intros G1 G2 G3 G4). idtac.
  pose proof (zlen_nonneg (tmp ++ [b])) as ZT.
  assert (ZT2 : zlen (tmp ++ [b]) < 2^62) by (pose proof (qc_bytes_lb (tmp ++ [b])); unfold QBATCH_SIZE in *; lia).
  destruct (Z_le_gt_dec (qc_bytes rest) mn) as [DONE|MORE].
  - (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rec_popdone_spec ra sp gp tp _ _ _ s0 s1 a0 a1 a2 a3 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 vs4 vs3 vs2 vs1 vs0 vra F fc m1
                _ _ tl _ mn (qc_bytes rest) (zlen (tmp ++ [b])) (qb_addr b));
        [exact MI1| exact Ha1| reflexivity| reflexivity| reflexivity| lia| lia| lia| lia| unfold KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, CEIL in *; lia
        | idtac; lia| lia| exact FR1]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 6%nat; intros m2 -> MU2 WM2 MI2 FR2).
    apply evt_done. unfold loop_post.
    nexists 7%nat. exists m2, (Wd1 ++ [(bv_unsigned sp, bv_unsigned sp + 32)]), [b], rest.
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact PI1|].
    assert (D2 : forall a sz, a + sz <= CEIL -> disjoint_from [(bv_unsigned sp, bv_unsigned sp + 32)] a sz).
    { intros a sz Ha. cbn. unfold CEIL in *. split; [lia| exact I]. }
    (* [comment removed for export] *)
    destruct (bk_used_a K b WF Hb) as [UKb Eb].
    assert (HW2 : Forall (ucz_ok K 24 (bk K b)) [(bv_unsigned sp, bv_unsigned sp + 32)]).
    { unfold ucz_ok. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold CEIL in *. lia. }
    (nelimp (bzone_a K WF b Hb _ HW2 m1 m2 MU2 WM2) 8%nat; intros Yc Ya Yt Yl Yq Yrl Ycu Yqb).
    pose proof (ainv_nodup K WF qt cur _ _ PI1) as ND.
    assert (SUBa : forall x, In x (qt ++ rest ++ (tmp ++ [b]) ++ map fst cur) -> In (qb_addr x) (qbatch_addrs K)) by (intros x Hx; exact (pin_Ka _ _ x PI1 Hx)).
    assert (CNa : forall x, In x (qt ++ rest ++ (tmp ++ [b]) ++ map fst cur) -> 0 <= qb_count x <= QBATCH_CAP) by (intros x Hx; exact (pin_Kc _ _ x PI1 Hx)).
    replace (qt ++ rest ++ (tmp ++ [b]) ++ map fst cur) with ((qt ++ rest ++ tmp) ++ b :: map fst cur) in ND
      by (rewrite <- !app_assoc; reflexivity).
    assert (NEb : forall x, In x ((qt ++ rest ++ tmp) ++ map fst cur) -> qb_addr x <> qb_addr b).
    { intros x Hx. exact (nodup_map_mid qb_addr (qt ++ rest ++ tmp) (map fst cur) b x ND Hx). }
    (nelimp X1 14%nat; intros CO A4 XA XL XH XS TX TCq LV QR RL1 RL2 RL3 RC).
    split.
    { split; [exact (Yc CO)|]. split; [exact (Ya A4)|].
      split; [apply (UZ_QA _ m1 m2 MU2 WM2 XA); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QLK _ m1 m2 MU2 WM2 1 1 XL); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QH4 _ m1 m2 MU2 WM2 _ _ _ _ XH); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [apply (UZ_QS _ m1 m2 MU2 WM2 XS); apply D2; unfold A_QUAR, A_ALLOC, CEIL; lia|].
      split; [exact (Yt TX)|].
      split; [apply (UZ_TC K _ m1 m2 MU2 WM2 qt TCq); apply D2; pose proof (t_range K WF); unfold qcache_t, T_QCACHE, CEIL in *; lia|].
      split; [exact (Yl LV)|]. split; [exact (Yq QR)|].
      split; [apply (Yrl qt RL1); intros x Hx; split; [apply SUBa| split; [apply CNa| apply NEb]]; rewrite !in_app_iff; cbn [In]; rewrite ?in_app_iff; (cut_on [Hmn Cb G4 Hx] tauto)|].
      split; [apply (Yrl rest RL2); intros x Hx; split; [apply SUBa| split; [apply CNa| apply NEb]]; rewrite !in_app_iff; cbn [In]; rewrite ?in_app_iff; (cut_on [Hmn Cb G4 Hx] tauto)|].
      split.
      { apply (proj2 (R_qlist_app m2 tmp [b])). split.
        - intros q1 x q2 E. apply (Yqb x); [apply SUBa; rewrite E, !in_app_iff; cbn [In]; rewrite ?in_app_iff; cbn [In]; (cut_on [Hmn Cb G4] tauto)
                                          | apply CNa; rewrite E, !in_app_iff; cbn [In]; rewrite ?in_app_iff; cbn [In]; (cut_on [Hmn Cb G4] tauto)
                                          | apply NEb; rewrite E, !in_app_iff; cbn [In]; rewrite ?in_app_iff; cbn [In]; (cut_on [Hmn Cb G4] tauto)|].
          exact (proj1 (proj1 (R_qlist_app m1 tmp [b]) RL3) q1 x q2 E).
        - apply R_qlist_one. apply QBC_split. pose proof (proj2 (proj1 (R_qlist_app m1 tmp [b]) RL3)) as Q1. apply R_qlist_one, QBC_split in Q1 as [Q1 Q2].
          split; [eapply (rwT _ m1 m2 MU2 WM2); [exact Q1| cbn; apply D2; unfold QBATCH_SIZE in *; lia]|].
          apply (QBCx_keep_a K _ m1 m2 b WF MU2 WM2 Hb Cb Q2). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold CEIL in *. lia. }
      apply (Ycu cur RC). intros bd Hbd. pose proof (in_map fst cur bd Hbd). split; [apply SUBa| split; [apply CNa| apply NEb]]; rewrite !in_app_iff; cbn [In]; rewrite ?in_app_iff; (cut_on [H] tauto). }
    split; [rewrite qc_last_snoc; exact FR2|].
    split; [exact MI2|]. split; [eapply munch_cat; [exact MU1| exact MU2]|].
    split; [| eapply wmono_trans; [exact WM1| exact WM2]].
    apply Forall_app. split; [exact HW1|]. apply Forall_cons; [| apply Forall_nil]. unfold dwin. cbn [fst snd]. left. lia.
  - (* [comment removed for export] *)
    assert (RNE : rest <> []) by (intros ->; cbn in MORE; lia).
    eapply evt_cut.
    { eapply (rec_popmore_spec ra sp gp tp _ _ _ s0 s1 a0 a1 a2 a3 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 mn (qc_bytes rest));
        [exact Ha1| reflexivity| lia| lia| lia]. }
    cbv beta. intros ms2 ->.
    eapply evt_cut.
    { eapply (IH ra sp gp tp _ _ _ s0 s1 a0 a1 a2 a3 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 vs4 vs3 vs2 vs1 vs0 vra F fc m1 rest (tmp ++ [b]) tn _ tl);
        [lia| exact PI1| exact X1| exact MI1| lia| exact Ha0| exact Ha1| reflexivity| intros _; rewrite qc_last_snoc; reflexivity| reflexivity| reflexivity
        | intros _; reflexivity| idtac; lia| lia| lia| lia| exact FR1]. }
    cbv beta. intros ms3 nelH_; (nelim nelH_ 21%nat; intros t0' t1' t2' a4' a5' a6' a7' m3 Wd3 popped qgF -> -> BF PI3 X3 FR3 MI3 MU3 HW3 WM3).
    apply evt_done. unfold loop_post.
    nexists 7%nat. exists m3, (Wd1 ++ Wd3), (b :: popped), qgF.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact BF|].
    rewrite <- !app_assoc in *. cbn [app] in *.
    split; [exact PI3|]. split; [exact X3|]. split; [exact FR3|]. split; [exact MI3|].
    split; [eapply munch_cat; [exact MU1| exact MU3]|].
    split; [apply Forall_app; split; [exact HW1| exact HW3]| eapply wmono_trans; [exact WM1| exact WM3]].
Qed.
End POPS.


End CeilWrap.
