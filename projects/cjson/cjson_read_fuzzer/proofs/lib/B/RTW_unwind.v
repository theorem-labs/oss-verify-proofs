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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_unwind_loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition agree_on (lo hi : Z) (m m' : mem) : Prop := forall a, lo <= a < hi -> mrd bsegs m' (wa a) = mrd bsegs m (wa a).
Lemma bytes_at_agree : forall m m' A bs lo hi, bytes_at bsegs m A bs -> agree_on lo hi m m' ->
  lo <= A -> A + Z.of_nat (length bs) <= hi -> bytes_at bsegs m' A bs.
Proof.
  intros m m' A bs lo hi (H0 & H1 & HB) AG HL HH. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). apply AG. lia.
Qed.
(* [comment removed for export] *)
Definition tb_prefix (ws : list word) (done : list Z) : Prop := firstn (length done) ws = map wz done.

Section UWF.
  (* [comment removed for export] *)
  Variables (raU spE gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (s0v s1v s2v s3v s4v s5v s6v : word).          (* [comment removed for export] *)
  Variables (t0v t1v t2v t3v t4v t5v t6v : word).          (* [comment removed for export] *)
  Variables (m0 me : mem) (S pc0 bp TOP lo ubyte spI : Z) (tr : list Z).
  Hypothesis RS : bv_unsigned spE <= spI /\ spI <= S /\ spI <= bp - 16 /\ (S + BST_SIZE <= bp - 16 \/ TOP <= S) /\ S + BST_SIZE <= 2^64.
  Hypothesis RT : bp < 2^64 /\ TOP + 16 < 2^64 /\ 0 <= pc0 < 2^64.
  Hypothesis RLO : alloc_ceiling <= lo /\ lo + 64 <= bv_unsigned spE.
  Hypothesis RU : ubyte + 1 <= alloc_ceiling /\ 4096 <= ubyte /\ (ubyte + 1 <= AIMG_LO \/ AIMG_HI <= ubyte).   (* [comment removed for export] *)
  Hypothesis TRL : zlen tr <= 30.
  Hypothesis AG0 : agree_on (bp - 16) TOP m0 me.
  (* [comment removed for export] *)
  Definition W : list (Z * Z) := [(lo, spI); (S + 8, S + 12); (S + 16, S + 16 + 8 * zlen tr); (S + 2056, S + 2064); (ubyte, ubyte + 1)].
  Lemma WOUT : forall a, bp - 16 <= a < TOP -> outside W a.
  Proof.
    intros a Ha. pose proof (bv_unsigned_in_range 64 spE) as R. unfold BST_SIZE in RS. idtac.
    pose proof (zlen_nonneg tr). cbn. lia.
  Qed.

  Lemma ag_of_munch : forall mc, munch W me mc -> agree_on (bp - 16) TOP m0 mc.
  Proof.
    intros mc MU a Ha. pose proof (bv_unsigned_in_range 64 spE) as R. unfold bv_modulus in R.
    unfold BST_SIZE in RS.
    unfold mrd. rewrite (MU (wa a)). { apply AG0. exact Ha. }
    rewrite wa_unsigned by lia. apply WOUT. exact Ha.
  Qed.

  #[warnings="-notation-for-abbreviation"] Notation ST_ pc mm prev k f x17 :=
    (MS (mkR raU (Z_to_bv 64 (bv_unsigned spE + -64)) gp tp t0v t1v t2v (Z_to_bv 64 30) (Z_to_bv 64 (TOP + -16)) (Z_to_bv 64 S) (Z_to_bv 64 pc0) (Z_to_bv 64 prev) (Z_to_bv 64 4096)
              (Z_to_bv 64 (S + 16)) (Z_to_bv 64 k) (Z_to_bv 64 f) x17 (Z_to_bv 64 0x139460) s3v s4v s5v s6v s7 s8 s9 s10 s11 t3v t4v t5v t6v)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma tb_prefix_snoc : forall ws done (v : word), tb_prefix ws done -> (length done < length ws)%nat ->
    tb_prefix (upd ws (length done) v) (done ++ [bv_unsigned v]).
  Proof.
    intros ws done v TB HL. unfold tb_prefix in *. rewrite length_app. cbn [length].
    rewrite (upd_firstn_skipn ws (length done) v HL).
    rewrite firstn_app. rewrite firstn_firstn by lia. replace (Nat.min (length done + 1) (length done)) with (length done) by lia.
    rewrite firstn_length_le by lia. replace (length done + 1 - length done)%nat with 1%nat by lia. cbn [firstn].
    rewrite TB, map_app. cbn [map]. unfold wz. rewrite Z_to_bv_bv_unsigned. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition uinv (mc : mem) (k : Z) (done : list Z) : Prop :=
    exists ws, u64arr bsegs mc (S + 16) ws /\ length ws = 255%nat /\ tb_prefix ws done /\ k = zlen done
    /\ rw_cells bsegs mc S [C8 (wz (S + 16)); C4 (wz k); C4 (wz 0)]
    /\ rw_cells bsegs mc (S + 2056) [C8 (wz bp)]
    /\ rw_cells bsegs mc ubyte [C1 (zb 1)]
    /\ rw_cells bsegs mc (bv_unsigned spE + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 raU]
    /\ mem_inv bsegs mc /\ munch W me mc /\ wmono bsegs me mc /\ stk bsegs mc lo (bv_unsigned spE + -64).

  (* [comment removed for export] *)
  Definition upost (m' : mem) (tr : list Z) : Prop :=
    exists ws k', u64arr bsegs m' (S + 16) ws /\ length ws = 255%nat /\ tb_prefix ws tr /\ k' = zlen tr /\ 1 <= k' <= 30
    /\ rw_cells bsegs m' S [C8 (wz (S + 16)); C4 (wz k'); C4 (wz 0)]
    /\ rw_cells bsegs m' (S + 2056) [C8 (wz bp)]
    /\ rw_cells bsegs m' ubyte [C1 (zb 1)]
    /\ mem_inv bsegs m' /\ munch W me m' /\ wmono bsegs me m' /\ stk bsegs m' lo (bv_unsigned spE).

  Definition uwf_post (tr : list Z) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
      ms' = MS (mkR raU spE gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc raU) fc None m' (seg_rom bsegs)
      /\ upost m' tr.

  (* [comment removed for export] *)
  Lemma uwf_exit : forall (x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word) mc k done,
    uinv mc k done -> 1 <= k <= 30 ->
    evt bsegs (uwf_post done)
      (MS (mkR raU (Z_to_bv 64 (bv_unsigned spE + -64)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 S) (Z_to_bv 64 pc0) x12 x13 x14 x15 x16 x17 x18 s3v s4v s5v s6v s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x74e2c) fc None mc (seg_rom bsegs)).
  Proof.
    intros until done. intros (ws & ARR & LEN & TB & Kd & OBJ & TFB & UNW & FRU & MI & MU & WM & ST) HK.
    pose proof (bv_unsigned_in_range 64 spE) as RSP. unfold bv_modulus in RSP. unfold BST_SIZE in RS. idtac. unfold AIMG_LO, AIMG_HI in RU.
    do 10 zstep.
    release_frame FRU ST (bv_unsigned spE).
    apply evt_done. unfold uwf_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. exists ws, k.
    split; [exact ARR|]. split; [exact LEN|]. split; [exact TB|]. split; [exact Kd|]. split; [exact HK|].
    split; [exact OBJ|]. split; [exact TFB|]. split; [exact UNW|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. exact ST.
  Qed.

  Lemma land7_mod8 : forall f, 0 <= f -> Z.land f 7 = f mod 8.
  Proof. intros f Hf. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma uwf_loop : forall tl (prev k f : Z) x17 mc done,
    uwt m0 bp TOP pc0 prev f k tl ->
    bp <= prev < TOP -> 0 <= f < 2^64 -> 1 <= k <= 30 -> done ++ tl = tr ->
    uinv mc k done ->
    evt bsegs (uwf_post (done ++ tl)) (ST_ 0x74e18 mc prev k f x17).
  Proof.
    intros tl prev k f x17 mc done U. revert x17 mc done. unfold W in *.
    pose proof (bv_unsigned_in_range 64 spE) as RSP. unfold bv_modulus in RSP.
    unfold BST_SIZE in RS. idtac. unfold AIMG_LO, AIMG_HI in RU.
    induction U as [prev f k STOP| prev f k nxt pc1 PF AL FT KM LOF REC LOW | prev f k nxt pc1 tl PF AL FT KM LOF REC HIGH U IH];
      intros x17 mc done BP RF HK TR UI;
      (nelimp UI 13%nat; intros ws ARR LEN TB Kd OBJ TFB UNW FRU MI MU WM ST);
      pose proof (ag_of_munch mc MU) as AG; pose proof (zlen_nonneg tr) as TR0; unfold W in MU.
    - (* [comment removed for export] *)
      unfold TRACE_MAX_LEN in STOP. rewrite app_nil_r.
      zstep. (if_cases K1; zify_cond K1). { eapply uwf_exit; [exact UI| lia]. }
      zstep. (if_cases K2; zify_cond K2). { eapply uwf_exit; [exact UI| lia]. }
      zstep. zstep. zstep. (if_cases K3; zify_cond K3).
      2:{ eapply uwf_exit; [exact UI| lia]. }
      rewrite land7_mod8 in K3 by lia.
      zstep. (if_cases K4; zify_cond K4). { eapply uwf_exit; [exact UI| lia]. }
      exfalso. lia.
    - (* [comment removed for export] *)
      unfold TRACE_MAX_LEN in KM. rewrite app_nil_r.
      zstep. if_lia. zstep. if_lia. zstep. zstep. zstep.
      (if_cases K3; zify_cond K3). 2:{ exfalso. rewrite land7_mod8 in K3 by lia. lia. }
      zstep. if_lia. (* [comment removed for export] *)
      assert (RECc : ro_cells bsegs mc (f + -16) [C8 nxt; C8 pc1]).
      { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        eapply (bytes_at_agree m0 mc); [exact REC| exact AG| lia| rewrite length_app, !length_le8; cbn; lia]. }
      zstep. (* [comment removed for export] *)
      zstep. (if_cases K5; zify_cond K5). 2:{ exfalso. lia. }
      eapply uwf_exit; [exact UI| lia].
    - (* [comment removed for export] *)
      unfold TRACE_MAX_LEN in KM.
      zstep. if_lia. zstep. if_lia. zstep. zstep. zstep.
      (if_cases K3; zify_cond K3). 2:{ exfalso. rewrite land7_mod8 in K3 by lia. lia. }
      zstep. if_lia. (* [comment removed for export] *)
      assert (RECc : ro_cells bsegs mc (f + -16) [C8 nxt; C8 pc1]).
      { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        eapply (bytes_at_agree m0 mc); [exact REC| exact AG| lia| rewrite length_app, !length_le8; cbn; lia]. }
      zstep. (* [comment removed for export] *)
      zstep. (if_cases K5; zify_cond K5). { exfalso. lia. }
      zstep. (if_cases K6; zify_cond K6).
      + (* [comment removed for export] *)
        replace (bv_unsigned pc1 =? pc0) with true in * by (symmetry; apply Z.eqb_eq; exact K6).
        cbn [app]. rewrite Z.add_0_r in *.
        zstep. (* [comment removed for export] *)
        replace nxt with (Z_to_bv 64 (bv_unsigned nxt)) by (apply Z_to_bv_bv_unsigned).
        eapply IH; [lia| pose proof (bv_unsigned_in_range 64 nxt) as R; unfold bv_modulus in R; cbn in R; lia| lia| exact TR| exact UI].
      + (* [comment removed for export] *)
        replace (bv_unsigned pc1 =? pc0) with false in * by (symmetry; apply Z.eqb_neq; exact K6).
        cbn [app]. cbn [app] in TR.
        assert (TR1 : k + 1 <= zlen tr) by (rewrite <- TR, zlen_app, zlen_cons; pose proof (zlen_nonneg tl); lia).
        zstep. zstep. zstep. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        setreg 17 (Z_to_bv 64 (S + 16 + 8 * k)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
        pose proof (u64arr_store_ok bsegs _ (S + 16) ws k (wa (S + 16 + 8 * k)) ARR ltac:(rewrite LEN; lia) eq_refl) as SOK.
        zstep. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
          pose proof (u64arr_write bsegs mm (S + 16) ws k pc1 ARR ltac:(rewrite LEN; lia)) as ARR' end.
        store_done.
        zstep. (* [comment removed for export] *)
        replace nxt with (Z_to_bv 64 (bv_unsigned nxt)) by (apply Z_to_bv_bv_unsigned).
        replace (done ++ bv_unsigned pc1 :: tl) with ((done ++ [bv_unsigned pc1]) ++ tl) by (rewrite <- app_assoc; reflexivity).
        eapply IH; [lia| pose proof (bv_unsigned_in_range 64 nxt) as R; unfold bv_modulus in R; cbn in R; lia| lia| rewrite <- app_assoc; exact TR|].
        (* [comment removed for export] *)
        exists (upd ws (Z.to_nat k) pc1).
        split; [exact ARR'|]. split; [rewrite upd_length; exact LEN|].
        split. { replace (Z.to_nat k) with (length done) by (rewrite Kd; unfold zlen; lia). apply tb_prefix_snoc; [exact TB| rewrite LEN; unfold zlen in Kd; lia]. }
        split; [unfold zlen in *; rewrite length_app; cbn [length]; lia|].
        repeat (split; [assumption|]). assumption.
  Qed.

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Notation STE_ pc mm x13 x14 x15 x16 x17 x18 :=
    (MS (mkR raU spE gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 S) (Z_to_bv 64 pc0) (Z_to_bv 64 bp) x13 x14 x15 x16 x17
              s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3v t4v t5v t6v)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (BOTTOM : Z) (sp0 : Z) (rac s0c : word) (tl : list Z).
  Hypothesis HTOP : TOP = ASTACK_TOP sp0.
  Hypothesis HBOT : BOTTOM = ASTACK_BOTTOM sp0 /\ 0 <= BOTTOM.
  Hypothesis REC0 : bytes_at bsegs m0 (bp - 16) (le8 s0c ++ le8 rac).
  Hypothesis RAC : 4096 <= bv_unsigned rac /\ bv_unsigned rac <> pc0.
  Hypothesis UWT : hop1_ok sp0 bp = true -> uwt m0 bp TOP pc0 bp (bv_unsigned s0c) 2 tl.
  Hypothesis HTR : tr = hook_tr pc0 sp0 bp (bv_unsigned rac) tl.

  Lemma uwf_entry : forall mc ws (szj x16 x17 : word),
    u64arr bsegs mc (S + 16) ws -> length ws = 255%nat ->
    rw_cells bsegs mc S [C8 (wz (S + 16)); C4 szj; C4 (wz 0)] ->
    rw_cells bsegs mc (S + 2056) [C8 (wz bp)] ->
    rw_cells bsegs mc ubyte [C1 (zb 1)] ->
    ro_cells bsegs mc 0xa16e0 [C8 (Z_to_bv 64 0x139460)] -> ro_cells bsegs mc 0x139460 [C8 (Z_to_bv 64 4096)] ->
    mem_inv bsegs mc -> munch W me mc -> wmono bsegs me mc -> stk bsegs mc lo (bv_unsigned spE) ->
    evt bsegs (uwf_post tr) (STE_ 0x74d30 mc (Z_to_bv 64 TOP) (Z_to_bv 64 BOTTOM) (Z_to_bv 64 30) x16 x17 w0).
  Proof.
    intros mc ws szj x16 x17 ARR LEN OBJ TFB UNW GOTC PSC MI MU WM ST.
    pose proof (bv_unsigned_in_range 64 spE) as RSP. unfold bv_modulus in RSP.
    unfold BST_SIZE in RS. idtac. unfold AIMG_LO, AIMG_HI in RU. unfold W in MU.
    pose proof (zlen_nonneg tr) as TR0.
    assert (TR1 : 1 <= zlen tr) by (rewrite HTR; unfold hook_tr; destruct (hop1_ok sp0 bp); unfold zlen; cbn [length]; lia).
    assert (TOPB : 4096 <= TOP /\ BOTTOM < TOP) by (destruct HBOT as [HB1 HB2]; rewrite HTOP, HB1 in *; unfold ASTACK_BOTTOM, ASTACK_TOP, roundup in *; lia).
    carve_frame 64%nat ST.
    do 9 zstep. (* [comment removed for export] *)
    do 4 zstep. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. zstep. fl. clear GOTC. (* [comment removed for export] *)
    zstep. fl. clear PSC. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (u64arr_store_ok bsegs _ (S + 16) ws 0 (wa (S + 16)) ARR ltac:(rewrite LEN; lia) ltac:(f_equal; lia)) as SOK.
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u64arr_write bsegs mm (S + 16) ws 0 (Z_to_bv 64 pc0) ARR ltac:(rewrite LEN; lia)) as ARR1;
      replace (S + 16 + 8 * 0) with (S + 16) in ARR1 by lia end.
    store_done.
    assert (TB1 : tb_prefix (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) [pc0]).
    { unfold tb_prefix. cbn [length map]. destruct ws; [cbn in LEN; lia| reflexivity]. }
    zstep. (if_cases K0; zify_cond K0); [clear K0| exfalso; rewrite Z.shiftr_div_pow2 in K0 by lia; change (2^12) with 4096 in K0; lia].
    zstep. if_lia. (* [comment removed for export] *)
    zstep. (if_cases K1; zify_cond K1).
    { destruct (hop1_ok sp0 bp) eqn:E.
      { exfalso; unfold hop1_ok in E; destruct HBOT as [HB1 HB2]; rewrite <- HTOP, <- HB1 in E.
        rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq in E. lia. }
      rewrite HTR, (hook_tr_ko _ _ _ _ _ E). eapply uwf_exit.
      { exists (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)); split; [exact ARR1|]; split; [rewrite upd_length; assumption|].
        split; [exact TB1|]. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
      unfold zlen; cbn [length]; lia. }
    zstep. zstep. (if_cases K2; zify_cond K2).
    { destruct (hop1_ok sp0 bp) eqn:E.
      { exfalso; unfold hop1_ok in E; destruct HBOT as [HB1 HB2]; rewrite <- HTOP, <- HB1 in E.
        rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq in E. lia. }
      rewrite HTR, (hook_tr_ko _ _ _ _ _ E). eapply uwf_exit.
      { exists (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)); split; [exact ARR1|]; split; [rewrite upd_length; assumption|].
        split; [exact TB1|]. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
      unfold zlen; cbn [length]; lia. }
    zstep. zstep. (if_cases K3; zify_cond K3).
    { rewrite land7_mod8 in K3 by lia. destruct (hop1_ok sp0 bp) eqn:E.
      { exfalso; unfold hop1_ok in E; destruct HBOT as [HB1 HB2]; rewrite <- HTOP, <- HB1 in E.
        rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq in E. lia. }
      rewrite HTR, (hook_tr_ko _ _ _ _ _ E). eapply uwf_exit.
      { exists (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)); split; [exact ARR1|]; split; [rewrite upd_length; assumption|].
        split; [exact TB1|]. split; [reflexivity|]. repeat (split; [assumption|]). assumption. }
      unfold zlen; cbn [length]; lia. }
    rewrite land7_mod8 in K3 by lia.
    assert (H1 : hop1_ok sp0 bp = true).
    { unfold hop1_ok. destruct HBOT as [HB1 HB2]. rewrite <- HTOP, <- HB1.
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia. reflexivity. }
    specialize (UWT H1). rewrite HTR. rewrite (hook_tr_ok _ _ _ _ _ H1).
    zstep. zstep. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RECc : ro_cells bsegs mm (bp + -16) [C8 s0c; C8 rac]) end.
    { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. replace (bp + -16) with (bp - 16) by lia.
      eapply (bytes_at_agree m0); [exact REC0| apply ag_of_munch; assumption| lia| rewrite length_app, !length_le8; cbn; lia]. }
    zstep. (* [comment removed for export] *)
    zstep. if_lia. (* [comment removed for export] *)
    zstep. (if_cases K5; zify_cond K5). { exfalso. lia. }
    zstep. zstep. zstep. fl. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    assert (TR2 : 2 <= zlen tr) by (rewrite HTR, (hook_tr_ok _ _ _ _ _ H1); unfold zlen; cbn [length]; pose proof (Zle_0_nat (length tl)); lia).
    pose proof (u64arr_store_ok bsegs _ (S + 16) (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) 1 (wa (S + 24)) ARR1
                  ltac:(rewrite upd_length, LEN; lia) ltac:(f_equal; lia)) as SOK1.
    zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u64arr_write bsegs mm (S + 16) (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) 1 rac ARR1 ltac:(rewrite upd_length, LEN; lia)) as ARR2;
      replace (S + 16 + 8 * 1) with (S + 24) in ARR2 by lia end.
    store_done.
    zstep. (* [comment removed for export] *)
    replace s0c with (Z_to_bv 64 (bv_unsigned s0c)) by (apply Z_to_bv_bv_unsigned).
    change (pc0 :: bv_unsigned rac :: tl) with ([pc0; bv_unsigned rac] ++ tl).
    eapply uwf_loop; [exact UWT| lia| pose proof (bv_unsigned_in_range 64 s0c) as R; unfold bv_modulus in R; cbn in R; lia| lia
                     | rewrite HTR, (hook_tr_ok _ _ _ _ _ H1); reflexivity|].
    exists (upd (upd ws (Z.to_nat 0) (Z_to_bv 64 pc0)) (Z.to_nat 1) rac).
    split; [exact ARR2|]. split; [rewrite !upd_length; exact LEN|].
    split. { change (Z.to_nat 1) with (length [pc0]). apply tb_prefix_snoc; [exact TB1| rewrite upd_length, LEN; cbn; lia]. }
    split; [reflexivity|].
    repeat (split; [assumption|]). assumption.
  Qed.
End UWF.


End CeilWrap.
(* [comment removed for export] *)
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
End RTW_unwind_loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_fs_art.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_fs_art.RTW_leaves_tiny.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_fs_art.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_fs_art.RTW_leaves_thread.
Import RTW_unwind_loop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_kitL RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma uwt_len : forall m lo top pc0 prev f k tl, uwt m lo top pc0 prev f k tl -> k <= TRACE_MAX_LEN -> k + zlen tl <= TRACE_MAX_LEN.
Proof.
  intros m lo top pc0 prev f k tl U. induction U; intros Hk.
  - unfold zlen. cbn. lia.
  - unfold zlen. cbn. lia.
  - rewrite zlen_app. destruct (bv_unsigned pc1 =? pc0); unfold zlen in *; cbn [length app] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma stk_of_wr_high : forall m a n, wr_at bsegs m a n -> AIMG_HI <= a -> stk bsegs m a (a + n).
Proof.
  intros m a n (H0 & H1 & HW) Ha. split; [lia|]. split; [lia|]. intros x Hx.
  pose proof (HW (x - a) ltac:(lia)) as W. replace (a + (x - a)) with x in W by lia. split; [exact W|].
  assert (NS : noseg bsegs (wa x)) by (apply noseg_Z; lia).
  pose proof (wview_noseg_some m (wa x) NS W) as Hs. unfold mrd. destruct (m (wa x)) as [b|]; [exists b; reflexivity| congruence].
Qed.

Lemma stk_of_wr_mono : forall m m' a n, wr_at bsegs m a n -> wmono bsegs m m' -> AIMG_HI <= a -> stk bsegs m' a (a + n).
Proof. intros m m' a n WR WM Ha. eapply stk_wmono_noseg; [apply stk_of_wr_high; [exact WR| exact Ha]| exact WM| exact Ha]. Qed.

Lemma c8_of_stk : forall m a, stk bsegs m a (a + 8) -> exists v : word, rw_cells bsegs m a [C8 v].
Proof. intros m a ST. (nelim ST 3%nat; intros H0 H1 H). apply c8_of_bytes; [lia| lia|]. intros i Hi. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma u64arr_of_stk : forall n m a, stk bsegs m a (a + 8 * Z.of_nat n) -> exists ws, length ws = n /\ u64arr bsegs m a ws.
Proof.
  induction n as [|n IH]; intros m a ST.
  - exists []. split; [reflexivity|]. (nelim ST 3%nat; intros H0 H1 _). split; [split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia|].
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (stk_split bsegs m a (a + 8) (a + 8 * Z.of_nat (S n)) ST ltac:(lia)) as [ST1 ST2].
    destruct (c8_of_bytes m a ltac:((nelim ST 3%nat; intros ? ? ?); lia) ltac:((nelim ST 3%nat; intros ? ? ?); lia)
                ltac:(intros i Hi; (nelim ST1 3%nat; intros _ _ H); apply H; lia)) as [v Hv].
    replace (a + 8 * Z.of_nat (S n)) with ((a + 8) + 8 * Z.of_nat n) in ST2 by lia.
    (nelim (IH m (a + 8) ST2) 3%nat; intros ws Hlen Hws). exists (v :: ws). split; [cbn; lia|].
    destruct Hv as [[_ Hb] Hw]. destruct Hws as [Hb2 Hw2]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
    split.
    + cbn [u64s]. apply bytes_at_app. split; [exact Hb|]. rewrite length_le8. replace (a + Z.of_nat 8) with (a + 8) by lia. exact Hb2.
    + cbn [length]. replace (8 * Z.of_nat (S (length ws))) with (8 + 8 * Z.of_nat (length ws)) by lia.
      apply wr_at_app; [lia| lia|]. split. { cbn [cells_size Cells.csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw. } exact Hw2.
Qed.

(* [comment removed for export] *)
Lemma trace_cells_of_u64arr : forall m a ws tr, u64arr bsegs m a ws -> tb_prefix ws tr -> (length tr <= length ws)%nat ->
  rw_cells bsegs m a (trace_cells tr).
Proof.
  intros m a ws tr [HB HW] TB HL. unfold tb_prefix in TB.
  assert (E : u64s ws = u64s (map wz tr) ++ u64s (skipn (length tr) ws)).
  { rewrite <- (firstn_skipn (length tr) ws) at 1. rewrite u64s_app, TB. reflexivity. }
  rewrite E in HB. apply bytes_at_app in HB. destruct HB as [HB1 _].
  assert (CB_ : cells_bytes (trace_cells tr) = u64s (map wz tr)).
  { unfold trace_cells. clear. induction tr as [|x tr' IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. }
  assert (CS : cells_size (trace_cells tr) = (8 * length tr)%nat).
  { unfold trace_cells. clear. induction tr as [|x tr' IH]; [reflexivity|]. cbn [map cells_size Cells.csize length]. rewrite IH. lia. }
  split; [split|].
  - unfold trace_cells. clear. induction tr; cbn; tauto.
  - rewrite CB_. exact HB1.
  - rewrite CS. (nelim HW 3%nat; intros W0 W1 HW). split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
Qed.

(* [comment removed for export] *)
Lemma munch_drop_byte : forall W a m m', munch (W ++ [(a, a + 1)]) m m' -> 0 <= a < 2^64 -> m' (wa a) = m (wa a) -> munch W m m'.
Proof.
  intros W a m m' MU Ha E x Hx. destruct (Z.eq_dec (bv_unsigned x) a) as [EQ|NE].
  - replace x with (wa a); [exact E|]. apply bv_eq. rewrite wa_unsigned by lia. symmetry. exact EQ.
  - apply MU. clear -Hx NE. induction W as [|[lo hi] W IH]; cbn in *; [lia|]. destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma cell1_overlay : forall m a v, rw_cells bsegs m a [C1 (zb v)] -> 0 <= a < 2^64 /\ (a < AIMG_LO \/ AIMG_HI <= a) -> m (wa a) = Some (zb v).   (* [comment removed for export] *)
Proof.
  intros m a v [[_ (H0 & H1 & HB)] _] [Ha0 Ha]. cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *. cbn [length] in *.
  specialize (HB 0%nat ltac:(lia)). cbn [nth_error] in HB. rewrite Z.add_0_r in HB.
  unfold mrd in HB. destruct (m (wa a)) as [b|] eqn:E; [congruence|].
  exfalso.
  assert (NS : noseg bsegs (wa a)) by (apply noseg_out; assumption). unfold seg_rom in HB.
  rewrite (memory_read_noseg bsegs (wa a) 1 NS ltac:(lia)) in HB. discriminate.
Qed.


(* [comment removed for export] *)
Lemma sel_mask_true : forall a b x, a < b -> 0 <= x < 2^64 -> Z.land ((0 - Z.b2z (a <? b)) mod 18446744073709551616) x = x.
Proof.
  intros a b x Hab Hx. rewrite (proj2 (Z.ltb_lt a b) Hab). cbn [Z.b2z].
  change ((0 - 1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma unwind_cells : forall st m, RTREP st m ->
  (exists j1 j2 j3 j4 j5, rw_cells bsegs m (st_t st)
      [C8 (wz (st_ctx st)); C8 (wz (ASTACK_TOP (st_sp0 st))); C8 (wz (ASTACK_BOTTOM (st_sp0 st))); CB 16 j1; C1 (zb 0); CB 7 j2; C8 j3; C8 j4; C8 j5; C8 (wz (st_fs st))])
  /\ rw_cells bsegs m (st_t st + 3168) [C1 (zb 0)]
  /\ ro_cells bsegs m 0xa16e0 [C8 (Z_to_bv 64 0x139460)]
  /\ ro_cells bsegs m 0x139460 [C8 (Z_to_bv 64 4096)].
Proof.
  intros st m HR. pose proof (rr_thread st m HR) as HT. pose proof (rr_consts st m HR) as HC.
  destruct HT as (_ & (j1 & j2 & j3 & j4 & j5 & T2) & _ & T4 & _).
  (nelim HC 6%nat; intros _ _ _ _ K5 _).
  split; [exists j1, j2, j3, j4, j5; exact T2|].
  split; [unfold T_UNWINDING in T4; exact T4|].
  split; [apply (R_link_at m 0xa16e0 0x139460 (rr_link st m HR)); vm_compute; reflexivity|].
  exact K5.
Qed.

Section UW.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost)
            (st : rtstate) (S pc0 bp : Z) (rac s0c : word) (tl : list Z) (lo : Z).
  Hypothesis HRTS : RTS st m mo g.
  Hypothesis A0 : a0 = wz S. Hypothesis A1 : a1 = wz pc0. Hypothesis A2 : a2 = wz bp. Hypothesis A3 : a3 = wz 0.
  Hypothesis A4 : a4 = wz 1. Hypothesis A5 : a5 = wz TRACE_MAX_LEN. Hypothesis TP : tp = wz ATP.
  Hypothesis OBJ0 : rw_cells bsegs m S [C8 (wz (S + 16)); C4 (wz 0); C4 (wz 0)].
  Hypothesis WR : wr_at bsegs m S BST_SIZE.
  Hypothesis SPS : bv_unsigned sp <= S.
  Hypothesis SPB : bv_unsigned sp <= bp - 16.
  Hypothesis BPR : bp < 2^64.
  Hypothesis PCR : 0 <= pc0 < 2^64.
  Hypothesis REC0 : bytes_at bsegs m (bp - 16) (le8 s0c ++ le8 rac).
  Hypothesis RAC1 : 4096 <= bv_unsigned rac. Hypothesis RAC2 : bv_unsigned rac <> pc0.
  Hypothesis UWT : hop1_ok (st_sp0 st) bp = true -> uwt m bp (ASTACK_TOP (st_sp0 st)) pc0 bp (bv_unsigned s0c) 2 tl.
  Hypothesis DISJ : S + BST_SIZE <= bp - 16 \/ ASTACK_TOP (st_sp0 st) <= S.
  Hypothesis ST0 : stk bsegs m lo (bv_unsigned sp).
  Hypothesis HCEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AUNWIND_STACK.
  Hypothesis MI0 : mem_inv bsegs m.

  Let tr := hook_tr pc0 (st_sp0 st) bp (bv_unsigned rac) tl.
  Let TOP := ASTACK_TOP (st_sp0 st).
  Let BOT := ASTACK_BOTTOM (st_sp0 st).

  Lemma unwind_walk :
    evt bsegs (unwind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st S bp tr lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AUNWIND_IMPL) fc None m (seg_rom bsegs)).
  Proof.
    (nelimp HRTS 4%nat; intros HR WF HM HG).
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    (* [comment removed for export] *)
    pose proof REC0 as RECb. change (bytes_at bsegs m (bp - 16) (le8 s0c ++ le8 rac)) with (id (bytes_at bsegs m (bp - 16) (le8 s0c ++ le8 rac))) in RECb.
    clear REC0.
    pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
    pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0.
    assert (HTB : 0 <= BOT /\ BOT + 0x800000 = TOP /\ TOP + 16 < 2^64 /\ 4096 <= TOP).
    { subst BOT TOP. unfold ASTACK_BOTTOM, ASTACK_TOP, roundup. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_bound _ _ _ _ OBJ0) as SB0. (nelimp WR 3%nat; intros WR0 WR1 WRi).
    pose proof (munch_refl (W S lo (st_t st + 3168) (bv_unsigned sp) tr) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (S + 8, S + 12)] m) as MUhi.
    unfold W in MU.
    destruct (unwind_cells st m HR) as ((j1 & j2 & j3 & j4 & j5 & TPG) & UNW & GOTC & PSC). cbv beta delta [zb wz] in TPG, UNW.
    unfold AUNWIND_IMPL, AUNWIND_STACK, BST_SIZE, TRACE_MAX_LEN in *. subst a0 a1 a2 a3 a4 a5 tp. leaf_prep.
    carve_frame 80%nat ST.
    do 11 lstep. (* [comment removed for export] *)
    do 6 lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    pose proof HR as HR1. rtrep_high HR1 WF MUhi WM.
    call asan_inited_proof; [exact HR1| exact MI| discriminate| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
    after_call.
    assert (E80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    rewrite E80 in *.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    clear HR1. pose proof HR as HR1. rtrep_high HR1 WF MUhi WM.
    call get_current_thread_proof; [exact HR1| exact WF| exact MI| reflexivity| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
    after_call. rewrite E80 in *. clear HR1.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    clear MUhi.
    lstep. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep. fl. lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    rewrite sel_mask_true by lia.
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. fl. lstep. lstep. if_lia.
    lstep. lstep. lstep. lstep. lstep.
    rewrite sel_mask_true by lia.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) lstep. if_lia. (* [comment removed for export] *)
    do 8 lstep.
    lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 8 lstep. (* [comment removed for export] *)
    do 4 lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    setreg 6 (Z_to_bv 64 bp) ltac:(f_equal; change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64);
                                     rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with WMc : wmono bsegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_wr_mono m mm S 2064 (conj WR0 (conj WR1 WRi)) WMc ltac:(unfold AIMG_HI; lia)) as SST;
      destruct (c8_of_stk mm (S + 2056) ltac:(eapply stk_sub; [exact SST| lia| lia])) as [tfb0 TFB];
      (nelim (u64arr_of_stk 255 mm (S + 16) ltac:(eapply stk_sub; [exact SST| lia| cbn; lia])) 3%nat; intros ws LEN ARR);
      clear SST end.
    lstep. (* [comment removed for export] *)
    lstep. if_lia. lstep. if_lia. lstep. if_lia. (* [comment removed for export] *)
    do 5 lstep. do 7 lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -80).
    assert (TRL : zlen tr <= 30).
    { subst tr. unfold hook_tr. destruct (Sumbool.sumbool_of_bool (hop1_ok (st_sp0 st) bp)) as [E|E]; rewrite E.
      - pose proof (uwt_len _ _ _ _ _ _ _ _ (UWT E) ltac:(unfold TRACE_MAX_LEN; lia)) as L. unfold TRACE_MAX_LEN in L.
        rewrite !zlen_cons. lia.
      - unfold zlen. cbn. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl (W S lo (st_t st + 3168) (bv_unsigned sp + -80) tr) mm) as MU1;
      pose proof (wmono_refl bsegs mm) as WM1;
      assert (AG1 : agree_on (bp - 16) TOP m mm)
        by (intros a Ha; unfold mrd; rewrite (MU (wa a)); [reflexivity|]; rewrite wa_unsigned by lia; cbn; subst TOP; lia)
    end.
    eapply evt_cut.
    { eapply (uwf_entry _ _ gp _ _ _ s9 s10 s11 F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ S pc0 bp TOP lo (st_t st + 3168) (bv_unsigned sp + -80) tr);
        [ | | | | exact TRL | exact AG1 | reflexivity | | exact RECb | split; [exact RAC1| exact RAC2] | exact UWT | reflexivity
        | exact ARR | exact LEN | exact OBJ0 | exact TFB | exact UNW | exact GOTC | exact PSC | exact MI | exact MU1 | exact WM1 | ].
      - rewrite E80. unfold BST_SIZE. lia.
      - subst TOP. lia.
      - rewrite E80. lia.
      - idtac. unfold AIMG_LO, AIMG_HI. lia.
      - subst BOT. lia.
      - rewrite E80. exact ST. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 18%nat; intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' -> UP).
    (nelim UP 14%nat; intros ws' k' ARR' LEN' TB' K' HK' OBJ' TFB' UNW' MI' MU' WM' ST').
    unfold W in MU'. rewrite E80 in ST'.
    (* [comment removed for export] *)
    lazymatch type of MU' with munch ?W1 ?ma ?mb =>
      lazymatch type of MU with munch ?W0 _ _ =>
      apply (rw_cells_transport bsegs W1 ma mb) in FR; [| exact MU'| exact WM'| cbn; lia];
      apply (munch_weaken W1 W0 ma mb) in MU'; [| unfold sub_fp; cbn; intros; lia];
      apply (munch_trans W0 m ma mb MU) in MU' end end.
    apply (wmono_trans bsegs m _ _ WM) in WM'.
    clear MI ST TFB ARR LEN UNW OBJ0 GOTC PSC TPG MU WM MU1 WM1 AG1. rename MI' into MI. rename ST' into ST.
    replace (ret_pc (Z_to_bv 64 377720)) with (Z_to_bv 64 377720) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbv beta delta [wz zb] in OBJ', TFB', UNW'.
    lstep. (* [comment removed for export] *)
    do 12 lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold unwind_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI|]. split; [exact ST|].
    split; [| split; [| split]].
    - (* [comment removed for export] *)
      assert (MUd : munch [(lo, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 16 + 8 * zlen tr); (S + 2056, S + 2064)] m m2).
      { eapply munch_drop_byte; [exact MU'| lia|].
        rewrite (cell1_overlay m2 _ 0 UNW' ltac:(unfold AIMG_LO, AIMG_HI; lia)).
        pose proof (rr_thread st m HR) as HT. (nelim HT 5%nat; intros _ _ _ T4 _). unfold T_UNWINDING in T4.
        rewrite (cell1_overlay m _ 0 T4 ltac:(unfold AIMG_LO, AIMG_HI; lia)). reflexivity. }
      eapply (RTREP_high st _ m m2 WF); [| exact MUd| exact WM'| exact HR].
      repeat (constructor; [cbn; lia|]). constructor.
    - subst k'. exact (rw_cells_mid m2 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr))] [C4 (Z_to_bv 64 0)] OBJ').
    - eapply trace_cells_of_u64arr; [exact ARR'| exact TB'| rewrite LEN'; unfold zlen in TRL; lia].
    - exact TFB'.
  Qed.
End UW.

Theorem unwind_proof : unwind_spec.
Proof.
  unfold unwind_spec. intros until lo. intros HRTS A0 A1 A2 A3 A4 A5 TP OBJ WR SPS SPB BPR PCR REC RAC1 RAC2 UWT DISJ ST HCEIL LO MI.
  eapply unwind_walk; eassumption.
Qed.


End CeilWrap.
