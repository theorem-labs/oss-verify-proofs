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
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_mmapN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_p_pop2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_map OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_loops OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_efa OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_libo OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
(* [comment removed for export] *)
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].

(* [comment removed for export] *)
Lemma pop_tail : forall (x1 sp gp tp y5 y6 y7 x9 x10 x11 x12 x14 x15 y16 y17 x18 x20 s6v s7 s8 s9 s10 s11 y28 y29 y30 y31 : word) (s6 s5 s4 s3 s2 s1 s0 ra : word) (mtx sem : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc S alloc mapped' nf N lo : Z) (jr je js : list byte) (exh : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells bsegs m Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)] ->
  rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling ->
  0 < S <= 65536 -> 0 <= alloc -> 0 <= N -> alloc + N * S <= mapped' -> mapped' <= KFREEARRAY_OFF -> 0 <= nf -> 4 * (nf + N) <= 2^29 ->
  evt bsegs (fun ms2 => exists (z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) m2,
      ms2 = MS (mkR ra sp gp tp z5 z6 z7 s0 s1 (wz 1) z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Rc + 16, Rc + 24); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69)] m m2
      /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + N))]
      /\ rw_cells bsegs m2 (Rc + 32) [C8 (Z_to_bv 64 (alloc + N * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js])
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp y5 y6 y7 (wz Rc) x9 x10 x11 x12 (wz alloc) x14 x15 y16 y17
             x18 (wz N) x20 (wz S) s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (wz 0x372f4) fc None m (seg_rom bsegs)).
Proof.
  intros until exh. intros MI ST CEIL LO FR RIa RIb HR1 HR2 HS Ha HN HNS Hmx Hnf Htf.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Rc + 16, Rc + 24); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, pop_frame in *. cbv beta delta [wz] in *.
  assert (NS0 : 0 <= N * S) by nia.
  lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. fl. lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  do 8 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. nexists 15%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact RIa| exact RIb].
Qed.

(* [comment removed for export] *)
Lemma pop_G : forall (sp gp tp y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 s6v s7 s8 s9 s10 s11 y28 y29 y30 y31 : word) (s6 s5 s4 s3 s2 s1 s0 ra : word) (mtx sem : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc RB S alloc mapped' nf N lo : Z) (jr je js : list byte) (exh : Z) (dpre : list word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells bsegs m Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)] ->
  rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> KHIGHMEM_BEG <= RB -> RB + 2^32 <= alloc_ceiling -> RB + 2^32 <= Rc ->
  32 <= S <= 65536 -> 0 <= alloc <= mapped' -> mapped' <= KFREEARRAY_OFF -> 0 <= nf -> 4 * (nf + N) <= 2^29 ->
  N = (mapped' - alloc) / S -> length dpre = Z.to_nat N ->
  u32arr bsegs m (RB + KFREEARRAY_OFF + 4 * nf) dpre ->
  evt bsegs (fun ms2 => exists (z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 : word) m2,
      ms2 = MS (mkR ra sp gp tp z5 z6 z7 s0 s1 (wz 1) z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (RB + KFREEARRAY_OFF + 4 * nf, RB + KFREEARRAY_OFF + 4 * nf + 4 * N); (Rc + 16, Rc + 24); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69)] m m2
      /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + N))]
      /\ rw_cells bsegs m2 (Rc + 32) [C8 (Z_to_bv 64 (alloc + N * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js]
      /\ u32arr bsegs m2 (RB + KFREEARRAY_OFF + 4 * nf) (fill_vals alloc S (Z.to_nat N)))
    (MS (mkR (wz 0x372ac) (wz (bv_unsigned sp + -64)) gp tp y5 y6 y7 (wz Rc) (wz (nf + N)) (wz 1) y11 y12 y13 y14 y15 y16 y17
             (wz RB) (wz N) (wz (mapped' - alloc)) (wz S) s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (wz 0x372ac) fc None m (seg_rom bsegs)).
Proof.
  intros until dpre. intros MI ST CEIL LO FR RIa RIb HR1 HR2 HB1 HB2 HBR HS Ham Hmx Hnf Htf HN LD DST.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, pop_frame in *. cbv beta delta [wz] in *.
  assert (NR : 0 <= N /\ N * S <= mapped' - alloc /\ mapped' - alloc < N * S + S).
  { subst N. split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod (mapped' - alloc) S ltac:(lia)). pose proof (Z.mod_pos_bound (mapped' - alloc) S ltac:(lia)). nia. }
  (nelim NR 3%nat; intros N0 N1 N2).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    assert (NZ : N = 0) by (cut_on [HS Ham HN RSP N0 N1 N2 K0] nia). clear HN. subst N.
    eapply evt_mono; [eapply pop_tail; [exact MI| exact ST| exact CEIL| exact LO| exact FR| exact RIa| exact RIb| ..]; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF; idtac; lia|].
    cbv beta. intros ms2 nelH_; (nelim nelH_ 22%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m2 -> MU WM MI2 ST2 RIa2 RIb2).
    nexists 15%nat. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU]. subfp. }
    split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact RIa2|]. split; [exact RIb2|].
    destruct dpre; [| cbn in LD; lia]. cbn [fill_vals Z.to_nat rev map seq].
    eapply (u32arr_transport bsegs _ m m2); [exact DST| exact MU| exact WM| cbn [disjoint_from]; rewrite fill_vals_length; lia].
  - (* [comment removed for export] *)
    assert (NP : 0 < N) by nia.
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (RB + 3758096384 + 4 * nf + 4 * N)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    setreg 12 (Z_to_bv 64 (alloc + 0 * S)) ltac:(f_equal; lia).
    rewrite <- (app_nil_r dpre) in DST. change ([] : list word) with (fill_vals alloc S (Z.to_nat 0)) in DST.
    eapply (fill_loop (Z.to_nat N) 0 N (RB + 3758096384 + 4 * nf) S alloc dpre);
      [lia| lia| lia| lia| lia| unfold KFREEARRAY_OFF in *; lia| unfold AIMG_HI; lia| exact LD| exact DST| exact MI|].
    intros m' ARR2 MU2 WM2 MI2 x14 x15. replace (alloc + 0 * S) with alloc by lia.
    transport_after_call bsegs m m' MU2 WM2.
    eapply evt_mono; [eapply pop_tail; [exact MI2| exact ST| exact CEIL| exact LO| exact FR| exact RIa| exact RIb| ..]; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF; idtac; lia|].
    cbv beta. intros ms2 nelH_; (nelim nelH_ 22%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m2 -> MU WM MI3 ST2 RIa2 RIb2).
    nexists 15%nat. split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU]]; subfp. }
    split; [eapply wmono_trans; [exact WM2| exact WM]|]. split; [exact MI3|]. split; [exact ST2|]. split; [exact RIa2|]. split; [exact RIb2|].
    eapply (u32arr_transport bsegs _ m' m2); [exact ARR2| exact MU| exact WM|].
    cbn [disjoint_from]. rewrite fill_vals_length. lia.
Qed.

(* [comment removed for export] *)
Lemma pop_X : forall (sp gp tp x5 x6 x7 x15 x16 x17 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc stt c q alloc mapped RB : Z) (jr je js : list byte) (a1v : word),
  mem_inv bsegs m ->
  ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)] ->
  rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= c <= 30 -> 0 <= q -> csize c * q <= 262144 -> 0 <= alloc <= mapped ->
  mapped < alloc + csize c * q -> mapped = KFREEARRAY_OFF ->
  evt bsegs (fun ms1 =>
      ms1 = MS (mkR (wz 0x370cc) sp gp tp x5 x6 x7 (wz Rc) (wz stt) (wz 0) (wz (KFREEARRAY_OFF + 1)) (wz c) (wz (mapped + 262144)) (wz q) x15 x16 x17
                    (wz RB) (wz 262144) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x373e0) fc None m (seg_rom bsegs))
    (MS (mkR (wz 0x370cc) sp gp tp x5 x6 x7 (wz Rc) (wz stt) (wz A_ALLOC) a1v (wz c) (wz alloc) (wz q) x15 x16 x17
             (wz RB) (wz (alloc + csize c * q)) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x371b8) fc None m (seg_rom bsegs)).
Proof.
  intros until a1v. intros MI AC40 RIb HR1 HR2 Hc Hq QS Ham LT EXH.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *. cbv beta delta [wz] in *. idtac.
  pose proof (csize_pos c ltac:(lia)) as CP.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite zb_lxor_ones by lia; rewrite land_align18 by (apply Z.mod_pos_bound; lia); Z.div_mod_to_equations; lia).
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. lstep. if_lia. (* [comment removed for export] *)
  apply evt_done. subst mapped. cbv delta [mkR]. reflexivity.
Qed.

Definition LUMP : Z := 294912.        (* [comment removed for export] *)
Definition POP_STACK : Z := 1264.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition p1_W (lo sp Rc T D Nv Ufa : Z) (fm : bool) : list (Z * Z) :=
  [(lo, sp); (Rc + 16, Rc + 24); (Rc + 24, Rc + 32); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69); (T + 2872, T + 2888); (D, D + 4 * Nv)]
  ++ (if fm then [(Ufa, Ufa + 262144); (SH Ufa, SH Ufa + 32768)] else []).

(* [comment removed for export] *)
Lemma spin_or_lscps_evt : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) mo g (Q : machine_state -> Prop) ms,
  evt bsegs Q ms ->
  (forall ms', Q ms' -> if spin then evt bsegs (jself bsegs) ms' else LSCPS bsegs P ms' mo g) ->
  if spin then evt bsegs (jself bsegs) ms else LSCPS bsegs P ms mo g.
Proof. intros spin P mo g Q ms EV K. destruct spin. - eapply evt_cut; [exact EV| exact K]. - eapply lscps_evt_then; [exact EV| exact K]. Qed.

Section P1.
  Hypothesis PS : poison_shadow_spec.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m1 : word -> option byte) (mo1 : Model) (G1 : list (Z * Z)) (R1 : Z) (st : rtstate)
            (Rc RB S alloc mapped1 nf fam lo : Z) (tj1 tj2 mtx sem : word) (jr je js : list byte) (exh1 : Z).
  Let Nv := (mapped1 - alloc) / S.
  Let n := nf + Nv.
  Let nm := (4 * n + 262143) / 262144 * 262144.
  Let Ufa := RB + KFREEARRAY_OFF + fam.
  Let D := RB + KFREEARRAY_OFF + 4 * nf.
  Let fam' := if fam <? 4 * n then nm else fam.
  Hypothesis HC1 : mmap_consts m1.
  Hypothesis IC1 : icpt_cells m1.
  Hypothesis PC1 : poison_cells m1.
  Hypothesis LC1 : leafc st m1.
  Hypothesis WF : RTWF st.
  Hypothesis TP : tp = wz ATP.
  Hypothesis MI1 : mem_inv bsegs m1.
  Hypothesis ST1 : stk bsegs m1 lo (bv_unsigned sp + -64).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + POP_STACK <= bv_unsigned sp.
  Hypothesis FR1 : rw_cells bsegs m1 (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra).
  Hypothesis RIa1 : rw_cells bsegs m1 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)].
  Hypothesis RI241 : rw_cells bsegs m1 (Rc + 24) [C8 (Z_to_bv 64 fam)].
  Hypothesis RIb1 : rw_cells bsegs m1 (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped1); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh1); CB 3 je; CB 56 js].
  Hypothesis A56 : ro_cells bsegs m1 0xa6390 [C1 (Z_to_bv 8 0)].
  Hypothesis TST1 : rw_cells bsegs m1 (st_t st + 2872) [C8 tj1; C8 tj2].
  Hypothesis VFA1 : stk bsegs m1 (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam).
  Hypothesis HRc : KHIGHMEM_BEG <= Rc /\ Rc + 128 <= alloc_ceiling /\ (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st) /\ (st_t st + 4096 <= Rc \/ Rc + 128 <= st_t st)
                   /\ RB + 2^32 <= Rc.
  Hypothesis HRB : KHIGHMEM_BEG <= RB /\ RB + 2^32 <= alloc_ceiling /\ RB mod 65536 = 0
                   /\ (st_ctx st + 160 <= RB \/ RB + 2^32 <= st_ctx st) /\ (st_t st + 4096 <= RB \/ RB + 2^32 <= st_t st).
  Hypothesis HS : 32 <= S <= 65536.
  Hypothesis Hm1 : 0 <= alloc <= mapped1 /\ mapped1 <= KFREEARRAY_OFF /\ mapped1 - alloc <= S + 524288.
  Hypothesis Hnf : 0 <= nf <= 8 /\ 4 * nf <= fam.
  Hypothesis Hfam : 0 <= fam /\ fam mod 262144 = 0 /\ fam <= 2^29.
  Hypothesis LZS1 : fam < 4 * n -> forall x : word, SH Ufa <= bv_unsigned x < SH Ufa + 32768 -> lzf mo1 x = true.
  Hypothesis HVIS1 : fam < 4 * n -> forall x : word, SH Ufa <= bv_unsigned x < SH Ufa + 32768 -> lzf mo1 x = true -> in_winb G1 x = true -> m1 x <> None.
  Hypothesis SITE1 : fam < 4 * n -> mmap_fixed_site mo1 Ufa 262144.
  Hypothesis HR1 : fam < 4 * n -> LUMP <= R1.

  Let RET (r : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom bsegs).

  #[using="Hfam Hnf Hm1 HS HRB HRc fam' D Ufa nm n fam nf RB Rc st ACEIL"] Lemma Nv_bound : 0 <= Nv <= 16385 /\ Nv * S <= mapped1 - alloc.
  Proof.
    subst Nv. (nelimp Hm1 3%nat; intros A1 A2 A3).
    split. { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. (cut_on [HRc HRB HS Hm1 Hnf Hfam A1 A2 A3] nia). }
    pose proof (Z.mul_div_le (mapped1 - alloc) S ltac:(lia)). lia.
  Qed.

  Lemma pop_P1 : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop) (x1 x5 x6 x7 x9 x11 x12 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 : word),
    (* [comment removed for export] *)
    True ->
    (* [comment removed for export] *)
    (forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 (m' : word -> option byte) (tj1' tj2' : word),
       mem_inv bsegs m' -> munch (p1_W lo (bv_unsigned sp) Rc (st_t st) D Nv Ufa (fam <? 4 * n)) m1 m' -> wmono bsegs m1 m' -> stk bsegs m' lo (bv_unsigned sp) ->
       rw_cells bsegs m' Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + Nv))] ->
       rw_cells bsegs m' (Rc + 24) [C8 (Z_to_bv 64 fam')] ->
       rw_cells bsegs m' (Rc + 32) [C8 (Z_to_bv 64 (alloc + Nv * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped1); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
       rw_cells bsegs m' (st_t st + 2872) [C8 tj1'; C8 tj2'] ->
       stk bsegs m' (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam') ->
       u32arr bsegs m' D (fill_vals alloc S (Z.to_nat Nv)) ->
       (if fam <? 4 * n then rw_cells bsegs m' (SH Ufa) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       LSCPS bsegs P (RET 1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m')
             (if fam <? 4 * n then mm_commit (wz Ufa) (wz 262144) mo1 else mo1)
             (mkG (if fam <? 4 * n then (SH Ufa, SH Ufa + 32768) :: G1 else G1) (R1 - (if fam <? 4 * n then LUMP else 0)))) ->
    LSCPS bsegs P
      (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz Rc) x9 (wz A_ALLOC) x11 x12 (wz alloc) x14 x15 x16 x17
               (wz RB) x19 (wz mapped1) (wz S) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x3728c) fc None m1 (seg_rom bsegs)) mo1 (mkG G1 R1).
  Proof.
    intros spin P x1 x5 x6 x7 x9 x11 x12 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 _ K1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [CEIL LO2]. pose proof CEIL as CEILn. idtac. unfold POP_STACK in LO2.
    (nelimp HRc 5%nat; intros RC1 RC2 RC3 RC4 RC5). (nelimp HRB 5%nat; intros RB1 RB2 RB3 RB4 RB5). (nelimp Hm1 3%nat; intros A1 A2 A3). destruct Hnf as [N1 N2]. (nelimp Hfam 3%nat; intros F1 F2 F3).
    pose proof RC2 as RC2n. idtac. pose proof RB2 as RB2n. idtac. unfold KHIGHMEM_BEG, AIMG_HI in RC1, RB1. olin_all. unfold KFREEARRAY_OFF in *.
    pose proof Nv_bound as [NB1 NB2].
    assert (EUfa : Ufa = RB + 3758096384 + fam) by reflexivity. assert (ED : D = RB + 3758096384 + 4 * nf) by reflexivity.
    assert (ENv : Nv = (mapped1 - alloc) / S) by reflexivity. assert (En : n = nf + Nv) by reflexivity.
    assert (E64 : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (unfold wz; apply unsigned_lit; lia).
    apply lscps_assume. intros NWX HOK HBINV.
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply pop_C; [exact MI1| exact RIa1| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RC2| lia| lia| lia| lia]. }
    cbv beta. intros ms1 ->. fold Nv. fold n.
    assert (Hn4 : 4 * n <= fam + 262144) by (subst n; lia).
    eapply (efa_spec PS) with (st := st) (fam := fam) (lo := lo) (tj1 := tj1) (tj2 := tj2) (spin := spin) (n := n);
      [exact HC1| exact IC1| exact PC1| exact LC1| exact WF| exact TP| exact MI1| rewrite E64; exact ST1| rewrite E64; unfold EFA_STACK; lia
      | exact RI241| exact A56| exact TST1| unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia
      | unfold KHIGHMEM_BEG, AIMG_HI; repeat split; try assumption; try (lia_on HRc HRB HS Hm1 RC5 RB1 RB3 N1); clear -RB3; Z.div_mod_to_equations; lia
      | subst n; (lia_on HRc HRB HS Hm1 RC5 RB1 N1 NB1)| repeat split; lia| exact HOK
      | intros LT; replace ((4 * n + 262143) / 262144 * 262144 - fam) with 262144 by (clear -LT F1 F2 Hn4; Z.div_mod_to_equations; lia); exact (SITE1 LT)
      | | | ..].
    1,2: assert (SZ8 : (fam < 4 * n /\ ((4 * n + 262143) / 262144 * 262144 - fam) / 8 = 32768) \/ (4 * n + 262143) / 262144 * 262144 <= fam)
           by (destruct (Z_lt_le_dec fam (4 * n)) as [LT|GE]; [left; split; [exact LT| clear -LT F1 F2 Hn4; Z.div_mod_to_equations; (lia_on F2 Hn4 LT H H0 H4 H5 H9)]
                                                                | right; clear -GE F1 F2 N1 NB1; subst n; Z.div_mod_to_equations; nia]).
    { intros x Hx. destruct SZ8 as [[LT E]|GE]; [rewrite E in Hx; exact (LZS1 LT x Hx)|]. exfalso. clear -Hx GE. Z.div_mod_to_equations. lia. }
    { intros x Hx. destruct SZ8 as [[LT E]|GE]; [rewrite E in Hx; exact (HVIS1 LT x Hx)|]. exfalso. clear -Hx GE. Z.div_mod_to_equations. lia. }
    { unfold LUMP in HR1. intros LT. pose proof (HR1 LT). clear -H LT F1 F2 Hn4. Z.div_mod_to_equations. lia. }
    all: cbv beta delta [wz]; cbv delta [wz] in E64; rewrite ?E64.
    all: replace (ret_pc (Z_to_bv 64 225964)) with (Z_to_bv 64 225964 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    - (* [comment removed for export] *)
      intros GE y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2 RI2.
      pose proof FR1 as FR2. eapply (rw_cells_transport bsegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; lia].
      pose proof RIa1 as RIa2. eapply (rw_cells_transport bsegs _ m1 m2) in RIa2; [| exact MU2| exact WM2| cbn; lia].
      pose proof RIb1 as RIb2. eapply (rw_cells_transport bsegs _ m1 m2) in RIb2; [| exact MU2| exact WM2| cbn; lia].
      pose proof TST1 as TST2. eapply (rw_cells_transport bsegs _ m1 m2) in TST2; [| exact MU2| exact WM2| cbn; pose proof (t_range st WF); unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on HRc HRB HS Hm1 CEILn RC3 RC4 RC5 RB4 RB5 N1 RC2n RB2n H)].
      pose proof VFA1 as VFA2. eapply (stk_transport_disjoint bsegs _ m1 m2) in VFA2; [| exact MU2| exact WM2| cbn; lia].
      (* [comment removed for export] *)
      destruct (stk_split bsegs m2 _ D _ VFA2 ltac:(subst D n; lia)) as [VL VR0].
      destruct (stk_split bsegs m2 _ (D + 4 * Nv) _ VR0 ltac:(subst D n; lia)) as [VM VR].
      (nelim (stk_carve bsegs m2 D (D + 4 * Nv) (Z.to_nat (4 * Nv)) VM ltac:(lia)) 3%nat; intros _ junk JK).
      replace (D + 4 * Nv - Z.of_nat (Z.to_nat (4 * Nv))) with D in JK by (lia_on HRc HRB HS Hm1 RC5 RB1 N1 NB1).
      destruct (p_u32arr_of_u8arr bsegs m2 D junk (Z.to_nat Nv) (u8arr_of_rw_cells bsegs _ _ _ _ JK)) as (dpre & LD & DST). (* [comment removed for export] *)
      { pose proof (rw_cells_bound bsegs m2 D _ JK). cbn [cells_size Cells.csize] in H. destruct JK as [[WFj _] _]. cbn in WFj. (lia_on HRc HRB HS Hm1 RC5 RB1 N1 WFj). }
      eapply lscps_evt_then.
      { eapply (pop_G sp gp tp) with (lo := lo) (nf := nf) (N := Nv) (dpre := dpre);
          [exact MI2| exact ST2| exact CEIL| lia| exact FR2| exact RIa2| exact RIb2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RC2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RB2| exact RC5
          | exact HS| lia| unfold KFREEARRAY_OFF; lia| lia| subst n; lia| reflexivity| exact LD| unfold KFREEARRAY_OFF; exact DST]. }
      cbv beta. intros ms3 nelH_; (nelim nelH_ 23%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 -> MU3 WM3 MI3 ST3 RIa3 RIb3 FILL).
      unfold KFREEARRAY_OFF in MU3, FILL.
      subst fam'. assert (EF : (fam <? 4 * n) = false) by (apply Z.ltb_ge; lia). rewrite !EF in K1. rewrite ?EF.
      cbv beta iota delta [wz] in K1. rewrite Z.sub_0_r in K1.
      eapply (K1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 tj1 tj2); [exact MI3| | eapply wmono_trans; [exact WM2| exact WM3]| exact ST3| exact RIa3| | exact RIb3| | | exact FILL| exact I].
      + unfold p1_W. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; subfp.
      + eapply (rw_cells_transport bsegs _ m2 m3); [exact RI2| exact MU3| exact WM3| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 RC2n NB1)].
      + eapply (rw_cells_transport bsegs _ m2 m3); [exact TST2| exact MU3| exact WM3| cbn; pose proof (t_range st WF); unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on HRc HRB HS Hm1 CEILn RC3 RC4 RC5 RB4 RB5 N1 F3 RC2n RB2n NB1 EF H)].
      + unfold KFREEARRAY_OFF.
        apply (stk_merge bsegs m3 _ D); [| | subst D n; (lia_on HRc HRB HS Hm1 Hnf RC5 RB1 N1)].
        { eapply (stk_transport_disjoint bsegs _ m2 m3); [exact VL| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 RC2n)]. }
        apply (stk_merge bsegs m3 _ (D + 4 * Nv)); [| | subst D n; lia].
        { pose proof (stk_of_rw_cells bsegs m3 D _ (rw_cells_of_u8arr bsegs _ _ _ (p_u8arr_of_u32arr bsegs _ _ _ FILL))) as SF.
          cbn [cells_size Cells.csize] in SF. rewrite Nat.add_0_r, u32s_length, fill_vals_length in SF.
          replace (D + Z.of_nat (4 * Z.to_nat Nv)) with (D + 4 * Nv) in SF by (lia_on HRc HRB HS Hm1 RC5 RB1 N1 NB1). exact SF. }
        eapply (stk_transport_disjoint bsegs _ m2 m3); [exact VR| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 F3 RC2n)].
    - (* [comment removed for export] *) exact I.
    - (* [comment removed for export] *)
      intros LT y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 tj1' tj2' MI2 MU2 WM2 ST2 RI2 STU SHP TST2. unfold KFREEARRAY_OFF in *.
      assert (SZV : (4 * n + 262143) / 262144 * 262144 - fam = 262144) by (clear -LT F1 F2 Hn4; Z.div_mod_to_equations; lia).
      rewrite !SZV in *. change (262144 / 8) with 32768 in *.
      assert (F0 : fam = 0) by (clear -LT F1 F2 N1 NB1; subst n; Z.div_mod_to_equations; nia).
      pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
      assert (SHR : SH (RB + 3758096384 + fam) + 32768 <= 17594333495296).
      { unfold SH, SHADOW_OFFSET. clear -RB1 RB2n F1 F3. Z.div_mod_to_equations. lia. }
      assert (SHR' : SH Ufa + 32768 <= 17594333495296) by exact SHR.
      pose proof FR1 as FR2. eapply (rw_cells_transport bsegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; (lia_on HRc LO2 CEILn F0 TR SHR)].
      pose proof RIa1 as RIa2. eapply (rw_cells_transport bsegs _ m1 m2) in RIa2; [| exact MU2| exact WM2| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0 TR SHR)].
      pose proof RIb1 as RIb2. eapply (rw_cells_transport bsegs _ m1 m2) in RIb2; [| exact MU2| exact WM2| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0 TR SHR)].
      pose proof VFA1 as VFA2. eapply (stk_transport_disjoint bsegs _ m1 m2) in VFA2; [| exact MU2| exact WM2| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0 TR SHR)].
      pose proof (stk_merge bsegs m2 _ _ _ VFA2 STU ltac:(lia)) as VALL.
      destruct (stk_split bsegs m2 _ D _ VALL ltac:(subst D n; lia)) as [VL VR0].
      destruct (stk_split bsegs m2 _ (D + 4 * Nv) _ VR0 ltac:(subst D n; lia)) as [VM VR].
      (nelim (stk_carve bsegs m2 D (D + 4 * Nv) (Z.to_nat (4 * Nv)) VM ltac:(lia)) 3%nat; intros _ junk JK).
      replace (D + 4 * Nv - Z.of_nat (Z.to_nat (4 * Nv))) with D in JK by (lia_on HRc HRB HS Hm1 RC5 RB1 NB1 LT F0).
      destruct (p_u32arr_of_u8arr bsegs m2 D junk (Z.to_nat Nv) (u8arr_of_rw_cells bsegs _ _ _ _ JK)) as (dpre & LD & DST). (* [comment removed for export] *)
      { pose proof (rw_cells_bound bsegs m2 D _ JK). cbn [cells_size Cells.csize] in H. destruct JK as [[WFj _] _]. cbn in WFj. (lia_on HRc HRB HS Hm1 RC5 RB1 N2 LT F0 WFj). }
      eapply lscps_evt_then.
      { eapply (pop_G sp gp tp) with (lo := lo) (nf := nf) (N := Nv) (dpre := dpre);
          [exact MI2| exact ST2| exact CEIL| lia| exact FR2| exact RIa2| exact RIb2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RC2| unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RB2| exact RC5
          | exact HS| lia| unfold KFREEARRAY_OFF; lia| lia| subst n; lia| reflexivity| exact LD| unfold KFREEARRAY_OFF; exact DST]. }
      cbv beta. intros ms3 nelH_; (nelim nelH_ 23%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 -> MU3 WM3 MI3 ST3 RIa3 RIb3 FILL).
      unfold KFREEARRAY_OFF in MU3, FILL.
      subst fam'. assert (EF : (fam <? 4 * n) = true) by (apply Z.ltb_lt; lia). rewrite !EF in K1.
      cbv beta iota delta [wz] in K1. unfold LUMP in K1. replace (R1 - 262144 - 32768) with (R1 - 294912) by lia.
      eapply (K1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 tj1' tj2'); [exact MI3| | eapply wmono_trans; [exact WM2| exact WM3]| exact ST3| exact RIa3| | exact RIb3| | | exact FILL|].
      + unfold p1_W. eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]]; subfp.
      + eapply (rw_cells_transport bsegs _ m2 m3); [exact RI2| exact MU3| exact WM3| cbn; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n Hn4 LT F0 TR EF)].
      + sepM. sepM. eapply (rw_cells_transport bsegs _ m2 m3); [exact TST2| exact MU3| exact WM3| cbn; (lia_on HRc HRB CEILn N1 SZV F0 TR)].
      + unfold KFREEARRAY_OFF.
        apply (stk_merge bsegs m3 _ D); [| | subst D n; (lia_on HRc HRB HS Hm1 RC5 RB1 N1 N2 LT SZV F0 EF)].
        { eapply (stk_transport_disjoint bsegs _ m2 m3); [exact VL| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N2 RC2n LT F0)]. }
        apply (stk_merge bsegs m3 _ (D + 4 * Nv)); [| | subst D n; clear -Hn4 N1 NB1 F1; Z.div_mod_to_equations; (lia_on N1 NB1)].
        { pose proof (stk_of_rw_cells bsegs m3 D _ (rw_cells_of_u8arr bsegs _ _ _ (p_u8arr_of_u32arr bsegs _ _ _ FILL))) as SF.
          cbn [cells_size Cells.csize] in SF. rewrite Nat.add_0_r, u32s_length, fill_vals_length in SF.
          replace (D + Z.of_nat (4 * Z.to_nat Nv)) with (D + 4 * Nv) in SF by (lia_on HRc HRB HS Hm1 RC5 RB1 NB1 LT F0 EF). exact SF. }
        try replace (RB + 3758096384 + nm) with (RB + 3758096384 + fam + 262144) by (subst nm; lia).
        try replace (RB + 3758096384 + (4 * n + 262143) / 262144 * 262144) with (RB + 3758096384 + fam + 262144) by lia.
        eapply (stk_transport_disjoint bsegs _ m2 m3); [exact VR| exact MU3| exact WM3| cbn; subst D; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 RC2n LT F0)].
      + eapply (rw_cells_transport bsegs _ m2 m3); [exact SHP| exact MU3| exact WM3| cbn [disjoint_from cells_size Cells.csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; (lia_on HRc HRB HS Hm1 CEILn RC5 RB1 N1 LT F0 SHR' EF)].
  Qed.
End P1.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition prf_W (lo sp Rc T stt U : Z) (um : bool) : list (Z * Z) :=
  [(lo, sp); (Rc + 48, Rc + 56); (T + 2872, T + 2888); (stt + 24, stt + 32)] ++ (if um then [(U, U + 262144); (SH U, SH U + 32768)] else []).
Definition pop_W (lo sp Rc T stt U D Nv Ufa : Z) (um fm : bool) : list (Z * Z) :=
  prf_W lo sp Rc T stt U um ++ [(Rc + 16, Rc + 24); (Rc + 24, Rc + 32); (Rc + 32, Rc + 40); (Rc + 68, Rc + 69); (D, D + 4 * Nv)]
  ++ (if fm then [(Ufa, Ufa + 262144); (SH Ufa, SH Ufa + 32768)] else []).

Section POPW.
  Hypothesis PS : poison_shadow_spec.
  Variables (sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Let ra : word := wz 0x370cc.
  Variables (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate)
            (S Rc stt c q alloc mapped nf fam lo : Z) (tj1 tj2 sa mtx sem : word) (jr je js : list byte) (exhb : bool).
  Let RB := S + c * 2^32.
  Let total := alloc + csize c * q.
  Let U := RB + mapped.
  Let Ufa := RB + KFREEARRAY_OFF + fam.
  Let D := RB + KFREEARRAY_OFF + 4 * nf.
  Let exh := if exhb then 1 else 0.
  Hypothesis HC : mmap_consts m.
  Hypothesis IC : icpt_cells m.
  Hypothesis PC : poison_cells m.
  Hypothesis LC : leafc st m.
  Hypothesis WF : RTWF st.
  Hypothesis TP : tp = wz ATP.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + POP_STACK <= bv_unsigned sp.
  Hypothesis AC32 : ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 S)].
  Hypothesis AC40 : ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)].
  Hypothesis AC56 : ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)].
  Hypothesis RIa : rw_cells bsegs m Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)].
  Hypothesis RI24 : rw_cells bsegs m (Rc + 24) [C8 (Z_to_bv 64 fam)].
  Hypothesis RIb : rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js].
  Hypothesis TST : rw_cells bsegs m (st_t st + 2872) [C8 tj1; C8 tj2].
  Hypothesis SA : rw_cells bsegs m (stt + 24) [C8 sa].
  Hypothesis Hstt : stt = st_t st + 2768.
  Hypothesis VFA : stk bsegs m (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam).
  Hypothesis HRc : KHIGHMEM_BEG <= Rc /\ Rc + 128 <= alloc_ceiling /\ (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st) /\ (st_t st + 4096 <= Rc \/ Rc + 128 <= st_t st)
                   /\ RB + 2^32 <= Rc.
  Hypothesis HS : KHIGHMEM_BEG <= S /\ S + 2^37 + 4096 <= alloc_ceiling /\ S mod 65536 = 0.
  Hypothesis HRBd : (st_ctx st + 160 <= RB \/ RB + 2^32 <= st_ctx st) /\ (st_t st + 4096 <= RB \/ RB + 2^32 <= st_t st).
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hq : 0 <= q <= 8 /\ csize c * q <= 262144.
  Hypothesis Ham : 0 <= alloc <= mapped /\ mapped mod 262144 = 0 /\ mapped <= KFREEARRAY_OFF /\ mapped <= alloc + csize c + 262144.
  Hypothesis Hnf : 0 <= nf <= 8 /\ 4 * nf <= fam.
  Hypothesis Hfam : 0 <= fam /\ fam mod 262144 = 0 /\ fam <= 2^29.
  Hypothesis LZS : forall x : word, SH RB <= bv_unsigned x < SH (RB + 2^32) -> lzf mo x = true.
  Hypothesis HVIS : forall x : word, SH RB <= bv_unsigned x < SH (RB + 2^32) -> lzf mo x = true -> in_winb G x = true -> m x <> None.
  Hypothesis SITEU : mmap_fixed_site mo U 262144.
  Hypothesis SITEF : forall mo1, fam + 262144 <= 2^29 -> (mo1 = mo \/ mo1 = mm_commit (wz U) (wz 262144) mo) -> mmap_fixed_site mo1 Ufa 262144.

  Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz stt) (wz c) (wz Rc) (wz q) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_POPULATE) fc None m (seg_rom bsegs).
  Let RET (r : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom bsegs).
  (* [comment removed for export] *)
  Let XST (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte) :=
    MS (mkR (wz 0x370cc) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz Rc) (wz stt) (wz 0) (wz (KFREEARRAY_OFF + 1)) (wz c) (wz (mapped + 262144)) (wz q) x15 x16 x17
             (wz RB) (wz 262144) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (wz 0x373e0) fc None m1 (seg_rom bsegs).

  Lemma RB_facts : KHIGHMEM_BEG <= RB /\ RB + 2^32 <= alloc_ceiling /\ RB mod 65536 = 0.
  Proof.
    subst RB. (nelimp HS 3%nat; intros S1 S2 S3). unfold KHIGHMEM_BEG, AIMG_HI in *. split; [(cut_on [Hstt HRc HS HRBd Hc Ham Hfam S1 S3] nia)|]. split; [nia|].
    rewrite Z.add_mod, S3 by lia. replace (2^32) with (65536 * 65536) by reflexivity. rewrite Z.mul_assoc, Z_mod_mult. reflexivity.
  Qed.

  Lemma populate_spec : forall (um fm : bool) (spin : bool) (P : machine_state -> Model -> lghost -> Prop),
    let mapped' := mapped + (if um then 262144 else 0) in
    let Nv := (mapped' - alloc) / csize c in
    let n := nf + Nv in
    let nm := (4 * n + 262143) / 262144 * 262144 in
    let fam' := if fm then nm else fam in
    let mo1 := if um then mm_commit (wz U) (wz 262144) mo else mo in
    let G1 := if um then (SH U, SH U + 32768) :: G else G in
    let R1 := R - (if um then LUMP else 0) in
    um = (mapped <? total) -> fm = (fam <? 4 * n) ->
    (if um then LUMP else 0) + (if fm then LUMP else 0) <= R ->
    (* [comment removed for export] *)
    (exhb = true -> um = true -> mapped = KFREEARRAY_OFF ->
     forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte),
       mem_inv bsegs m' -> munch [(lo, bv_unsigned sp)] m m' -> wmono bsegs m m' -> stk bsegs m' lo (bv_unsigned sp) ->
       LSCPS bsegs P (RET 0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') mo (mkG G R)) ->
    (* [comment removed for export] *)
    (exhb = false -> um = true -> mapped = KFREEARRAY_OFF ->
     forall x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 (m1 : word -> option byte),
       mem_inv bsegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono bsegs m m1 -> stk bsegs m1 lo (bv_unsigned sp + -64) ->
       rw_cells bsegs m1 (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
       rw_cells bsegs m1 Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)] -> rw_cells bsegs m1 (Rc + 24) [C8 (Z_to_bv 64 fam)] ->
       rw_cells bsegs m1 (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
       rw_cells bsegs m1 (st_t st + 2872) [C8 tj1; C8 tj2] -> rw_cells bsegs m1 (stt + 24) [C8 sa] ->
       LSCPS bsegs P (XST x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 m1) mo (mkG G R)) ->
    (* [comment removed for export] *)
    True ->
    True ->
    (* [comment removed for export] *)
    ((um = true -> mapped + 262144 <= KFREEARRAY_OFF) ->
     forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte) (tj1' tj2' sa' : word),
       mem_inv bsegs m' -> munch (pop_W lo (bv_unsigned sp) Rc (st_t st) stt U D Nv Ufa um fm) m m' -> wmono bsegs m m' -> stk bsegs m' lo (bv_unsigned sp) ->
       rw_cells bsegs m' Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 (nf + Nv))] ->
       rw_cells bsegs m' (Rc + 24) [C8 (Z_to_bv 64 fam')] ->
       rw_cells bsegs m' (Rc + 32) [C8 (Z_to_bv 64 (alloc + Nv * csize c)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
       rw_cells bsegs m' (st_t st + 2872) [C8 tj1'; C8 tj2'] -> rw_cells bsegs m' (stt + 24) [C8 sa'] ->
       stk bsegs m' (RB + KFREEARRAY_OFF) (RB + KFREEARRAY_OFF + fam') ->
       u32arr bsegs m' D (fill_vals alloc (csize c) (Z.to_nat Nv)) ->
       (if um then stk bsegs m' U (U + 262144) /\ rw_cells bsegs m' (SH U) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       (if fm then rw_cells bsegs m' (SH Ufa) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True) ->
       LSCPS bsegs P (RET 1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m')
             (if fm then mm_commit (wz Ufa) (wz 262144) mo1 else mo1)
             (mkG (if fm then (SH Ufa, SH Ufa + 32768) :: G1 else G1) (R1 - (if fm then LUMP else 0)))) ->
    LSCPS bsegs P ENTRY mo (mkG G R).
  Proof.
    intros um fm spin P. cbv zeta. intros EUM EFM HR KX1 KX _ _ K1.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [CEIL LO2]. pose proof CEIL as CEILn. idtac. unfold POP_STACK in LO2.
    (nelimp HRc 5%nat; intros RC1 RC2 RC3 RC4 RC5). (nelimp RB_facts 3%nat; intros RB1 RB2 RB3). destruct HRBd as [RB4 RB5]. (nelimp HS 3%nat; intros HS1 HS2 HS3). unfold KHIGHMEM_BEG, AIMG_HI in RB1, RC1, HS1. olin_all.
    destruct Hq as [Hq1 Hq2]. (nelimp Ham 4%nat; intros A1 A2 A3 A4). destruct Hnf as [N1 N2]. (nelimp Hfam 3%nat; intros F1 F2 F3).
    pose proof RC2 as RC2n. idtac. pose proof RB2 as RB2n. idtac. pose proof HS2 as HS2n. idtac.
    pose proof (csize_pos c ltac:(lia)) as CP. pose proof (csize_max c ltac:(lia)) as CL.
    assert (CS32 : 32 <= csize c). { destruct (Z_le_gt_dec c 16); [rewrite csize_small by lia; lia|]. cases_17_30 c; vm_compute; discriminate. }
    pose proof (t_range st WF) as TR. sepM. olin TR. pose proof (ctx_range st WF) as CR. sepM. olin CR. unfold KHIGHMEM_BEG, AIMG_HI in TR, CR. sepM. sepM. olin_all.
    assert (E64 : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (unfold wz; apply unsigned_lit; (lia_on RSP LO2 CEILn RB1 HS1 CP)).
    apply lscps_assume. intros NWX HOK HBINV.
    (* [comment removed for export] *)
    eapply lscps_evt_then.
    { eapply pop_A; [exact MI| exact ST| exact CEIL| lia| exact AC32| exact RIb| exact RC1| exact RC2| exact Hc| lia| lia| exact A3| exact HS1| exact HS2]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 18%nat; intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 m1 -> MU1 WM1 MI1 ST1 FR1 RIb1).
    fold total. fold RB.
    pose proof RIa as RIa1. eapply (rw_cells_transport bsegs _ m m1) in RIa1; [| exact MU1| exact WM1| cbn; (lia_on HRc HRBd CEILn RC5 RB1 HS1 RC2n CP TR CR)].
    pose proof RI24 as RI241. eapply (rw_cells_transport bsegs _ m m1) in RI241; [| exact MU1| exact WM1| cbn; (lia_on HRc HRBd CEILn RC5 RB1 HS1 RC2n CP TR CR)].
    pose proof TST as TST1. eapply (rw_cells_transport bsegs _ m m1) in TST1; [| exact MU1| exact WM1| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on HRc HRBd Hc CEILn RC3 RC4 RC5 RB1 RB4 RB5 HS1 RC2n HS2n CP TR CR)].
    pose proof SA as SA1. eapply (rw_cells_transport bsegs _ m m1) in SA1; [| exact MU1| exact WM1| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on Hstt HRc HRBd Hc CEILn RC3 RC4 RC5 RB1 RB4 RB5 HS1 RC2n HS2n CP TR CR)].
    pose proof AC40 as AC401. eapply (ro_cells_transport bsegs _ m m1) in AC401; [| exact MU1| cbn; (lia_on CEILn RB1 HS1 CP)].
    pose proof AC56 as AC561. eapply (ro_cells_transport bsegs _ m m1) in AC561; [| exact MU1| cbn; (lia_on CEILn RB1 HS1 CP)].
    pose proof VFA as VFA1. eapply (stk_transport_disjoint bsegs _ m m1) in VFA1; [| exact MU1| exact WM1| cbn; unfold KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; (lia_on HRc HS HRBd CEILn RC5 RB1 F3 RC2n CP TR CR)].
    assert (HC1 : mmap_consts m1) by (eapply mmap_consts_high; [exact MU1| repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on CEILn RB1 HS1 CP)| exact HC]).
    assert (IC1 : icpt_cells m1) by (eapply icpt_cells_high'; [exact MU1| repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on CEILn RB1 HS1 CP)| exact IC]).
    assert (PC1 : poison_cells m1) by (eapply poison_cells_high'; [exact MU1| repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on CEILn RB1 HS1 CP)| exact PC]).
    pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
    assert (LC1 : leafc st m1).
    { eapply (leafc_munch st _ _ _ MU1 WM1); [| exact LC]. intros lo' hi' a b Hin Hab. cbn in Hin, Hab.
      destruct Hin as [E|[]]; injection E; intros; subst.
      destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on HS CEIL RB1 HRc HRBd Hc RC3 RC4 RC5 RB4 RB5 RC2n HS2n CP TR CR CT). }
    replace (wz A_RAR_MAP) with (wz RTW_p_map.A_RAR_MAP) in * by reflexivity.
    assert (NVB : forall mp, alloc <= mp <= alloc + csize c + 524288 -> 0 <= (mp - alloc) / csize c <= 16385).
    { intros mp Hmp. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|].
      assert (32 * 16384 <= csize c * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). (lia_on HRc HRBd RC5 RB1 HS1 A1 CP Hmp H). }
    assert (FAM0 : forall k, 0 <= k <= 16393 -> fam < 4 * k -> fam = 0).
    { intros k Hk LTF. clear -Hk LTF F1 F2. Z.div_mod_to_equations. lia. }
    assert (SHFA : forall x, SH (RB + 3758096384 + 0) <= x < SH (RB + 3758096384 + 0) + 32768 ->
                   (SH RB <= x < SH (RB + 2^32)) /\ x < 17594333495296).
    { intros x Hx. unfold SH, SHADOW_OFFSET in Hx |- *. clear -Hx RB1 RB2n RB3. Z.div_mod_to_equations. lia. }
    assert (SHM : SH (RB + mapped) + 32768 = SH (RB + mapped + 262144)).
    { unfold SH, SHADOW_OFFSET. clear -RB3 A2. Z.div_mod_to_equations. lia. }
    assert (SHK : forall a, 0 <= a -> a + 262144 <= 2^47 -> SH a + 32768 <= 17594333495296).
    { intros a Ha1 Ha2. unfold SH, SHADOW_OFFSET. clear -Ha1 Ha2. Z.div_mod_to_equations. lia. }
    assert (SHle : forall a b, a <= b -> SH a <= SH b) by (intros a b Hab; unfold SH; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
    destruct um.
    - (* [comment removed for export] *)
      assert (LT : mapped < total) by (symmetry in EUM; apply Z.ltb_lt in EUM; exact EUM).
      rewrite <- EUM. cbv iota. cbv iota in EFM, HR, KX1, KX, K1. assert (Hfm0 : 0 <= (if fm then LUMP else 0)) by (destruct fm; unfold LUMP; lia).
      destruct (Z.eq_dec mapped KFREEARRAY_OFF) as [EXH|NEXH].
      + (* [comment removed for export] *)
        destruct exhb; subst exh; cbv iota in RIb1.
        * eapply lscps_evt_then.
          { eapply (pop_exh1 sp gp tp) with (lo := lo);
              [exact MI1| exact ST1| exact CEIL| lia| exact FR1| exact AC401| exact RIb1| exact RC1| exact RC2| exact Hc| lia| exact Hq2| lia| exact LT| exact EXH| exact RB1| exact RB2]. }
          cbv beta. intros ms2 nelH_; (nelim nelH_ 9%nat; intros y11 y12 y13 m2 -> MU2 WM2 MI2 ST2).
          apply (KX1 eq_refl eq_refl EXH); [exact MI2| eapply munch_trans; [exact MU1| exact MU2]| eapply wmono_trans; [exact WM1| exact WM2]| exact ST2].
        * eapply lscps_evt_then.
          { eapply (pop_X (wz (bv_unsigned sp + -64)) gp tp); [exact MI1| exact AC401| exact RIb1| exact RC1| exact RC2| exact Hc| lia| exact Hq2| lia| exact LT| exact EXH]. }
          cbv beta. intros ms2 ->.
          apply (KX eq_refl eq_refl EXH); [exact MI1| exact MU1| exact WM1| exact ST1| exact FR1| exact RIa1| exact RI241| exact RIb1| exact TST1| exact SA1].
      + (* [comment removed for export] *)
        assert (NEX : mapped + 262144 <= KFREEARRAY_OFF) by (unfold KFREEARRAY_OFF in *; clear -A2 A3 NEXH A1; Z.div_mod_to_equations; lia).
        assert (U1 : KHIGHMEM_BEG <= U /\ U + 262144 <= RB + KFREEARRAY_OFF /\ U mod 32768 = 0).
        { subst U. split; [lia|]. split; [lia|]. clear -RB3 A2. Z.div_mod_to_equations. lia. }
        (nelim U1 3%nat; intros U1 U2 U3). unfold KHIGHMEM_BEG, AIMG_HI in U1. olin_all. unfold KFREEARRAY_OFF in U2.
        assert (SHFB : forall x, SH (RB + 3758096384 + 0) <= x -> SH (RB + mapped + 262144) <= x).
        { intros x Hx. unfold SH, SHADOW_OFFSET in Hx |- *. unfold KFREEARRAY_OFF in NEX. clear -Hx NEX. Z.div_mod_to_equations. lia. }
        eapply lscps_evt_then.
        { eapply (pop_B_map (wz 0x370cc) (wz (bv_unsigned sp + -64)) gp tp) with (S := S);
            [exact MI1| exact AC401| exact AC561| exact RIb1| exact RC1| exact RC2| exact Hc| lia| exact Hq2| lia| exact LT| exact NEX| exact RB1| exact RB2]. }
        cbv beta. intros ms2 (y15 & ->). fold U.
        eapply (map_tol_spec (wz 0x37238) (wz (bv_unsigned sp + -64))) with (lo := lo) (spin := spin);
          [exact HC1| exact MI1| rewrite E64; exact ST1| rewrite E64; split; [exact CEIL| unfold MAPTOL_STACK; lia]
          | (lia_on Ham RC5 RB1 RB3 HS1 A1 A2 CP CL U1 U3)| clear -U3; Z.div_mod_to_equations; lia| unfold AIMG_HI; lia| lia| exact SITEU| unfold LUMP in *; (lia_on HRc HRBd Ham HR RC5 RB1 HS1 A1 CP Hfm0 U1)| |].
        * (* [comment removed for export] *) exact I.
        * (* [comment removed for export] *)
          intros y5 y6 y7 y11 y12 y13 y14 y15' y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2 ZN. rewrite E64 in MU2, ST2.
          cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 225848)) with (Z_to_bv 64 225848 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          assert (SHU : SH U mod 4096 = 0 /\ 2147450880 <= SH U /\ SH U + 32768 <= 17594333495296 /\ SH (U + 262144) = SH U + 32768).
          { unfold SH, SHADOW_OFFSET. clear - U1 U2 U3 RB2n. Z.div_mod_to_equations. lia. }
          (nelim SHU 4%nat; intros SH1 SH2 SH3 SH4).
          assert (SHU' : SH (RB + mapped) mod 4096 = 0 /\ 2147450880 <= SH (RB + mapped) /\ SH (RB + mapped) + 32768 <= 17594333495296) by exact (conj SH1 (conj SH2 SH3)). (nelim SHU' 3%nat; intros SH1' SH2' SH3').
          eapply (lscps_open bsegs _ _ _ G (R - 262144) (SH U) (SH U + 32768)).
          { unfold win_ok. cbn [fst snd]. clear - SH1 SH2 SH3. Z.div_mod_to_equations. lia. }
          { replace (4096 * ((SH U + 32768 - SH U) / 4096)) with 32768 by (replace (SH U + 32768 - SH U) with 32768 by lia; reflexivity). unfold LUMP in *. (lia_on HRc HRBd Ham HR RC5 RB1 HS1 A1 CP Hfm0 U1 SH2 SH2'). }
          intros mv' Emv ZFN FRZ. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS msw] in Emv |- *.
          replace (4096 * ((SH U + 32768 - SH U) / 4096)) with 32768 by (replace (SH U + 32768 - SH U) with 32768 by lia; reflexivity).
          assert (VNN : forall x : word, SH U <= bv_unsigned x < SH U + 32768 -> mv' x <> None).
          { intros x Hx.
            assert (HxR : SH RB <= bv_unsigned x < SH (RB + 2^32)) by (unfold SH, SHADOW_OFFSET in *; clear -Hx U1 U2 RB1 A1; subst U RB; Z.div_mod_to_equations; lia).
            pose proof (LZS x HxR) as Hz. destruct (in_winb G x) eqn:EW.
            - assert (V0 : m x <> None) by (apply (HVIS x HxR Hz EW)).
              assert (V1 : m1 x <> None) by (rewrite (MU1 x); [exact V0|]; cbn; (lia_on Ham CEILn RB1 HS1 CP U1 SH2 SH3 SH2' Hx)).
              assert (V2 : m2 x <> None) by (rewrite (MU2 x); [exact V1|]; cbn; (lia_on HRc HRBd Hc Ham CEILn RC5 RB1 HS1 A1 CP U1 SH2 SH3 SH2' Hx)).
              rewrite Emv, (open_mem_mono _ _ _ _ _ V2). exact V2.
            - rewrite (FRZ x Hx); [discriminate| | exact EW]. rewrite (lzf_commit_out mo U 262144 HOK); [exact Hz| unfold RT_artF.CEIL, KHIGHMEM_BEG, AIMG_HI; (lia_on HRc HRBd Ham RC5 RB1 HS1 RC2n CP TR CR U1 U2 SH2 SH2')|].
              unfold in_range. apply andb_false_iff. left. apply Z.leb_gt. (lia_on HRc HRBd Hc Ham RC5 RB1 HS1 A1 CP U1 SH2 SH3 SH2' Hx). }
          assert (STSH : stk bsegs mv' (SH U) (SH U + 32768)) by (apply stk_of_some; [lia| lia| exact VNN]).
          (nelim (stk_carve bsegs mv' (SH U) (SH U + 32768) (Z.to_nat (262144 / 8)) STSH ltac:((lia_on Ham RC5 RB1 RB3 HS1 A1 A2 CP CL U1 U3 SH2 SH2'))) 3%nat; intros _ shj SHJ).
          replace (SH U + 32768 - Z.of_nat (Z.to_nat (262144 / 8))) with (SH U) in SHJ by (lia_on Ham RC5 RB1 RB3 HS1 A1 A2 CP CL U1 U3 SH2 SH2').
          (* [comment removed for export] *)
          pose proof (rw_cells_open bsegs _ (SH U) (SH U + 32768) m2 _ _ ZFN ZN) as ZNv. rewrite <- Emv in ZNv.
          pose proof (stk_open bsegs _ (SH U) (SH U + 32768) m2 _ _ ZFN ST2) as STv. rewrite <- Emv in STv.
          pose proof (mem_inv_open bsegs _ (SH U) (SH U + 32768) m2 ZFN MI2) as MIv. rewrite <- Emv in MIv.
          assert (MUv : munch [(lo, bv_unsigned sp); (U, U + 262144); (SH U, SH U + 32768)] m mv').
          { rewrite Emv. apply munch_open_r; [| cbn; intros; lia].
            eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; subfp. }
          assert (WMv : wmono bsegs m mv'). { rewrite Emv. apply wmono_open. eapply wmono_trans; [exact WM1| exact WM2]. }
          assert (HWv : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp); (U, U + 262144); (SH U, SH U + 32768)]).
          { repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on Ham CEILn RB1 HS1 CP U1 SH2 SH2'). }
          pose proof (icpt_cells_high' _ _ _ MUv HWv IC) as ICv. pose proof (poison_cells_high' _ _ _ MUv HWv PC) as PCv.
          pose proof (mmap_consts_high _ _ _ MUv HWv HC) as HCv.
          assert (LCv : leafc st mv').
          { eapply (leafc_munch st _ _ _ MUv WMv); [| exact LC]. intros lo' hi' a b Hin Hab. cbn in Hin, Hab.
            destruct Hin as [E|[E|[E|[]]]]; injection E; intros; subst;
            destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on CEIL RB1 SH2 HRBd Ham CR U2 OLx0 SH3). }
          assert (MU2v : munch [(lo, bv_unsigned sp + -64); (U, U + 262144); (SH U, SH U + 32768)] m1 mv').
          { rewrite Emv. apply munch_open_r; [eapply munch_weaken; [| exact MU2]; subfp| cbn; intros; lia]. }
          assert (WM2v : wmono bsegs m1 mv') by (rewrite Emv; apply wmono_open; exact WM2).
          pose proof FR1 as FRv. eapply (rw_cells_transport bsegs _ m1 mv') in FRv; [| exact MU2v| exact WM2v| cbn; (lia_on HRc HRBd Ham LO2 CEILn RC5 RB1 HS1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof RIa as RIav. eapply (rw_cells_transport bsegs _ m mv') in RIav; [| exact MUv| exact WMv| cbn; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof RI24 as RI24v. eapply (rw_cells_transport bsegs _ m mv') in RI24v; [| exact MUv| exact WMv| cbn; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof RIb as RIbv. eapply (rw_cells_transport bsegs _ m mv') in RIbv; [| exact MUv| exact WMv| cbn; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          pose proof TST as TSTv. eapply (rw_cells_transport bsegs _ m mv') in TSTv; [| exact MUv| exact WMv| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on HRBd Ham CEILn TR OLx U2 SH2 SH3)].
          pose proof SA as SAv. eapply (rw_cells_transport bsegs _ m mv') in SAv; [| exact MUv| exact WMv| cbn; unfold KHIGHMEM_BEG, AIMG_HI in TR; (lia_on Hstt HRBd Ham CEILn TR OLx U2 SH2 SH3)].
          pose proof AC56 as AC56v. eapply (ro_cells_transport bsegs _ m mv') in AC56v; [| exact MUv| cbn; (lia_on Ham CEILn RB1 HS1 CP U1 SH2 SH2')].
          pose proof VFA as VFAv. eapply (stk_transport_disjoint bsegs _ m mv') in VFAv; [| exact MUv| exact WMv| cbn; unfold KFREEARRAY_OFF in *; (lia_on HRc HRBd Ham CEILn RC5 RB1 HS1 F3 RC2n CP TR CR U1 U2 SH2 SH3 SH2')].
          clear ZN ST2 MI2 VNN STSH.
          lazymatch goal with |- LSCPS _ _ (msw (MS ?RR ?FF ?p ?cc ?v ?mm ?ro) ?mv) _ _ => change (msw (MS RR FF p cc v mm ro) mv) with (MS RR FF p cc v mv ro) end.
          subst exh.
          eapply lscps_evt_then.
          { eapply (pop_D PS sp gp tp) with (st := st) (lo := lo) (msz := 262144) (stt := stt);
              [exact ICv| exact PCv| exact LCv| exact WF| exact TP| exact MIv| exact STv| exact CEIL| lia| exact RIbv| exact RC1| exact RC2| exact RC3| exact RC4| exact RC5
              | exact TSTv| exact SAv| exact Hstt| exact RB1| exact RB2| exact RB3| exact RB4| exact RB5| (lia_on HRc HRBd Ham RC5 RB1 HS1 A1 CP U1 SH2 SH2')| clear -A2; Z.div_mod_to_equations; lia| reflexivity| exact NEX| exact SHJ]. }
          cbv beta. intros ms3 nelH_; (nelim nelH_ 27%nat; intros w1 w5 w6 w7 w11 w12 w14 w15 w16 w17 w28 w29 w30 w31 m3 tj1' tj2' sa' -> MU3 WM3 MI3 ST3 RIb3 SHP3 TST3 SA3).
          cbv beta delta [wz] in *|-. change (262144 / 8) with 32768 in *.
          pose proof FRv as FR3. eapply (rw_cells_transport bsegs _ mv' m3) in FR3; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc LO2 CEILn TR SH3')].
          pose proof RIav as RIa3. eapply (rw_cells_transport bsegs _ mv' m3) in RIa3; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 SH2 SH2' SH3')].
          pose proof RI24v as RI243. eapply (rw_cells_transport bsegs _ mv' m3) in RI243; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc HRBd Ham CEILn RC5 RB1 HS1 A1 RC2n CP TR CR U1 SH2 SH2' SH3')].
          pose proof AC56v as AC563. eapply (ro_cells_transport bsegs _ mv' m3) in AC563; [| exact MU3| cbn; (lia_on Hstt Ham CEILn RC1 RC5 RB1 HS1 A1 CP OLx OLx2 U1 SH2 SH2')].
          pose proof VFAv as VFA3. eapply (stk_transport_disjoint bsegs _ mv' m3) in VFA3; [| exact MU3| exact WM3| cbn; unfold KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *; (lia_on Hstt HRc HS HRBd Ham CEILn RC5 RB1 F3 RC2n CP U1 SH2 SH2' SH3')].
          pose proof ZNv as STU3. apply (stk_of_rw_cellsZ _ _ _ 262144) in STU3; [| cbn; (lia_on HRc HRBd Ham RC5 RB1 HS1 A1 CP U1 SH2 SH2')]. eapply (stk_transport_disjoint bsegs _ mv' m3) in STU3; [| exact MU3| exact WM3| cbn; (lia_on Hstt HRc HRBd Hc Ham CEILn RC5 RB1 HS1 A1 RC2n CP U1 U2 SH2 SH2' SH3')].
          assert (MUt : munch (prf_W lo (bv_unsigned sp) Rc (st_t st) stt U true) m m3).
          { unfold prf_W. cbn [app]. eapply munch_trans; [eapply munch_weaken; [| exact MUv]| eapply munch_weaken; [| exact MU3]]; subfp. }
          assert (WMt : wmono bsegs m m3) by (eapply wmono_trans; [exact WMv| exact WM3]).
          pose proof (t_range st WF) as [TRo _]. (nelimp (oclr_lin _ _ TRo ltac:(lia)) 3%nat; intros TRa _ TRi). unfold AIMG_LO, AIMG_HI in TRi. clear TRo.
          assert (HWt : Forall outI (prf_W lo (bv_unsigned sp) Rc (st_t st) stt U true)).   (* [comment removed for export] *)
          { unfold prf_W, outI. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; (lia_on HS Ham CEILn RB1 CP U1 SH2 SH2' HRc RC1 RC5 A1 OLx2 Hstt). }
          assert (LC3 : leafc st m3).
          { eapply (leafc_munch st _ _ _ MUt WMt); [| exact LC]. intros lo' hi' a b Hin Hab. unfold prf_W in Hin. cbn in Hin, Hab.
            sepM. sepM. destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E; intros; subst;
            destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on CEIL RB1 SH2 HRc HRBd Ham CR CT OLx2 U2 OLx0 SH3). }
          eapply (pop_P1 PS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m3 (mm_commit (Z_to_bv 64 U) (Z_to_bv 64 262144) mo) ((SH U, SH U + 32768) :: G) (R - 262144 - 32768) st Rc RB (csize c) alloc (mapped + 262144) nf fam lo tj1' tj2' mtx sem jr je js) with (spin := spin);
            [exact (mmap_consts_out _ _ _ MUt HWt HC)| exact (icpt_cells_out _ _ _ MUt HWt IC)| exact (poison_cells_out _ _ _ MUt HWt PC)| exact LC3| exact WF| exact TP| exact MI3| exact ST3
            | split; [exact CEIL| unfold POP_STACK; lia]| exact FR3| exact RIa3| exact RI243| exact RIb3| exact AC563| exact TST3| exact VFA3
            | unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| lia| unfold KFREEARRAY_OFF in *; lia| lia| lia| | | | | |].
          -- (* [comment removed for export] *) intros LTF x Hx. unfold KFREEARRAY_OFF in Hx. pose proof (NVB (mapped + 262144) ltac:(lia)) as NB.
             assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK). pose proof (SHFB _ (proj1 Hx)) as HxU.
             unfold wz. rewrite (lzf_commit_out mo U 262144 HOK); [apply LZS; exact HxR| unfold RT_artF.CEIL, KHIGHMEM_BEG, AIMG_HI; (lia_on HRc HRBd Ham RC5 RB1 HS1 RC2n CP TR CR U1 U2 SH2 SH2')|].
             unfold in_range. apply andb_false_iff. left. apply Z.leb_gt. (lia_on HRc HRBd Hc Ham RC5 RB1 HS1 A1 CP U1 SH2 SH2' HxK).
          -- (* [comment removed for export] *) intros LTF x Hx Hz EW. unfold KFREEARRAY_OFF in Hx. pose proof (NVB (mapped + 262144) ltac:(lia)) as NB.
             assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK). pose proof (SHFB _ (proj1 Hx)) as HxU.
             assert (EW' : in_winb G x = true).
             { unfold in_winb in EW |- *. cbn [existsb] in EW. apply orb_true_iff in EW. destruct EW as [EW|EW]; [| exact EW].
               exfalso. unfold in_range in EW. apply andb_true_iff in EW. destruct EW as [EW1 EW2]. apply Z.leb_le in EW1. apply Z.ltb_lt in EW2.
               cbn [fst snd] in EW1, EW2. subst U. lia. }
             assert (V0 : m x <> None) by (apply (HVIS x HxR (LZS x HxR) EW')).
             rewrite (MUt x); [exact V0|]. unfold prf_W. cbn. subst U. (lia_on Hstt HRc HRBd Hc Ham CEILn RC5 RB1 HS1 A1 CP OLx U1 SH2 SH4 SH2' HxK HxU).
          -- (* [comment removed for export] *) intros LTF. pose proof (NVB (mapped + 262144) ltac:(lia)) as NB. assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). apply SITEF; [lia| right; reflexivity].
          -- (* [comment removed for export] *) intros LTF. assert (EF : fm = true) by (rewrite EFM; apply Z.ltb_lt; exact LTF). rewrite EF in HR. cbv iota in HR. unfold LUMP in *. lia.
          -- (* [comment removed for export] *) exact I.
          -- (* [comment removed for export] *) intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 tj1'' tj2'' MI4 MU4 WM4 ST4 RIa4 RI244 RIb4 TST4 VFA4 FILL4 SHF4.
             rewrite <- !EFM in *. replace (R - 262144 - 32768) with (R - LUMP) by (unfold LUMP; lia).
             assert (NB : 0 <= (mapped + 262144 - alloc) / csize c <= 16385) by (apply NVB; lia).
             assert (SK : SH (RB + 3758096384 + fam) + 32768 <= 17594333495296) by (apply SHK; (lia_on Ham RC1 RB1 HS1 F1 CP U1 SH2 SH2' HRc HRBd RC5 F3 RC2n TR CR)).
             assert (SLE : SH (RB + mapped + 262144) <= SH (RB + 3758096384 + fam)) by (apply SHle; unfold KFREEARRAY_OFF in NEX; (lia_on HRc HRBd Ham RC5 RB1 HS1 F1 CP NEX U1 SH2 SH2')).
             assert (SHMU : SH U + 32768 = SH (RB + mapped + 262144)) by exact SHM.
             unfold p1_W in MU4. unfold pop_W, prf_W, KFREEARRAY_OFF. destruct fm; cbn [app] in MU4 |- *.
             all: apply (K1 (fun _ => NEX)) with (tj1' := tj1'') (tj2' := tj2'') (sa' := sa');
               [exact MI4| | eapply wmono_trans; [exact WMt| exact WM4]| exact ST4| exact RIa4| exact RI244| exact RIb4| exact TST4| | exact VFA4| exact FILL4| | exact SHF4].
             all: try (eapply munch_trans; [eapply munch_weaken; [| exact MUt]| eapply munch_weaken; [| exact MU4]]; unfold prf_W; cbn [app]; subfp).
             all: try (eapply (rw_cells_transport bsegs _ m3 m4); [exact SA3| exact MU4| exact WM4| cbn; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *; (cut_on [Hstt HRc HRBd EFM CEILn N1 F1 F3 TR OLx SHM SH2' NB SK SLE] (repeat match goal with |- context [?a / csize c] => let Q := fresh "Qd" in set (Q := a / csize c) in *; clearbody Q end; (lia_on Hstt HRc HRBd EFM CEILn N1 F1 TR OLx SHM SH2' NB SK SLE)))]).
             all: split.
             all: try (eapply (stk_transport_disjoint bsegs _ m3 m4); [exact STU3| exact MU4| exact WM4| cbn; unfold KFREEARRAY_OFF in *; (lia_on HRc HRBd Ham CEILn RB1 N1 F1 NEX SK)]).
             all: eapply (rw_cells_transport bsegs _ m3 m4); [exact SHP3| exact MU4| exact WM4| cbn [disjoint_from cells_size Cells.csize app]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold KFREEARRAY_OFF in *; (lia_on HRc CEILn RB1 N1 F1 OLx SH2 SK SLE SHMU)].
    - (* [comment removed for export] *)
      assert (GE : total <= mapped) by (symmetry in EUM; apply Z.ltb_ge in EUM; exact EUM).
      rewrite <- EUM. cbv iota. cbv iota in EFM, HR, KX1, KX, K1.
      try replace (mapped + 0) with mapped in EFM by lia. try replace (mapped + 0) with mapped in K1 by lia.
      try replace (R - 0) with R in K1 by lia. try replace (0 + (if fm then LUMP else 0)) with (if fm then LUMP else 0) in HR by lia.
      try replace (mapped + 0) with mapped by lia.
      subst exh.
      eapply (pop_P1 PS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 mo G R st Rc RB (csize c) alloc mapped nf fam lo tj1 tj2 mtx sem jr je js) with (spin := spin);
        [exact HC1| exact IC1| exact PC1| exact LC1| exact WF| exact TP| exact MI1| exact ST1
        | split; [exact CEIL| unfold POP_STACK; lia]| exact FR1| exact RIa1| exact RI241| exact RIb1| exact AC561| exact TST1| exact VFA1
        | unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| unfold KHIGHMEM_BEG, AIMG_HI; repeat split; assumption || lia| lia| unfold KFREEARRAY_OFF in *; lia| lia| lia| | | | | |].
      + (* [comment removed for export] *) intros LTF x Hx. unfold KFREEARRAY_OFF in Hx. pose proof (NVB mapped ltac:(lia)) as NB.
        assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK). apply LZS. exact HxR.
      + (* [comment removed for export] *) intros LTF x Hx Hz EW. unfold KFREEARRAY_OFF in Hx. pose proof (NVB mapped ltac:(lia)) as NB.
        assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). rewrite F0 in Hx. destruct (SHFA _ Hx) as (HxR & HxK).
        rewrite (MU1 x); [exact (HVIS x HxR Hz EW)|]. cbn. lia.
      + (* [comment removed for export] *) intros LTF. pose proof (NVB mapped ltac:(lia)) as NB. assert (F0 : fam = 0) by (eapply FAM0; [| exact LTF]; cycle 1; clear -NB N1; lia). apply SITEF; [lia| left; reflexivity].
      + (* [comment removed for export] *) intros LTF. assert (EF : fm = true) by (rewrite EFM; apply Z.ltb_lt; exact LTF). rewrite EF in HR. cbv iota in HR. unfold LUMP in *. lia.
      + (* [comment removed for export] *) exact I.
      + (* [comment removed for export] *) intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 tj1'' tj2'' MI4 MU4 WM4 ST4 RIa4 RI244 RIb4 TST4 VFA4 FILL4 SHF4.
        rewrite <- !EFM in *. rewrite ?Z.sub_0_r.
        assert (NB : 0 <= (mapped - alloc) / csize c <= 16385) by (apply NVB; lia).
        assert (SK : SH (RB + 3758096384 + fam) + 32768 <= 17594333495296) by (apply SHK; (lia_on Ham RC1 RB1 HS1 F1 CP HRc HRBd RC5 F3 RC2n TR CR)).
        unfold p1_W in MU4. unfold pop_W, prf_W, KFREEARRAY_OFF. destruct fm; cbn [app] in MU4 |- *.
        all: apply (K1 ltac:(discriminate)) with (tj1' := tj1'') (tj2' := tj2'') (sa' := sa);
          [exact MI4| | eapply wmono_trans; [exact WM1| exact WM4]| exact ST4| exact RIa4| exact RI244| exact RIb4| exact TST4| | exact VFA4| exact FILL4| exact I| exact SHF4].
        all: try (eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU4]]; subfp).
        all: sepM. all: (pose proof (t_range st WF) as TRq; olin TRq).   (* [comment removed for export] *)
        all: (pose proof (rt_SH_mono 0 (RB + 3758096384 + fam) ltac:((lia_on Ham RC1 RB1 HS1 F1 CP))) as SKlo; change (SH 0) with 2147450880 in SKlo).   (* [comment removed for export] *)
        all: eapply (rw_cells_transport bsegs _ m1 m4); [exact SA1| exact MU4| exact WM4| cbn; unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *; (cut_on [Hstt HRc HRBd EFM CEILn N1 N2 F3 NB SK TRq SKlo] (repeat match goal with |- context [?a / csize c] => let Q := fresh "Qd" in set (Q := a / csize c) in *; clearbody Q end; (cut_on [Hstt HRc HRBd EFM CEILn N1 N2 NB SK TRq SKlo F3] (cut_on [Hstt HRc HRBd EFM CEILn N1 N2 NB SK TRq SKlo F3] blia))))].
  Qed.
End POPW.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].
End RTW_p_pop2.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_cd_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Module RTW_p_refillA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_map OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_loops OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_efa OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1 RTW_p_pop2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_gfa OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_refillw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_cd_main.RTW_p_absf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma refill_cells : forall st m cls, RTREP st m -> RTWF st -> 1 <= cls <= 30 -> cch st cls = [] ->
  let r := rg st cls in
  exists (jr je js : list byte) (tj1 tj2 sa : word),
    ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 (st_spacebeg st))]
    /\ ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)]
    /\ ro_cells bsegs m 0xa6388 [C8 (Z_to_bv 64 (ris st))]
    /\ ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m (rinfo st cls) [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 (num_freed st cls))]
    /\ rw_cells bsegs m (rinfo st cls + 24) [C8 (Z_to_bv 64 (r_mapped_fa r))]
    /\ rw_cells bsegs m (rinfo st cls + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_mapped r)); C8 (Z_to_bv 64 0);
                                            CB 4 jr; C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js]
    /\ rw_cells bsegs m (st_t st + 2872) [C8 tj1; C8 tj2]
    /\ rw_cells bsegs m (st_t st + 2768 + 24) [C8 sa]
    /\ vis m (fabeg st cls) (fabeg st cls + r_mapped_fa r)
    /\ (forall i, 0 <= i < num_freed st cls -> rw_cells bsegs m (fabeg st cls + 4 * i) [W4 (nthz (r_fa r) i 0)])
    /\ rw_cells bsegs m (pcaddr st cls) [C4 (wz 0); C4 (Z_to_bv 64 (pc_max_count st cls)); C8 (wz (pc_class_size st cls))].
Proof.
  intros st m cls HR WF Hc HC0. cbv zeta.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (nelimp (proj1 (rr_alloc st m HR)) 4%nat; intros j1 j2 j3 AL).
  (nelim (proj2 (rr_rinfo st m HR) cls Hcls) 4%nat; intros jr je js RC).
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TR. olin_all.
  pose proof (proj1 (rr_thread st m HR)) as VT.
  destruct (vis_c8 m _ _ (st_t st + 2872) VT ltac:(lia) ltac:(lia)) as [tj1 T1].
  destruct (vis_c8 m _ _ (st_t st + 2880) VT ltac:(lia) ltac:(lia)) as [tj2 T2].
  destruct (vis_c8 m _ _ (st_t st + 2768 + 24) VT ltac:(lia) ltac:(lia)) as [sa SA].
  (nelim (rr_regions st m HR cls Hcls) 6%nat; intros V1 V2 V3 V4 EN TL).
  destruct (rr_cache st m HR cls Hcls) as [PC _]. rewrite HC0 in PC. change (zlen (@nil Z)) with 0 in PC.
  exists jr, je, js, tj1, tj2, sa.
  unfold A_ALLOC in AL.
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1] [W8 (st_spacebeg st)]
             [W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st)] [W4 (2^32 - 1)]
             [CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2] [W8 (st_spacebeg st + KSPACESIZE)]
             [W1 0; CB 7 j3]). exact AL. }
  split. { apply rw_cells_cells. apply (rw_cells_mid m 0xa6358 [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE)] [W1 0]
             [CB 7 j3]). exact AL. }
  unfold rinfo_cells in RC.
  split. { apply (rw_cells_take m _ _ [W8 (r_mapped_fa (rg st cls)); W8 (r_allocated (rg st cls)); W8 0; W8 (r_mapped (rg st cls)); W8 0; CB 4 jr; W1 (if r_exhausted (rg st cls) then 1 else 0); CB 3 je; CB 56 js]). exact RC. }
  split. { apply (rw_cells_mid m _ [W8 0; W8 0; W8 (num_freed st cls)] [W8 (r_mapped_fa (rg st cls))] [W8 (r_allocated (rg st cls)); W8 0; W8 (r_mapped (rg st cls)); W8 0; CB 4 jr; W1 (if r_exhausted (rg st cls) then 1 else 0); CB 3 je; CB 56 js]). exact RC. }
  split. { apply (rw_cells_drop m _ [W8 0; W8 0; W8 (num_freed st cls); W8 (r_mapped_fa (rg st cls))]). exact RC. }
  split. { apply (proj2 (rw_cells_app m _ [C8 tj1] [C8 tj2])). split; [exact T1|]. replace (st_t st + 2872 + Z.of_nat (cells_size [C8 tj1])) with (st_t st + 2880) by (cbn; lia). exact T2. }
  split; [exact SA|]. split; [exact V3|]. split; [exact EN|]. exact PC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WPRE (lo sp P : Z) : list (Z * Z) := [(lo, sp); (P + 80, P + 2560)].

Lemma refill_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (cls lo : Z),
  RTREP st m -> RTWF st -> 1 <= cls <= 30 -> cch st cls = [] ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  let P := acache st in let pc := pcaddr st cls in
  evt bsegs (fun ms1 => exists (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (j : list byte) (m1 : word -> option byte),
      ms1 = refill_call sp gp tp x5 x6 x7 pc (nrefill cls) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc (P + 2560) cls m1
      /\ munch (WPRE lo (bv_unsigned sp) P) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells bsegs m1 (bv_unsigned sp + -32) (refill_frame j s1 s0 ra)
      /\ (forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m1 (pcaddr st c) [W4 (zlen (cch st c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)])
      /\ (forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m1 (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz pc) (wz A_ALLOC) (wz cls) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AREFILL) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HR WF Hc HC0 MI ST CEIL LO. cbv zeta.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TR. olin_all. pose proof CEIL as CEILn. idtac.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct (rr_cache st m HR cls Hcls) as [PC _]. rewrite HC0 in PC. change (zlen (@nil Z)) with 0 in PC.
  assert (PCB : (4096 <= pcaddr st cls /\ (pcaddr st cls + 80 <= AIMG_LO \/ AIMG_HI <= pcaddr st cls)) /\ pcaddr st cls + 80 <= alloc_ceiling /\ pcaddr st cls = acache st + 80 * cls /\ acache st = st_t st + 208)
    by (unfold pcaddr, acache, T_ACACHE, KHIGHMEM_BEG, AIMG_LO, AIMG_HI; idtac; lia).
  (nelim PCB 4%nat; intros PB1 PB2 PB3 PB4).
  pose proof (cmaxcount_range cls ltac:(lia)) as [CMR _].
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (refill_pro ra sp gp tp) with (lo := lo) (mc := pc_max_count st cls); [exact MI| exact ST| exact CEIL| exact LO| exact PC| exact PB1| exact PB2|].
    unfold pc_max_count. destruct (st_cache_inited st && negb (cls =? 0)); lia. }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 9%nat; intros j m1 -> MU1 WM1 MI1 ST1 FR1 PC1).
  unfold pc_max_count. destruct (st_cache_inited st) eqn:INI.
  - (* [comment removed for export] *)
    cbn [andb negb]. rewrite (proj2 (Z.eqb_neq cls 0)) by lia. cbn [negb]. rewrite (proj2 (Z.eqb_neq (cmaxcount cls) 0)) by lia.
    eapply evt_cut. { eapply (refill_B ra sp gp tp) with (P := acache st); [exact MI1| exact PB3| unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI; blia| unfold acache, T_ACACHE; idtac; lia| exact Hc]. }
    cbv beta. intros ms2 ->. apply evt_done. nexists 12%nat. split; [reflexivity|].
    split. { eapply munch_weaken; [| exact MU1]. unfold WPRE, sub_fp. cbn. intros x Hx. tauto. }
    split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1|]. split.
    + intros c Hc'. destruct (rr_cache st m HR c Hc') as [H _]. unfold pc_max_count, pc_class_size in H. rewrite INI in H. cbn [andb] in H.
      replace (if negb (c =? 0) then cmaxcount c else 0) with (if c =? 0 then 0 else cmaxcount c) in H by (destruct (c =? 0); reflexivity).
      replace (if negb (c =? 0) then csize c else 0) with (if c =? 0 then 0 else csize c) in H by (destruct (c =? 0); reflexivity).
      eapply rw_cells_transport; [exact H| exact MU1| exact WM1|]. cbn. unfold pcaddr, acache, T_ACACHE. unfold KNUMCLASSES in Hc'. lia.
    + intros c i Hc' Hi. destruct (rr_cache st m HR c Hc') as [_ H]. specialize (H i Hi).
      pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. pose proof (cmaxcount_le16 c).
      eapply rw_cells_transport; [exact H| exact MU1| exact WM1|]. cbn. unfold pcaddr, acache, T_ACACHE. unfold KNUMCLASSES in Hc'. lia.
  - (* [comment removed for export] *)
    cbn [andb]. cbn [Z.eqb].
    assert (CELLS : forall c, 1 <= c <= 31 -> rw_cells bsegs m1 (acache st + 80 * c) [C4 (wz (zlen (cch st c))); CB 4 (le4 (wz 0)); CB 8 (le8 (wz 0))]).
    { intros c Hc'. destruct (rr_cache st m HR c ltac:(unfold KNUMCLASSES; lia)) as [H _]. unfold pc_max_count, pc_class_size in H. rewrite INI in H. cbn [andb] in H.
      eapply rw_cells_transport in H; [| exact MU1| exact WM1| cbn; unfold pcaddr, acache, T_ACACHE; lia].
      change (pcaddr st c) with (acache st + 80 * c) in H.
      eapply rw_cells_recast_p; [exact H| cbn; repeat split; reflexivity| reflexivity]. }
    eapply evt_cut.
    { eapply (refill_init ra sp gp tp) with (P := acache st) (cnt := fun c => wz (zlen (cch st c))) (j2 := fun _ => le4 (wz 0)) (j3 := fun _ => le8 (wz 0));
        [exact MI1| exact PB3| unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI; blia| unfold acache, T_ACACHE; idtac; lia| exact Hc| exact CELLS]. }
    cbv beta. intros ms2 nelH_; (nelim nelH_ 11%nat; intros x13 x15 x28 x29 x30 m2 -> MU2 WM2 MI2 CELLS2).
    assert (MU12 : munch (WPRE lo (bv_unsigned sp) (acache st)) m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold WPRE, sub_fp; cbn; intros x Hx; tauto. }
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
    eapply evt_cut. { eapply (refill_B ra sp gp tp) with (P := acache st); [exact MI2| exact PB3| unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI; blia| unfold acache, T_ACACHE; idtac; lia| exact Hc]. }
    cbv beta. intros ms3 ->. apply evt_done. nexists 12%nat. split; [reflexivity|].
    split; [exact MU12|]. split; [exact WM12|]. split; [exact MI2|].
    split. { eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. unfold acache, T_ACACHE. lia. }
    split. { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. unfold acache, T_ACACHE. lia. }
    split.
    + intros c Hc'. destruct (Z.eq_dec c 0) as [->|NZ].
      * cbn [Z.eqb]. destruct (rr_cache st m HR 0 Hc') as [H _]. unfold pc_max_count, pc_class_size in H. rewrite INI in H. cbn [andb] in H.
        eapply rw_cells_transport; [exact H| exact MU12| exact WM12|]. unfold WPRE. cbn. unfold pcaddr, acache, T_ACACHE. lia.
      * rewrite (proj2 (Z.eqb_neq c 0)) by lia. unfold KNUMCLASSES in Hc'. exact (CELLS2 c ltac:(lia)).
    + intros c i Hc' Hi. exfalso. rewrite (wb_uninit st (wf_base_ok st WF) INI c) in Hi. change (zlen (@nil Z)) with 0 in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fa_entry_small : forall st c i, RTWF st -> 1 <= c <= 30 -> 0 <= i < num_freed st c -> 0 <= nthz (r_fa (rg st c)) i 0 < 2^28.
Proof.
  intros st c i WF Hc Hi. assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (wf_class_ok st WF c HcK) as WC.
  set (k := nthz (r_fa (rg st c)) i 0).
  assert (IN : In k (r_fa (rg st c))).
  { unfold k, nthz. destruct (Z.ltb_spec0 i 0); [lia|]. apply nth_In. unfold num_freed, zlen in Hi. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c WC). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. left. exact IN. }
  (nelim CV 3%nat; intros j Hj Ek). pose proof (chunk_cptr_eq c j ltac:(lia)) as E16. rewrite <- Ek in E16.
  pose proof (wc_alloc_carved st c WC) as AC. pose proof (wc_alloc_mapped st c WC) as AM. pose proof (wc_mapped_max st c WC) as MM.
  pose proof (csize_pos c ltac:(lia)) as CP. unfold ncarved in Hj. unfold KFREEARRAY_OFF in MM.
  assert (j * csize c <= r_allocated (rg st c) - csize c).
  { rewrite AC. unfold ncarved. pose proof (Z.mul_div_le (r_allocated (rg st c)) (csize c) ltac:(lia)).
    assert (j * csize c + csize c <= r_allocated (rg st c) / csize c * csize c) by nia. nia. }
  nia.
Qed.

Lemma u32arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u32arr bsegs m A [].
Proof.
  intros m A H1 H2. split.
  - split; [exact H1|]. split; [cbn [u32s length Z.of_nat flat_map]; rewrite Z.add_0_r; exact H2|]. intros i Hi. cbn in Hi. exfalso. clear -Hi. lia.
  - split; [exact H1|]. split; [cbn [length Z.of_nat]; rewrite Z.mul_0_r, Z.add_0_r; exact H2|]. intros i Hi. exfalso. clear -Hi. cbn in Hi. lia.
Qed.

Lemma nthz_map_seq : forall (f : nat -> Z) k i d, 0 <= i < Z.of_nat k -> nthz (map f (seq 0 k)) i d = f (Z.to_nat i).
Proof.
  intros f k i d Hi. unfold nthz. destruct (Z.ltb_spec0 i 0); [lia|]. apply map_seq_nth. lia.
Qed.

(* [comment removed for export] *)
Lemma fill_vals_nth : forall alloc SZ (N t : nat), (t < N)%nat ->
  nth_error (fill_vals alloc SZ N) t = Some (Z_to_bv 64 ((alloc + Z.of_nat (N - 1 - t) * SZ) / 16)).
Proof.
  intros alloc SZ N. induction N as [|N IH]; intros t Ht; [lia|].
  rewrite fill_vals_S. destruct t as [|t].
  - cbn [nth_error]. replace (S N - 1 - 0)%nat with N by lia. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. replace (S N - 1 - S t)%nat with (N - 1 - t)%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma chunk_cptr_small : forall c j, 1 <= c <= 30 -> 0 <= j -> j * csize c + csize c <= 3758096384 -> 0 <= chunk_cptr c j < 2^28.
Proof.
  intros c j Hc Hj Hb. pose proof (chunk_cptr_eq c j ltac:(lia)) as E. pose proof (csize_pos c ltac:(lia)). nia.
Qed.

Ltac dj := cbn; repeat match goal with |- _ /\ _ => split end; try exact I; first [left; lia | right; lia | lia].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition WREST (lo sp pc t Rc U usz FA nf : Z) : list (Z * Z) :=
  [(lo, sp); (pc, pc + 80); (t + 2768, t + 2896); (Rc, Rc + 128); (U, U + usz); (SH U, SH U + 32768);
   (FA + 4 * nf, FA + 536870912); (SH FA, SH FA + 67108864)].
(* [comment removed for export] *)
Definition WTOT (lo sp P pc t Rc U usz FA nf : Z) : list (Z * Z) := WPRE lo sp P ++ WREST lo sp pc t Rc U usz FA nf.

Definition hideP (P : Prop) : Prop := P.

(* [comment removed for export] *)
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; repeat match goal with H' : ~ _ |- _ => clear H' end; first [exact Cq| lia] end ].

(* [comment removed for export] *)
Definition pch_at (st : rtstate) (cls : Z) (m' : word -> option byte) (k : Z) : Prop :=
  forall c, 0 <= c < KNUMCLASSES ->
    rw_cells bsegs m' (pcaddr st c) [W4 (if c =? cls then k else zlen (cch st c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)].
Definition pco_at (st : rtstate) (m' : word -> option byte) : Prop :=
  forall c i, 0 <= c < KNUMCLASSES -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m' (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPC.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable cls : Z.
Hypothesis Hc : 1 <= cls <= 30.
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.

Lemma tail_blockfree : forall lo hi, rbeg st cls + r_mapped (rg st cls) <= lo -> hi <= rbeg st cls + KREGIONSIZE -> blockfree st lo hi.
Proof.
  intros lo hi H1 H2. (nelimp (cls_facts st WF cls Hc) 8%nat; intros C1 C2 C3 C4 C5 C6 C7 _).
  apply (prim_nonuser_blockfree st WF); [lia| lia|].
  intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE]; [right; exact H1|].
  (nelim (region_range st WF c Hc') 6%nat; intros _ R2 _ _ R5 _).
  rewrite !(rbeg_val st) in *. unfold KFREEARRAY_OFF, KREGIONSIZE, KNUMCLASSES in *.
  destruct (Z_lt_le_dec c cls); [right| left]; nia.
Qed.

Lemma pz_not_client : forall lo hi a, pz_ok st cls (lo, hi) -> (CEIL <= lo -> hi <= SP) -> lo <= a < hi ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros lo hi a PZ HS Ha. (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).
  pose proof (t_range st WF) as [T1 T2].
  unfold pz_ok in PZ. cbn [fst snd] in PZ. destruct PZ as [Z1|[Z2|[Z3|[Z4|[Z5|Z6]]]]].
  - eapply (tpage_not_client st WF SP); try exact HSP. unfold T_ACACHE, T_UNWINDING in *. lia.
  - eapply (below_sp_not_client st WF SP); try exact HSP. specialize (HS (proj1 (conj Z2 I))). lia.
  - eapply (hm_not_client st WF SP) with (lo := ris st) (hi := ris st + 4096); try exact HSP;
      [apply (ris_blockfree st WF)| apply (prim_framefree st WF); pose proof (ris_range st WF); lia
      | pose proof (ris_range st WF); blia| pose proof (ris_range st WF); unfold CEIL; lia| unfold KNUMCLASSES in *; lia].
  - eapply (hm_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply tail_blockfree; lia| apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia| unfold KFREEARRAY_OFF, KREGIONSIZE in *; lia].
  - eapply (hm_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply tail_blockfree; lia| apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia
      | rewrite C13 in Z5; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia].
  - eapply (hmsh_not_client st WF SP) with (lo := rbeg st cls + r_mapped (rg st cls)) (hi := rbeg st cls + KREGIONSIZE); try exact HSP;
      [apply (prim_framefree st WF); unfold KREGIONSIZE in *; lia| blia| unfold CEIL, KREGIONSIZE in *; lia| lia].
Qed.

Lemma cli_pres_pz : forall W m m', munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) W -> cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as [A1 A2]. cbn [fst snd] in A2. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. exact (pz_not_client lo hi a A1 A2 Hin HC).
Qed.

(* [comment removed for export] *)
Lemma outside_intro' : forall W a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof. intros W a H. induction W as [|[l' h'] W IH]; [exact I|]. cbn. split; [exact (H (l', h') ltac:(left; reflexivity))| apply IH; intros iv Hiv; apply H; right; exact Hiv]. Qed.
Lemma rt_frame_pz : forall W m m' lo FP, munch W m m' ->
  (forall a iv, In iv W -> fst iv <= a < snd iv -> (lo <= a < SP) \/ in_ivs FP a) ->
  rt_frame FP lo SP m m'.
Proof.
  intros W m m' lo FP MU HW a Ha Hs Hn. apply MU. rewrite wa_unsigned by lia. apply outside_intro'.
  intros iv Hiv Hin. destruct (HW a iv Hiv Hin) as [X|X]; [exact (Hs X)| exact (Hn X)].
Qed.
End FPC.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rinfo_join3 : forall m Rc (a b c d : cell) rest,
  rw_cells bsegs m Rc [a; b; c] -> rw_cells bsegs m (Rc + 24) [d] -> rw_cells bsegs m (Rc + 32) rest ->
  cells_size [a; b; c] = 24%nat -> cells_size [d] = 8%nat ->
  rw_cells bsegs m Rc ([a; b; c] ++ [d] ++ rest).
Proof.
  intros m Rc a b c d rest H1 H2 H3 E1 E2. apply rw_cells_app. split; [exact H1|]. rewrite E1. change (Z.of_nat 24) with 24.
  apply rw_cells_app. split; [exact H2|]. rewrite E2. change (Z.of_nat 8) with 8. replace (Rc + 24 + 8) with (Rc + 32) by lia. exact H3.
Qed.

Lemma nth_error_wl : forall (fa : list Z) k, (k < length fa)%nat -> nth_error (wl fa) k = Some (wz (nth k fa 0)).
Proof.
  intros fa k Hk. unfold wl. rewrite nth_error_map. rewrite (nth_error_nth' fa 0 Hk). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma GWIN_addwin : forall st m mo G R R' lo hi,
  GWIN st m mo (mkG G R) -> (forall x : word, lo <= bv_unsigned x < hi -> m x <> None) -> GWIN st m mo (mkG ((lo, hi) :: G) R').
Proof.
  intros st m mo G R R' lo hi HG VIS. apply (GWIN_open st m mo G R lo hi R' HG). intros x Hx _ _. exact (VIS x Hx).   (* [comment removed for export] *)
Qed.
Lemma GWIN_R : forall st m mo G R R', GWIN st m mo (mkG G R) -> GWIN st m mo (mkG G R').
Proof. intros st m mo G R R' HG x Hw Hz Hr. exact (HG x Hw Hz Hr). Qed.

Lemma vis_bytes : forall m lo hi, stk bsegs m lo hi -> AIMG_HI <= lo -> forall x : word, lo <= bv_unsigned x < hi -> m x <> None.
Proof.
  intros m lo hi ST Hlo x Hx. pose proof (stk_some m lo hi (bv_unsigned x) ST Hx Hlo) as H. unfold wa in H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma zsum_ge_In : forall (f : Z -> Z) l x, (forall y, In y l -> 0 <= f y) -> In x l -> List.NoDup l -> f x <= zsum (map f l).
Proof.
  intros f l x Hf Hx ND. induction l as [|y l IH]; [destruct Hx|]. cbn [map]. rewrite zsum_cons. inversion ND; subst.
  destruct Hx as [->|Hx].
  - pose proof (zsum_nonneg (map f l) ltac:(apply Forall_map; apply Forall_forall; intros z Hz; apply Hf; right; exact Hz)). lia.
  - specialize (IH ltac:(intros z Hz; apply Hf; right; exact Hz) Hx ltac:(assumption)). pose proof (Hf y ltac:(left; reflexivity)). lia.
Qed.
Lemma prov_cls_le : forall st cls, RTWF st -> 1 <= cls <= 30 -> provU st cls + provF st cls <= rt_prov st.
Proof.
  intros st cls WF Hc. (nelimp (rt_prov_parts_nonneg st WF) 8%nat; intros P1 P2 P3 P4 P5 P6 P7 P8).
  pose proof (prov_l24_nonneg st) as P9. pose proof (prov_emb_nonneg st) as [P10 _].
  assert (provU st cls + provF st cls <= prov_classes st).
  { unfold prov_classes. apply (zsum_ge_In (fun c => provU st c + provF st c) classes cls).
    - intros y _. unfold provU, provF. lia.
    - unfold classes. apply in_map_iff. exists (Z.to_nat cls). split; [lia| apply in_seq; lia].
    - apply classes_nodup. }
  unfold rt_prov. lia.
Qed.
Lemma lumpU_ok : forall st cls, RTWF st -> 1 <= cls <= 30 -> cch st cls = [] -> num_freed st cls < nrefill cls ->
  r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls * (nrefill cls - num_freed st cls) -> LUMPU <= provU st cls.
Proof.
  intros st cls WF Hc HC0 LT UM. (nelimp (slack_ok' cls Hc) 3%nat; intros SL1 SL2 SL3). pose proof (csize_pos cls ltac:(lia)) as CP.
  pose proof (wc_num_freed st cls (wf_class_ok st WF cls ltac:(unfold KNUMCLASSES; lia))) as NF. pose proof (zlen_nonneg (r_fa (rg st cls))) as NF0. unfold num_freed in *.
  unfold provU, delta, navail, avail_cptrs. rewrite HC0, app_nil_r.
  replace (r_mapped (rg st cls) - r_allocated (rg st cls) <? nrefill cls * csize cls) with true.
  2:{ symmetry. apply Z.ltb_lt. assert (csize cls * (nrefill cls - zlen (r_fa (rg st cls))) <= csize cls * nrefill cls) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  unfold Nmax, FAPROV. pose proof (Z.div_pos (2^18) (csize cls) ltac:(lia) ltac:(lia)).
  assert (2 * csize cls * zlen (r_fa (rg st cls)) <= 2 * csize cls * (nrefill cls - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold LUMPU in *. lia.
Qed.
Lemma lumpF_ok : forall st cls, RTWF st -> 1 <= cls <= 30 -> r_mapped_fa (rg st cls) = 0 -> LUMPF <= provF st cls.
Proof.
  intros st cls WF Hc F0. unfold provF, fa_cap. rewrite F0. cbn [Z.div].
  pose proof (wc_alloc_nonneg st cls (wf_class_ok st WF cls ltac:(unfold KNUMCLASSES; lia))) as A0. pose proof (csize_pos cls ltac:(lia)).
  assert (0 <= ncarved st cls) by (unfold ncarved; apply Z.div_pos; lia). unfold FAPROV, LUMPF, LUMPU. lia.
Qed.

(* [comment removed for export] *)
Lemma WTOT_facts : forall st cls lo SP usz, RTWF st -> 1 <= cls <= 30 -> CEIL <= lo -> lo <= SP -> 0 <= usz <= 262144 -> r_mapped (rg st cls) + usz <= KFREEARRAY_OFF ->
  let U := rbeg st cls + r_mapped (rg st cls) in
  Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls))
  /\ (forall st', rbeg st' cls = rbeg st cls -> rinfo st' cls = rinfo st cls -> st_t st' = st_t st ->
      forall a iv, In iv (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)) -> fst iv <= a < snd iv ->
      (lo <= a < SP) \/ in_ivs (primary_fp_fine st cls ++ fp_emb st') a).
Proof.
  intros st cls lo SP usz WF Hc HCE HLS HU1 HU2. cbv zeta.
  (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).
  pose proof (t_range st WF) as [T1 T2].
  assert (SHU : SH (rbeg st cls + r_mapped (rg st cls)) + 32768 <= SH (rbeg st cls + KREGIONSIZE) /\ SH (rbeg st cls + r_mapped (rg st cls)) <= SH (fabeg st cls)
                /\ SH (fabeg st cls) + 67108864 <= SH (rbeg st cls + KREGIONSIZE) /\ SH (rbeg st cls) + KREGIONSIZE / 8 = SH (rbeg st cls + KREGIONSIZE)
                /\ SH (rbeg st cls + KREGIONSIZE) <= KHIGHMEM_BEG).
  { rewrite C13. unfold SH, SHADOW_OFFSET, KFREEARRAY_OFF, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. (nelimp (ris_range st WF) 3%nat; intros Z1 Z2 _). unfold KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *.
    clear -C1 C3 C6 C7 C11 C12 Z2. Z.div_mod_to_equations. lia. }
  (nelim SHU 5%nat; intros S1 S2 S3 S4 S5).
  unfold WTOT, WPRE, WREST. unfold pcaddr, acache, T_ACACHE, T_UNWINDING, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  split.
  - apply Forall_forall. intros iv Hiv. unfold pz_ok. unfold T_ACACHE, T_UNWINDING, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, CEIL, KHIGHMEM_BEG, AIMG_HI.
    cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd]; split; try (intros HH; lia).
    + right; left; lia.
    + left; lia.
    + right; left; lia.
    + left; lia.
    + left; lia.
    + right; right; left; lia.
    + right; right; right; left; lia.
    + do 5 right; lia.
    + do 4 right; left; lia.
    + do 5 right; lia.
  - intros st' E1 E2 E3 a iv Hiv Hr. unfold primary_fp_fine, fp_class_fine, fp_tpage.
    cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Hr.
    + left. exact Hr.
    + right. exists (st_t st), (st_t st + 4096). split; [apply in_or_app; left; do 3 right; left; reflexivity| lia].
    + left. exact Hr.
    + right. exists (st_t st), (st_t st + 4096). split; [apply in_or_app; left; do 3 right; left; reflexivity| lia].
    + right. exists (st_t st), (st_t st + 4096). split; [apply in_or_app; left; do 3 right; left; reflexivity| lia].
    + right. exists (rinfo st cls), (rinfo st cls + 128). split; [apply in_or_app; left; do 2 right; left; reflexivity| lia].
    + right. exists (rbeg st cls + r_mapped (rg st cls)), (rbeg st cls + 4294967296). split; [apply in_or_app; left; left; reflexivity| lia].
    + right. exists (SH (rbeg st cls + r_mapped (rg st cls))), (SH (rbeg st cls) + 4294967296 / 8). split; [apply in_or_app; left; right; left; reflexivity| lia].
    + right. exists (rbeg st cls + r_mapped (rg st cls)), (rbeg st cls + 4294967296). split; [apply in_or_app; left; left; reflexivity| rewrite C13 in Hr; lia].
    + right. exists (SH (rbeg st cls + r_mapped (rg st cls))), (SH (rbeg st cls) + 4294967296 / 8). split; [apply in_or_app; left; right; left; reflexivity| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FINF.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Variables (cls : Z) (um : bool) (m m' : word -> option byte) (mo : Model) (G : list (Z * Z)) (R SP lo : Z) (jr je js : list byte).
Let st' := mkRT a1 a2 a3 (updz a4 cls (r_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um)) true a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Let r := rg st cls.
Let nf := num_freed st cls.
Let mapped := r_mapped r.
Let U := rbeg st cls + mapped.
Let usz := Z.min 262144 (3758096384 - mapped).
Let mapped' := mapped + (if um then 262144 else 0).
Let mo1 := if um then mm_commit (wz U) (wz 262144) mo else mo.
Let G1 := if um then (SH U, SH U + 32768) :: G else G.
Let R1 := R - (if um then LUMP else 0).
Hypothesis HR : RTREP st m.
Hypothesis WF : RTWF st.
Hypothesis HM : RTMODEL st mo.
Hypothesis HG : GWIN st m mo (mkG G R).
Hypothesis HFR : FRONTR mo R.
Hypothesis HSW : SWIN st (mkG G R).
Hypothesis HOK : LOK bsegs mo.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Hypothesis HUM : um = true -> nf < nrefill cls /\ mapped < r_allocated r + (nrefill cls - nf) * csize cls /\ mapped + 262144 <= KFREEARRAY_OFF.
Hypothesis MI' : mem_inv bsegs m'.
Hypothesis MU : munch (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis ST' : stk bsegs m' lo SP.
Hypothesis LO : CEIL <= lo /\ lo <= SP /\ SP <= 2^64.
Hypothesis RIa : rw_cells bsegs m' (rinfo st cls) [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)].
Hypothesis RI24 : rw_cells bsegs m' (rinfo st cls + 24) [C8 (Z_to_bv 64 (r_mapped_fa r))].
Hypothesis RIb : rw_cells bsegs m' (rinfo st cls + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr;
                                                     C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js].
Hypothesis VUH : if um then stk bsegs m' U (U + 262144) /\ rw_cells bsegs m' (SH U) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True.
Hypothesis PCH : pch_at st cls m' 0.
Hypothesis PCO : pco_at st m'.
Hypothesis HRu : (if um then LUMP else 0) <= R.

Lemma Hcls : 0 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma WX : wf_pd st. Proof. intros c Hc'. exact (RTWF_pd st c WF Hc'). Qed.
Lemma usz_ok : 0 <= usz <= 262144 /\ mapped + usz <= KFREEARRAY_OFF /\ (um = true -> usz = 262144).
Proof.
  (nelimp (cls_facts st WF cls Hc) 8%nat; intros _ _ _ _ _ C6 C7 _). pose proof HUM as HU. unfold usz, KFREEARRAY_OFF in *. fold r mapped in C6, C7.
  split; [lia|]. split; [lia|]. intros E. (nelim (HU E) 3%nat; intros _ _ X). lia.
Qed.
Lemma WT : Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)).
Proof. (nelimp usz_ok 3%nat; intros U1 U2 _). exact (proj1 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2)). Qed.
Lemma WTz : Forall (pz_ok st cls) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz (fabeg st cls) (num_freed st cls)).
Proof. eapply Forall_impl; [| exact WT]. intros iv [H _]. exact H. Qed.

Theorem RTREP_finf : RTREP st' m'.
Proof.
  pose proof VUH as VU0. pose proof PCH as PCH0.
  eapply (RTREP_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um); try exact WX; try exact WTz; try exact PCO; try eassumption.
  - (* [comment removed for export] *) exists jr, je, js. unfold rinfo_cells.
    rewrite (num_freed_all a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um) by (first [exact WX| eassumption]).
    rewrite (rg_same a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um) by (first [exact WX| eassumption]).
    cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_f]. change (rinfo st' cls) with (rinfo st cls).
    apply (rinfo_join3 m' (rinfo st cls)); [exact RIa| exact RI24| exact RIb| reflexivity| reflexivity].
  - (* [comment removed for export] *) intros E. rewrite E in VU0. destruct VU0 as [V1 V2]. split; [exact V1|]. apply CB_to_zcells_zrep; [lia| exact V2].
  - (* [comment removed for export] *) intros c Hc'. pose proof (PCH0 c Hc') as X. unfold pch_at in X. destruct (Z.eqb_spec c cls) as [->|NE]; [fold st; rewrite HC0; exact X| exact X].
Qed.
Theorem RTWF_finf : RTWF st'.
Proof. eapply (RTWF_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um); try exact WX; eassumption. Qed.
Lemma U_facts : KHIGHMEM_BEG <= U /\ U + 262144 <= CEIL /\ (um = true -> U + 262144 <= rbeg st cls + KFREEARRAY_OFF) /\ 2147450880 <= SH U /\ SH U + 32768 <= KHIGHMEM_BEG.
Proof.
  (nelimp (cls_facts st WF cls Hc) 8%nat; intros C1 C2 C3 C4 C5 C6 C7 _). pose proof HUM as HU. fold r mapped in C6, C7.
  unfold U, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, KREGIONSIZE, CEIL, SH, SHADOW_OFFSET in *. (nelimp (ris_range st WF) 3%nat; intros _ Z2 _).
  split; [lia|]. split; [lia|]. split; [intros E; (nelim (HU E) 3%nat; intros _ _ X); lia|]. clear -C1 C3 C6 C7 Z2. Z.div_mod_to_equations. lia.
Qed.
Theorem RTMODEL_finf : RTMODEL st' mo1.
Proof.
  apply (RTMODEL_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um).
  (nelimp U_facts 3%nat; intros U1 U2 _). unfold mo1. destruct um; [| exact HM]. apply (RTMODEL_commit mo U 262144 HOK ltac:(lia) st HM).
Qed.
Theorem GWIN_finf : GWIN st' m' mo1 (mkG G1 R1).
Proof.
  apply (GWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um).
  (nelimp U_facts 5%nat; intros U1 U2 _ U4 U5). pose proof VUH as VU0. pose proof (GWIN_mem st m m' mo (mkG G R) HG HOK WM) as G0.
  unfold mo1, G1, R1. destruct um.
  - destruct VU0 as [V1 V2]. apply (GWIN_commit mo U 262144 HOK ltac:(lia) st m').
    apply (GWIN_addwin st m' mo G R). { exact G0. }
    pose proof (stk_of_rw_cells bsegs m' _ _ V2) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
    apply (vis_bytes m' (SH U) (SH U + 32768) SV). unfold AIMG_HI. lia.
  - rewrite Z.sub_0_r. exact G0.
Qed.
Theorem FRONTR_finf : FRONTR mo1 R1.
Proof. unfold mo1, R1. destruct um; [apply FRONTR_commit; apply (FRONTR_le mo R); [exact HFR| unfold LUMP in *; lia| unfold LUMP; lia]| rewrite Z.sub_0_r; exact HFR]. Qed.
Theorem SWIN_finf : SWIN st' (mkG G1 R1).
Proof.
  apply (SWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um).
  apply (SWIN_mono st (mkG G R)); [exact HSW|]. unfold G1. intros w Hw. cbn [g_win] in *. destruct um; [right; exact Hw| exact Hw].
Qed.
Theorem RTS_finf : RTS st' m' mo1 (mkG G1 R1).
Proof. exact (RTS_intro _ _ _ _ RTREP_finf RTWF_finf RTMODEL_finf GWIN_finf FRONTR_finf SWIN_finf). Qed.
Theorem gmono_finf : gmono (mkG G R) (mkG G1 R1).
Proof. unfold G1. intros w Hw. cbn [g_win] in *. destruct um; [right; exact Hw| exact Hw]. Qed.
Theorem budget_finf : budget_ok st (mkG G R) st' (mkG G1 R1) 0.
Proof.
  unfold budget_ok, R1. cbn [g_res].
  pose proof (rt_prov_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um) as P0.
  assert (P : rt_prov st' + (if um then LUMPU else 0) <= rt_prov st) by (apply P0; first [exact WX| assumption]). clear P0.
  unfold LUMP, LUMPU in *. destruct um; lia.
Qed.
Theorem cli_pres_finf : cli_pres st SP m m'.
Proof. exact (cli_pres_pz st WF cls Hc SP (ltac:(lia)) _ m m' MU WM WT). Qed.
Theorem rt_frame_finf : rt_frame (primary_fp_fine st cls ++ fp_emb st') lo SP m m'.
Proof.
  (nelimp usz_ok 3%nat; intros U1 U2 _).
  apply (rt_frame_pz SP _ m m' lo _ MU). exact (proj2 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2) st' eq_refl eq_refl eq_refl).
Qed.
Theorem rt_frame_finf' : rt_frame (primary_fp st cls ++ fp_emb st') lo SP m m'.
Proof.
  eapply rt_frame_weaken; [| exact rt_frame_finf]. intros a Ha. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  unfold primary_fp_fine, primary_fp, fp_class_fine, fp_class in *. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  (nelimp (cls_facts st WF cls Hc) 7%nat; intros _ _ _ _ _ C6 _). (nelim Ha 4%nat; intros l h Hin Hr).
  destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
  - exists (rbeg st cls), (rbeg st cls + KREGIONSIZE). split; [left; reflexivity| lia].
  - exists (SH (rbeg st cls)), (SH (rbeg st cls) + KREGIONSIZE / 8). split; [right; left; reflexivity|]. pose proof (rt_SH_mono (rbeg st cls) (rbeg st cls + r_mapped (rg st cls)) ltac:(lia)). lia.
  - exists (rinfo st cls), (rinfo st cls + 128). split; [right; right; left; reflexivity| lia].
Qed.
Theorem rel_finf : refill_rel st st' cls 0.
Proof.
  split; [| split; [reflexivity| split; [reflexivity| split]]].
  - unfold same_but_primary. repeat match goal with |- _ /\ _ => split end; try reflexivity; [apply dtls_same_of_eq; reflexivity| apply loose0_ext_of_eq; reflexivity].
  - intros c Hc' NE. split; [| reflexivity]. apply (rg_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls um); first [exact NE| exact WX| assumption].
  - right. split; [reflexivity|]. exact HC0.
Qed.
End FINF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FINS.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Variables (cls Nv nm : Z) (um fm pop : bool) (m m' : word -> option byte) (mo : Model) (G : list (Z * Z)) (R SP lo : Z) (jr je js : list byte) (fa : list Z).
Let n := nrefill cls.
Let r := rg st cls.
Let S := csize cls.
Let nf := num_freed st cls.
Let alloc := r_allocated r.
Let mapped := r_mapped r.
Let fam := r_mapped_fa r.
Let mapped' := mapped + (if um then 262144 else 0).
Let fam' := if fm then nm else fam.
Let base := nf + Nv - n.
Let L := r_fa r ++ newc cls (ncarved st cls) Nv.
Let FA := fabeg st cls.
Let U := rbeg st cls + mapped.
Let Ufa := FA + fam.
Let D := FA + 4 * nf.
Let usz := Z.min 262144 (3758096384 - mapped).
Let mo1 := if um then mm_commit (wz U) (wz 262144) mo else mo.
Let G1 := if um then (SH U, SH U + 32768) :: G else G.
Let R1 := R - (if um then LUMP else 0).
Let mo2 := if fm then mm_commit (wz Ufa) (wz 262144) mo1 else mo1.
Let G2 := if fm then (SH Ufa, SH Ufa + 32768) :: G1 else G1.
Let R2 := R1 - (if fm then LUMP else 0).
Let st' := mkRT a1 a2 a3 (updz a4 cls (r_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop)) true
                (updz a6 cls (skipn (Z.to_nat base) L)) a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Hypothesis HR : RTREP st m.
Hypothesis WF : RTWF st.
Hypothesis HM : RTMODEL st mo.
Hypothesis HG : GWIN st m mo (mkG G R).
Hypothesis HFR : FRONTR mo R.
Hypothesis HSW : SWIN st (mkG G R).
Hypothesis HOK : LOK bsegs mo.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Hypothesis HNv : 0 <= Nv /\ n <= nf + Nv.
Hypothesis HPOP : pop = true ->
  nf < n /\ Nv = (r_mapped r + (if um then 262144 else 0) - r_allocated r) / S
  /\ um = (r_mapped r <? r_allocated r + (n - nf) * S) /\ (um = true -> r_mapped r + 262144 <= KFREEARRAY_OFF)
  /\ fm = (r_mapped_fa r <? 4 * (nf + Nv)) /\ nm = (4 * (nf + Nv) + 262143) / 262144 * 262144.
Hypothesis HHAVE : pop = false -> Nv = 0 /\ um = false /\ fm = false.
Hypothesis NVB : Nv <= 16385.
Hypothesis FAM0 : fm = true -> fam = 0 /\ nm = 262144.
Hypothesis MI' : mem_inv bsegs m'.
Hypothesis MU : munch (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz FA nf) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis ST' : stk bsegs m' lo SP.
Hypothesis LO : CEIL <= lo /\ lo <= SP /\ SP <= 2^64.
Hypothesis RIa : rw_cells bsegs m' (rinfo st cls) [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 base)].
Hypothesis RI24 : rw_cells bsegs m' (rinfo st cls + 24) [C8 (Z_to_bv 64 fam')].
Hypothesis RIb : rw_cells bsegs m' (rinfo st cls + 32) [C8 (Z_to_bv 64 (alloc + Nv * S)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped'); C8 (Z_to_bv 64 0); CB 4 jr;
                                                     C1 (Z_to_bv 8 (if pop then 0 else if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js].
Hypothesis VFA' : stk bsegs m' FA (FA + fam').
Hypothesis FILL : u32arr bsegs m' D (fill_vals alloc S (Z.to_nat Nv)).
Hypothesis VUH : if um then stk bsegs m' U (U + 262144) /\ rw_cells bsegs m' (SH U) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True.
Hypothesis VFH : if fm then rw_cells bsegs m' (SH Ufa) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))] else True.
Hypothesis Hfa : length fa = Z.to_nat n /\ (forall i, 0 <= i < n -> nthz fa i 0 = nthz L (base + i) 0).
Hypothesis CHU : u32arr bsegs m' (pcaddr st cls + 16) (wl fa).
Hypothesis PCH : pch_at st cls m' n.
Hypothesis PCO : pco_at st m'.
Hypothesis HRR : (if um then LUMP else 0) + (if fm then LUMP else 0) <= R.

Lemma SHcls : 0 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma SWX : wf_pd st. Proof. intros c Hc'. exact (RTWF_pd st c WF Hc'). Qed.
Lemma SHn : n = nrefill cls. Proof. reflexivity. Qed.
Lemma NR : 1 <= n <= 8. Proof. exact (proj2 (nrefill_eq cls ltac:(lia))). Qed.
Lemma s_usz_ok : 0 <= usz <= 262144 /\ mapped + usz <= KFREEARRAY_OFF /\ (um = true -> usz = 262144).
Proof.
  (nelimp (cls_facts st WF cls Hc) 8%nat; intros _ _ _ _ _ C6 C7 _). pose proof HPOP as HP. pose proof HHAVE as HH. unfold usz, KFREEARRAY_OFF in *. fold r mapped in C6, C7.
  split; [lia|]. split; [lia|]. intros E. destruct pop; [(nelim (HP eq_refl) 5%nat; intros _ _ _ X _); pose proof (X E); lia| (nelim (HH eq_refl) 3%nat; intros _ X _); congruence].
Qed.
Lemma SWT : Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz FA nf).
Proof. (nelimp s_usz_ok 3%nat; intros U1 U2 _). exact (proj1 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2)). Qed.
Lemma SWTz : Forall (pz_ok st cls) (WTOT lo SP (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) U usz FA nf).
Proof. eapply Forall_impl; [| exact SWT]. intros iv [H _]. exact H. Qed.
Lemma SU_facts : KHIGHMEM_BEG <= U /\ (um = true -> U + 262144 <= rbeg st cls + KFREEARRAY_OFF) /\ 2147450880 <= SH U /\ SH U + 32768 <= KHIGHMEM_BEG
                 /\ KHIGHMEM_BEG <= FA /\ FA + 262144 <= CEIL /\ 2147450880 <= SH FA /\ SH FA + 32768 <= KHIGHMEM_BEG /\ rbeg st cls + KFREEARRAY_OFF = FA /\ FA + 262144 <= CEIL.
Proof.
  (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14). (nelimp s_usz_ok 3%nat; intros _ _ U3). fold r mapped in C6, C7. fold FA in C13.
  unfold U, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, CEIL, SH, SHADOW_OFFSET in *. (nelimp (ris_range st WF) 3%nat; intros _ Z2 _).
  split; [lia|]. split; [intros E; pose proof (U3 E); unfold usz in *; lia|]. clear -C1 C3 C6 C7 C13 Z2. Z.div_mod_to_equations. lia.
Qed.
Lemma zlen_cache' : zlen (cch st' cls) = n.
Proof.
  assert (E : cch st' cls = skipn (Z.to_nat base) L) by (apply (RTW_p_abs.cch_same a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); first [exact SWX| exact SHn| assumption]).
  rewrite E. unfold zlen. rewrite length_skipn.
  assert (LL : Z.of_nat (length L) = nf + Nv).
  { unfold L. rewrite length_app, Nat2Z.inj_add. pose proof (newc_length cls (ncarved st cls) Nv (proj1 HNv)) as NL. unfold zlen in NL. rewrite NL. reflexivity. }
  pose proof HNv as [H0 H1]. pose proof NR as NR'. unfold base in *.
  assert (G8 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg).
  rewrite Nat2Z.inj_sub by lia. rewrite LL. rewrite Z2Nat.id by lia. lia.
Qed.

Theorem RTREP_fins : RTREP st' m'.
Proof.
  pose proof SHcls as HK. pose proof NR as NR0. pose proof VUH as VU0. pose proof VFH as VF0. pose proof PCH as PCH0. pose proof Hfa as [FL FN]. pose proof FAM0 as F0. pose proof HHAVE as HH. pose proof HPOP as HP.
  (nelimp SU_facts 10%nat; intros U1 U2 U3 U4 U5 U6 U7 U8 U9 U10). pose proof zlen_cache' as ZC.
  pose proof (wc_alloc_carved st cls (wf_class_ok st WF cls HK)) as EAL. fold r alloc in EAL. change (csize cls) with S in EAL.
  pose proof (csize_pos cls ltac:(lia)) as CP. change (csize cls) with S in CP.
  eapply (RTREP_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); try exact SWX; try exact SHn; try exact SWTz; try eassumption.
  - (* [comment removed for export] *) exists jr, je, js. unfold rinfo_cells.
    rewrite (num_freed_same' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) by (first [exact SWX| exact SHn| eassumption]).
    rewrite (RTW_p_abs.rg_same a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) by (first [exact SWX| exact SHn| eassumption]).
    cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_new]. change (rinfo st' cls) with (rinfo st cls).
    pose proof RIb as RIb0. destruct pop; cbv iota in RIb0; cbv iota;
      (apply (rinfo_join3 m' (rinfo st cls)); [exact RIa| exact RI24| exact RIb0| reflexivity| reflexivity]).
  - (* [comment removed for export] *) intros E. rewrite E in VU0. destruct VU0 as [V1 V2]. split; [exact V1|]. apply CB_to_zcells_zrep; [lia| exact V2].
  - (* [comment removed for export] *) split; [exact VFA'|]. change (if fm then nm else r_mapped_fa (rg st cls)) with fam'. unfold fam'. destruct fm.
    + destruct (F0 eq_refl) as [FZ ->]. change (262144 / 8) with 32768.
      pose proof (stk_of_rw_cells bsegs m' _ _ VF0) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
      unfold Ufa in SV. rewrite FZ, Z.add_0_r in SV. exact SV.
    + (nelim (rr_regions st m HR cls HK) 5%nat; intros _ _ _ V4 _). eapply (stk_wmono_noseg m m'); [exact V4| exact WM| match goal with |- _ <= ?x => change x with (SH FA) end; unfold AIMG_HI; clear -U7; lia].
  - (* [comment removed for export] *) intros t Ht.
    match goal with |- rw_cells _ _ ?a _ => replace a with (D + 4 * t) by (unfold D, FA, nf, st; lia) end.
    assert (NC0 : 0 <= ncarved st cls) by (pose proof (wc_alloc_nonneg st cls (wf_class_ok st WF cls HK)) as A0; fold r alloc in A0; clear -A0 EAL CP; nia).
    match goal with |- rw_cells _ _ _ [W4 ?v] => replace v with ((alloc + Z.of_nat (Z.to_nat Nv - 1 - Z.to_nat t) * S) / 16) end.
    2:{ unfold chunk_cptr. change (csize cls) with S. change (ncarved _ cls) with (ncarved st cls). rewrite EAL.
        f_equal. rewrite <- Z.mul_add_distr_r. f_equal. clear -Ht NC0 HNv. lia. }
    eapply (cells_of_u32arr _ _ _ t); [exact FILL| apply fill_vals_nth; clear -Ht HNv; lia| clear -Ht; lia].
  - (* [comment removed for export] *) intros c Hc'. pose proof (PCH0 c Hc') as X. unfold pch_at in X. destruct (Z.eqb_spec c cls) as [->|NE].
    { match goal with |- rw_cells _ _ _ (W4 ?z :: _) => replace z with n by (first [exact ZC| symmetry; exact ZC]) end. exact X. }
    rewrite (RTW_p_abs.cch_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) by (first [exact NE| exact SWX| exact SHn| eassumption]). exact X.
  - (* [comment removed for export] *) intros i Hi.
    match goal with |- rw_cells _ _ _ [W4 ?v] => replace v with (nthz fa i 0) by (first [apply FN; exact Hi| symmetry; apply FN; exact Hi]) end.
    change (pcaddr _ cls) with (pcaddr st cls).
    eapply (cells_of_u32arr _ _ _ i); [exact CHU| | clear -Hi; lia]. rewrite nth_error_wl by (rewrite FL; clear -Hi NR0; lia).
    unfold nthz. destruct (Z.ltb_spec0 i 0); [lia| reflexivity].
  - (* [comment removed for export] *) intros c i Hc' NE Hi. exact (PCO c i Hc' Hi).
Qed.
Theorem RTWF_fins : RTWF st'.
Proof. eapply (RTWF_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); try exact SWX; try exact SHn; eassumption. Qed.
Lemma LOK1 : LOK bsegs mo1. Proof. unfold mo1. destruct um; [apply mm_commit_LOK; exact HOK| exact HOK]. Qed.
Theorem RTMODEL_fins : RTMODEL st' mo2.
Proof.
  apply (RTMODEL_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop). (nelimp SU_facts 7%nat; intros U1 U2 U3 U4 U5 U6 _). pose proof FAM0 as F0. pose proof LOK1 as LK1.
  assert (M1 : RTMODEL st mo1).
  { unfold mo1. destruct um; [| exact HM].
    assert (UC : KHIGHMEM_BEG <= U /\ U + 262144 <= CEIL /\ 0 < 262144).
    { (nelimp (cls_facts st WF cls Hc) 6%nat; intros _ _ C3 C4 C5 _). specialize (U2 eq_refl). unfold CEIL, KFREEARRAY_OFF, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI in *. clear -U1 U2 C3 C4 C5. lia. }
    exact (RTMODEL_commit mo U 262144 HOK UC st HM). }
  unfold mo2. destruct fm; [| exact M1]. destruct (F0 eq_refl) as [FZ _]. unfold Ufa. rewrite FZ, Z.add_0_r.
  apply (RTMODEL_commit mo1 FA 262144 LK1 ltac:(clear -U5 U6; lia) st M1).
Qed.
Theorem GWIN_fins : GWIN st' m' mo2 (mkG G2 R2).
Proof.
  apply (GWIN_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop). (nelimp SU_facts 9%nat; intros U1 U2 U3 U4 U5 U6 U7 U8 _). pose proof VUH as VU0. pose proof VFH as VF0. pose proof FAM0 as F0. pose proof LOK1 as LK1.
  pose proof (GWIN_mem st m m' mo (mkG G R) HG HOK WM) as G0.
  assert (GW1 : GWIN st m' mo1 (mkG G1 R1)).
  { unfold mo1, G1, R1. destruct um.
    - destruct VU0 as [V1 V2].
      assert (UC : KHIGHMEM_BEG <= U /\ U + 262144 <= CEIL /\ 0 < 262144).
      { (nelimp (cls_facts st WF cls Hc) 6%nat; intros _ _ C3 C4 C5 _). specialize (U2 eq_refl). unfold CEIL, KFREEARRAY_OFF, KREGIONSIZE, KHIGHMEM_BEG, AIMG_HI in *. clear -U1 U2 C3 C4 C5. lia. }
      apply (GWIN_commit mo U 262144 HOK UC st m').
      apply (GWIN_addwin st m' mo G R). { exact G0. }
      pose proof (stk_of_rw_cells bsegs m' _ _ V2) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
      apply (vis_bytes m' (SH U) (SH U + 32768) SV). unfold AIMG_HI, KHIGHMEM_BEG in *. lia.
    - rewrite Z.sub_0_r. exact G0. }
  unfold mo2, G2, R2. destruct fm.
  - destruct (F0 eq_refl) as [FZ _]. apply (GWIN_commit mo1 Ufa 262144 LK1 ltac:(unfold Ufa; rewrite FZ, Z.add_0_r; clear -U5 U6; lia) st m').
    apply (GWIN_addwin st m' mo1 G1 R1). { exact GW1. }
    pose proof (stk_of_rw_cells bsegs m' _ _ VF0) as SV. replace (Z.of_nat (cells_size [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 250) (Z.to_nat 32768))])) with 32768 in SV by reflexivity.
    apply (vis_bytes m' (SH Ufa) (SH Ufa + 32768) SV). unfold Ufa. rewrite FZ, Z.add_0_r. unfold AIMG_HI, KHIGHMEM_BEG in *. lia.
  - rewrite Z.sub_0_r. exact GW1.
Qed.
Theorem FRONTR_fins : FRONTR mo2 R2.
Proof.
  unfold mo2, R2, mo1, R1. assert (F1 : FRONTR (if um then mm_commit (wz U) (wz 262144) mo else mo) (R - (if um then LUMP else 0))).
  { generalize HRR. destruct um; intros HRR'; [apply FRONTR_commit; apply (FRONTR_le mo R); [exact HFR| revert HRR'; destruct fm; intros HRR'; unfold LUMP in *; lia| unfold LUMP; lia]| rewrite Z.sub_0_r; exact HFR]. }
  generalize HRR. destruct fm; intros HRR'; [apply FRONTR_commit; eapply FRONTR_le; [exact F1| revert HRR'; destruct um; intros HRR'; unfold LUMP in *; lia| unfold LUMP; lia]| rewrite Z.sub_0_r; exact F1].
Qed.
Theorem gmono_fins : gmono (mkG G R) (mkG G2 R2).
Proof. unfold G2, G1. intros w Hw. cbn [g_win] in *. destruct fm; destruct um; cbn; tauto. Qed.
Theorem SWIN_fins : SWIN st' (mkG G2 R2).
Proof. apply (SWIN_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop). apply (SWIN_mono st (mkG G R)); [exact HSW| exact gmono_fins]. Qed.
Theorem RTS_fins : RTS st' m' mo2 (mkG G2 R2).
Proof. exact (RTS_intro _ _ _ _ RTREP_fins RTWF_fins RTMODEL_fins GWIN_fins FRONTR_fins SWIN_fins). Qed.
Theorem budget_fins : budget_ok st (mkG G R) st' (mkG G2 R2) 0.
Proof.
  unfold budget_ok, R2, R1. cbn [g_res].
  pose proof (rt_prov_new a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop) as P0.
  assert (P : rt_prov st' + (if um then LUMPU else 0) + (if fm then LUMPF else 0) <= rt_prov st) by (apply P0; first [exact SWX| exact SHn| assumption]). clear P0.
  unfold LUMP, LUMPU, LUMPF, LUMPU in *. destruct um; destruct fm; lia.
Qed.
Theorem cli_pres_fins : cli_pres st SP m m'.
Proof. exact (cli_pres_pz st WF cls Hc SP (ltac:(lia)) _ m m' MU WM SWT). Qed.
Theorem rt_frame_fins : rt_frame (primary_fp_fine st cls ++ fp_emb st') lo SP m m'.
Proof.
  (nelimp s_usz_ok 3%nat; intros U1 U2 _).
  apply (rt_frame_pz SP _ m m' lo _ MU). exact (proj2 (WTOT_facts st cls lo SP usz WF Hc (proj1 LO) (proj1 (proj2 LO)) U1 U2) st' eq_refl eq_refl eq_refl).
Qed.
Theorem rt_frame_fins' : rt_frame (primary_fp st cls ++ fp_emb st') lo SP m m'.
Proof.
  eapply rt_frame_weaken; [| exact rt_frame_fins]. intros a Ha. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  unfold primary_fp_fine, primary_fp, fp_class_fine, fp_class in *. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  (nelimp (cls_facts st WF cls Hc) 7%nat; intros _ _ _ _ _ C6 _). (nelim Ha 4%nat; intros l h Hin Hr).
  destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
  - exists (rbeg st cls), (rbeg st cls + KREGIONSIZE). split; [left; reflexivity| lia].
  - exists (SH (rbeg st cls)), (SH (rbeg st cls) + KREGIONSIZE / 8). split; [right; left; reflexivity|]. pose proof (rt_SH_mono (rbeg st cls) (rbeg st cls + r_mapped (rg st cls)) ltac:(lia)). lia.
  - exists (rinfo st cls), (rinfo st cls + 128). split; [right; right; left; reflexivity| lia].
Qed.
Theorem rel_fins : refill_rel st st' cls 1.
Proof.
  split; [| split; [reflexivity| split; [reflexivity| split]]].
  - unfold same_but_primary. repeat match goal with |- _ /\ _ => split end; try reflexivity; [apply dtls_same_of_eq; reflexivity| apply loose0_ext_of_eq; reflexivity].
  - intros c Hc' NE. split.
    + apply (RTW_p_abs.rg_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); first [exact NE| exact SWX| exact SHn| assumption].
    + apply (RTW_p_abs.cch_other a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls n Nv nm um fm pop); first [exact NE| exact SWX| exact SHn| assumption].
  - left. split; [reflexivity|]. exact zlen_cache'.
Qed.
End FINS.



End CeilWrap.
(* [comment removed for export] *)
Ltac dj := cbn; repeat match goal with |- _ /\ _ => split end; try exact I; first [left; lia | right; lia | lia].
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; repeat match goal with H' : ~ _ |- _ => clear H' end; first [exact Cq| lia] end ].
End RTW_p_refillA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_kit RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp RT_artF RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_zone RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_cd_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_cd_main.RTW_p_absf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_primary_iface.
Import RTW_p_refillA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_grant RT_sec RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_mallocN.RTW_m_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_emb0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_embz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_embz.RT_emb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_embz RT_wokapp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac3 RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_ci (st : rtstate) : rtstate :=
  match st with mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 a4 true a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 end.
Definition st_exh (st : rtstate) (cls : Z) : rtstate :=
  match st with mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 (updz a4 cls (rg_set_exh (nthz a4 cls region0))) a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 end.
Definition st_emb (st : rtstate) (d sz : Z) : rtstate :=
  match st with mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    if tl_emb_d a20 =? 0
    then mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 (mkTLS (tl_dtls_block a20) (tl_dtls_w a20) d sz) (a21 ++ [(d, EMB_CAP)]) a22 a23 b1 b2 b3 b4 b5
    else mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 (mkTLS (tl_dtls_block a20) (tl_dtls_w a20) (tl_emb_d a20) sz) a21 a22 a23 b1 b2 b3 b4 b5 end.
(* [comment removed for export] *)
Definition st_fx (st : rtstate) (cls d sz : Z) : rtstate := st_emb (st_exh (st_ci st) cls) d sz.

Lemma updz_nat_id : forall {A} (l : list A) k d, updz_nat l k (nth k l d) = l.
Proof. induction l as [|y l IH]; intros [|k] d; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma updz_nthz_id : forall {A} (l : list A) i d, updz l i (nthz l i d) = l.
Proof. intros A l i d. unfold updz, nthz. destruct (i <? 0); [reflexivity|]. apply updz_nat_id. Qed.

(* [comment removed for export] *)
Lemma r_f_false : forall a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls,
  updz a4 cls (r_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) = a4.
Proof.
  intros. unfold r_f. cbn [rg st_regions]. rewrite Z.add_0_r.
  replace (mkRegion _ _ _ _ _) with (nthz a4 cls region0); [apply updz_nthz_id|]. unfold rg. cbn [st_regions]. destruct (nthz a4 cls region0); reflexivity.
Qed.

Section CHAIN.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable cls : Z.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].

Lemma RTWF_ci : RTWF (st_ci st).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci.
  pose proof (RTWF_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma RTMODEL_ci : forall mo, RTMODEL st mo -> RTMODEL (st_ci st) mo.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci. intros mo HM.
  pose proof (RTMODEL_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| exact HM| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma GWIN_ci : forall m mo g, GWIN st m mo g -> GWIN (st_ci st) m mo g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci. intros m mo g HG.
  pose proof (GWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| exact HG| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma SWIN_ci : forall g, SWIN st g -> SWIN (st_ci st) g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci. intros g HS.
  pose proof (SWIN_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. apply X; first [exact WF| exact Hc| exact HC0| exact HS| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
Lemma rt_prov_ci : rt_prov (st_ci st) <= rt_prov st.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_ci.
  pose proof (rt_prov_f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 cls false) as X.
  rewrite r_f_false in X. cbn [Z.add] in X. rewrite Z.add_0_r in X.
  apply X; first [exact WF| exact Hc| exact HC0| intros c Hc'; exact (RTWF_pd _ c WF Hc')| intros E; discriminate E].
Qed.
End CHAIN.

(* [comment removed for export] *)
Lemma RTWF_exh_g : forall st cls, RTWF st -> 1 <= cls <= 31 ->
  r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls -> RTWF (st_exh st cls).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc HX. exact (RTWF_exh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF cls Hc HX). Qed.
Lemma rt_prov_exh_g : forall st cls, RTWF st -> 1 <= cls <= 31 ->
  r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls -> rt_prov (st_exh st cls) = rt_prov st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc HX. exact (rt_prov_exh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF cls Hc). Qed.
Lemma RTMODEL_exh_g : forall st cls mo, RTWF st -> 1 <= cls <= 31 -> RTMODEL st mo -> RTMODEL (st_exh st cls) mo.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls mo WF Hc HM. eapply RTMODEL_exh; eassumption. Qed.
Lemma GWIN_exh_g : forall st cls m mo g, RTWF st -> 1 <= cls <= 31 -> GWIN st m mo g -> GWIN (st_exh st cls) m mo g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls m mo g WF Hc HG. eapply GWIN_exh; eassumption. Qed.
Lemma SWIN_exh_g : forall st cls g, RTWF st -> 1 <= cls <= 31 -> SWIN st g -> SWIN (st_exh st cls) g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls g WF Hc HS. eapply SWIN_exh; eassumption. Qed.
Lemma nexh_exh_g : forall st cls, RTWF st -> 1 <= cls <= 31 -> nexh st <= nexh (st_exh st cls) <= nexh st + 1.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc. eapply nexh_exh_ge; eassumption. Qed.

(* [comment removed for export] *)
Section EMBG.
Variables (st : rtstate) (d sz : Z).
Hypothesis WF : RTWF st.
Hypothesis Hsz : 0 <= sz <= EMB_MSG * nexh st.
(* [comment removed for export] *)
Hypothesis HN : emb_d st = 0 -> d mod 4096 = 0 /\ ablk d (d + EMB_CAP) /\ d + EMB_CAP <= CEIL
                               /\ (forall r, In r (rt_ranges st) -> d + EMB_CAP <= fst r \/ snd r <= d).

Lemma RTWF_emb_g : RTWF (st_emb st d sz).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb.
  destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - destruct (HN E) as (N1 & N2 & N3 & N4). eapply RTWF_embN; eassumption.
  - eapply RTWF_embA; eassumption.
Qed.
Lemma rt_prov_emb_g : rt_prov (st_emb st d sz) = rt_prov st - (if emb_d st =? 0 then EMB_CAP else 0).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb, emb_d. cbn [st_tls].
  destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - destruct (HN E) as (N1 & N2 & N3 & N4). eapply rt_prov_embN; eassumption.
  - rewrite Z.sub_0_r. eapply rt_prov_embA; eassumption.
Qed.
Lemma RTMODEL_emb_g : forall mo, RTMODEL st mo ->
  RTMODEL (st_emb st d sz) (if emb_d st =? 0 then mm_add_map (wz d) (wz EMB_CAP) mo else mo).
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb, emb_d. cbn [st_tls].
  intros mo HM. destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - destruct (HN E) as (N1 & N2 & N3 & N4). eapply RTMODEL_embN; try eassumption. pose proof (ablk_lin _ _ N2). lia.
  - exact HM.
Qed.
Lemma GWIN_emb_g : forall m mo g, GWIN st m mo g ->
  GWIN (st_emb st d sz) m (if emb_d st =? 0 then mm_add_map (wz d) (wz EMB_CAP) mo else mo) g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb, emb_d. cbn [st_tls].
  intros m mo g HG. destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE].
  - intros x Hw Hz Hr. rewrite mm_add_map_lzf in Hz. exact (HG x Hw Hz Hr).
  - exact HG.
Qed.
Lemma SWIN_emb_g : forall g, SWIN st g -> SWIN (st_emb st d sz) g.
Proof.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_emb.
  intros g HS. destruct (tl_emb_d a20 =? 0); exact HS.
Qed.
End EMBG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FXP.
Variables (st : rtstate) (cls d sz : Z).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.

Lemma fx_rg : forall c, rg (st_fx st cls d sz) c = if c =? cls then rg_set_exh (rg st cls) else rg st c.
Proof.
  intros c. pose proof (wb_len_regions st (wf_base_ok st WF)) as L.
  destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5].
  unfold st_fx, st_emb, st_exh, st_ci. cbn [st_regions] in L. destruct (tl_emb_d a20 =? 0); unfold rg; cbn [st_regions];
    (destruct (Z.eqb_spec c cls) as [->|NE]; [apply nthz_updz_same; unfold zlen; rewrite L; lia| rewrite nthz_updz_other by lia; reflexivity]).
Qed.
Lemma fx_proj : forall c,
  r_allocated (rg (st_fx st cls d sz) c) = r_allocated (rg st c) /\ r_mapped (rg (st_fx st cls d sz) c) = r_mapped (rg st c)
  /\ r_mapped_fa (rg (st_fx st cls d sz) c) = r_mapped_fa (rg st c) /\ r_fa (rg (st_fx st cls d sz) c) = r_fa (rg st c).
Proof. intros c. rewrite fx_rg. destruct (Z.eqb_spec c cls) as [->|NE]; [cbn; repeat split; reflexivity| repeat split; reflexivity]. Qed.
Lemma fx_exhausted : forall c, r_exhausted (rg (st_fx st cls d sz) c) = if c =? cls then true else r_exhausted (rg st c).
Proof. intros c. rewrite fx_rg. destruct (c =? cls); reflexivity. Qed.
Lemma fx_num_freed : forall c, num_freed (st_fx st cls d sz) c = num_freed st c.
Proof. intros c. unfold num_freed. rewrite (proj2 (proj2 (proj2 (fx_proj c)))). reflexivity. Qed.
Lemma fx_cch : forall c, cch (st_fx st cls d sz) c = cch st c.
Proof. intros c. destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); reflexivity. Qed.
Lemma fx_avail : forall c, avail_cptrs (st_fx st cls d sz) c = avail_cptrs st c.
Proof. intros c. unfold avail_cptrs. rewrite (proj2 (proj2 (proj2 (fx_proj c)))), fx_cch. reflexivity. Qed.
End FXP.

(* [comment removed for export] *)
Local Ltac fxconv := intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz m H;
  unfold st_fx, st_emb, st_exh, st_ci; destruct (tl_emb_d a20 =? 0); exact H.
Lemma R_alloc_fx : forall st cls d sz m, R_alloc st m -> R_alloc (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_thread_fx : forall st cls d sz m, R_thread st m -> R_thread (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_live_fx : forall st cls d sz m, R_live st m -> R_live (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_quar_fx : forall st cls d sz m, R_quar st m -> R_quar (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_batches_fx : forall st cls d sz m, R_batches st m -> R_batches (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_ptrarr_fx : forall st cls d sz m, R_ptrarr st m -> R_ptrarr (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_depot_fx : forall st cls d sz m, R_depot st m -> R_depot (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma R_fs_fx : forall st cls d sz m, R_fs st m -> R_fs (st_fx st cls d sz) m. Proof. fxconv. Qed.
Lemma fx_ia_inited : forall st cls d sz, st_ia_inited (st_fx st cls d sz) = st_ia_inited st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); reflexivity. Qed.
Lemma fx_cache_inited : forall st cls d sz, st_cache_inited (st_fx st cls d sz) = true.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); reflexivity. Qed.
Lemma fx_geom : forall st cls d sz, st_pbase (st_fx st cls d sz) = st_pbase st /\ st_t (st_fx st cls d sz) = st_t st /\ st_apend (st_fx st cls d sz) = st_apend st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); repeat split; reflexivity. Qed.

Lemma fx_addr : forall st cls d sz,
  ris (st_fx st cls d sz) = ris st /\ (forall c, rinfo (st_fx st cls d sz) c = rinfo st c) /\ (forall c, rbeg (st_fx st cls d sz) c = rbeg st c)
  /\ (forall c, fabeg (st_fx st cls d sz) c = fabeg st c) /\ (forall c, pcaddr (st_fx st cls d sz) c = pcaddr st c)
  /\ (forall c k, cptr_addr (st_fx st cls d sz) c k = cptr_addr st c k) /\ (forall c, apend_cptrs (st_fx st cls d sz) c = apend_cptrs st c).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz. unfold st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0); repeat split; reflexivity. Qed.

Section XREP.
Variables (st : rtstate) (cls d sz : Z).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Variables (W1 W2 : list (Z * Z)) (elo ehi : Z) (m m' : word -> option byte).
Hypothesis HW1 : Forall (pz_ok st cls) W1.
Hypothesis HBA : ablk elo ehi.
Hypothesis Hz : forall a n, (a + n <= A_EMB \/ A_EMB + 56 <= a) -> a + n <= CEIL -> (a + n <= elo \/ ehi <= a) -> disjoint_from W2 a n.
Hypothesis HBLK : (forall r, In r (rt_ranges st) -> ehi <= fst r \/ snd r <= elo)
               \/ (emb_d st <> 0 /\ elo = emb_d st /\ ehi = emb_d st + EMB_CAP).
Hypothesis HR : RTREP st m.
Hypothesis MU : munch (W1 ++ W2) m m'.
Hypothesis WM : wmono bsegs m m'.
(* [comment removed for export] *)
Hypothesis RINFO : exists jr je js, rw_cells bsegs m' (rinfo st cls) (rinfo_cells (st_fx st cls d sz) cls jr je js).
Hypothesis PCH : pch_at st cls m' 0.
Hypothesis PCO : pco_at st m'.
Hypothesis EMB : R_emb (st_fx st cls d sz) m'.

Let W := W1 ++ W2.
Local Ltac tapp T := first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].

Local Ltac pzz L := first [ exact (L st WF cls Hc W1 HW1) | exact (L st cls W1 HW1) | eapply L; eassumption ].
Local Ltac ezz L := first [ exact (L st WF W2 elo ehi HBA Hz HBLK) | exact (L st WF W2 elo ehi HBA Hz) | exact (L W2 elo ehi HBA Hz) | eapply L; eassumption ].

Lemma T_consts_rest : R_consts_rest st m -> WOK_consts_rest W -> R_consts_rest st m'.
Proof.
  intros H K. unfold R_consts_rest, WOK_consts_rest in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & [oom H15] & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  Local Ltac trx MU WM H K := first [ eapply (roT _ _ _ MU _ _ H); exact K | eapply (rwT _ _ _ MU WM _ _ H); exact K
                           | eapply (roTn _ _ _ MU _ _ _ H); [| exact K]; cbn; lia | eapply (rwTn _ _ _ MU WM _ _ _ H); [| exact K]; cbn; lia ].
  split; [trx MU WM H1 K1|]. split; [trx MU WM H2 K2|]. split; [trx MU WM H3 K3|]. split; [trx MU WM H4 K4|]. split; [trx MU WM H5 K5|]. split; [trx MU WM H6 K6|].
  split; [trx MU WM H7 K7|]. split; [trx MU WM H8 K8|]. split; [trx MU WM H9 K9|]. split; [trx MU WM H10 K10|]. split; [trx MU WM H11 K11|]. split; [trx MU WM H12 K12|].
  split; [trx MU WM H13 K13|]. split; [trx MU WM H14 K14|]. split; [exists oom; trx MU WM H15 K15|]. split; [trx MU WM H16 K16|]. split; [trx MU WM H17 K17|].
  split; [trx MU WM H18 K18|]. split; [trx MU WM H19 K19|]. split; [trx MU WM H20 K20|]. split; [trx MU WM H21 K21|]. split; [trx MU WM H22 K22|]. split; [trx MU WM H23 K23|]. split; [trx MU WM H24 K24|].
  split; [trx MU WM H25 K25|]. split; [trx MU WM H26 K26|]. trx MU WM H27 K27.
Qed.

Theorem RTREP_fx : RTREP (st_fx st cls d sz) m'.
Proof.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (* [comment removed for export] *)
  assert (Y1 : R_link m').
  { tapp T_link; [exact (rr_link st m HR)| apply WOK_link_app; [pzz PZ_link| ezz EZ_link]]. }
  assert (Y3 : R_alloc st m').
  { tapp T_alloc; [exact (rr_alloc st m HR)| apply WOK_alloc_app; [pzz PZ_alloc| ezz EZ_alloc]]. }
  assert (Y5 : R_regions st m').
  { tapp T_regions; [exact (rr_regions st m HR)| apply WOK_regions_app; [pzz PZ_regions| ezz EZ_regions]]. }
  assert (Y6 : R_avail st m').
  { tapp T_avail; [exact (rr_avail st m HR)| apply WOK_avail_app; [pzz PZ_avail| ezz EZ_avail]]. }
  assert (Y8 : R_thread st m').
  { tapp T_thread; [exact (rr_thread st m HR)| apply WOK_thread_app; [pzz PZ_thread| ezz EZ_thread]]. }
  assert (Y9 : R_live st m').
  { tapp T_live; [exact (rr_live st m HR)| apply WOK_live_app; [pzz PZ_live| ezz EZ_live]]. }
  assert (Y10 : R_quar st m').
  { tapp T_quar; [exact (rr_quar st m HR)| apply WOK_quar_app; [pzz PZ_quar| ezz EZ_quar]]. }
  assert (Y11 : R_batches st m').
  { tapp T_batches; [exact (rr_batches st m HR)| apply WOK_batches_app; [pzz PZ_batches| ezz EZ_batches]]. }
  assert (Y12 : R_ptrarr st m').
  { tapp T_ptrarr; [exact (rr_ptrarr st m HR)| apply WOK_ptrarr_app; [pzz PZ_ptrarr| ezz EZ_ptrarr]]. }
  assert (Y13 : R_depot st m').
  { tapp T_depot; [exact (rr_depot st m HR)| apply WOK_depot_app; [pzz PZ_depot| ezz EZ_depot]]. }
  assert (Y14 : R_fs st m').
  { tapp T_fs; [exact (rr_fs st m HR)| apply WOK_fs_app; [pzz PZ_fs| ezz EZ_fs]]. }
  assert (Y15 : R_ia m').
  { tapp T_ia; [exact (rr_ia st m HR)| apply WOK_ia_app; [pzz PZ_ia| ezz EZ_ia]]. }
  assert (Y16 : R_lowshadow m').
  { tapp T_lowshadow; [exact (rr_lowshadow st m HR)| apply WOK_lowshadow_app; [pzz PZ_lowshadow| ezz EZ_lowshadow]]. }
  assert (Y2 : R_consts_rest st m').
  { apply T_consts_rest; [exact (proj1 (R_consts_split st m (rr_consts st m HR)))|].
    apply WOK_consts_rest_app; [apply WOK_consts_rest_of; pzz PZ_consts| ezz EZ_consts_rest]. }
  pose proof (fx_proj st cls d sz WF Hc) as PJ. pose proof (fx_num_freed st cls d sz WF Hc) as NF. pose proof (fx_avail st cls d sz WF Hc) as AV.
  assert (CC : forall c, cch (st_fx st cls d sz) c = cch st c) by (intros c0; apply fx_cch; assumption). pose proof (fx_rg st cls d sz WF Hc) as RG. pose proof (fx_geom st cls d sz) as (GP & GT & GA).
  pose proof (fx_addr st cls d sz) as (AR & AI & AB & AF & AP & ACP & AAP).
  constructor.
  - exact Y1.
  - apply R_consts_join; [apply (R_consts_rest_indep st); [apply fx_ia_inited| exact Y2]| exact EMB].
  - apply R_alloc_fx. exact Y3.
  - (* [comment removed for export] *) destruct (rr_rinfo st m HR) as [VR HLn]. pose proof (ris_range st WF) as (Z1 & Z2 & Z3 & Z4).
    split.
    { rewrite AR. eapply stk_wmono_noseg; [exact VR| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]. }
    intros c Hc'. rewrite AI.
    destruct (Z.eq_dec c cls) as [->|NE]; [exact RINFO|].
    destruct (HLn c Hc') as (jr & je & js & RC). exists jr, je, js.
    replace (rinfo_cells (st_fx st cls d sz) c jr je js) with (rinfo_cells st c jr je js).
    2:{ unfold rinfo_cells. rewrite NF. destruct (PJ c) as (P1 & P2 & P3 & P4). rewrite P1, P2, P3. rewrite (fx_exhausted st cls d sz WF Hc c).
        replace (c =? cls) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. }
    eapply (rw_cells_transport bsegs _ m m'); [exact RC| exact MU| exact WM|].
    assert (E128 : Z.of_nat (cells_size (rinfo_cells st c jr je js)) = 128).
    { destruct RC as [[Wf _] _]. cbn in Wf. unfold rinfo_cells. cbn [cells_size Cells.csize]. destruct Wf as (_ & _ & _ & _ & _ & _ & _ & _ & L1 & _ & L2 & L3 & _). lia. }
    rewrite E128. apply dj_app; [pzz PZ_rinfo_other; assumption| exact (EZ_rinfo st WF W2 elo ehi HBA Hz HBLK c Hc')].
  - (* [comment removed for export] *) intros c Hc'. pose proof (Y5 c Hc') as R5. cbn zeta in *. destruct (PJ c) as (P1 & P2 & P3 & P4).
    rewrite AB, AF, P1, P2, P3, P4, NF. exact R5.
  - (* [comment removed for export] *) intros c k Hc' Hk. rewrite AV, AAP in Hk. rewrite ACP. exact (Y6 c k Hc' Hk).
  - (* [comment removed for export] *) intros c Hc'. rewrite AP.
    assert (PM : pc_max_count (st_fx st cls d sz) c = (if c =? 0 then 0 else cmaxcount c)) by (unfold pc_max_count; rewrite fx_cache_inited; destruct (c =? 0); reflexivity).
    assert (PS' : pc_class_size (st_fx st cls d sz) c = (if c =? 0 then 0 else csize c)) by (unfold pc_class_size; rewrite fx_cache_inited; destruct (c =? 0); reflexivity).
    rewrite PM, PS', CC. split.
    + pose proof (PCH c Hc') as X. unfold pch_at in X. destruct (Z.eqb_spec c cls) as [->|NE]; [rewrite HC0; exact X| exact X].
    + intros i Hi. exact (PCO c i Hc' Hi).
  - apply R_thread_fx. exact Y8.
  - apply R_live_fx. exact Y9.
  - apply R_quar_fx. exact Y10.
  - apply R_batches_fx. exact Y11.
  - apply R_ptrarr_fx. exact Y12.
  - apply R_depot_fx. exact Y13.
  - apply R_fs_fx. exact Y14.
  - exact Y15.
  - exact Y16.
Qed.
End XREP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ci_same : forall st, rt_ranges (st_ci st) = rt_ranges st /\ (forall c, rg (st_ci st) c = rg st c) /\ nexh (st_ci st) = nexh st
  /\ emb_d (st_ci st) = emb_d st /\ emb_sz (st_ci st) = emb_sz st /\ (forall c, cch (st_ci st) c = cch st c).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5]. repeat split; reflexivity. Qed.
Lemma exh_same : forall st cls, rt_ranges (st_exh st cls) = rt_ranges st /\ emb_d (st_exh st cls) = emb_d st /\ emb_sz (st_exh st cls) = emb_sz st.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls. repeat split; reflexivity. Qed.
Lemma nexh_exh_flip : forall st cls, RTWF st -> 1 <= cls <= 31 -> r_exhausted (rg st cls) = false -> nexh (st_exh st cls) = nexh st + 1.
Proof.
  intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls WF Hc HE.
  pose proof (nexh_exh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 WF cls Hc) as X.
  cbv zeta in X. rewrite HE in X. exact X.
Qed.
Lemma fx_emb : forall st cls d sz, (emb_d st <> 0 -> d = emb_d st) -> emb_d (st_fx st cls d sz) = d /\ emb_sz (st_fx st cls d sz) = sz.
Proof.
  intros [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5] cls d sz H.
  unfold st_fx, st_emb, st_exh, st_ci, emb_d, emb_sz in *. cbn [st_tls] in *. destruct (Z.eqb_spec (tl_emb_d a20) 0) as [E|NE]; cbn [st_tls tl_emb_d tl_emb_sz]; [split; reflexivity| split; [symmetry; exact (H NE)| reflexivity]].
Qed.

Section FINX.
Variables (st : rtstate) (cls d sz : Z) (mo mo' : Model) (G : list (Z * Z)) (R R' : Z).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Hypothesis HX : r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls.
Hypothesis HEX : r_exhausted (rg st cls) = false.
Hypothesis HSZ : emb_sz st <= sz <= emb_sz st + EMB_MSG.
Hypothesis HM : RTMODEL st mo.
Hypothesis HOK : LOK bsegs mo.
Hypothesis HFR : FRONTR mo R.
Hypothesis HRV : rt_prov st <= R.
Hypothesis STEP : (emb_d st <> 0 /\ d = emb_d st /\ mo' = mo /\ R' = R)
   \/ (emb_d st = 0 /\ d <> 0 /\ mmap_grant mo (wz d) EMB_CAP /\ mo' = mm_add_map (wz d) (wz EMB_CAP) mo /\ R' = R - EMB_CAP).

Let st2 := st_exh (st_ci st) cls.

Hypothesis HD64 : 0 <= d < 2^64.

(* [comment removed for export] *)
Lemma fx_new : emb_d st = 0 -> d mod 4096 = 0 /\ ablk d (d + EMB_CAP) /\ d + EMB_CAP <= CEIL
                               /\ (forall r, In r (rt_ranges st) -> d + EMB_CAP <= fst r \/ snd r <= d).
Proof.
  intros Z0. destruct STEP as [(NZ & _)|(_ & NZ & GR & _)]; [exfalso; exact (NZ Z0)|].
  pose proof (grant_ablk st mo (wz d) EMB_CAP HOK HM ltac:(unfold EMB_CAP; lia) GR) as BK.
  pose proof (grant_fresh st mo (wz d) EMB_CAP HOK HM WF ltac:(unfold EMB_CAP; lia) GR) as FR.
  destruct GR as (GA & _ & GC & _). unfold wz, page_size in *. rewrite unsigned_lit in * by lia.
  split; [exact GA|]. split; [exact BK|]. split; [unfold CEIL; exact GC| exact FR].
Qed.
Lemma fx_mo : mo' = (if emb_d st =? 0 then mm_add_map (wz d) (wz EMB_CAP) mo else mo) /\ R' = R - (if emb_d st =? 0 then EMB_CAP else 0).
Proof.
  destruct STEP as [(NZ & _ & -> & ->)|(Z0 & _ & _ & -> & ->)].
  - replace (emb_d st =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). split; [reflexivity| lia].
  - rewrite Z0. cbn [Z.eqb]. split; reflexivity.
Qed.

Lemma RTWF_st2 : RTWF st2.
Proof.
  destruct (ci_same st) as (_ & RGc & _). apply RTWF_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia| rewrite !RGc; exact HX].
Qed.
Lemma st2_emb : emb_d st2 = emb_d st /\ emb_sz st2 = emb_sz st /\ rt_ranges st2 = rt_ranges st /\ nexh st2 = nexh st + 1.
Proof.
  destruct (ci_same st) as (C1 & C2 & C3 & C4 & C5 & _). destruct (exh_same (st_ci st) cls) as (E1 & E2 & E3). unfold st2.
  rewrite E2, E3, E1, C4, C5, C1. repeat split.
  rewrite (nexh_exh_flip (st_ci st) cls (RTWF_ci st WF cls Hc HC0) ltac:(lia)); [rewrite C3; reflexivity| rewrite C2; exact HEX].
Qed.
Lemma fx_sz : 0 <= sz <= EMB_MSG * nexh st2.
Proof. destruct st2_emb as (_ & _ & _ & NX). rewrite NX. pose proof (wb_emb_sz st (wf_base_ok st WF)) as SZ. unfold EMB_MSG in *. lia. Qed.
Lemma fx_hn : emb_d st2 = 0 -> d mod 4096 = 0 /\ ablk d (d + EMB_CAP) /\ d + EMB_CAP <= CEIL
                               /\ (forall r, In r (rt_ranges st2) -> d + EMB_CAP <= fst r \/ snd r <= d).
Proof. destruct st2_emb as (E1 & _ & E3 & _). rewrite E1, E3. exact fx_new. Qed.

Theorem RTWF_fx : RTWF (st_fx st cls d sz).
Proof. exact (RTWF_emb_g st2 d sz RTWF_st2 fx_sz fx_hn). Qed.
Theorem RTMODEL_fx : RTMODEL (st_fx st cls d sz) mo'.
Proof.
  rewrite (proj1 fx_mo). destruct st2_emb as (E1 & _). rewrite <- E1.
  apply (RTMODEL_emb_g st2 d sz RTWF_st2 fx_sz fx_hn). apply RTMODEL_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia| eapply RTMODEL_ci; eassumption].
Qed.
Theorem GWIN_fx : forall m m', GWIN st m mo (mkG G R) -> wmono bsegs m m' -> GWIN (st_fx st cls d sz) m' mo' (mkG G R').
Proof.
  intros m m' HG WM. rewrite (proj1 fx_mo). destruct st2_emb as (E1 & _). rewrite <- E1.
  eapply GWIN_emb_g; first [exact RTWF_st2| exact fx_sz| exact fx_hn| idtac].
  apply GWIN_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia|]. eapply GWIN_ci; try eassumption.
  apply (GWIN_R st m' mo G R R'). exact (GWIN_mem st m m' mo (mkG G R) HG HOK WM).
Qed.
Theorem SWIN_fx : SWIN st (mkG G R) -> SWIN (st_fx st cls d sz) (mkG G R').
Proof.
  intros HS. eapply SWIN_emb_g; first [exact RTWF_st2| exact fx_sz| exact fx_hn| idtac]. apply SWIN_exh_g; [exact (RTWF_ci st WF cls Hc HC0)| lia|]. eapply SWIN_ci; try eassumption.
Qed.
Theorem rt_prov_fx : rt_prov (st_fx st cls d sz) + (if emb_d st =? 0 then EMB_CAP else 0) <= rt_prov st.
Proof.
  pose proof (rt_prov_emb_g st2 d sz RTWF_st2 fx_sz fx_hn) as P1. destruct st2_emb as (E1 & _). rewrite E1 in P1. unfold st_fx. fold st2. rewrite P1.
  destruct (ci_same st) as (_ & RGc & _).
  pose proof (rt_prov_exh_g (st_ci st) cls (RTWF_ci st WF cls Hc HC0) ltac:(lia) ltac:(rewrite !RGc; exact HX)) as P2. fold st2 in P2. rewrite P2.
  assert (P3 : rt_prov (st_ci st) <= rt_prov st) by (eapply rt_prov_ci; eassumption). lia.
Qed.
Theorem FRONTR_fx : FRONTR mo' R'.
Proof.
  destruct STEP as [(NZ & _ & -> & ->)|(Z0 & _ & _ & -> & ->)]; [exact HFR|].
  apply FRONTR_grant; [exact HFR| unfold FR_MINGRANT, EMB_CAP; lia| unfold EMB_CAP; lia|].
  pose proof (prov_emb_nonneg st) as PE. pose proof (rt_prov_parts_nonneg st WF) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). pose proof (prov_l24_nonneg st) as Q9.
  assert (PV : prov_emb st <= rt_prov st) by (unfold rt_prov; lia).
  unfold prov_emb in PV. rewrite Z0 in PV. cbn [Z.eqb] in PV. lia.
Qed.
Theorem budget_fx : budget_ok st (mkG G R) (st_fx st cls d sz) (mkG G R') 0.
Proof. unfold budget_ok. cbn [g_res]. rewrite (proj2 fx_mo). pose proof rt_prov_fx. lia. Qed.
Theorem gmono_fx : gmono (mkG G R) (mkG G R').
Proof. intros w Hw. exact Hw. Qed.
End FINX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rel_fx : forall st cls d sz, RTWF st -> 1 <= cls <= 30 -> cch st cls = [] -> refill_rel st (st_fx st cls d sz) cls 0.
Proof.
  intros st cls d sz WF Hc HC0. pose proof (fx_rg st cls d sz WF Hc) as RG. assert (CC : forall c, cch (st_fx st cls d sz) c = cch st c) by (intros c0; apply fx_cch; assumption).
  split; [| split; [| split; [apply fx_cache_inited| split]]].
  - destruct st as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5].
    unfold same_but_primary, st_fx, st_emb, st_exh, st_ci. destruct (tl_emb_d a20 =? 0);
      (repeat match goal with |- _ /\ _ => split end; try reflexivity; [split; reflexivity|]);
      [exists [(d, EMB_CAP)]; reflexivity| exists []; cbn [st_loose0]; rewrite app_nil_r; reflexivity].
  - apply (fx_geom st cls d sz).
  - intros c Hc' NE. split; [rewrite RG; replace (c =? cls) with false by (symmetry; apply Z.eqb_neq; exact NE); reflexivity| apply CC].
  - right. split; [reflexivity|]. rewrite CC. exact HC0.
Qed.

Lemma fresh_blockfree : forall st lo hi, RTWF st -> (forall r, In r (rt_ranges st) -> hi <= fst r \/ snd r <= lo) -> blockfree st lo hi.
Proof.
  intros st lo hi WF FR A n Hin. pose proof (block_geom st WF A n Hin) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs).
  destruct (bprim n) eqn:EB.
  - destruct (Gp eq_refl) as (P1 & P2 & P3 & P4 & P5 & P6).
    destruct (FR (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity)) as [D|D]; cbn [fst snd] in D; lia.
  - destruct (Gs eq_refl) as (S1 & S2 & S3 & S4).
    destruct (FR (b_lo A n, b_lo A n + smapsize n) ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1])) as [D|D];
      cbn [fst snd] in D; lia.
Qed.
Lemma fresh_framefree : forall st lo hi, RTWF st -> (forall r, In r (rt_ranges st) -> hi <= fst r \/ snd r <= lo) -> framefree st lo hi.
Proof.
  intros st lo hi WF FR. unfold framefree.
  destruct (FR (st_fs st, st_fs st + FS_TOTAL) ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; left; apply in_map_iff; exists (st_fs st, FS_TOTAL); split; [reflexivity| exact (wb_fs_loose st (wf_base_ok st WF))])) as [D|D];
    cbn [fst snd] in D; [left| right]; exact D.
Qed.

Section FRAMEX.
Variables (st st' : rtstate) (cls d : Z) (SP lo : Z) (W1 : list (Z * Z)) (m m' : word -> option byte).
Hypothesis WF : RTWF st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HSP : CEIL <= SP.
Hypothesis HW1c : Forall (fun iv : Z * Z => pz_ok st cls iv /\ (CEIL <= fst iv -> snd iv <= SP)) W1.
Hypothesis HW1f : forall a iv, In iv W1 -> fst iv <= a < snd iv -> (lo <= a < SP) \/ in_ivs (primary_fp_fine st cls ++ fp_emb st') a.
Hypothesis HD : d <> 0 /\ emb_d st' = d.
Hypothesis HBK : (emb_d st <> 0 /\ d = emb_d st)
              \/ (ablk d (d + EMB_CAP) /\ forall r, In r (rt_ranges st) -> d + EMB_CAP <= fst r \/ snd r <= d).
Let W2 : list (Z * Z) := [(A_EMB, A_EMB + 56); (d, d + EMB_CAP)].
Hypothesis MU : munch (W1 ++ W2) m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma blk_not_client : forall a, d <= a < d + EMB_CAP -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha. destruct HBK as [(NZ & E)|(BK & FR)].
  - pose proof (emb_block_range st WF NZ) as (BK & B2 & B3). pose proof (wb_emb_loose st (wf_base_ok st WF) NZ) as LS. rewrite <- E in *.
    eapply (hm_not_client st WF SP HSP d (d + EMB_CAP) a); [exact (loose_blockfree st WF d EMB_CAP LS)| | exact (oclr_of_ablk _ _ BK)| unfold CEIL; exact B2| exact Ha].
    apply (loose_framefree st WF d EMB_CAP LS). intros EQ. injection EQ as E1 E2. unfold EMB_CAP, FS_TOTAL in E2. lia.
  - eapply (hm_not_client st WF SP HSP d (d + EMB_CAP) a); [exact (fresh_blockfree st _ _ WF FR)| exact (fresh_framefree st _ _ WF FR)| exact (oclr_of_ablk _ _ BK)
      | unfold CEIL; exact (ablk_top _ _ BK)| exact Ha].
Qed.

Theorem cli_pres_fx : cli_pres st SP m m'.
Proof.
  unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. apply outside_intro'. intros iv Hiv Hin. apply in_app_or in Hiv. destruct Hiv as [H1|H2].
  - rewrite Forall_forall in HW1c. destruct (HW1c iv H1) as [A1 A2]. destruct iv as [l h]. cbn [fst snd] in *.
    exact (pz_not_client st WF cls Hc SP HSP l h a A1 A2 Hin HC).
  - destruct H2 as [E|[E|[]]]; subst iv; cbn [fst snd] in Hin.
    + revert HC. apply (wstatic_not_client st SP a WF HSP). unfold A_EMB in Hin. lia.
    + exact (blk_not_client a Hin HC).
Qed.

Theorem rt_frame_fx : rt_frame (primary_fp st cls ++ fp_emb st') lo SP m m'.
Proof.
  assert (FINE : rt_frame (primary_fp_fine st cls ++ fp_emb st') lo SP m m').
  { apply (rt_frame_pz SP _ m m' lo _ MU). intros a iv Hiv Hin. apply in_app_or in Hiv. destruct Hiv as [H1|H2]; [exact (HW1f a iv H1 Hin)|].
    right. apply in_ivs_app. right. destruct HD as [NZ ED]. unfold fp_emb. rewrite ED. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ).
    destruct H2 as [E|[E|[]]]; subst iv; cbn [fst snd] in Hin; [exists A_EMB, (A_EMB + 56)| exists d, (d + EMB_CAP)]; (split; [cbn; tauto| exact Hin]). }
  eapply rt_frame_weaken; [| exact FINE]. intros a Ha. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  unfold primary_fp_fine, primary_fp, fp_class_fine, fp_class in *. apply in_ivs_app in Ha as [Ha|Ha]; apply in_ivs_app; [left| right; exact Ha].
  pose proof (cls_facts st WF cls Hc) as (_ & _ & _ & _ & _ & C6 & _). destruct Ha as (l & h & Hin & Hr).
  destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
  - exists (rbeg st cls), (rbeg st cls + KREGIONSIZE). split; [left; reflexivity| lia].
  - exists (SH (rbeg st cls)), (SH (rbeg st cls) + KREGIONSIZE / 8). split; [right; left; reflexivity|]. pose proof (rt_SH_mono (rbeg st cls) (rbeg st cls + r_mapped (rg st cls)) ltac:(lia)). lia.
  - exists (rinfo st cls), (rinfo st cls + 128). split; [right; right; left; reflexivity| lia].
Qed.
End FRAMEX.

End CeilWrap.
