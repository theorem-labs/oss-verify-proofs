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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_spz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_mmapN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_sec_alloc1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap.
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
Lemma smapsize_facts : forall n, 0 <= n -> bprim n = false -> needed n <= 2^40 ->
  needed n = rounded8 n + 4096 /\ smapsize n = roundup (needed n) 4096 + 4096 /\ smapsize n mod 4096 = 0
  /\ needed n mod 8 = 0 /\ 65536 < needed n /\ needed n + 4096 <= smapsize n /\ smapsize n < needed n + 8192
  /\ 0x12000 <= smapsize n <= 2^40 + 8192.
Proof.
  intros n Hn HP HN. pose proof (sec_facts n HP) as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (R8 : rounded8 n mod 8 = 0 /\ n <= rounded8 n) by (unfold rounded8, roundup; Z.div_mod_to_equations; lia).
  unfold smapsize, roundup in *. rewrite H6 in *.
  assert (NB : 65536 < rounded8 n + 4096).
  { unfold bprim, is_primary, KMAXSIZE, needed0 in HP. apply Z.leb_gt in HP. rewrite H2 in HP. lia. }
  repeat split; try lia; Z.div_mod_to_equations; lia.
Qed.

Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx.
  replace 18446744073709551608 with (Z.lxor (Z.ones 64) (Z.ones 3)) by reflexivity.
  replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 3) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 3)) by lia. rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 3 + 3) with i by lia. rewrite (Z.ones_spec_high 3 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section A0.
  Variables (ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (st : rtstate) (n lo : Z) (nmv : word).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis Hn : 0 <= n.
  Hypothesis HP : bprim n = false.
  Hypothesis HN : needed n <= 2^40.
  Hypothesis CEIL0 : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ALARGE_ALLOC_STACK.
  Hypothesis NAMEC : ro_cells asegs m 0xa3e40 [C8 nmv].

  (* [comment removed for export] *)
  Definition la_frame (mm : word -> option byte) : Prop :=
    exists j, rw_cells asegs mm (bv_unsigned sp + -96) [CB 8 j; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  Lemma la_A0 : forall (POST : machine_state -> Prop) t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    (forall m1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       la_frame m1 -> stk asegs m1 lo (bv_unsigned sp + -96) -> mem_inv asegs m1 ->
       munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 ->
       evt asegs POST (MS (mkR (wz 0x36928) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                               (wz (smapsize n)) nmv x12 x13 x14 x15 x16 x17 (wz (smapsize n)) (wz (needed n)) s4e (wz 8) s6e s7e (wz 7) s9e s10 s11
                               x28 x29 x30 x31)
                          F (wz A_MMAP_ONFATAL) fc None m1 (seg_rom asegs))) ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (wz A_SECONDARY) (wz A_GSTATS) (wz (needed n)) (wz 8) a4 a5 a6 a7
                             s2e s3e s4e s5e s6e s7e s8e s9e s10 s11 t3 t4 t5 t6)
                        F (wz ALARGE_ALLOC) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros ST MI K.
    pose proof (smapsize_facts n Hn HP HN) as SF.
    pose proof (sec_obj_cells st m HR) as (j1 & j2 & j3 & SECC & MUT).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (rr_link st m HR) as HL.
    assert (GOT18 : ro_cells asegs m 0xa1f68 [C8 (Z_to_bv 64 0xa3e40)]) by (apply (R_link_at m 0xa1f68 0xa3e40 HL); vm_compute; reflexivity).
    unfold ALARGE_ALLOC, A_MMAP_ONFATAL, ALARGE_ALLOC_STACK in *. rewrite A_SECONDARY_val, A_GSTATS_val in *. cbv beta delta [wz] in *. leaf_prep.
    carve_frame 96%nat ST.
    do 12 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. fl. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. fl. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    rewrite land_align12 by lia.
    lstep. fl. lstep. fl. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    replace ((needed n + 4095) / 4096 * 4096 + 4096) with (smapsize n) by (destruct SF as (_ & -> & _); unfold roundup; lia).
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. fl. lstep. lstep. lstep. (* [comment removed for export] *)
    eapply K; [eexists; exact FR| exact ST| exact MI| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  Lemma la_R : forall (POST : machine_state -> Prop) m1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    la_frame m1 -> stk asegs m1 lo (bv_unsigned sp + -96) -> mem_inv asegs m1 ->
    (forall m2 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       stk asegs m2 lo (bv_unsigned sp) -> mem_inv asegs m2 -> munch [] m1 m2 -> wmono asegs m1 m2 ->
       evt asegs POST (MS (mkR ra sp gp tp y5 y6 y7 s0e s1e (wz 0) y11 y12 y13 y14 y15 y16 y17 s2e s3e s4e s5e s6e s7e s8e s9e s10 s11 y28 y29 y30 y31)
                          F (ret_pc ra) fc None m2 (seg_rom asegs))) ->
    evt asegs POST (MS (mkR (wz 0x36928) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            (wz 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (wz 0x36928) fc None m1 (seg_rom asegs)).
  Proof.
    intros until x31. intros [j FR] ST MI K.
    pose proof (munch_refl [] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    unfold ALARGE_ALLOC_STACK in *. rewrite A_SECONDARY_val, A_GSTATS_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep; try if_lia. (* [comment removed for export] *)
    do 11 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    eapply K; [exact ST| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma la_A1 : forall (POST : machine_state -> Prop) m1 mb v0 v1 v2 j1 v5 v6 j2 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    mem_inv asegs m1 -> AIMG_HI <= mb -> mb + smapsize n <= CEIL -> mb mod 4096 = 0 ->
    rw_cells asegs m1 0xa6c58 [C8 (Z_to_bv 64 4096); C8 v0; C8 v1; C8 v2; CB 16 j1; C8 v5; C8 v6; CB 552 j2] ->
    (forall y5 y6 y7 y13 y14 y15 y16 y17,
       evt asegs POST (MS (mkR (wz 0x36980) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y5 y6 y7 (wz A_GSTATS) (wz A_SECONDARY)
                               (wz mb) (wz 4096) (wz 250) y13 y14 y15 y16 y17
                               (wz (smapsize n)) (wz (needed n)) (wz mb) (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n))
                               (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
                          F (wz APOISON_SHADOW) fc None m1 (seg_rom asegs))) ->
    evt asegs POST (MS (mkR (wz 0x36928) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            (wz mb) x11 x12 x13 x14 x15 x16 x17 (wz (smapsize n)) (wz (needed n)) s4e (wz 8) s6e s7e (wz 7) s9e s10 s11 x28 x29 x30 x31)
                       F (wz 0x36928) fc None m1 (seg_rom asegs)).
  Proof.
    intros until x31. intros MI HB HE HA SECC K.
    pose proof (smapsize_facts n Hn HP HN) as SF.
    unfold ALARGE_ALLOC_STACK, APOISON_SHADOW, CEIL, KHIGHMEM_BEG, AIMG_HI in *. rewrite A_SECONDARY_val, A_GSTATS_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    change 4095 with (Z.ones 12). rewrite (Z.land_comm (Z.ones 12) mb), Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace (mb mod 4096) with 0 by lia.
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    rewrite (land7_mod (4096 + mb)) by lia. replace ((4096 + mb) mod 8) with 0 by lia.
    lstep. fl. lstep. lstep. fl. lstep. fl. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    rewrite !land_m8 by lia.
    replace ((0 + (4096 + mb) + needed n) / 8 * 8) with (sec_alloc_beg mb + needed n) by (unfold sec_alloc_beg, SEC_HDR; Z.div_mod_to_equations; lia).
    replace ((0 + (4096 + mb) + 7) / 8 * 8) with (4096 + mb) by (Z.div_mod_to_equations; lia).
    replace (0 + (4096 + mb) + needed n) with (sec_alloc_beg mb + needed n) by (unfold sec_alloc_beg, SEC_HDR; lia).
    replace (0 + (4096 + mb)) with (sec_alloc_beg mb) by (unfold sec_alloc_beg, SEC_HDR; lia).
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    replace (4096 + mb - mb) with 4096 by lia. replace (smapsize n + mb) with (mb + smapsize n) by lia.
    apply K.
  Qed.
End A0.


End CeilWrap.
End RTW_sec_alloc1.

(* [comment removed for export] *)
Module RTW_sec_alloc2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs RTW_sec_alloc1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section A3.
  Variables (sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m1 : word -> option byte) (n mb t k : Z) (v1 v2 v3 : word) (j1 : list byte) (nres nsc : Z) (j2 : list byte).
  Variables (j72 j80 h0 h8 h16 h24 : word) (b1 b2 b3 : byte) (j4 : list byte).
  Hypothesis Hn : 0 <= n.
  Hypothesis HP : bprim n = false.
  Hypothesis HN : needed n <= 2^40.
  Hypothesis HB : (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0.
  Hypothesis HT : (4096 <= t /\ bandf (t + 4096 <= AIMG_LO \/ AIMG_HI <= t) /\ bandf (t + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= t)) /\ t + 4096 <= CEIL.
  Hypothesis DJ : t + 4096 <= mb \/ mb + smapsize n <= t.
  Hypothesis HK : 0 <= k < 2^24.
  Hypothesis NRS : 0 <= nres < 2^64 /\ 0 <= nsc < 2^20.
  Hypothesis E0 : le4 (wz (256 * k)) = [zb 0; b1; b2; b3].
  Hypothesis E1 : le4 (wz (256 * k + 1)) = [zb 1; b1; b2; b3].

  Definition a3_post (POSTK : Z -> word -> (word -> option byte) -> Prop) : machine_state -> Prop :=
    fun ms' => exists (y5 y6 y7 y11 y15 y17 y28 y29 y30 y31 : word) (v : Z) m2,
      ms' = MS (mkR (wz 0x36994) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y5 y6 y7 (wz A_GSTATS) (wz A_SECONDARY)
                    (wz (sec_alloc_beg mb)) y11 (wz 0) (wz nsc) (wz 1) y15 (wz 0) y17
                    (wz (smapsize n)) (wz (needed n)) (wz mb) (wz mb) (wz (mb + smapsize n))
                    (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 y28 y29 y30 y31)
               F (wz 0x36a24) fc None m2 (seg_rom asegs)
      /\ POSTK v y15 m2.

  (* [comment removed for export] *)
  Definition a3_mem (v : Z) (y15 : word) (m2 : word -> option byte) : Prop :=
    munch [(t + 2872, t + 2888); (mb, mb + 32); (0xa6ec0, 0xa6ec4)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2
    /\ (exists j72' j80', rw_cells asegs m2 (t + 2872) [C8 j72'; C8 j80'])
    /\ rw_cells asegs m2 mb [C8 (wz mb); C8 (wz (smapsize n)); C8 (wz (needed n)); C8 h24]
    /\ y15 = wz v /\ 0 <= v < 2^64 /\ v mod 2^32 = 256 * k /\ le4 (wz (v + 1)) = [zb 1; b1; b2; b3]
    /\ rw_cells asegs m2 0xa6ec0 [C4 (wz (v + 1))] /\ rw_cells asegs m2 0xa6ec4 [CB 4 j4].

  Lemma la_A3 : forall (POST : machine_state -> Prop) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    mem_inv asegs m1 ->
    rw_cells asegs m1 0xa6c58 [C8 (Z_to_bv 64 4096); C8 v1; C8 v2; C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsc); CB 552 j2] ->
    rw_cells asegs m1 (t + 2872) [C8 j72; C8 j80] ->
    rw_cells asegs m1 mb [C8 h0; C8 h8; C8 h16; C8 h24] ->
    rw_cells asegs m1 0xa6ec0 [C4 (wz (256 * k))] -> rw_cells asegs m1 0xa6ec4 [CB 4 j4] ->
    (forall ms', a3_post a3_mem ms' -> evt asegs POST ms') ->
    evt asegs POST (MS (mkR (wz 0x36994) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            (wz (t + T_STATS)) x11 x12 x13 x14 x15 x16 x17
                            (wz (smapsize n)) (wz (needed n)) (wz mb) (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n))
                            (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
                       F (wz 0x36994) fc None m1 (seg_rom asegs)).
  Proof.
    intros until x31. intros MI SECC TS HDR MW MJ K.
    pose proof (smapsize_facts n Hn HP HN) as SF.
    pose proof (munch_refl [(t + 2872, t + 2888); (mb, mb + 32); (0xa6ec0, 0xa6ec4)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    unfold bandf, AIMG_LO, KLOWSHADOW_BEG, T_STATS, CEIL, KHIGHMEM_BEG, AIMG_HI, sec_alloc_beg, SEC_HDR in *. rewrite A_SECONDARY_val, A_GSTATS_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    rewrite (land7_mod (mb + 4096)) by lia. replace ((mb + 4096) mod 8) with 0 by lia.
    lstep. lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    change 4095 with (Z.ones 12). rewrite (Z.land_comm (Z.ones 12) (mb + 4096)), Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace ((mb + 4096) mod 4096) with 0 by lia.
    lstep; try if_lia. (* [comment removed for export] *)
    lstep; try if_lia. lstep; try if_lia. (* [comment removed for export] *)
    lstep. replace (mb + 4096 - 4096) with mb by lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    pose proof (sx32_256k_facts k HK) as VF. cbv zeta in VF.
    remember (sx32 (Z_to_bv 64 (256 * k))) as a5v eqn:Ea5. destruct VF as (VR & VM & V32 & _).
    pose proof (lock_word_val (bv_unsigned a5v) ltac:(lia) VM) as [LW1 LW2].
    lstep. lstep. lstep. lstep. rewrite LW1. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. rewrite LW2. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. (* [comment removed for export] *)
    rewrite (Z.shiftr_div_pow2 nsc 20), Z.div_small by lia.
    lstep; try if_lia. (* [comment removed for export] *)
    apply K. unfold a3_post, a3_mem. cbv beta delta [wz].
    do 10 eexists. exists (bv_unsigned a5v). eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [do 2 eexists; exact TS|]. split; [exact HDR|].
    split; [symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact VR|]. split; [exact V32|].
    split; [| split; [exact MW| exact MJ]].
    rewrite <- E1. apply le4_mod32; [lia| lia|]. rewrite <- V32. Z.div_mod_to_equations. lia.
  Qed.
End A3.


End CeilWrap.
End RTW_sec_alloc2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_msb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StepFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Module RTW_sec_alloc3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_msb RTW_sec_alloc1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegFold.simp_regs_raw.
(* [comment removed for export] *)

#[local] Ltac2 Set OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StepFast.SF.sf_mode := 0.
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac pos_lit_chk p := lazymatch p with xI ?q => pos_lit_chk q | xO ?q => pos_lit_chk q | xH => constr:(tt) end.
Local Ltac size_lit sz ::=
  let v := eval cbv beta iota zeta delta
      [cells_size csize length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes u32s u64s
       Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Pos.add] in sz in
  lazymatch v with Z0 => v | Zpos ?p => let _ := pos_lit_chk p in v | Zneg ?p => let _ := pos_lit_chk p in v end.

Section A4.
  Variables (ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m2 : word -> option byte) (n mb k v lo : Z) (PA : Z) (v2 v3 : word) (j1 : list byte) (nres nsc : Z) (j2 : list byte).
  Variables (h24 jp : word) (jg : list byte) (b1 b2 b3 : byte) (j4 jfr : list byte).
  Hypothesis Hn : 0 <= n.
  Hypothesis HP : bprim n = false.
  Hypothesis HN : needed n <= 2^40.
  Hypothesis HB : (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0.
  Hypothesis HPA : (AIMG_HI <= PA /\ bandf (PA + PTRARR_RES_SIZE <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= PA)) /\ PA + PTRARR_RES_SIZE <= CEIL /\ 8 * nsc + 8 <= PTRARR_RES_SIZE.
  Hypothesis DJ : PA + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= PA.
  Hypothesis NRS : 0 <= nres < 2^64 /\ 0 <= nsc < 2^20.
  Hypothesis HK : k = Z.log2 (smapsize n).
  Hypothesis HV : 0 <= v < 2^64 /\ le4 (wz (v + 1)) = [zb 1; b1; b2; b3].
  Hypothesis CEIL0 : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ALARGE_ALLOC_STACK.

  Definition a4_post : machine_state -> Prop :=
    fun ms' => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m3,
      ms' = MS (mkR ra sp gp tp y5 y6 y7 s0e s1e (wz (sec_alloc_beg mb)) y11 y12 y13 y14 y15 y16 y17 s2e s3e s4e s5e s6e s7e s8e s9e s10 s11 y28 y29 y30 y31)
               F (ret_pc ra) fc None m3 (seg_rom asegs)
      /\ munch [(0xa6c58 + 56, 0xa6c58 + 620); (mb + 24, mb + 32); (PA + 8 * nsc, PA + 8 * nsc + 8); (0xa6ec8 + 16, 0xa6ec8 + 32)] m2 m3
      /\ wmono asegs m2 m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo (bv_unsigned sp)
      /\ (exists j2', rw_cells asegs m3 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 v2; C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsc + 1)); CB 552 j2'])
      /\ rw_cells asegs m3 (mb + 24) [C8 (wz nsc)]
      /\ rw_cells asegs m3 (PA + 8 * nsc) [C8 (wz mb)]
      /\ (exists jg', rw_cells asegs m3 0xa6ec8 [CB 40 jg'])
      /\ rw_cells asegs m3 0xa6ec0 [C1 (zb 0); CB 3 [b1; b2; b3]; CB 4 j4].

  Lemma la_A4 : forall x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x20 x28 x29 x30 x31,
    mem_inv asegs m2 ->
    rw_cells asegs m2 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 v2; C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsc); CB 552 j2] ->
    rw_cells asegs m2 (mb + 24) [C8 h24] ->
    rw_cells asegs m2 (PA + 8 * nsc) [C8 jp] ->
    rw_cells asegs m2 0xa6ec8 [CB 40 jg] ->
    rw_cells asegs m2 0xa6ec0 [C4 (wz (v + 1))] -> rw_cells asegs m2 0xa6ec4 [CB 4 j4] ->
    rw_cells asegs m2 (bv_unsigned sp + -96) [CB 8 jfr; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
    stk asegs m2 lo (bv_unsigned sp + -96) ->
    evt asegs a4_post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            (wz (sec_alloc_beg mb)) x11 x12 (wz nsc) x14 x15 x16 x17
                            (wz (smapsize n)) (wz (63 - k)) x20 (wz mb) (wz (mb + smapsize n))
                            (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
                          F (wz 0x36ad0) fc None m2 (seg_rom asegs)).
  Proof.
    intros until x31. intros MI SECC HDR PC GST MW MJ FR ST.
    pose proof (smapsize_facts n Hn HP HN) as SF.
    pose proof (log2_range (smapsize n) 16 40 ltac:(lia) ltac:(lia)) as LR. rewrite <- HK in LR.
    pose proof (munch_refl [(0xa6c58 + 56, 0xa6c58 + 620); (mb + 24, mb + 32); (PA + 8 * nsc, PA + 8 * nsc + 8); (0xa6ec8 + 16, 0xa6ec8 + 32)] m2) as MU.
    pose proof (wmono_refl asegs m2) as WM.
    unfold ALARGE_ALLOC_STACK, CEIL, KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE, sec_alloc_beg, SEC_HDR in *. rewrite A_SECONDARY_val, A_GSTATS_val in *.
    cbv beta delta [wz] in *. leaf_prep.
    set (q := PA + 8 * nsc) in *.
    lstep. lstep. (* [comment removed for export] *)
    rewrite HK, (proj2 (popc_T_val (Z.log2 (smapsize n)) ltac:(rewrite <- HK; exact LR))). rewrite <- HK.
    lstep. (* [comment removed for export] *)
    lstep. lstep. replace (PA + Z.shiftl nsc 3) with q by (subst q; rewrite Z.shiftl_mul_pow2 by lia; lia). (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) _ _ _ _ ?mm _) =>
      assert (CONT : forall amax : word,
        evt asegs a4_post (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 amax x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                              F (Z_to_bv 64 0x36b18) fc None mm (seg_rom asegs)))
    end.
    2:{ lstep. if_cases KM; [|lstep]; apply CONT. }
    intros amax.
    (* [comment removed for export] *)
    lazymatch goal with SECC : rw_cells _ ?mm 683096 ?cs |- _ => rename mm into mA end.
    lazymatch type of SECC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: [CB 520 ?jj]) =>
      apply (rw_cells_split_CB _ _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] _ _ [] [8; Z.to_nat (8 * k); 8; Z.to_nat (504 - 8 * k)]%nat) in SECC; [| cbn [sum_nat]; lia];
      cbn [mk_CB_cells app] in SECC
    end.
    lazymatch type of SECC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?rest) =>
      pose proof (proj1 (rw_cells_app asegs mA 683096 [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] rest) SECC) as [SLO BSL]
    end.
    clear SECC. cbn [cells_size Cells.csize Nat.add] in BSL.
    set (q8 := 683096 + 8 * k) in *.
    match type of BSL with rw_cells _ _ ?a _ => replace a with (q8 + 104) in BSL by (subst q8; lia) end.
    lstep. lstep. (* [comment removed for export] *)
    replace (683096 + Z.shiftl k 3) with q8 by (subst q8; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. amo_step. (* [comment removed for export] *)
    lstep. amo_step. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    pose proof (mutex_cells_to _ _ _ _ _ _ _ _ (proj2 HV) MW MJ) as MX. clear MW MJ.
    lstep. (* [comment removed for export] *)
    do 11 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    lazymatch type of SLO with rw_cells _ _ _ ?cs1 => lazymatch type of BSL with rw_cells _ _ ?a ?cs2 =>
      replace a with (683096 + Z.of_nat (cells_size cs1)) in BSL by (cbn [cells_size Cells.csize]; subst q8; lia);
      pose proof (proj2 (rw_cells_app asegs m3 683096 cs1 cs2) (conj SLO BSL)) as SECC3 end end.
    clear SLO BSL. cbn [app] in SECC3.
    lazymatch type of SECC3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      pose proof (rw_cells_merge asegs m3 683096 [c0; c1; c2; c3; c4; c5; c6] rest [] ) as MG;
      cbn [app] in MG; rewrite ?app_nil_r in MG; specialize (MG SECC3); rewrite ?app_nil_r in MG; cbn [app] in MG
    end.
    match type of MG with rw_cells _ _ _ [_; _; _; _; _; _; _; CB ?sz ?bs] => replace sz with 552%nat in MG by (cbn [cells_size Cells.csize]; lia) end.
    (* [comment removed for export] *)
    lazymatch type of GST with rw_cells _ _ _ ?cs =>
      pose proof (rw_cells_merge asegs m3 683720 [] cs [] ) as MG2; cbn [app] in MG2; rewrite ?app_nil_r in MG2; specialize (MG2 GST); rewrite ?app_nil_r in MG2
    end.
    match type of MG2 with rw_cells _ _ _ [CB ?sz ?bs] => replace sz with 40%nat in MG2 by (cbn [cells_size Cells.csize]; lia) end.
    apply evt_done. unfold a4_post. cbv beta delta [wz].
    do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [eexists; exact MG|]. split; [exact HDR|]. split; [exact PC|]. split; [eexists; exact MG2|]. exact MX.
  Qed.
End A4.


End CeilWrap.
End RTW_sec_alloc3.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artO.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_state.
Module RTW_sec_alloc5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artO OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_state OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
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
Section TR.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWF st.
Variables (mb n : Z).
Hypothesis HP : bprim n = false.
Hypothesis Hn : 0 <= n.
Hypothesis Hneed : needed n <= 2^40.
Hypothesis Hal : mb mod 4096 = 0.
Hypothesis Hlo : ablk mb (mb + smapsize n).   (* [comment removed for export] *)
Hypothesis Hhi : mb + smapsize n <= CEIL.
Hypothesis FRESH : forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb.
Hypothesis ROOM : nsec st < 2^20.
Let stR := mkRT a1 a2 a3 a4 a5 a6 a7 (a8 + (if zlen a9 =? a8 then 2^14 else 0)) (a9 ++ [(mb, n)]) a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP ((mb, n) :: SP) QP b4 b5.

Lemma R_block_secreg : forall m md A k, In (A, k) (all_blocks st) -> R_block st m md A k -> R_block stR m md A k.
Proof.
  intros m md A k HB (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [| split; [exact H4| exact H5]].
  intros HPk. destruct (H3 HPk) as (V1 & V2 & HC). split; [exact V1|]. split; [exact V2|].
  pose proof (wk_block st (wf_blocks_ok st WF) (A, k) HB) as WB. unfold wf_block in WB. cbn [fst snd] in WB. destruct WB as (_ & _ & _ & HS).
  specialize (HS HPk).
  replace (sec_index stR (b_map_beg A)) with (sec_index st (b_map_beg A)); [exact HC|].
  unfold sec_index. cbn [st_sec st stR]. symmetry. apply index_of_app_old. apply in_map_iff. exists (b_map_beg A, k). split; [reflexivity| exact HS].
Qed.

Lemma RTREP_nsec_secreg : forall m, RTREP_nsec st m -> RTREP_nsec stR m.
Proof.
  intros m (X1 & X2 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X13 & X14 & X15 & X16).
  unfold RTREP_nsec.
  split; [exact X1|]. split; [exact X2|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X8|].
  split. { intros A k Hin. apply R_block_secreg; [unfold all_blocks; apply in_or_app; left; exact Hin| exact (X9 A k Hin)]. }
  split. { destruct X10 as [Q1 Q2]. split.
           - intros A k Hin. apply R_block_secreg; [| exact (Q1 A k Hin)]. unfold all_blocks. apply in_or_app; right. apply in_or_app; left. exact Hin.
           - intros A k Hin. apply R_block_secreg; [| exact (Q2 A k Hin)]. unfold all_blocks. apply in_or_app; right. apply in_or_app; right. exact Hin. }
  split; [exact X11|]. split; [exact X13|]. split; [exact X14|]. split; [exact X15| exact X16].
Qed.
End TR.

Lemma RTREP_nsec_secreg' : forall st mb n m, RTWF st -> RTREP_nsec st m -> RTREP_nsec (st_secreg st mb n) m.
Proof. intros st mb n m WF H. destruct st. eapply RTREP_nsec_secreg; [exact WF| exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cj_pres_trans : forall sp0 LB LF SP m1 m2 m3,
  cj_pres sp0 LB LF SP m1 m2 -> cj_pres sp0 LB LF SP m2 m3 -> cj_pres sp0 LB LF SP m1 m3.
Proof.
  intros sp0 LB LF SP m1 m2 m3 H1 H2 a Ha HC. destruct (H1 a Ha HC) as [E1 V1]. destruct (H2 a Ha HC) as [E2 V2].
  split; [rewrite E2; exact E1| auto].
Qed.
Lemma cli_pres_trans : forall st SP m1 m2 m3, cli_pres st SP m1 m2 -> cli_pres st SP m2 m3 -> cli_pres st SP m1 m3.
Proof. intros st SP m1 m2 m3. unfold cli_pres. apply cj_pres_trans. Qed.

(* [comment removed for export] *)
Lemma cj_pres_open : forall sp0 LB LF SP zf lo hi m,
  (forall a, 0 <= a < 2^64 -> cj_client_addr sp0 LB LF SP a -> lo <= a < hi -> m (wa a) <> None) ->
  cj_pres sp0 LB LF SP m (open_mem zf lo hi m).
Proof.
  intros sp0 LB LF SP zf lo hi m HV a Ha HC. split.
  - unfold open_mem. destruct (m (wa a)) as [b|] eqn:E; [reflexivity|].
    destruct (Z.leb_spec0 lo (bv_unsigned (wa a))) as [L|L]; destruct (Z.ltb_spec0 (bv_unsigned (wa a)) hi) as [U|U]; cbn [andb]; try reflexivity.
    exfalso. apply (HV a Ha HC); [rewrite wa_unsigned in L, U by lia; lia| exact E].
  - intros V. apply (wmono_open asegs zf lo hi m m (wmono_refl asegs m)). exact V.
Qed.

Lemma rt_frame_open : forall FP lo SP zf wlo whi m,
  (forall a, wlo <= a < whi -> in_ivs FP a) -> rt_frame FP lo SP m (open_mem zf wlo whi m).
Proof.
  intros FP lo SP zf wlo whi m HI a Ha HS HN. unfold open_mem. destruct (m (wa a)) as [b|] eqn:E; [reflexivity|].
  destruct (Z.leb_spec0 wlo (bv_unsigned (wa a))) as [L|L]; destruct (Z.ltb_spec0 (bv_unsigned (wa a)) whi) as [U|U]; cbn [andb]; try reflexivity.
  exfalso. apply HN. apply HI. rewrite wa_unsigned in L, U by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLI2.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hm_not_client : forall lo hi a, blockfree st lo hi -> framefree st lo hi -> oclr lo hi -> hi <= CEIL ->
  lo <= a < hi -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros lo hi a HBF HFF H1 H2 Ha HC. pose proof (oclr_lin lo hi H1 ltac:(lia)) as (L1 & L2 & L3). unfold CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_LO, AIMG_HI in *.
  destruct HC as [H|[H|[(A & n0 & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. lia.
  - destruct (blockfree_lb st WF lo hi HBF A n0 Hb); lia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    destruct Hr as [Hr|Hr].
    + destruct (framefree_lf st WF lo hi HFF F k Hb); lia.
    + assert (8 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
      pose proof (rt_SH_bounds (F + fsz k) ltac:(blia)) as B. rewrite (rt_SH_aligned_add F (fsz k) AL) in B. pose proof (rt_SH_bounds F ltac:(blia)) as B0. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. lia.
Qed.

(* [comment removed for export] *)
Lemma hmsh_not_client : forall lo hi a, framefree st lo hi -> 0 <= lo -> hi <= CEIL ->     (* [comment removed for export] *)
  SH lo <= a < SH hi -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros lo hi a HFF H1 H2 Ha HC. 
  pose proof (SH_mono 0 lo H1) as M1. pose proof (SH_mono hi CEIL H2) as M2.
  change (SH 0) with 0x7fff8000 in M1. rewrite SH_CEIL in M2.
  unfold CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *.
  destruct HC as [H|[H|[(A & n0 & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. lia.
  - assert (HB : In (A, n0) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n0 HB) as (_ & _ & X0 & X & Y & _). unfold usz, KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    assert (8 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [blia|].
    rewrite <- (rt_SH_aligned_add F (fsz k) AL) in Hr.
    destruct (framefree_sh st WF lo hi HFF F k Hb) as [D|D].
    + pose proof (SH_mono hi F D). lia.
    + pose proof (SH_mono (F + fsz k) lo D). lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. lia.
Qed.

(* [comment removed for export] *)
Lemma pa_not_client : forall a, st_pa st <= a < st_pa st + PTRARR_RES_SIZE -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha. pose proof (pa_range st WF) as (P1 & P2 & _).
  apply (hm_not_client (st_pa st) (st_pa st + PTRARR_RES_SIZE)); [apply pa_blockfree; exact WF| apply pa_framefree; exact WF| apply oclr_of_ablk; exact P1| unfold CEIL; lia| lia].
Qed.

(* [comment removed for export] *)
Variables (mb sz : Z).
Hypothesis FRESH : forall r, In r (rt_ranges st) -> mb + sz <= fst r \/ snd r <= mb.
Lemma fresh_blockfree : blockfree st mb (mb + sz).
Proof.
  intros A n0 HB. pose proof (block_geom st WF A n0 HB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Gp & Gs).
  destruct (bprim n0) eqn:EP.
  - destruct (Gp eq_refl) as (_ & _ & _ & Q1 & Q2 & _).
    destruct (FRESH (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity)); cbn [fst snd] in *; lia.
  - destruct (Gs eq_refl) as (S1 & T1 & _).
    destruct (FRESH (b_lo A n0, b_lo A n0 + smapsize n0)); cbn [fst snd] in *; [| lia| lia].
    unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; left. apply in_map_iff. exists (b_lo A n0, n0). auto.
Qed.
Lemma fresh_framefree : framefree st mb (mb + sz).
Proof.
  unfold framefree. destruct (FRESH (st_fs st, st_fs st + FS_TOTAL)); cbn [fst snd] in *; [| lia| lia].
  unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (st_fs st, FS_TOTAL). split; [reflexivity|]. exact (wb_fs_loose st (wf_base_ok st WF)).
Qed.
Hypothesis HMB : ablk mb (mb + sz).   (* [comment removed for export] *)
Lemma fresh_not_client : forall a, mb <= a < mb + sz -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof. intros a Ha. apply (hm_not_client mb (mb + sz)); [apply fresh_blockfree| apply fresh_framefree| apply oclr_of_ablk; exact HMB| unfold CEIL; exact (ablk_top _ _ HMB)| lia]. Qed.
Lemma fresh_shadow_not_client : forall a, SH mb <= a < SH (mb + sz) -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof. intros a Ha. destruct (ablk_lin _ _ HMB) as (_ & B0 & B1 & _). apply (hmsh_not_client mb (mb + sz)); [apply fresh_framefree| lia| unfold CEIL; lia| lia]. Qed.
(* [comment removed for export] *)
Lemma client_highshadow_vis : forall m a, RTREP st m -> 0 <= a < 2^64 -> cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a ->
  KLOWSHADOW_BEG <= a < SH CEIL -> m (wa a) <> None.   (* [comment removed for export] *)
Proof.
  intros m a HR Ha HC Hs. rewrite SH_CEIL in Hs. unfold CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in *.
  destruct HC as [H|[H|[(A & n0 & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - exfalso. lia.
  - exfalso. unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. lia.
  - exfalso. assert (HB : In (A, n0) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n0 HB) as (_ & _ & X0 & X & Y & _). unfold usz, KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    assert (8 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [exfalso; blia|].
    pose proof (rr_fs st m HR) as (_ & V & _).
    rewrite <- (rt_SH_aligned_add F (fsz k) AL) in Hr.
    pose proof (SH_mono (st_fs st + FS_FRAMES_OFF) F ltac:(unfold FS_FRAMES_OFF; lia)) as M1.
    pose proof (SH_mono (F + fsz k) (st_fs st + FS_TOTAL) ltac:(lia)) as M2.
    destruct V as (_ & _ & V). destruct (V a ltac:(lia)) as [W _]. apply (wview_noseg_some m (wa a)); [apply noseg_Z; unfold AIMG_HI; lia| exact W].
  - exfalso. unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. lia.
Qed.
End CLI2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_site_range' : forall st, RTWF st -> nsec st < 2^20 -> sec_grow st = true ->
  st_pa st <= st_pa st + 8 * st_nreserved st /\ st_pa st + 8 * st_nreserved st + PTRARR_BLOCK <= st_pa st + PTRARR_RES_SIZE
  /\ (st_pa st + 8 * st_nreserved st) mod 4096 = 0 /\ ablk (st_pa st) (st_pa st + PTRARR_RES_SIZE) /\ st_pa st + PTRARR_RES_SIZE <= CEIL.
Proof. intros st WF ROOM HG. unfold sec_grow, nsec in HG. destruct st. unshelve (eapply grow_site_range; eauto); exact 0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section REG.
Variables (st : rtstate) (mb n : Z) (W : list (Z * Z)) (mv m : word -> option byte) (nres9 : Z).
Hypothesis WF : RTWF st.
Hypothesis HP : bprim n = false.
Hypothesis Hn : 0 <= n.
Hypothesis Hneed : needed n <= 2^40.
Hypothesis Hal : mb mod 4096 = 0.
Hypothesis Hlo : ablk mb (mb + smapsize n).   (* [comment removed for export] *)
Hypothesis Hhi : mb + smapsize n <= CEIL.
Hypothesis FRESH : forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb.
Hypothesis MU : munch W mv m.
Hypothesis WM : wmono asegs mv m.
Hypothesis Enres : nres9 = st_nreserved st + (if sec_grow st then 2^14 else 0).
Hypothesis ROOM : nsec st < 2^20.

Lemma R_alloc_secreg_intro : forall j1 j2 j3 jg,
  R_alloc st mv ->
  disjoint_from W A_ALLOC 64 -> disjoint_from W A_QUAR 256 -> disjoint_from W A_MAXUSERSZ 13 ->
  rw_cells asegs m A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 nres9; W8 (nsec st + 1); CB 552 j2; W1 0; CB 7 j3] ->
  rw_cells asegs m A_GSTATS [CB 40 jg] ->
  R_alloc (st_secreg st mb n) m.
Proof.
  intros j1 j2 j3 jg HA D1 D2 D3 SEC GST.
  destruct HA as ((k1 & k2 & k3 & X1) & _ & _ & (l1 & l2 & l3 & l4 & X4) & X5).
  pose proof (st_secreg_fields st mb n) as (_ & _ & E3 & E4 & _ & _ & _ & _ & _ & _ & _ & E12).
  unfold R_alloc. rewrite E4, E3, E12, <- Enres.
  replace (st_pbase (st_secreg st mb n)) with (st_pbase st) by (destruct st; reflexivity).
  replace (st_spacebeg (st_secreg st mb n)) with (st_spacebeg st) by (destruct st; reflexivity).
  replace (st_qglobal (st_secreg st mb n)) with (st_qglobal st) by (destruct st; reflexivity).
  split; [exists k1, k2, k3; eapply rw_cells_transport; [exact X1| exact MU| exact WM| exact D1]|].
  split; [exists j1, j2, j3; exact SEC|].
  split; [exists jg; exact GST|].
  split; [exists l1, l2, l3, l4; eapply rw_cells_transport; [exact X4| exact MU| exact WM| exact D2]|].
  eapply (ro_cells_transport asegs W mv m); [exact X5| exact MU| exact D3].
Qed.

Lemma R_ptrarr_secreg_intro :
  R_ptrarr st mv -> WOK_ptrarr st W ->
  vis m (st_pa st) (st_pa st + 8 * nres9) ->
  rw_cells asegs m (st_pa st + 8 * nsec st) [W8 mb] ->
  vis m mb (mb + smapsize n) -> vis m (SH mb) (SH mb + smapsize n / 8) ->
  rw_cells asegs m mb [W8 mb; W8 (smapsize n); W8 (needed n); W8 (nsec st)] ->
  R_ptrarr (st_secreg st mb n) m.
Proof.
  intros (V & HC & HS) [K KS] VPA PC VM VSH HDR.
  pose proof (st_secreg_fields st mb n) as (E1 & E2 & E3 & E4 & _ & _ & _ & _ & _ & _ & _ & E12).
  pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5).
  unfold R_ptrarr. rewrite E4, E3, E12, E2, <- Enres.
  split; [exact VPA|]. split.
  - intros i Hi. destruct (Z_lt_le_dec i (nsec st)) as [L|L].
    + rewrite (sec_nth_old' st mb n) by first [assumption| lia]. eapply rw_cells_transport; [exact (HC i ltac:(lia))| exact MU| exact WM| exact (K i ltac:(lia))].
    + replace i with (nsec st) by lia. rewrite (sec_nth_new' st mb n) by first [assumption| lia]. cbn [fst]. exact PC.
  - intros e [<-|He].
    + cbn [fst snd]. split; [exact VM|]. split; [exact VSH|].
      rewrite (sec_index_new' st mb n) by first [assumption| lia]. exact HDR.
    + destruct (HS e He) as (V1 & V2 & HCe). destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
      destruct (ws_entry st (wf_sec_ok st WF) e HE) as (X1 & X2 & X3 & _).
      pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as RG. cbn [fst snd] in RG.
      specialize (RG ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
      pose proof (rt_SH_bounds (fst e) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in *; blia)).
      split; [eapply stk_wmono_noseg; [exact V1| exact WM| exact (ablk_img _ _ (proj1 (sec_range st WF e HE)))]|].
      split; [eapply stk_wmono_noseg; [exact V2| exact WM| unfold AIMG_HI in *; lia]|].
      rewrite (sec_index_old' st mb n); try assumption; [| apply in_map_iff; exists e; split; [reflexivity| exact HE]].
      eapply rw_cells_transport; [exact HCe| exact MU| exact WM| exact (KS e He)].
Qed.
End REG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vis_c8x2 : forall m lo hi a, stk asegs m lo hi -> lo <= a -> a + 16 <= hi ->
  exists v0 v1 : word, rw_cells asegs m a [C8 v0; C8 v1].
Proof.
  intros m lo hi a ST H1 H2.
  destruct (vis_c8 m lo hi a ST ltac:(lia) ltac:(lia)) as [v0 R0].
  destruct (vis_c8 m lo hi (a + 8) ST ltac:(lia) ltac:(lia)) as [v1 R1].
  exists v0, v1. apply (proj2 (RT_kit.rw_cells_app m a [C8 v0] [C8 v1])). split; [exact R0| exact R1].
Qed.
Lemma vis_c8x4 : forall m lo hi a, stk asegs m lo hi -> lo <= a -> a + 32 <= hi ->
  exists v0 v1 v2 v3 : word, rw_cells asegs m a [C8 v0; C8 v1; C8 v2; C8 v3].
Proof.
  intros m lo hi a ST H1 H2.
  destruct (vis_c8x2 m lo hi a ST ltac:(lia) ltac:(lia)) as (v0 & v1 & R0).
  destruct (vis_c8x2 m lo hi (a + 16) ST ltac:(lia) ltac:(lia)) as (v2 & v3 & R1).
  exists v0, v1, v2, v3. apply (proj2 (RT_kit.rw_cells_app m a [C8 v0; C8 v1] [C8 v2; C8 v3])). split; [exact R0| exact R1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sub_fp_nil : forall W', sub_fp [] W'.
Proof. intros W' x _. exact I. Qed.
Lemma outside_In : forall W lo hi x, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[l h] W IH]; intros lo hi x HO HI; [destruct HI|].
  cbn in HO. destruct HO as [H1 H2]. destruct HI as [E|HI]; [injection E; intros; subst; exact H1| exact (IH lo hi x H2 HI)].
Qed.
Lemma sub_fp_cons_in : forall lo hi W W' lo' hi', In (lo', hi') W' -> lo' <= lo -> hi <= hi' -> sub_fp W W' -> sub_fp ((lo, hi) :: W) W'.
Proof.
  intros lo hi W W' lo' hi' HI H1 H2 HS x HO. cbn. split; [| exact (HS x HO)].
  pose proof (outside_In W' lo' hi' x HO HI). lia.
Qed.

(* [comment removed for export] *)
Lemma vis_of_CB : forall m A k bs, 0 <= k -> rw_cells asegs m A [CB (Z.to_nat k) bs] -> stk asegs m A (A + k).
Proof.
  intros m A k bs Hk H. pose proof (stk_of_rw_cells asegs m A _ H) as V. cbn [cells_size Cells.csize] in V.
  rewrite Nat.add_0_r, Z2Nat.id in V by lia. exact V.
Qed.

(* [comment removed for export] *)
Lemma wstatic_not_client' : forall st SP a, RTWF st -> CEIL <= SP -> 0xa6c18 <= a < 0x5cc8d0 ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros st SP a WF HSP Ha HC. unfold CEIL in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H.
    destruct H as [H|[H|(H1 & H2 & H3)]]; [lia| lia|]. apply H2. exists 0xa6c18, 0x5cc8d0. split; [right; left; reflexivity| lia].
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n HB) as (_ & _ & X0 & X & Y & _). unfold usz, KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    change FS_FRAMES_OFF with 36864 in X. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    assert (8 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [blia|].
    pose proof (rt_SH_bounds F ltac:(blia)) as B. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. lia.
Qed.


End CeilWrap.
End RTW_sec_alloc5.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison2.
Module RTW_sec_dealloc1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMadv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AMEMTOSHADOW2 : Z := 0x541e8.   (* [comment removed for export] *)
Definition ARELEASE_PAGES : Z := 0x6f430.  (* [comment removed for export] *)
Definition AFLUSH_SHADOW : Z := 0x5419c.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma memtoshadow2_ok :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z),
  icpt_cells m -> mem_inv asegs m ->
  a0 = Z_to_bv 64 p -> addr_in_mem p ->
  evt asegs (fun ms' => exists a1' a2' a3' a4' a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (SH p)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMTOSHADOW2) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros IC MI -> AR.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  icpt_split IC.
  assert (R47 : 0 <= p < 2^47) by (destruct AR; unfold KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END in *; lia).
  unfold AMEMTOSHADOW2.
  do 8 zstep. fold_lits.
  (if_cases K; zify_cond K).
  - (* [comment removed for export] *) zstep. zstep. zstep.
    apply evt_done. do 8 eexists. split; [| split; [exact MU| split; [exact WM| exact MI]]].
    unfold mkR. rewrite <- SH_shiftr, (Z.add_comm (Z.shiftr p 3)). reflexivity.
  - (* [comment removed for export] *)
    destruct AR as [AR|AR]; [exfalso; lia|].
    unfold KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END in AR.
    do 8 zstep. fold_lits. sh_if_true.
    do 6 zstep. fold_lits.
    sh_if_false. zstep. fold_lits. sh_if_false.
    zstep. zstep. zstep.
    apply evt_done. do 8 eexists. split; [| split; [exact MU| split; [exact WM| exact MI]]].
    unfold mkR. rewrite <- SH_shiftr, (Z.add_comm (Z.shiftr p 3)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PAGE_MASK : Z := 18446744073709547520.
Definition rp_beg (b : Z) : Z := Z.land (b + 4095) PAGE_MASK.   (* [comment removed for export] *)
Definition rp_end (e : Z) : Z := Z.land e PAGE_MASK.            (* [comment removed for export] *)

Lemma rp_beg_val : forall b, 0 <= b -> b + 4096 < 2^64 -> rp_beg b = (b + 4095) / 4096 * 4096.
Proof. intros b H0 H1. unfold rp_beg, PAGE_MASK. apply land_align12. lia. Qed.
Lemma rp_end_val : forall e, 0 <= e < 2^64 -> rp_end e = e / 4096 * 4096.
Proof. intros e H. unfold rp_end, PAGE_MASK. apply land_align12. exact H. Qed.

(* [comment removed for export] *)
Definition madv_gate (mo : Model) (G : list (Z * Z)) (A n : Z) : Prop :=
  AIMG_HI <= A /\ A + n <= alloc_ceiling
  /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true
  /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true
  /\ region_free (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 n) = true
  /\ (forall x : word, A <= bv_unsigned x < A + n -> in_rangesb (m_vm_lazy mo) x = true -> in_winb G x = true).

Section RELEASE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (lo b e : Z).
  Hypothesis PC : poison_cells mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 32 <= bv_unsigned sp.
  Hypothesis HBE : 0 <= b /\ b + 4096 < 2^64 /\ 0 <= e < 2^64.
  Hypothesis GATE : rp_beg b < rp_end e -> madv_gate mo G (rp_beg b) (rp_end e - rp_beg b).

  Lemma release_pages_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    (forall (x10 x11 x12 x13 x17 : word) (m' : word -> option byte),
       mem_inv asegs m' -> munch [(bv_unsigned sp - 32, bv_unsigned sp); (rp_beg b, rp_end e)] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) mo (mkG G R)) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 ARELEASE_PAGES) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P K. destruct HBE as (Hb0 & Hb1 & He). destruct LO as [CEIL SPB].
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (rp_beg b, rp_end e)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    poison_split PC. unfold ARELEASE_PAGES.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 32%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 6 zstep. (* [comment removed for export] *)
    zstep. zstep. fold_lits. zstep. fold_lits. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. sh_if_true. (* [comment removed for export] *)
    zstep. zstep. fold_lits. zstep. sh_if_false. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    fold PAGE_MASK. fold (rp_beg b). fold (rp_end e).
    zstep. (if_cases KB; zify_cond KB). (* [comment removed for export] *)
    - (* [comment removed for export] *)
      do 6 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply K; [exact MI| exact MU| exact WM| exact ST].
    - (* [comment removed for export] *)
      assert (RB : rp_beg b = (b + 4095) / 4096 * 4096) by (apply rp_beg_val; lia).
      assert (RE : rp_end e = e / 4096 * 4096) by (apply rp_end_val; lia).
      assert (KB' : rp_beg b < rp_end e) by (rewrite !Z.mod_small in KB by (rewrite ?RB, ?RE; Z.div_mod_to_equations; lia); exact KB).
      destruct (GATE KB') as (GA & GC & G1 & G2 & G3 & G4). unfold AIMG_HI in GA.
      assert (RA : rp_beg b mod 4096 = 0 /\ (rp_end e - rp_beg b) mod 4096 = 0) by (rewrite RB, RE; Z.div_mod_to_equations; lia).
      zstep. zstep. do 6 zstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      do 2 zstep. fold_lits. zstep. sh_if_false. (* [comment removed for export] *)
      zstep. zstep. sh_if_true. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step_ecall. cbv beta.
      eapply lscps_madvise_dontneed with (A := rp_beg b) (len := rp_end e - rp_beg b).
      { unfold at_madvise. repeat split; reflexivity. }
      { lia. } { lia. } { lia. } { lia. }
      { rewrite pru_id by lia. lia. } { rewrite pru_id by lia. exact G1. } { rewrite pru_id by lia. exact G2. } { rewrite pru_id by lia. exact G3. }
      { rewrite pru_id by lia. replace (rp_beg b + (rp_end e - rp_beg b)) with (rp_beg b + (rp_end e - rp_beg b)) by lia. exact G4. }
      rewrite pru_id by lia.
      apply lscps_step_evt. sys_nret. fixMI.
      zstep. zstep. (* [comment removed for export] *)
      apply evt_done. eapply K; [exact MI| exact MU| exact WM| exact ST].
      Unshelve. apply (ro_addr_noseg asegs). apply asegs_noseg_high. unfold AIMG_HI. lia.
  Qed.
End RELEASE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FLUSH.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (lo p sz : Z).
  Hypothesis IC : icpt_cells mv.
  Hypothesis PC : poison_cells mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 64 <= bv_unsigned sp.
  Hypothesis HP : ablk p (p + sz) /\ 0 <= sz.
  Hypothesis GATE : rp_beg (SH p) < rp_end (SH (p + sz)) -> madv_gate mo G (rp_beg (SH p)) (rp_end (SH (p + sz)) - rp_beg (SH p)).

  Lemma flush_shadow_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    (forall (x5 x10 x11 x12 x13 x14 x15 x16 x17 : word) (m' : word -> option byte),
       mem_inv asegs m' -> munch [(bv_unsigned sp - 64, bv_unsigned sp); (rp_beg (SH p), rp_end (SH (p + sz)))] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) mo (mkG G R)) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AFLUSH_SHADOW) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P K. destruct HP as [HB Hsz]. destruct LO as [CEIL SPB].
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (ablk_lin _ _ HB) as (B1 & B2 & B3 & B4). pose proof (ablk_disj_band _ _ HB) as BD.
    unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in B1, BD. pose proof (@alloc_ceiling_hi ACEIL) as CH.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    unfold AFLUSH_SHADOW.
    apply lscps_step_evt.
    carve_frame 32%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 7 zstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (IC1 : icpt_cells mm) by (eapply icpt_cells_munch; [exact IC| exact MU|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
      assert (PC1 : poison_cells mm) by (eapply poison_cells_munch; [exact PC| exact MU|]; unfold poison_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
    end.
    zstep. (* [comment removed for export] *)
    call memtoshadow2_ok; [exact IC1| exact MI| reflexivity| unfold addr_in_mem, KHIGHMEM_BEG, KHIGHMEM_END; lia|].
    zstep. zstep. (* [comment removed for export] *) rewrite (Z.add_comm sz p).
    zstep. (* [comment removed for export] *)
    call memtoshadow2_ok; [exact IC1| exact MI| reflexivity| unfold addr_in_mem, KHIGHMEM_BEG, KHIGHMEM_END; lia|].
    zstep. zstep. (* [comment removed for export] *)
    do 6 zstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    pose proof (rt_SH_bounds p ltac:(lia)) as SB1. pose proof (rt_SH_bounds (p + sz) ltac:(lia)) as SB2.
    apply evt_done.
    eapply (release_pages_spec) with (lo := lo) (b := SH p) (e := SH (p + sz));
      [ exact PC1 | exact MI | exact ST | split; [exact CEIL| lia] | lia | exact GATE | ].
    intros y10 y11 y12 y13 y17 m' MI' MU' WM' ST'.
    eapply K; [exact MI'| | eapply wmono_trans; [exact WM| exact WM']| exact ST'].
    eapply munch_trans.
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn. intros; lia.
    - eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn. intros; lia.
  Qed.
End FLUSH.


End CeilWrap.
End RTW_sec_dealloc1.

(* [comment removed for export] *)
Module RTW_sec_unmap.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_UNMAP_OR_DIE : Z := 0x67880.

Section UNMAPORDIE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (A len lo : Z).
  Hypothesis IC : icpt_cells mv.
  Hypothesis PC : poison_cells mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 48 <= bv_unsigned sp.
  Hypothesis HA : AIMG_HI <= A /\ A mod 4096 = 0 /\ 0 < len /\ len mod 4096 = 0 /\ A + len <= alloc_ceiling.
  Hypothesis MH : map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 A) (Z_to_bv 64 len) = true.
  Hypothesis PLAIN : forall x : word, A <= bv_unsigned x < A + len ->
    in_rangesb (vm_noaccess (m_vmmaps mo)) x = false /\ in_rangesb (m_vm_lazy mo) x = false.

  Lemma unmap_or_die_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    (forall (x5 x10 x11 x12 x13 x14 x15 x16 x17 : word) (m' : word -> option byte),
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (A, A + len)] mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) (mm_unmap (Z_to_bv 64 A) (Z_to_bv 64 len) mo) (mkG G (R + len))) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 len) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_UNMAP_OR_DIE) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P K.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + len)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac. unfold KHIGHMEM_BEG, AIMG_HI in HA.
    unfold A_UNMAP_OR_DIE.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 4; 4; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    step_ecall. cbv beta.
    eapply lscps_munmap with (A := A) (len := len).
    { at_node_red. split_spine; reflexivity. }
    { lia. } { lia. } { lia. } { lia. } { rewrite pru_id by lia. idtac. lia. } { rewrite pru_id by lia. exact MH. }
    { rewrite pru_id by lia. exact PLAIN. }
    rewrite pru_id by lia.
    apply lscps_step_evt. sys_nret. fixMI.
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (IC1 : icpt_cells mm) by (eapply icpt_cells_munch; [exact IC| exact MU|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
      assert (PC1 : poison_cells mm) by (eapply poison_cells_munch; [exact PC| exact MU|]; unfold poison_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil)
    end.
    call dec_total_mmap_ok; [exact IC1| exact PC1| exact MI|].
    do 4 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. eapply K; [exact MI| exact MU| exact ST].
  Qed.
End UNMAPORDIE.


End CeilWrap.
End RTW_sec_unmap.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_sec_dealloc2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs RTW_sec_alloc1 RTW_sec_dealloc1 RTW_sec_unmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma smapsize_facts' : forall n, 0 <= n < 2^40 -> bprim n = false ->
  needed n = rounded8 n + 4096 /\ smapsize n = roundup (needed n) 4096 + 4096 /\ smapsize n mod 4096 = 0
  /\ needed n mod 8 = 0 /\ 65536 < needed n /\ needed n + 4096 <= smapsize n /\ smapsize n < needed n + 8192
  /\ 0x12000 <= smapsize n <= 2^40 + 16384.
Proof.
  intros n Hn HP. (nelimp (sec_facts n HP) 6%nat; intros H1 H2 H3 H4 H5 H6).
  assert (R8 : rounded8 n mod 8 = 0 /\ n <= rounded8 n <= n + 8) by (unfold rounded8, roundup; Z.div_mod_to_equations; lia).
  unfold smapsize, roundup in *. rewrite H6 in *.
  assert (NB : 65536 < rounded8 n + 4096).
  { unfold bprim, is_primary, KMAXSIZE, needed0 in HP. apply Z.leb_gt in HP. rewrite H2 in HP. lia. }
  repeat split; try lia; Z.div_mod_to_equations; lia.
Qed.

Section D0.
  Variables (ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (n mb k lo : Z) (PA : Z) (v3 : word) (j1 : list byte) (nres nsc idx : Z) (j2 : list byte).
  Variables (h16 : word) (b1 b2 b3 : byte) (j4 jg : list byte).
  Hypothesis Hn : 0 <= n.
  Hypothesis HP : bprim n = false.
  Hypothesis HN : n < 2^40.
  (* [comment removed for export] *)
  Hypothesis HB : (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0.
  Hypothesis HPA : (AIMG_HI <= PA /\ (PA + PTRARR_RES_SIZE <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= PA)) /\ PA + PTRARR_RES_SIZE <= CEIL /\ 8 * nsc <= PTRARR_RES_SIZE.
  Hypothesis DJ : PA + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= PA.
  Hypothesis NRS : 0 <= nres < 2^64 /\ 0 <= idx < nsc /\ nsc <= 2^20.
  Hypothesis HK : 0 <= k < 2^24.
  Hypothesis E0 : le4 (wz (256 * k)) = [zb 0; b1; b2; b3].
  Hypothesis E1 : le4 (wz (256 * k + 1)) = [zb 1; b1; b2; b3].
  Hypothesis CEIL0 : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ALARGE_DEALLOC_STACK.

  (* [comment removed for export] *)
  Definition d0_post (POSTK : (word -> option byte) -> Prop) : machine_state -> Prop :=
    fun ms' => exists (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m1,
      ms' = MS (mkR (wz 0x3480c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7 (wz mb) (wz mb)
                    (wz mb) (wz (smapsize n)) (wz 0) y13 y14 y15 y16 y17
                    (wz (smapsize n)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
               F (wz APOISON_SHADOW) fc None m1 (seg_rom asegs)
      /\ POSTK m1.

  (* [comment removed for export] *)
  Definition d0_mem (W : list (Z * Z)) (m1 : word -> option byte) : Prop :=
    munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -32)
    /\ rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2e; C8 s1e; C8 s0e; C8 ra]
    /\ (exists j2', rw_cells asegs m1 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 (wz PA); C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsc - 1)); CB 552 j2'])
    /\ rw_cells asegs m1 0xa6ec0 [C1 (zb 0); CB 3 [b1; b2; b3]; CB 4 j4]
    /\ (exists jg', rw_cells asegs m1 0xa6ec8 [CB 40 jg']).

  (* [comment removed for export] *)
  Lemma ld_D0a : forall (POST : machine_state -> Prop) (mbl : Z) (hl : word) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    idx < nsc - 1 ->
    (AIMG_HI <= mbl /\ (mbl + 32 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mbl)) /\ mbl + 32 <= CEIL /\ (mbl + 32 <= mb \/ mb + smapsize n <= mbl) /\ (PA + PTRARR_RES_SIZE <= mbl \/ mbl + 32 <= PA) ->
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 (wz PA); C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsc); CB 552 j2] ->
    rw_cells asegs m 0xa6ec0 [W4 (256 * k)] -> rw_cells asegs m 0xa6ec4 [CB 4 j4] ->
    rw_cells asegs m mb [C8 (wz mb); C8 (wz (smapsize n)); C8 h16; C8 (wz idx)] ->
    rw_cells asegs m (PA + 8 * idx) [C8 (wz mb)] ->
    rw_cells asegs m (PA + 8 * (nsc - 1)) [C8 (wz mbl)] ->
    rw_cells asegs m (mbl + 24) [C8 hl] ->
    rw_cells asegs m 0xa6ec8 [CB 40 jg] ->
    (forall ms', d0_post (fun m1 => d0_mem [(lo, bv_unsigned sp); (0xa6c58 + 56, 0xa6c58 + 96); (0xa6ec0, 0xa6ec4); (PA + 8 * idx, PA + 8 * idx + 8); (mbl + 24, mbl + 32); (0xa6ec8 + 16, 0xa6ec8 + 32)] m1
                                   /\ rw_cells asegs m1 mb [C8 (wz mb); C8 (wz (smapsize n)); C8 h16; C8 (wz idx)]
                                   /\ rw_cells asegs m1 (PA + 8 * idx) [C8 (wz mbl)]
                                   /\ rw_cells asegs m1 (PA + 8 * (nsc - 1)) [C8 (wz mbl)]
                                   /\ rw_cells asegs m1 (mbl + 24) [C8 (wz idx)]) ms' -> evt asegs POST ms') ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (wz A_SECONDARY) (wz A_GSTATS) (wz (sec_alloc_beg mb)) a3 a4 a5 a6 a7
                            s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz ALARGE_DEALLOC) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros HIX HL MI ST SECC MW MJ HDR PIX PLS HL24 GST K.
    pose proof (smapsize_facts' n ltac:(lia) HP) as SF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(lo, bv_unsigned sp); (0xa6c58 + 56, 0xa6c58 + 96); (0xa6ec0, 0xa6ec4); (PA + 8 * idx, PA + 8 * idx + 8); (mbl + 24, mbl + 32); (0xa6ec8 + 16, 0xa6ec8 + 32)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold ALARGE_DEALLOC, ALARGE_DEALLOC_STACK, APOISON_SHADOW, CEIL, KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE, sec_alloc_beg, SEC_HDR in *.
    rewrite A_SECONDARY_val, A_GSTATS_val in *. idtac. cbv beta delta [wz] in *. leaf_prep.
    set (p := PA + 8 * idx) in *. set (q := PA + 8 * (nsc - 1)) in *.
    carve_frame 32%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    change 4095 with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace ((mb + 4096) mod 4096) with 0 by lia.
    lstep; try if_lia. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    pose proof (sx32_256k_facts k HK) as VF. cbv zeta in VF.
    remember (sx32 (Z_to_bv 64 (256 * k))) as a5v eqn:Ea5. (nelim VF 4%nat; intros VR VM V32 _).
    pose proof (lock_word_val (bv_unsigned a5v) ltac:(lia) VM) as [LW1 LW2].
    lstep. lstep. lstep. lstep. rewrite LW1. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. rewrite LW2. (* [comment removed for export] *)
    lstep. replace (mb + 4096 - 4096) with mb by lia. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    replace (PA + Z.shiftl idx 3) with p by (subst p; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    replace (Z.shiftl nsc 3 + PA) with (q + 8) by (subst q; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    replace (nsc + -1) with (nsc - 1) by lia.
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    assert (EV1 : le4 (wz (bv_unsigned a5v + 1)) = [zb 1; b1; b2; b3]).
    { rewrite <- E1. apply le4_mod32; [lia| lia|]. rewrite <- V32. Z.div_mod_to_equations. lia. }
    cbv beta delta [wz] in EV1.
    pose proof (mutex_cells_to _ _ _ _ _ _ _ _ EV1 MW MJ) as MX. clear MW MJ.
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
    lazymatch type of SECC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      pose proof (rw_cells_merge asegs mZ 683096 [c0; c1; c2; c3; c4; c5; c6] rest [] ) as MG;
      cbn [app] in MG; rewrite ?app_nil_r in MG; specialize (MG SECC); rewrite ?app_nil_r in MG; cbn [app] in MG
    end.
    match type of MG with rw_cells _ _ _ [_; _; _; _; _; _; _; CB ?sz ?bs] => replace sz with 552%nat in MG by (cbn [cells_size Cells.csize]; lia) end.
    lazymatch type of GST with rw_cells _ _ _ ?cs =>
      pose proof (rw_cells_merge asegs mZ 683720 [] cs [] ) as MG2; cbn [app] in MG2; rewrite ?app_nil_r in MG2; specialize (MG2 GST); rewrite ?app_nil_r in MG2
    end.
    match type of MG2 with rw_cells _ _ _ [CB ?sz ?bs] => replace sz with 40%nat in MG2 by (cbn [cells_size Cells.csize]; lia) end.
    apply K. unfold d0_post, d0_mem. cbv beta delta [wz].
    nexists 12%nat. exists mZ. split; [reflexivity|].
    split. { split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
             split; [eexists; exact MG|]. split; [exact MX| eexists; exact MG2]. }
    split; [exact HDR|]. split; [exact PIX|]. split; [exact PLS| exact HL24].
  Qed.

  (* [comment removed for export] *)
  Lemma ld_D0b : forall (POST : machine_state -> Prop) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    idx = nsc - 1 ->
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 (wz PA); C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsc); CB 552 j2] ->
    rw_cells asegs m 0xa6ec0 [W4 (256 * k)] -> rw_cells asegs m 0xa6ec4 [CB 4 j4] ->
    rw_cells asegs m mb [C8 (wz mb); C8 (wz (smapsize n)); C8 h16; C8 (wz idx)] ->
    rw_cells asegs m (PA + 8 * idx) [C8 (wz mb)] ->
    rw_cells asegs m 0xa6ec8 [CB 40 jg] ->
    (forall ms', d0_post (fun m1 => d0_mem [(lo, bv_unsigned sp); (0xa6c58 + 56, 0xa6c58 + 96); (0xa6ec0, 0xa6ec4); (PA + 8 * idx, PA + 8 * idx + 8); (mb + 24, mb + 32); (0xa6ec8 + 16, 0xa6ec8 + 32)] m1
                                   /\ rw_cells asegs m1 mb [C8 (wz mb); C8 (wz (smapsize n)); C8 h16; C8 (wz idx)]
                                   /\ rw_cells asegs m1 (PA + 8 * idx) [C8 (wz mb)]) ms' -> evt asegs POST ms') ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (wz A_SECONDARY) (wz A_GSTATS) (wz (sec_alloc_beg mb)) a3 a4 a5 a6 a7
                            s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz ALARGE_DEALLOC) fc None m (seg_rom asegs)).
  Proof.
    intros until t6. intros HIX MI ST SECC MW MJ HDR PIX GST K.
    pose proof (smapsize_facts' n ltac:(lia) HP) as SF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(lo, bv_unsigned sp); (0xa6c58 + 56, 0xa6c58 + 96); (0xa6ec0, 0xa6ec4); (PA + 8 * idx, PA + 8 * idx + 8); (mb + 24, mb + 32); (0xa6ec8 + 16, 0xa6ec8 + 32)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold ALARGE_DEALLOC, ALARGE_DEALLOC_STACK, APOISON_SHADOW, CEIL, KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE, sec_alloc_beg, SEC_HDR in *.
    rewrite A_SECONDARY_val, A_GSTATS_val in *. idtac. cbv beta delta [wz] in *. leaf_prep.
    set (p := PA + 8 * idx) in *.
    carve_frame 32%nat ST.
    do 5 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    change 4095 with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace ((mb + 4096) mod 4096) with 0 by lia.
    lstep; try if_lia. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    pose proof (sx32_256k_facts k HK) as VF. cbv zeta in VF.
    remember (sx32 (Z_to_bv 64 (256 * k))) as a5v eqn:Ea5. (nelim VF 4%nat; intros VR VM V32 _).
    pose proof (lock_word_val (bv_unsigned a5v) ltac:(lia) VM) as [LW1 LW2].
    lstep. lstep. lstep. lstep. rewrite LW1. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. rewrite LW2. (* [comment removed for export] *)
    lstep. replace (mb + 4096 - 4096) with mb by lia. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    replace (PA + Z.shiftl idx 3) with p by (subst p; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    replace (Z.shiftl nsc 3 + PA) with (p + 8) by (subst p; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    replace (nsc + -1) with (nsc - 1) by lia.
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    amo_step. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    assert (EV1 : le4 (wz (bv_unsigned a5v + 1)) = [zb 1; b1; b2; b3]).
    { rewrite <- E1. apply le4_mod32; [lia| lia|]. rewrite <- V32. Z.div_mod_to_equations. lia. }
    cbv beta delta [wz] in EV1.
    pose proof (mutex_cells_to _ _ _ _ _ _ _ _ EV1 MW MJ) as MX. clear MW MJ.
    lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
    lazymatch type of SECC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      pose proof (rw_cells_merge asegs mZ 683096 [c0; c1; c2; c3; c4; c5; c6] rest [] ) as MG;
      cbn [app] in MG; rewrite ?app_nil_r in MG; specialize (MG SECC); rewrite ?app_nil_r in MG; cbn [app] in MG
    end.
    match type of MG with rw_cells _ _ _ [_; _; _; _; _; _; _; CB ?sz ?bs] => replace sz with 552%nat in MG by (cbn [cells_size Cells.csize]; lia) end.
    lazymatch type of GST with rw_cells _ _ _ ?cs =>
      pose proof (rw_cells_merge asegs mZ 683720 [] cs [] ) as MG2; cbn [app] in MG2; rewrite ?app_nil_r in MG2; specialize (MG2 GST); rewrite ?app_nil_r in MG2
    end.
    match type of MG2 with rw_cells _ _ _ [CB ?sz ?bs] => replace sz with 40%nat in MG2 by (cbn [cells_size Cells.csize]; lia) end.
    apply K. unfold d0_post, d0_mem. cbv beta delta [wz].
    nexists 12%nat. exists mZ. split; [reflexivity|].
    split. { split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
             split; [eexists; exact MG|]. split; [exact MX| eexists; exact MG2]. }
    split; [exact HDR| exact PIX].
  Qed.
End D0.

Section D13.
  Variables (ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (n mb lo t : Z).
  Hypothesis Hn : 0 <= n.
  Hypothesis HP : bprim n = false.
  Hypothesis HN : n < 2^40.
  (* [comment removed for export] *)
  Hypothesis HB : (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0.
  Hypothesis CEIL0 : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ALARGE_DEALLOC_STACK.

  (* [comment removed for export] *)
  Lemma ld_D1 : forall (POST : machine_state -> Prop) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs POST (MS (mkR (wz 0x34818) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz mb) (wz mb)
                            (wz mb) (wz (smapsize n)) x12 x13 x14 x15 x16 x17 (wz (smapsize n)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (wz AFLUSH_SHADOW) fc None m (seg_rom asegs)) ->
    evt asegs POST (MS (mkR (wz 0x3480c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz mb) (wz mb)
                            x10 x11 x12 x13 x14 x15 x16 x17 (wz (smapsize n)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (wz 0x3480c) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros K. unfold AFLUSH_SHADOW in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. lstep. lstep. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_D2 : forall (POST : machine_state -> Prop) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs POST (MS (mkR (wz 0x3481c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz mb) (wz mb)
                            x10 x11 x12 x13 x14 x15 x16 x17 (wz (smapsize n)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (wz A_GET_THREAD_STATS) fc None m (seg_rom asegs)) ->
    evt asegs POST (MS (mkR (wz 0x34818) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz mb) (wz mb)
                            x10 x11 x12 x13 x14 x15 x16 x17 (wz (smapsize n)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (wz 0x34818) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros K. unfold A_GET_THREAD_STATS in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma ld_D3 : forall (POST : machine_state -> Prop) (j88 j96 h16 h24 : word) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    (4096 <= t /\ (t + 4096 <= AIMG_LO \/ AIMG_HI <= t) /\ (t + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= t)) -> t + 4096 <= CEIL -> (t + 4096 <= mb \/ mb + smapsize n <= t) ->   (* [comment removed for export] *)
    mem_inv asegs m ->
    rw_cells asegs m (t + 2888) [C8 j88; C8 j96] ->
    rw_cells asegs m mb [C8 (wz mb); C8 (wz (smapsize n)); C8 h16; C8 h24] ->
    rw_cells asegs m (bv_unsigned sp + -32) [C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
    stk asegs m lo (bv_unsigned sp + -32) ->
    (forall m' (y13 y14 : word), mem_inv asegs m' -> munch [(t + 2888, t + 2904)] m m' -> wmono asegs m m' -> stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' (t + 2888) [C8 y14; C8 y13] ->
       evt asegs POST (MS (mkR ra sp gp tp x5 x6 x7 s0e s1e (wz mb) (wz (smapsize n)) (wz 0) y13 y14 x15 x16 x17 s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (wz A_UNMAP_OR_DIE) fc None m' (seg_rom asegs))) ->
    evt asegs POST (MS (mkR (wz 0x3481c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz mb) (wz mb)
                            (wz (t + T_STATS)) x11 x12 x13 x14 x15 x16 x17 (wz (smapsize n)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (wz 0x3481c) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros HT1 HT2 DJT MI TS HDR FR ST K.
    pose proof (smapsize_facts' n ltac:(lia) HP) as SF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(t + 2888, t + 2904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_UNMAP_OR_DIE, ALARGE_DEALLOC_STACK, T_STATS, CEIL, KHIGHMEM_BEG, AIMG_HI in *. idtac. cbv beta delta [wz] in *. leaf_prep.
    set (ts := t + 2888) in *. replace (t + 2800) with (ts + -88) by lia.
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    do 4 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    eapply K; [assumption| exact MU| exact WM| exact ST| exact TS].
  Qed.
End D13.


End CeilWrap.
End RTW_sec_dealloc2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front RT_artO RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_spz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_secz RT_sec RTW_sec_state.
Import RTW_sec_alloc1.
Import RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac djs := cbn [disjoint_from cells_size Cells.csize fst snd length app]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; unfold PTRARR_RES_SIZE, APOISON_STACK in *; lia.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[b s] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 s). lia. Qed.
Lemma eager_used_nonneg : forall mo, 0 <= eager_used mo.
Proof. intros. unfold eager_used. apply live_bytes_nonneg. Qed.

(* [comment removed for export] *)
Lemma nsec_room : forall st mo g n, RTWF st -> RTMODEL st mo -> BINV mo g ->
  SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= g_res g -> 0 <= n -> nsec st < 2^20.
Proof.
  intros st mo g n WF HM (_ & _ & HB) DEP Hn.
  pose proof (prov_slots_le st WF) as PS. pose proof (eager_used_nonneg mo). pose proof (npages_nonneg (g_win g)).
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & VL & _). rewrite VL in HB. unfold target_alloc_limit in HB.
  unfold SEC_SLOT_TAX, SEC_ALLOC_COST in *. pose proof (smapsize_pos n Hn). lia.
Qed.


(* [comment removed for export] *)
Lemma stk_of_some : forall (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2^64 ->
  (forall x : word, lo <= bv_unsigned x < hi -> m x <> None) -> stk asegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  specialize (H (wa a) ltac:(rewrite wa_unsigned by lia; lia)).
  destruct (m (wa a)) as [b|] eqn:E; [| congruence].
  unfold wview, mrd. rewrite E. split; [discriminate| exists b; reflexivity].
Qed.

Lemma map_contains_cons : forall e maps (lo n : word), map_contains maps lo n = true -> map_contains (e :: maps) lo n = true.
Proof. intros e maps lo n H. unfold map_contains in *. cbn. rewrite H. apply orb_true_r. Qed.
Lemma mmap_fixed_site_add_map : forall mo a s A n, mmap_fixed_site mo A n -> mmap_fixed_site (mm_add_map a s mo) A n.
Proof.
  intros mo a s A n (S1 & S2 & S3 & S4 & S5). unfold mmap_fixed_site. rewrite mm_add_map_vmmaps. cbn [vm_reserved vm_maps].
  repeat (split; [assumption|]). apply map_contains_cons. exact S5.
Qed.
Lemma commit_add_map_comm : forall A n a s mo, mm_commit A n (mm_add_map a s mo) = mm_add_map a s (mm_commit A n mo).
Proof. intros. destruct mo; cbn. reflexivity. Qed.

(* [comment removed for export] *)
Lemma RTREP_szi : forall st W FR m m', RTWF st -> Forall (sz_ok st FR) W -> fresh_ok st FR -> (forall f, In f FR -> snd f <= CEIL) ->
  WOK_alloc W -> WOK_ptrarr st W -> munch W m m' -> wmono asegs m m' -> RTREP st m -> RTREP st m'.
Proof.
  intros st W FR m m' WF HW HFR HC WA WP MU WM HR.
  apply RTREP_of_nsec; [exact (szi_others st WF W FR HW HFR HC m m' MU WM HR)| |].
  - exact (T_alloc st W m m' MU WM (rr_alloc st m HR) WA).
  - exact (T_ptrarr st WF W m m' MU WM (rr_ptrarr st m HR) WP).
Qed.


(* [comment removed for export] *)
Lemma tail_facts : forall mb n, 0 <= n -> bprim n = false -> needed n <= 2^40 -> mb mod 4096 = 0 -> 0 <= mb ->
  let T := mb + smapsize n - (sec_alloc_beg mb + needed n) in
  0 <= T < 4096 /\ T mod 8 = 0 /\ SH (sec_alloc_beg mb + needed n) + T / 8 = SH (mb + smapsize n)
  /\ SH (sec_alloc_beg mb + needed n) = SH mb + 512 + needed n / 8 /\ (sec_alloc_beg mb + needed n) mod 8 = 0
  /\ sec_alloc_beg mb + needed n + T = mb + smapsize n /\ SH mb + smapsize n / 8 = SH (mb + smapsize n).
Proof.
  intros mb n Hn HP HN HA H0. pose proof (smapsize_facts n Hn HP HN) as (_ & _ & SM & N8 & LB & S1 & S2 & _).
  cbv zeta. unfold sec_alloc_beg, SEC_HDR. rewrite !SH_def. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition shwin (g : lghost) (mb n : Z) : Prop :=
  forall x : word, SH mb <= bv_unsigned x < SH (mb + smapsize n) -> in_winb (g_win g) x = true.


(* [comment removed for export] *)
Lemma hmb_ablk : forall mb sz, (AIMG_HI <= mb /\ bandf (mb + sz <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + sz <= CEIL /\ mb mod 4096 = 0 ->
  ablk mb (mb + sz).
Proof. intros mb sz ((H1 & H2) & H3 & _). unfold bandf in H2. unfold ablk, CEIL in *. destruct H2 as [H2|H2]; [left| right]; split; assumption. Qed.
Lemma hmb_of_ablk : forall mb sz, ablk mb (mb + sz) -> mb mod 4096 = 0 ->
  (AIMG_HI <= mb /\ bandf (mb + sz <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + sz <= CEIL /\ mb mod 4096 = 0.
Proof.
  intros mb sz AB AL. pose proof (ablk_lin _ _ AB) as (L1 & _ & L3 & _). pose proof (ablk_disj_band _ _ AB) as D.
  unfold bandf, CEIL. repeat split; assumption.
Qed.

End CeilWrap.
(* [comment removed for export] *)
Ltac djs := cbn [disjoint_from cells_size Cells.csize fst snd length app]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; unfold PTRARR_RES_SIZE, APOISON_STACK in *; lia.
