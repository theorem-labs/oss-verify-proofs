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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_spz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_mmapN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_snp3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_sec_mapfix.
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
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_snp3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_MAPORDIE : Z := 0x700cc.
Definition A_ISNPRINTF : Z := 0x68ca4.
Definition A_FMT_MEMAT : Z := 0x1cdae.     (* [comment removed for export] *)
Definition ISNPRINTF_STACK : Z := 528.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition isnprintf_p_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 bufw a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v lo : Z) (junk : list byte),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ISNPRINTF_STACK <= bv_unsigned sp ->
    0 <= v < 2^64 -> bv_unsigned sp <= bv_unsigned bufw -> bv_unsigned bufw + 40 <= 2^64 ->
    rw_cells asegs m (bv_unsigned bufw) [CB 40 junk] ->
    evt asegs (fun ms' => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m' junk',
                 ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - ISNPRINTF_STACK, bv_unsigned sp); (bv_unsigned bufw, bv_unsigned bufw + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (bv_unsigned bufw) [CB 40 junk'])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 bufw (wz 40) (wz A_FMT_MEMAT) (wz v) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_ISNPRINTF) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Lemma site_AN : forall mo A n, mmap_fixed_site mo A n -> 0 < A /\ A + n <= alloc_ceiling.
Proof. intros mo A n ST. unfold mmap_fixed_site in ST. decompose [and] ST. lia. Qed.

Section MAPORDIE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mv : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (A sz lo : Z).
  Hypothesis HC : mmap_consts mv.
  Hypothesis MI0 : mem_inv asegs mv.
  Hypothesis ST0 : stk asegs mv lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + 720 <= bv_unsigned sp.
  Hypothesis SZ : 0 < sz /\ sz mod 4096 = 0 /\ sz + 4096 <= 2^63.
  Hypothesis AAL : A mod 4096 = 0.
  Hypothesis AHI : AIMG_HI <= A.
  Hypothesis SITE : mmap_fixed_site mo A sz.

  (* [comment removed for export] *)
  Lemma mapordie_spec : forall (P : machine_state -> Model -> lghost -> Prop),
    sz <= R ->
    (forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte),
       mem_inv asegs m' -> munch [(lo, bv_unsigned sp); (A, A + sz)] mv m' -> wmono asegs mv m' ->
       stk asegs m' lo (bv_unsigned sp) ->
       rw_cells asegs m' A [CB (Z.to_nat sz) (repeat (Z_to_bv 8 0) (Z.to_nat sz))] ->
       LSCPS asegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz A) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (ret_pc ra) fc None m' (seg_rom asegs)) (mm_commit (Z_to_bv 64 A) (Z_to_bv 64 sz) mo) (mkG G (R - sz))) ->
    LSCPS asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz A) (wz sz) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz A_MAPORDIE) fc None mv (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros P HRsz K.
    destruct HC as (GOTP & PSC & GOTC & CF260 & CF144 & GOTS & DY). hide GOTC. hide GOTS. hide CF260. hide CF144. hide DY.
    pose proof MI0 as MI. pose proof ST0 as ST. clear ST0.
    pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + sz)] mv) as MU. pose proof (wmono_refl asegs mv) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    pose proof (site_AN mo A sz SITE) as HAN. idtac. pose proof AHI as AH. unfold AIMG_HI in AH.
    unfold A_MAPORDIE. cbv beta delta [wz] in *.
    apply lscps_assume. intros NWX HOK HBINV.
    apply lscps_step_evt.
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 96%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [4; 4; 8; 8; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 7 lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. fl. clear GOTP. (* [comment removed for export] *)
    lstep. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. fl. lstep; try if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 8 (Z_to_bv 64 sz) ltac:(f_equal; symmetry; apply roundup_aligned; lia).
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    rewrite (land_align12 A) by lia. replace (A / 4096 * 4096) with A by (Z.div_mod_to_equations; lia).
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    pose proof GOTC as GOTC1. recell GOTC1 MU. pose proof CF260 as CF1. recell CF1 MU.
    call_sp getnamedfd_any_ok; [exact MI| lia| exact GOTC1| exact CF1| exact ST| idtac; lia| lia|].
    clear GOTC1 CF1. restk. fixMI.
    lstep. fl. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    step_ecall. cbv beta.
    eapply (lscps_mmap_fixed_rw_grant asegs) with (A := A) (len := sz); unfold mm_prot_rw, mm_flags_fixed; rewrite ?pru_id by lia.
    { at_node_red. split_spine; reflexivity. }
    { lia. } { lia. } { exact SITE. } { lia. }
    (* [comment removed for export] *)
    { (* [comment removed for export] *)
      assert (ROF : forall y : word, (A <= bv_unsigned y < A + sz)%Z -> ro_addr asegs y = false).
      { intros y Hy. apply (ro_addr_noseg asegs). apply asegs_noseg_high. lia. }
      apply (munch_weaken _ [(lo, bv_unsigned sp); (A, A + sz)]) in MU. 2:{ unfold sub_fp; cbn; intros; lia. }
      eapply lscps_step_evt. sys_nret. fixMI.
      lstep. (* [comment removed for export] *)
      lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
      lstep. lstep. fl. lstep. if_lia. lstep. fl. lstep. (* [comment removed for export] *)
      replace (18446744073709547520 <? A) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      lstep; try if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      pose proof GOTC as GOTC1. recell GOTC1 MU. lstep. lstep. fl. clear GOTC1. (* [comment removed for export] *)
      pose proof CF144 as CF1. recell CF1 MU. lstep. fl. clear CF1. (* [comment removed for export] *)
      lstep; try if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. do 6 lstep. lstep. lstep. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. eapply K; [exact MI| exact MU| exact WM| exact ST| exact ZNEW].
    }
  Qed.
End MAPORDIE.


End CeilWrap.
End RTW_sec_mapfix.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_lib.
Module RTW_sec_alloc4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs RTW_sec_mapfix OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section A4G.
  Variables (sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (n mb : Z).
  Hypothesis Hn : 0 <= n.
  Hypothesis HP : bprim n = false.
  Hypothesis HN : needed n <= 2^40.
  Hypothesis HB : (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0.
  Hypothesis MI : mem_inv asegs m.

  (* [comment removed for export] *)
  Lemma la_A2 : forall (POST : machine_state -> Prop) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs POST (MS (mkR (wz 0x36990) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n - (sec_alloc_beg mb + needed n))) (wz 250) x13 x14 x15 x16 x17
                            (wz (smapsize n)) (wz (needed n)) (wz mb) (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n))
                            (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
                       F (wz APOISON_SHADOW) fc None m (seg_rom asegs)) ->
    evt asegs POST (MS (mkR (wz 0x36980) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            x10 x11 x12 x13 x14 x15 x16 x17
                            (wz (smapsize n)) (wz (needed n)) (wz mb) (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n))
                            (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
                       F (wz 0x36980) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros K.
    pose proof (smapsize_facts n Hn HP HN) as SF.
    unfold APOISON_SHADOW, CEIL, KHIGHMEM_BEG, AIMG_HI, sec_alloc_beg, SEC_HDR in *. rewrite A_SECONDARY_val, A_GSTATS_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma la_A2c : forall (POST : machine_state -> Prop) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs POST (MS (mkR (wz 0x36994) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            x10 x11 x12 x13 x14 x15 x16 x17
                            (wz (smapsize n)) (wz (needed n)) (wz mb) (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n))
                            (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
                       F (wz A_GET_THREAD_STATS) fc None m (seg_rom asegs)) ->
    evt asegs POST (MS (mkR (wz 0x36990) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
                            x10 x11 x12 x13 x14 x15 x16 x17
                            (wz (smapsize n)) (wz (needed n)) (wz mb) (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n))
                            (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
                       F (wz 0x36990) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros K.
    unfold A_GET_THREAD_STATS, CEIL, KHIGHMEM_BEG, AIMG_HI, sec_alloc_beg, SEC_HDR in *. rewrite A_SECONDARY_val, A_GSTATS_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma la_B : forall (POST : machine_state -> Prop) (nsc nres : Z) x1 x5 x6 x7 x8 x10 x11 x12 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    0 <= nsc < 2^64 -> 0 <= nres < 2^64 ->
    evt asegs POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (wz A_SECONDARY) x10 x11 x12 (wz nsc) (wz nres) x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (wz (if nsc =? nres then 0x36ca4 else 0x36ad0)) fc None m (seg_rom asegs)) ->
    evt asegs POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (wz A_SECONDARY) x10 x11 x12 (wz nsc) (wz nres) x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (wz 0x36acc) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros H1 H2 K.
    rewrite A_SECONDARY_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. if_cases KM; zify_cond KM.
    - replace (nsc =? nres) with true in K by (symmetry; apply Z.eqb_eq; lia). exact K.
    - replace (nsc =? nres) with false in K by (symmetry; apply Z.eqb_neq; lia). exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma la_G1 : forall (POST : machine_state -> Prop) (PA nres nsc : Z) v3 j1 j2 x1 x5 x6 x7 x8 x10 x11 x12 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    0 <= nsc < 2^20 -> 0 <= PA -> PA + 8 * nsc + 8 <= 2^64 ->
    rw_cells asegs m 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 (wz PA); C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsc); CB 552 j2] ->
    evt asegs POST (MS (mkR (wz 0x36cc8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (wz A_SECONDARY) (wz (A_SECONDARY + 16)) (wz (PA + 8 * nsc)) (wz PTRARR_BLOCK) (wz 0) (wz (A_SECONDARY + 16)) x15 x16 x17
                            x18 x19 x10 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (wz A_MAPORDIE) fc None m (seg_rom asegs)) ->
    evt asegs POST (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (wz A_SECONDARY) x10 x11 x12 (wz nsc) (wz nsc) x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (wz 0x36ca4) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros H1 H2 H3 SECC K.
    unfold A_MAPORDIE, PTRARR_BLOCK in *. rewrite A_SECONDARY_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    replace (Z.shiftl nsc 3 + PA) with (PA + 8 * nsc) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma la_G2 : forall (POST : machine_state -> Prop) (PA nres nsc : Z) v3 j1 j2 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31,
    0 <= nsc < 2^20 -> 0 <= nres -> nres + 2^14 < 2^64 ->
    rw_cells asegs m 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 (wz PA); C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsc); CB 552 j2] ->
    (forall m', rw_cells asegs m' 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz PA); C8 (wz PA); C8 v3; CB 16 j1; C8 (Z_to_bv 64 (nres + 2^14)); C8 (Z_to_bv 64 nsc); CB 552 j2] ->
       mem_inv asegs m' -> munch [(0xa6c58 + 48, 0xa6c58 + 56)] m m' -> wmono asegs m m' ->
       evt asegs POST (MS (mkR (wz 0x36cc8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (wz A_SECONDARY) x20 (wz (nres + 2^14)) (wz (2^14)) (wz nsc) x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                          F (wz 0x36ad0) fc None m' (seg_rom asegs))) ->
    evt asegs POST (MS (mkR (wz 0x36cc8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 x8 (wz A_SECONDARY) x10 x11 x12 x13 x14 x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
                       F (wz 0x36cc8) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros H1 H2 H3 SECC K.
    pose proof (munch_refl [(0xa6c58 + 48, 0xa6c58 + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    rewrite A_SECONDARY_val in *. cbv beta delta [wz] in *. leaf_prep.
    lstep. lstep. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    eapply K; [exact SECC| assumption| exact MU| exact WM].
  Qed.
End A4G.


End CeilWrap.
End RTW_sec_alloc4.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artO.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_name.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_msb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_state.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_grant.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_sec_alloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artO OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_name OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_msb OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc3 RTW_sec_mapfix OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_state RTW_sec_alloc4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_grant OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition sec_alloc2_post_blkW (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists mb,
        a0' = wz (sec_alloc_beg mb) /\ sec_alloc_rel st st' n (sec_alloc_beg mb) /\ ablk mb (mb + smapsize n)
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m'
        /\ rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m'
        /\ budget_ok st g st' g' (SEC_ALLOC_COST n + SEC_SLOT_TAX)
        /\ rw_cells asegs m' (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512))
        /\ rw_cells asegs m' (SH (sec_alloc_beg mb + rounded8 n + 4096)) (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8)))
        /\ shwin g' mb n
        /\ gmono g g').

Lemma blkW_to_blk : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g',
  sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g' ->
  sec_alloc2_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g'.
Proof.
  intros until g'. intros H. unfold sec_alloc2_post_blkW, sec_alloc2_post_blk, rt_post_std in *.
  (nelim H 32%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st' -> MI' mb E REL HB RTS' ST' CP RF BUD P1 P2 SW GM).
  nexists 15%nat. exists m', st'. split; [reflexivity|]. split; [exact MI'|]. exists mb. repeat (split; [assumption|]). first [exact GM| split; [exact SW| exact GM]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LA2.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate) (n lo : Z).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HM : RTMODEL st mo.
  Hypothesis HG : GWIN st m mo (mkG G R).
  Hypothesis HFR : FRONTR mo R.
  Hypothesis HSW : SWIN st (mkG G R).
  Hypothesis Hn : 0 <= n.
  Hypothesis HP : bprim n = false.
  Hypothesis HN : needed n <= 2^40.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DEP : SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= R.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis HCEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 2048.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis NWX : no_wx asegs.
  Hypothesis HOK : LOK asegs mo.
  Hypothesis HBINV : BINV mo (mkG G R).
  (* [comment removed for export] *)
  Hypothesis FR1 : la_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m1.
  Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -96).
  Hypothesis MU1 : munch [(lo, bv_unsigned sp)] m m1.
  Hypothesis WM1 : wmono asegs m m1.

  (* [comment removed for export] *)
  Definition Wv (mb : Z) : list (Z * Z) :=
    [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n)); (st_t st + 2872, st_t st + 2888); (mb, mb + 32);
     (A_SECONDARY, A_SECONDARY + 624); (A_GSTATS + 16, A_GSTATS + 32); (st_pa st + 8 * nsec st, st_pa st + PTRARR_RES_SIZE)].
  (* [comment removed for export] *)
  Ltac inW n := lazymatch n with O => left; reflexivity | S ?k => right; inW k end.
  Ltac sub1 := first [ eapply sub_fp_cons_in; [inW 0%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 1%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 2%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 3%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 4%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 5%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 6%nat| lia| lia|] ].
  Ltac subfp := unfold Wv; rewrite ?A_SECONDARY_val, ?A_GSTATS_val; unfold PTRARR_RES_SIZE, APOISON_STACK in *;
                repeat (first [apply sub_fp_nil | sub1]).

  (* [comment removed for export] *)
  Lemma CPW' : forall mb mv', (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 ->
    (forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb) ->
    cli_pres st (bv_unsigned sp) m mv' ->
    forall mx, munch (Wv mb) mv' mx -> wmono asegs mv' mx -> cli_pres st (bv_unsigned sp) m mx.
  Proof.
    intros mb mv' HMB FRESH CPv mx MUx WMx. pose proof (smapsize_facts n Hn HP HN) as SF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac. pose proof (pa_range st WF) as PR. unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in PR.
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
    pose proof (rt_SH_bounds mb ltac:(unfold KHIGHMEM_BEG, AIMG_HI, CEIL in HMB; lia)) as SHlo.
    pose proof (SH_mono (mb + smapsize n) (@CEIL ACEIL) ltac:(lia)) as SHC. rewrite SH_CEIL in SHC.
    eapply cli_pres_trans; [exact CPv|]. unfold cli_pres. eapply cj_pres_of_munch; [exact MUx| exact WMx|].
    intros x Hx HC. unfold Wv. rewrite A_SECONDARY_val, A_GSTATS_val. cbn [outside fst snd].
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| exact I]]]]]]]; intros Hin.
    - exact (below_sp_not_client st WF (bv_unsigned sp) x ltac:(unfold CEIL in *; lia) HC).
    - exact (fresh_shadow_not_client st WF (bv_unsigned sp) HSPc mb (smapsize n) FRESH (hmb_ablk _ _ HMB) x Hin HC).
    - exact (tpage_not_client st WF (bv_unsigned sp) HSPc x ltac:(unfold T_ACACHE; lia) HC).
    - exact (fresh_not_client st WF (bv_unsigned sp) HSPc mb (smapsize n) FRESH (hmb_ablk _ _ HMB) x ltac:(lia) HC).
    - exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC).
    - exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC).
    - exact (pa_not_client st WF (bv_unsigned sp) HSPc x ltac:(unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in *; lia) HC).
  Qed.

  Lemma RFW' : forall mb mv', (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 ->
    rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m mv' ->
    forall mx, munch (Wv mb) mv' mx -> rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m mx.
  Proof.
    intros mb mv' HMB RFv mx MUx. pose proof (smapsize_facts n Hn HP HN) as SF. pose proof (pa_range st WF) as PR. unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in PR.
    pose proof (rt_SH_bounds mb ltac:(unfold KHIGHMEM_BEG, AIMG_HI, CEIL in HMB; lia)) as SHlo.
    eapply rt_frame_trans; [exact RFv|]. eapply rt_frame_of_munch; [exact MUx|].
    intros iv Hiv. unfold secondary_fp, fp_tpage. rewrite A_SECONDARY_val, A_GSTATS_val. unfold Wv in Hiv. rewrite A_SECONDARY_val, A_GSTATS_val in Hiv.
    cbn [In] in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd].
    - left. lia.
    - right. exists (SH mb - 4096, SH (mb + smapsize n) + 4096). split; [cbn; tauto| cbn [fst snd]; lia].
    - right. exists (st_t st, st_t st + 4096). split; [apply in_or_app; right; cbn; tauto| cbn [fst snd]; lia].
    - right. exists (mb, mb + smapsize n). split; [cbn; tauto| cbn [fst snd]; lia].
    - right. exists (683096, 683096 + 624). split; [cbn; tauto| cbn [fst snd]; lia].
    - right. exists (683720, 683720 + 40). split; [cbn; tauto| cbn [fst snd]; lia].
    - right. exists (st_pa st, st_pa st + PTRARR_RES_SIZE). split; [cbn; tauto| cbn [fst snd]; unfold PTRARR_RES_SIZE; lia].
  Qed.

  Lemma la_tail : forall (mb : Z) (mv9 m9 : word -> option byte) (mo9 : Model) (G9 : list (Z * Z)) (R9 nres9 v T : Z) (b1 b2 b3 : byte)
      (j1 j2 j4 jg jf : list byte) (h24 jp : word) (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 ->
    (forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb) ->
    nres9 = st_nreserved st + (if sec_grow st then 2^14 else 0) ->
    8 * nsec st + 8 <= 8 * nres9 <= PTRARR_RES_SIZE ->
    RTREP st mv9 -> munch (Wv mb) mv9 m9 -> wmono asegs mv9 m9 -> mem_inv asegs m9 ->
    vis mv9 mb (mb + smapsize n) -> vis mv9 (SH mb) (SH (mb + smapsize n)) ->
    rw_cells asegs m9 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (wz (st_pa st)); C8 (wz (st_pa st)); C8 (wz PTRARR_RES_SIZE); CB 16 j1;
                                C8 (Z_to_bv 64 nres9); C8 (Z_to_bv 64 (nsec st)); CB 552 j2] ->
    rw_cells asegs m9 mb [C8 (wz mb); C8 (wz (smapsize n)); C8 (wz (needed n))] -> rw_cells asegs m9 (mb + 24) [C8 h24] ->
    rw_cells asegs m9 (st_pa st + 8 * nsec st) [C8 jp] -> rw_cells asegs m9 0xa6ec8 [CB 40 jg] ->
    0 <= v < 2^64 /\ le4 (wz (v + 1)) = [zb 1; b1; b2; b3] -> rw_cells asegs m9 0xa6ec0 [W4 (v + 1)] -> rw_cells asegs m9 0xa6ec4 [CB 4 j4] ->
    rw_cells asegs m9 (bv_unsigned sp + -96) [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    vis m9 lo (bv_unsigned sp + -96) ->
    vis m9 (st_pa st) (st_pa st + 8 * nres9) ->
    rw_cells asegs m9 (SH mb) [CB 512 (repeat (Z_to_bv 8 250) 512)] ->
    T = mb + smapsize n - (sec_alloc_beg mb + needed n) ->
    rw_cells asegs m9 (SH (sec_alloc_beg mb + needed n)) [CB (Z.to_nat (T / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (T / 8)))] ->
    cli_pres st (bv_unsigned sp) m m9 -> rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m9 ->
    RTMODEL (st_secreg st mb n) mo9 -> GWIN st m9 mo9 (mkG G9 R9) -> FRONTR mo9 R9 ->
    rt_prov (st_secreg st mb n) + (R - R9) <= rt_prov st + SEC_ALLOC_COST n + SEC_SLOT_TAX ->
    gmono (mkG G R) (mkG G9 R9) ->
    shwin (mkG G9 R9) mb n ->
    LSCPS asegs (sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m (mkG G R))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 (wz A_GSTATS) (wz A_SECONDARY)
               (wz (sec_alloc_beg mb)) x11 x12 (wz (nsec st)) x14 x15 x16 x17
               (wz (smapsize n)) (wz (63 - Z.log2 (smapsize n))) x20 (wz mb) (wz (mb + smapsize n))
               (wz (sec_alloc_beg mb + needed n)) (wz 7) (wz (sec_alloc_beg mb)) s10 s11 x28 x29 x30 x31)
          F (wz 0x36ad0) fc None m9 (seg_rom asegs)) mo9 (mkG G9 R9).
  Proof.
    intros until x31. intros HMB FRESH Enres NR9 HRv MU9 WM9 MI9 VMv VSHv SEC9 HDR9 H24 PC9 GST9 HV MW9 MJ9 FR9 ST9 VPA9 PSA PSB_T PSB CP9 RF9 HM9 GW9 HFR9 BUD GM WIN9.
    pose proof (smapsize_facts n Hn HP HN) as SF. pose proof (pa_range st WF) as PR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    pose proof (nsec_room st mo (mkG G R) n WF HM HBINV DEP Hn) as ROOM.
    pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR.
    assert (HMBn : 0x5ff000 <= mb /\ mb + smapsize n <= alloc_ceiling) by (unfold AIMG_HI, CEIL in HMB; lia).   (* [comment removed for export] *)
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHBk. pose proof (rt_SH_bounds (mb + smapsize n) ltac:(lia)) as SHBk2.
    pose proof (hmb_ablk _ _ HMB) as HBKk. olin HBKk.
    pose proof (t_range st WF) as TRk. olin TRk. pose proof (pa_range st WF) as PRk. olin PRk.   (* [comment removed for export] *)
    pose proof PR as PRn. unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in PRn.
    assert (DJP : st_pa st + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= st_pa st).
    { destruct (FRESH (st_pa st, st_pa st + PTRARR_RES_SIZE) ltac:(unfold rt_ranges; right; left; reflexivity)) as [D|D]; cbn [fst snd] in D; lia. }
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHlo. pose proof (rt_SH_bounds (mb + smapsize n) ltac:(lia)) as SHhi.
    pose proof (SH_mono mb (mb + smapsize n) ltac:(lia)) as SHle. pose proof (SH_mono (mb + smapsize n) (@CEIL ACEIL) ltac:(lia)) as SHC. rewrite SH_CEIL in SHC.
    apply lscps_assume. intros _ HOK9 HBINV9.
    apply lscps_step_evt. eapply evt_cut.
    { eapply (la_A4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m9 n mb (Z.log2 (smapsize n)) v lo (st_pa st) _ _ j1 nres9 (nsec st) j2 h24 jp jg b1 b2 b3 j4 jf
              Hn HP HN HMB); [| exact DJP| unfold PTRARR_RES_SIZE in NR9; lia| reflexivity| exact HV| exact HCEIL| unfold ALARGE_ALLOC_STACK; lia
        | exact MI9| exact SEC9| exact H24| exact PC9| exact GST9| exact MW9| exact MJ9| exact FR9| exact ST9].
      pose proof (ablk_lin _ _ (proj1 PRk)) as PL1. pose proof (ablk_disj_band _ _ (proj1 PRk)) as PD1.
      clear - PRk PL1 PD1 NR9. unfold bandf, CEIL, KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI, PTRARR_RES_SIZE in *. lia. }
    cbv beta. intros ms10 nelH_; (nelim nelH_ 25%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m10 -> MUA WMA MI10 ST10 [j2' SEC10] H24' PC10 [jg' GST10] MX10).
    apply evt_done. apply lscps_done.
    (* [comment removed for export] *)
    assert (MU10 : munch (Wv mb) mv9 m10).
    { eapply munch_trans; [exact MU9|]. eapply munch_weaken; [| exact MUA]. unfold Wv, sub_fp. rewrite A_SECONDARY_val, A_GSTATS_val. cbn. unfold PTRARR_RES_SIZE in *. intros; (lia_on LO NR9 SF CEIL' HMBn ALx TRk ALx0 PRn DJP SHhi SHle SHC H). }
    pose proof (wmono_trans asegs _ _ _ WM9 WMA) as WM10.
    (nelimp (st_secreg_fields st mb n) 12%nat; intros Ef1 Ef2 Ef3 Ef4 Ef5 Ef6 Ef7 Ef8 Ef9 Ef10 Ef11 Ef12).
    assert (FOK : fresh_ok st [(mb, mb + smapsize n)]).
    { intros f [<-|[]]. cbn [fst snd]. split; [exact (hmb_ablk _ _ HMB)|]. intros r Hr. destruct (FRESH r Hr); lia. }
    assert (PAT : st_pa st + PTRARR_RES_SIZE <= st_t st \/ st_t st + 4096 <= st_pa st).
    { (nelim (PW_tail st WF) 3%nat; intros _ _ F2). rewrite Forall_forall in F2.
      specialize (F2 (st_t st, st_t st + 4096) ltac:(apply in_or_app; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])).
      cbn [fst snd] in F2. lia. }
    assert (HW : Forall (sz_ok st [(mb, mb + smapsize n)]) (Wv mb)).
    { unfold Wv. constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|].
      constructor; [eapply (sz_ok_fresh_sh st _ (mb, mb + smapsize n)); [left; reflexivity| cbn; lia| cbn; lia]|].
      constructor; [apply sz_ok_stats; cbn; unfold T_STATS, T_UNWINDING; lia|].
      constructor; [eapply (sz_ok_fresh st _ (mb, mb + smapsize n)); [left; reflexivity| cbn; lia| cbn; lia]|].
      constructor; [apply sz_ok_static; cbn; [lia| unfold A_QUAR, A_SECONDARY, A_ALLOC; lia]|].
      constructor; [apply sz_ok_static; cbn; unfold A_QUAR, A_GSTATS, A_SECONDARY, A_ALLOC; lia|].
      constructor; [apply sz_ok_pa; cbn; lia| constructor]. }
    pose proof (szi_others st WF (Wv mb) [(mb, mb + smapsize n)] HW FOK ltac:(intros f [<-|[]]; cbn; lia) mv9 m10 MU10 WM10 HRv) as HRn10.
    pose proof (RTREP_nsec_secreg' st mb n m10 WF HRn10) as HRn10'.
    assert (RA10 : R_alloc (st_secreg st mb n) m10).
    { eapply (R_alloc_secreg_intro st mb n (Wv mb) mv9 m10 nres9 WF FRESH MU10 WM10 Enres ROOM _ _ _ jg' (rr_alloc st mv9 HRv)).
      - unfold Wv, A_ALLOC. rewrite A_SECONDARY_val, A_GSTATS_val. cbn. lia.
      - unfold Wv, A_QUAR, A_ALLOC. rewrite A_SECONDARY_val, A_GSTATS_val. cbn. lia.
      - unfold Wv, A_MAXUSERSZ, A_ALLOC. rewrite A_SECONDARY_val, A_GSTATS_val. cbn. lia.
      - rewrite A_SECONDARY_val. apply (proj2 (rw_cells_app asegs m10 683096 [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 nres9; W8 (nsec st + 1); CB 552 j2'] [W1 0; CB 7 ([b1; b2; b3] ++ j4)])).
        split; [exact SEC10|]. cbn [cells_size Cells.csize Nat.add]. apply mutex_cells_merge. exact MX10.
      - rewrite A_GSTATS_val. exact GST10. }
    assert (RP10 : R_ptrarr (st_secreg st mb n) m10).
    { pose proof (hmb_ablk _ _ HMB) as HBK. (nelim HMB 3%nat; intros HB1 HB2 HB3).
      eapply (R_ptrarr_secreg_intro st mb n (Wv mb) mv9 m10 nres9 WF Hn HN HBK FRESH MU10 WM10 Enres ROOM (rr_ptrarr st mv9 HRv)).
      - split.
        + intros i Hi. unfold Wv. rewrite A_SECONDARY_val, A_GSTATS_val. cbn. unfold PTRARR_RES_SIZE in *. repeat split; try (lia_on NR9 SF CEIL' HMBn PRn Hi ROOM ALx0 SHlo SHhi PAT DJP).
        + intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
          pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. olin ER. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in ER.
          pose proof (sec_vs_t st WF e HE) as ET.
          assert (IR : In (fst e, fst e + smapsize (snd e)) (rt_ranges st)).
          { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists e. split; [reflexivity| exact HE]. }
          pose proof (FRESH _ IR) as EF. cbn [fst snd] in EF.
          (nelim (PW_tail st WF) 3%nat; intros _ _ F2). rewrite Forall_forall in F2.
          specialize (F2 (fst e, fst e + smapsize (snd e)) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists e; split; [reflexivity| exact HE])). cbn [fst snd] in F2.
          pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _].
          unfold Wv. rewrite A_SECONDARY_val, A_GSTATS_val. cbn. unfold PTRARR_RES_SIZE in *. repeat split; try (lia_on SF CEIL' HMBn ALx1 SP8 SHlo SHhi DJP PAT ET EF F2 HB3 ER PRn).
      - eapply stk_wmono_noseg; [exact VPA9| exact WMA| unfold AIMG_HI; lia].
      - exact PC10.
      - eapply stk_wmono_noseg; [exact VMv| exact WM10| unfold AIMG_HI; lia].
      - (nelimp (smapsize_facts n Hn HP HN) 4%nat; intros _ _ SM _).
        replace (SH mb + smapsize n / 8) with (SH (mb + smapsize n)) by (rewrite !SH_def; Z.div_mod_to_equations; lia).
        eapply stk_wmono_noseg; [exact VSHv| exact WM10| pose proof (rt_SH_bounds mb ltac:(lia)); unfold AIMG_HI; lia].
      - apply (proj2 (rw_cells_app asegs m10 mb [W8 mb; W8 (smapsize n); W8 (needed n)] [W8 (nsec st)])). split; [| cbn [cells_size Cells.csize Nat.add]; exact H24'].
        eapply rw_cells_transport; [exact HDR9| exact MUA| exact WMA| cbn; unfold PTRARR_RES_SIZE in *; lia]. }
    pose proof (RTREP_of_nsec _ _ HRn10' RA10 RP10) as HR10.
    pose proof (hmb_ablk _ _ HMB) as HBK. (nelim HMB 3%nat; intros HB1 HB2 HB3). olin HBK.
    (* [comment removed for export] *)
    unfold sec_alloc2_post_blkW, rt_post_std. nexists 15%nat. exists m10, (st_secreg st mb n).
    split; [reflexivity|]. split; [exact MI10|].
    exists mb. split; [reflexivity|].
    split; [exact (secreg_rel' st mb n WF HB3 HBK HB2 FRESH ROOM)|].
    split; [exact HBK|].
    split.
    { apply RTS_intro; [exact HR10| exact (RTWF_secreg' st mb n WF HP Hn HN HB3 HBK HB2 FRESH ROOM)| exact HM9| | exact HFR9| exact (SWIN_secreg' st mb n _ _ HSW GM WIN9)].
      apply (GWIN_secreg' st mb n WF FRESH ROOM). eapply GWIN_mem; [exact GW9| exact HOK9| exact WMA]. }
    split; [exact ST10|].
    split.
    { eapply cli_pres_trans; [exact CP9|]. unfold cli_pres. eapply cj_pres_of_munch; [exact MUA| exact WMA|].
      intros x Hx HC. cbn. split; [| split; [| split; [| split; [| exact I]]]]; intros Hin.
      - exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC).
      - exact (fresh_not_client st WF (bv_unsigned sp) HSPc mb (smapsize n) FRESH HBK x ltac:(lia) HC).
      - exact (pa_not_client st WF (bv_unsigned sp) HSPc x ltac:(unfold PTRARR_RES_SIZE in *; lia) HC).
      - exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC). }
    split.
    { eapply rt_frame_trans; [exact RF9|]. eapply rt_frame_of_munch; [exact MUA|].
      intros iv Hiv. right. unfold secondary_fp. rewrite A_SECONDARY_val, A_GSTATS_val.
      cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
      - exists (683096, 683096 + 624). split; [cbn; (cut_on [NR9 HV SF PR RSP TR HMBn SHBk SHBk2 ALx TRk OLx PRk ALx0 PRn DJP SHlo SHhi PAT HB1 ALx1] tauto)| cbn [fst snd]; lia].
      - exists (mb, mb + smapsize n). split; [cbn; (cut_on [NR9 HV SF PR RSP TR HMBn SHBk SHBk2 ALx TRk OLx PRk ALx0 PRn DJP SHlo SHhi PAT HB1 ALx1] tauto)| cbn [fst snd]; lia].
      - exists (st_pa st, st_pa st + PTRARR_RES_SIZE). split; [cbn; (cut_on [NR9 HV SF PR RSP TR HMBn SHBk SHBk2 ALx TRk OLx PRk ALx0 PRn DJP SHlo SHhi PAT HB1 ALx1] tauto)| cbn [fst snd]; unfold PTRARR_RES_SIZE in *; lia].
      - exists (683720, 683720 + 40). split; [cbn; (cut_on [NR9 HV SF PR RSP TR HMBn SHBk SHBk2 ALx TRk OLx PRk ALx0 PRn DJP SHlo SHhi PAT HB1 ALx1] tauto)| cbn [fst snd]; lia]. }
    split; [unfold budget_ok; cbn [g_res]; lia|].
    split.
    { apply CB_to_zcells_zrep; [lia|]. eapply rw_cells_transport; [exact PSA| exact MUA| exact WMA| djs]. }
    split.
    { pose proof (smapsize_facts n Hn HP HN) as (SF1 & _).
      replace (sec_alloc_beg mb + rounded8 n + 4096) with (sec_alloc_beg mb + needed n) by lia.
      replace ((mb + smapsize n - (sec_alloc_beg mb + needed n)) / 8) with (T / 8) by (subst T; reflexivity).
      pose proof (rt_SH_bounds (sec_alloc_beg mb + needed n) ltac:(unfold sec_alloc_beg, SEC_HDR; lia)) as SHB2.
      assert (T8 : 0 <= T / 8 /\ SH (sec_alloc_beg mb + needed n) + T / 8 <= SH (mb + smapsize n)).
      { subst T. unfold sec_alloc_beg, SEC_HDR in *. rewrite !SH_def in *. Z.div_mod_to_equations. lia. }
      apply CB_to_zcells_zrep; [lia|]. eapply rw_cells_transport; [exact PSB| exact MUA| exact WMA| djs]. }
    split; [exact WIN9| exact GM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma la_mid2 : forall (mb : Z) (mv' m7 : word -> option byte) (wlo whi R1 T v : Z) (jf k1 k2 j4 jg : list byte) (b1 b2 b3 : byte) (h24 : word)
      (r5 r6 r7 r11 r17 r28 r29 r30 r31 : word),
    (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 ->
    (forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb) ->
    RTREP st mv' -> vis mv' mb (mb + smapsize n) -> vis mv' (SH mb) (SH (mb + smapsize n)) ->
    cli_pres st (bv_unsigned sp) m mv' -> rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m mv' ->
    GWIN st mv' (mm_add_map (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) mo) (mkG ((wlo, whi) :: G) R1) ->
    FRONTR (mm_add_map (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) mo) (R - smapsize n) ->
    sec_plain mo mb (smapsize n) ->
    R1 = R - smapsize n - (whi - wlo) -> 0 <= whi - wlo <= smapsize n / 8 + 7168 ->
    munch (Wv mb) mv' m7 -> wmono asegs mv' m7 -> mem_inv asegs m7 ->
    rw_cells asegs m7 0xa6c58 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (st_pa st)); C8 (Z_to_bv 64 (st_pa st)); C8 (Z_to_bv 64 PTRARR_RES_SIZE); CB 16 k1;
                                C8 (Z_to_bv 64 (st_nreserved st)); C8 (Z_to_bv 64 (nsec st)); CB 552 k2] ->
    rw_cells asegs m7 (bv_unsigned sp + -96) [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m7 (SH mb) [CB 512 (repeat (Z_to_bv 8 250) 512)] ->
    T = mb + smapsize n - (sec_alloc_beg mb + needed n) ->
    rw_cells asegs m7 (SH (sec_alloc_beg mb + needed n)) [CB (Z.to_nat (T / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (T / 8)))] ->
    rw_cells asegs m7 0xa6ec8 [CB 40 jg] -> vis m7 lo (bv_unsigned sp + -96) ->
    rw_cells asegs m7 mb [C8 (wz mb); C8 (wz (smapsize n)); C8 (wz (needed n)); C8 h24] ->
    0 <= v < 2^64 -> le4 (wz (v + 1)) = [zb 1; b1; b2; b3] ->
    rw_cells asegs m7 0xa6ec0 [C4 (wz (v + 1))] -> rw_cells asegs m7 0xa6ec4 [CB 4 j4] ->
    wlo <= SH mb /\ SH (mb + smapsize n) <= whi ->
    LSCPS asegs (sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m (mkG G R))
      (MS (mkR (wz 0x36994) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp r5 r6 r7 (wz A_GSTATS) (wz A_SECONDARY)
               (wz (sec_alloc_beg mb)) r11 (wz 0) (wz (nsec st)) (wz 1) (wz v) (wz 0) r17
               (wz (smapsize n)) (wz (needed n)) (wz mb) (wz mb) (wz (mb + smapsize n)) (wz (sec_alloc_beg mb + needed n))
               (wz 7) (wz (sec_alloc_beg mb)) s10 s11 r28 r29 r30 r31)
          F (wz 0x36a24) fc None m7 (seg_rom asegs))
      (mm_add_map (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) mo) (mkG ((wlo, whi) :: G) R1).
  Proof.
    intros until r31. intros HMB FRESH HRv VMv VSH CPv RFv GWv HFR1 PLN ER1 WBd MU7 WM7 MI7 SEC7 FR7 PSH1_7 ET PSH2_7 GST7 ST7 HDR7 HV1 HV3 MW7 MJ7 WIv.

    pose proof (smapsize_facts n Hn HP HN) as SF. pose proof (pa_range st WF) as PR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    pose proof (nsec_room st mo (mkG G R) n WF HM HBINV DEP Hn) as ROOM.
    pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR.
    assert (HMBn : 0x5ff000 <= mb /\ mb + smapsize n <= alloc_ceiling) by (unfold AIMG_HI, CEIL in HMB; lia).   (* [comment removed for export] *)
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHBk. pose proof (rt_SH_bounds (mb + smapsize n) ltac:(lia)) as SHBk2.
    pose proof (hmb_ablk _ _ HMB) as HBKk. olin HBKk.
    pose proof (t_range st WF) as TRk. olin TRk. pose proof (pa_range st WF) as PRk. olin PRk.   (* [comment removed for export] *)
    pose proof PR as PRn. unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in PRn.
    assert (DJT : st_t st + 4096 <= mb \/ mb + smapsize n <= st_t st).
    { destruct (FRESH (st_t st, st_t st + 4096)) as [D|D]; [| cbn [fst snd] in D; lia| cbn [fst snd] in D; lia].
      unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (st_t st, 4096). split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))]. }
    assert (DJP : st_pa st + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= st_pa st).
    { destruct (FRESH (st_pa st, st_pa st + PTRARR_RES_SIZE) ltac:(unfold rt_ranges; right; left; reflexivity)) as [D|D]; cbn [fst snd] in D; lia. }
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
    pose proof (SH_mono mb (mb + smapsize n) ltac:(lia)) as SHle. pose proof (SH_mono (mb + smapsize n) (@CEIL ACEIL) ltac:(lia)) as SHC. rewrite SH_CEIL in SHC.
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHlo.
    assert (FOK : fresh_ok st [(mb, mb + smapsize n)]).
    { intros f [<-|[]]. cbn [fst snd]. split; [exact (hmb_ablk _ _ HMB)|]. intros r Hr. destruct (FRESH r Hr); lia. }
    assert (RTT : forall mx, munch [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n))] mv' mx -> wmono asegs mv' mx -> RTREP st mx).
    { intros mx MUx WMx.
      eapply (RTREP_szi st _ [(mb, mb + smapsize n)] mv' mx WF); [| exact FOK| intros f [<-|[]]; cbn; unfold CEIL; lia| | | exact MUx| exact WMx| exact HRv].
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|]. constructor; [| constructor].
        eapply (sz_ok_fresh_sh st _ (mb, mb + smapsize n)); [left; reflexivity| cbn; lia| cbn; lia].
      - unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn [disjoint_from]. repeat split; lia.
      - split; [intros i Hi| intros e He]; cbn [disjoint_from fst snd].
        + repeat split; lia.
        + destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
          pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. olin ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
          pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8k _]. repeat split; lia. }
    pose proof (tail_facts mb n Hn HP HN (proj2 (proj2 HMB)) ltac:(lia)) as TF. cbv zeta in TF. rewrite <- ET in TF.
    (nelim TF 7%nat; intros HT1 HT2 HT3 HT4 HT5 HT6 HT7).
    (* [comment removed for export] *)
    pose proof (rr_ptrarr st mv' HRv) as RPv. destruct RPv as (VPAv & _).
    pose proof (CPW' mb mv' HMB FRESH CPv) as CPW. pose proof (RFW' mb mv' HMB RFv) as RFW.
    pose proof (mmap_cells st mv' HRv) as MCv.
    (* [comment removed for export] *)
    apply lscps_step_evt.
    eapply (msb_block gp tp F fc m7 (smapsize n) ltac:(lia) _ _ _ _ k1 (st_nreserved st) (nsec st) k2 SEC7); [exact MI7|].
    intros q11 q12 q15 q16.
    eapply (la_B sp gp tp s10 s11 F fc m7 0) with (nsc := nsec st) (nres := st_nreserved st); [lia| lia|].
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m7 mb [C8 (wz mb); C8 (wz (smapsize n)); C8 (wz (needed n))] [C8 h24]) HDR7) as [HDR7a H24_7].
    cbn [cells_size Cells.csize Nat.add] in H24_7.
    assert (GM1 : gmono (mkG G R) (mkG ((wlo, whi) :: G) R1)) by (intros w Hw; cbn; right; exact Hw).
    assert (RW : R - R1 = smapsize n + (whi - wlo)) by (subst R1; lia).
    pose proof (rt_prov_secreg' st mb n WF FRESH ROOM) as RPS.
    assert (HM1 : RTMODEL (st_secreg st mb n) (mm_add_map (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) mo)).
    { exact (RTMODEL_secreg' st mb n WF Hn HN (hmb_ablk _ _ HMB) FRESH ROOM mo HM ltac:(lia) PLN). }
    destruct (nsec st =? st_nreserved st) eqn:EG.
    - (* [comment removed for export] *)
      apply Z.eqb_eq in EG as EGe. assert (EG' : sec_grow st = true) by (unfold sec_grow; rewrite EGe; apply Z.eqb_refl).
      (nelimp (grow_site_range' st WF ROOM EG') 4%nat; intros GS1 GS2 GS3 _). rewrite <- EGe in GS1, GS2, GS3. unfold PTRARR_BLOCK in GS2.
      rewrite <- EGe. replace (st_nreserved st) with (nsec st) in SEC7 by exact EGe.
      eapply (la_G1 sp gp tp s10 s11 F fc m7 0) with (PA := st_pa st) (nres := nsec st) (nsc := nsec st); [lia| lia| unfold PTRARR_RES_SIZE in *; lia| exact SEC7|].
      apply evt_done. apply lscps_assume. intros _ HOK7 _. unfold A_MAPORDIE, PTRARR_BLOCK. cbv beta delta [wz].
      assert (MC7 : mmap_consts m7).
      { eapply (mmap_consts_munch _ mv' m7 MCv MU7); unfold Wv; rewrite A_SECONDARY_val, A_GSTATS_val; (cut_on [SF CEIL' HMBn SHBk ALx OLx ALx0 HT1 HT6 GS1] djs). }
      pose proof (secreg_fixed_site' st mb n WF (hmb_ablk _ _ HMB) FRESH ROOM mo HOK HM EG') as SITE. rewrite <- EGe in SITE. unfold PTRARR_BLOCK in SITE.
      eapply mapordie_spec with (A := st_pa st + 8 * nsec st) (sz := 131072) (lo := lo) (R := R1) (G := (wlo, whi) :: G);
        [exact MC7| exact MI7| rewrite unsigned_lit by lia; exact ST7| rewrite unsigned_lit by lia; split; [exact HCEIL| lia]| lia| exact GS3| unfold AIMG_HI; lia
        | apply mmap_fixed_site_add_map; exact SITE
        | unfold SEC_ALLOC_COST, SEC_SLOT_TAX in DEP; pose proof (rt_prov_nonneg st WF); subst R1; lia|].
      intros e5 e6 e7 e11 e12 e13 e14 e15 e16 e17 e28 e29 e30 e31 m8 MI8 MU8c WM8c ST8 ZPA.
      rewrite unsigned_lit in MU8c, ST8 by lia.
      replace (ret_pc (Z_to_bv 64 0x36cc8)) with (Z_to_bv 64 0x36cc8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      sepM. assert (MU8 : munch (Wv mb) mv' m8) by (eapply munch_trans; [exact MU7|]; eapply munch_weaken; [| exact MU8c]; subfp).
      pose proof (wmono_trans asegs _ _ _ WM7 WM8c) as WM8.
      pose proof SEC7 as SEC8. eapply (rw_cells_transport asegs _ m7 m8) in SEC8; [| exact MU8c| exact WM8c| djs].
      apply lscps_assume. intros _ HOK8 _.
      apply lscps_step_evt.
      eapply (la_G2 sp gp tp s10 s11 F fc m8 0 MI8) with (PA := st_pa st) (nres := nsec st) (nsc := nsec st); [lia| lia| unfold PTRARR_RES_SIZE in *; lia| exact SEC8|].
      intros m9 SEC9 MI9 MU9c WM9c. apply evt_done.
      sepM. assert (MU9 : munch (Wv mb) mv' m9) by (eapply munch_trans; [exact MU8|]; eapply munch_weaken; [| exact MU9c]; subfp).
      pose proof (wmono_trans asegs _ _ _ WM8 WM9c) as WM9.
      assert (MU79 : munch [(lo, bv_unsigned sp + -96); (st_pa st + 8 * nsec st, st_pa st + 8 * nsec st + 131072); (683096 + 48, 683096 + 56)] m7 m9).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU8c]| eapply munch_weaken; [| exact MU9c]];
          repeat (first [apply sub_fp_nil | eapply sub_fp_cons_in; [inW 0%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 1%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 2%nat| lia| lia|]]). }
      pose proof (wmono_trans asegs _ _ _ WM8c WM9c) as WM79.
      pose proof (vis_of_CB m8 _ 131072 _ ltac:(lia) ZPA) as VB8.
      destruct (vis_c8 m8 _ _ (st_pa st + 8 * nsec st) VB8 ltac:(lia) ltac:(lia)) as [jp PC8].
      eapply (la_tail mb mv' m9 _ ((wlo, whi) :: G) (R1 - 131072) (nsec st + 2^14) v T b1 b2 b3 k1 k2 j4 jg jf h24 jp);
        [exact HMB| exact FRESH| rewrite EG', <- EGe; reflexivity| unfold PTRARR_RES_SIZE in *; lia| exact HRv| exact MU9| exact WM9| exact MI9| exact VMv| exact VSH
        | exact SEC9
        | eapply rw_cells_transport; [exact HDR7a| exact MU79| exact WM79| (cut_on [SF CEIL' HMBn PRn DJP GS2] djs)]
        | eapply rw_cells_transport; [exact H24_7| exact MU79| exact WM79| (cut_on [SF CEIL' HMBn PRn DJP GS2] djs)]
        | eapply rw_cells_transport; [exact PC8| exact MU9c| exact WM9c| djs]
        | eapply rw_cells_transport; [exact GST7| exact MU79| exact WM79| djs]
        | split; [exact HV1| exact HV3]
        | eapply rw_cells_transport; [exact MW7| exact MU79| exact WM79| djs]
        | eapply rw_cells_transport; [exact MJ7| exact MU79| exact WM79| djs]
        | eapply rw_cells_transport; [exact FR7| exact MU79| exact WM79| djs]
        | eapply (stk_transport_disjoint asegs _ m8 m9); [exact ST8| exact MU9c| exact WM9c| djs]
        | | eapply rw_cells_transport; [exact PSH1_7| exact MU79| exact WM79| djs]
        | exact ET
        | eapply rw_cells_transport; [exact PSH2_7| exact MU79| exact WM79| djs]
        | exact (CPW m9 MU9 WM9)| exact (RFW m9 MU9)
        | | | apply FRONTR_commit; eapply FRONTR_le; [exact HFR1| subst R1; unfold SEC_ALLOC_COST, SEC_SLOT_TAX in *; pose proof (rt_prov_nonneg st WF); lia| subst R1; lia]
        | rewrite EG' in RPS; unfold PTRC in RPS; unfold SEC_ALLOC_COST, SEC_SLOT_TAX in *; lia
        | intros w Hw; cbn; right; exact Hw
        | intros xw Hxw; cbn [g_win]; rewrite in_winb_cons; apply orb_true_iff; left; cbn [fst snd]; apply andb_true_iff; split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia] ].
      + (* [comment removed for export] *)
        replace (st_pa st + 8 * (nsec st + 2 ^ 14)) with (st_pa st + 8 * nsec st + 131072) by lia.
        eapply stk_merge; [| eapply (stk_transport_disjoint asegs _ m8 m9); [exact VB8| exact MU9c| exact WM9c| djs]| lia].
        rewrite <- EGe in VPAv. eapply stk_wmono_noseg; [exact VPAv| exact WM9| unfold AIMG_HI; lia].
      + (* [comment removed for export] *)
        rewrite commit_add_map_comm.
        pose proof (RTMODEL_commit_pa' st mb n WF (hmb_ablk _ _ HMB) FRESH ROOM mo st HOK HM HM EG') as HMc. rewrite <- EGe in HMc. unfold PTRARR_BLOCK in HMc. cbv beta delta [wz] in HMc.
        apply (RTMODEL_secreg' st mb n WF Hn HN (hmb_ablk _ _ HMB) FRESH ROOM _ HMc ltac:(lia)).
        apply (sec_plain_commit mo _ _ mb (smapsize n) HOK PLN). rewrite !unsigned_lit by (unfold PTRARR_RES_SIZE in *; lia). unfold PTRARR_RES_SIZE in *. lia.
      + (* [comment removed for export] *)
        assert (GW9o : GWIN st m9 mo (mkG ((wlo, whi) :: G) (R1 - 131072))).
        { intros x Hw Hz Hr. apply (GWIN_mem st mv' m9 _ _ GWv HOK7 WM9 x Hw); [rewrite mm_add_map_lzf; exact Hz| exact Hr]. }
        pose proof (GWIN_commit_pa' st mb n WF (hmb_ablk _ _ HMB) FRESH ROOM mo st m9 (mkG ((wlo, whi) :: G) (R1 - 131072)) HOK HM GW9o EG') as GWc.
        rewrite <- EGe in GWc. unfold PTRARR_BLOCK in GWc. cbv beta delta [wz] in GWc.
        rewrite commit_add_map_comm. intros x Hw Hz Hr. rewrite mm_add_map_lzf in Hz. exact (GWc x Hw Hz Hr).
    - (* [comment removed for export] *)
      apply Z.eqb_neq in EG as EGn. assert (EG' : sec_grow st = false) by (unfold sec_grow; apply Z.eqb_neq; exact EGn).
      apply evt_done. apply lscps_assume. intros _ HOK7 _.
      pose proof (stk_wmono_noseg _ _ _ _ VPAv WM7 ltac:(unfold AIMG_HI; lia)) as VPA7.
      destruct (vis_c8 m7 _ _ (st_pa st + 8 * nsec st) VPA7 ltac:(lia) ltac:(lia)) as [jp PC7].
      eapply (la_tail mb mv' m7 _ ((wlo, whi) :: G) R1 (st_nreserved st) v T b1 b2 b3 k1 k2 j4 jg jf h24 jp);
        [exact HMB| exact FRESH| rewrite EG'; lia| unfold PTRARR_RES_SIZE in *; lia| exact HRv| exact MU7| exact WM7| exact MI7| exact VMv| exact VSH
        | exact SEC7| exact HDR7a| exact H24_7| exact PC7| exact GST7| split; [exact HV1| exact HV3]| exact MW7| exact MJ7| exact FR7| exact ST7| exact VPA7
        | exact PSH1_7| exact ET| exact PSH2_7| exact (CPW m7 MU7 WM7)| exact (RFW m7 MU7)| exact HM1
        | eapply GWIN_mem; [exact GWv| exact HOK7| exact WM7]
        | eapply FRONTR_le; [exact HFR1| subst R1; unfold SEC_ALLOC_COST, SEC_SLOT_TAX in *; pose proof (rt_prov_nonneg st WF); lia| subst R1; lia]
        | rewrite EG' in RPS; unfold SEC_ALLOC_COST, SEC_SLOT_TAX in *; lia
        | exact GM1
        | intros xw Hxw; cbn [g_win]; rewrite in_winb_cons; apply orb_true_iff; left; cbn [fst snd]; apply andb_true_iff; split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia] ].
  Qed.

  Lemma la_mid : forall (mb : Z) (mv' m6 : word -> option byte) (wlo whi R1 T : Z) (jf : list byte)
      (u5' u6' u7' u11' u12' u13' u14' u15' u16' u17' u28' u29' u30' u31' : word),
    (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 ->
    (forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb) ->
    RTREP st mv' -> vis mv' mb (mb + smapsize n) -> vis mv' (SH mb) (SH (mb + smapsize n)) ->
    cli_pres st (bv_unsigned sp) m mv' -> rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m mv' ->
    GWIN st mv' (mm_add_map (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) mo) (mkG ((wlo, whi) :: G) R1) ->
    FRONTR (mm_add_map (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) mo) (R - smapsize n) ->
    sec_plain mo mb (smapsize n) ->
    R1 = R - smapsize n - (whi - wlo) -> 0 <= whi - wlo <= smapsize n / 8 + 7168 ->
    munch [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n))] mv' m6 -> munch (Wv mb) mv' m6 -> wmono asegs mv' m6 -> mem_inv asegs m6 ->
    rw_cells asegs m6 (bv_unsigned sp + -96) [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    vis m6 lo (bv_unsigned sp + -96) ->
    rw_cells asegs m6 (SH mb) [CB 512 (repeat (Z_to_bv 8 250) 512)] ->
    T = mb + smapsize n - (sec_alloc_beg mb + needed n) ->
    rw_cells asegs m6 (SH (sec_alloc_beg mb + needed n)) [CB (Z.to_nat (T / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (T / 8)))] ->
    wlo <= SH mb /\ SH (mb + smapsize n) <= whi ->
    LSCPS asegs (sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m (mkG G R))
      (MS (mkR (wz 0x36994) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u5' u6' u7' (wz A_GSTATS) (wz A_SECONDARY) (wz (st_t st + T_STATS)) u11' u12' u13' u14' u15' u16' u17'
               (wz (smapsize n)) (wz (needed n)) (wz mb) (wz (sec_alloc_beg mb + needed n)) (wz (mb + smapsize n)) (wz (sec_alloc_beg mb + needed n))
               (wz 7) (wz (sec_alloc_beg mb)) s10 s11 u28' u29' u30' u31')
          F (Z_to_bv 64 0x36994) fc None m6 (seg_rom asegs))
      (mm_add_map (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) mo) (mkG ((wlo, whi) :: G) R1).
  Proof.
    intros until u31'. intros HMB FRESH HRv VMv VSH CPv RFv GWv HFR1 PLN ER1 WBd MT6 MU6 WM6 MI6 FR6 ST6 PSH1_6 ET PSH2_6 WIv.
    pose proof (smapsize_facts n Hn HP HN) as SF. pose proof (pa_range st WF) as PR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    pose proof (nsec_room st mo (mkG G R) n WF HM HBINV DEP Hn) as ROOM.
    pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR.
    assert (HMBn : 0x5ff000 <= mb /\ mb + smapsize n <= alloc_ceiling) by (unfold AIMG_HI, CEIL in HMB; lia).   (* [comment removed for export] *)
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHBk. pose proof (rt_SH_bounds (mb + smapsize n) ltac:(lia)) as SHBk2.
    pose proof (hmb_ablk _ _ HMB) as HBKk. olin HBKk.
    pose proof (t_range st WF) as TRk. olin TRk. pose proof (pa_range st WF) as PRk. olin PRk.   (* [comment removed for export] *)
    pose proof PR as PRn. unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in PRn.
    assert (DJT : st_t st + 4096 <= mb \/ mb + smapsize n <= st_t st).
    { destruct (FRESH (st_t st, st_t st + 4096)) as [D|D]; [| cbn [fst snd] in D; lia| cbn [fst snd] in D; lia].
      unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (st_t st, 4096). split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))]. }
    assert (DJP : st_pa st + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= st_pa st).
    { destruct (FRESH (st_pa st, st_pa st + PTRARR_RES_SIZE) ltac:(unfold rt_ranges; right; left; reflexivity)) as [D|D]; cbn [fst snd] in D; lia. }
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
    pose proof (SH_mono mb (mb + smapsize n) ltac:(lia)) as SHle. pose proof (SH_mono (mb + smapsize n) (@CEIL ACEIL) ltac:(lia)) as SHC. rewrite SH_CEIL in SHC.
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHlo.
    assert (FOK : fresh_ok st [(mb, mb + smapsize n)]).
    { intros f [<-|[]]. cbn [fst snd]. split; [exact (hmb_ablk _ _ HMB)|]. intros r Hr. destruct (FRESH r Hr); lia. }
    assert (RTT : forall mx, munch [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n))] mv' mx -> wmono asegs mv' mx -> RTREP st mx).
    { intros mx MUx WMx.
      eapply (RTREP_szi st _ [(mb, mb + smapsize n)] mv' mx WF); [| exact FOK| intros f [<-|[]]; cbn; unfold CEIL; lia| | | exact MUx| exact WMx| exact HRv].
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|]. constructor; [| constructor].
        eapply (sz_ok_fresh_sh st _ (mb, mb + smapsize n)); [left; reflexivity| cbn; lia| cbn; lia].
      - unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn [disjoint_from]. repeat split; lia.
      - split; [intros i Hi| intros e He]; cbn [disjoint_from fst snd].
        + repeat split; lia.
        + destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
          pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. olin ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
          pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8k _]. repeat split; lia. }
    pose proof (tail_facts mb n Hn HP HN (proj2 (proj2 HMB)) ltac:(lia)) as TF. cbv zeta in TF. rewrite <- ET in TF.
    (nelim TF 7%nat; intros HT1 HT2 HT3 HT4 HT5 HT6 HT7).

    pose proof (RTT m6 MT6 WM6) as HR6.
    (* [comment removed for export] *)
    (nelimp (sec_obj_cells st m6 HR6) 5%nat; intros k1 k2 k3 SEC6 MUT6). rewrite A_SECONDARY_val in SEC6, MUT6. cbv beta delta [wz] in SEC6.
    replace (683096 + 616) with 683712 in MUT6 by reflexivity.
    (nelim (mutex_cells_of m6 683712 k3 MUT6) 10%nat; intros kk j4 b1 b2 b3 HK E0 E1 MW6 MJ6). replace (683712 + 4) with 683716 in MJ6 by reflexivity. clear MUT6.
    pose proof (rr_thread st m6 HR6) as RT6. destruct RT6 as (VT6 & _).
    (nelim (vis_c8x2 m6 _ _ (st_t st + 2872) VT6 ltac:(lia) ltac:(lia)) 3%nat; intros j72 j80 TS6).
    pose proof (stk_wmono_noseg _ _ _ _ VMv WM6 ltac:(unfold AIMG_HI; lia)) as VM6.
    (nelim (vis_c8x4 m6 _ _ mb VM6 ltac:(lia) ltac:(lia)) 5%nat; intros h0 h8 h16 h24 HDR6).
    pose proof (rr_alloc st mv' HRv) as RAv. (nelim RAv 4%nat; intros _ _ [jg GSTv] _). rewrite A_GSTATS_val in GSTv.
    pose proof GSTv as GST6. eapply (rw_cells_transport asegs _ mv' m6) in GST6; [| exact MT6| exact WM6| djs].
    (* [comment removed for export] *)
    apply lscps_step_evt.
    eapply (la_A3 sp gp tp s10 s11 F fc m6 n mb (st_t st) kk _ _ _ k1 (st_nreserved st) (nsec st) k2 j72 j80 h0 h8 h16 h24 b1 b2 b3 j4 Hn HP HN HMB);
      [destruct TRk as [_ TRc]; unfold bandf, CEIL, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *; lia| exact DJT| exact HK| lia| exact E1| exact MI6| exact SEC6| exact TS6| exact HDR6| exact MW6| exact MJ6|].
    intros ms7 A3P. (nelim A3P 14%nat; intros r5 r6 r7 r11 r15 r17 r28 r29 r30 r31 v m7 -> A3M).
    destruct A3M as (MU7c & WM7c & MI7 & [j72' [j80' TS7]] & HDR7 & -> & HV1 & HV2 & HV3 & MW7 & MJ7).
    sepM. assert (MU7 : munch (Wv mb) mv' m7) by (eapply munch_trans; [exact MU6|]; eapply munch_weaken; [| exact MU7c]; subfp).
    pose proof (wmono_trans asegs _ _ _ WM6 WM7c) as WM7.
    pose proof SEC6 as SEC7. eapply (rw_cells_transport asegs _ m6 m7) in SEC7; [| exact MU7c| exact WM7c| (cut_on [SF HMBn ALx OLx HT1 HT6 HV1] djs)].
    pose proof FR6 as FR7. eapply (rw_cells_transport asegs _ m6 m7) in FR7; [| exact MU7c| exact WM7c| djs].
    pose proof PSH1_6 as PSH1_7. eapply (rw_cells_transport asegs _ m6 m7) in PSH1_7; [| exact MU7c| exact WM7c| djs].
    pose proof PSH2_6 as PSH2_7. eapply (rw_cells_transport asegs _ m6 m7) in PSH2_7; [| exact MU7c| exact WM7c| djs].
    pose proof GST6 as GST7. eapply (rw_cells_transport asegs _ m6 m7) in GST7; [| exact MU7c| exact WM7c| djs].
    pose proof ST6 as ST7. eapply (stk_transport_disjoint asegs _ m6 m7) in ST7; [| exact MU7c| exact WM7c| djs].
    clear MU7c WM7c SEC6 FR6 PSH1_6 PSH2_6 GST6 ST6 TS6 HDR6 MW6 MJ6 VT6 VM6 HR6 MI6 TS7.
    apply evt_done.
    eapply (la_mid2 mb mv' m7 wlo whi R1 T v jf k1 k2 j4 jg b1 b2 b3 h24); [exact HMB| exact FRESH| exact HRv| exact VMv| exact VSH| exact CPv| exact RFv| exact GWv| exact HFR1
      | exact PLN| exact ER1| exact WBd| exact MU7| exact WM7| exact MI7| exact SEC7| exact FR7| exact PSH1_7| exact ET| exact PSH2_7| exact GST7| exact ST7| exact HDR7
      | exact HV1| exact HV3| exact MW7| exact MJ7| exact WIv].
  Qed.


  Lemma la_grant : forall (a : word) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2,
    mmap_grant mo a (smapsize n) ->
    mem_inv asegs m2 -> munch [(lo, (bv_unsigned sp) + -96); (bv_unsigned a, bv_unsigned a + smapsize n)] m1 m2 -> wmono asegs m1 m2 ->
    stk asegs m2 lo ((bv_unsigned sp) + -96) ->
    rw_cells asegs m2 (bv_unsigned a) [CB (Z.to_nat (smapsize n)) (repeat (Z_to_bv 8 0) (Z.to_nat (smapsize n)))] ->
    LSCPS asegs (sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m (mkG G R))
      (MS (mkR (Z_to_bv 64 0x36928) (Z_to_bv 64 ((bv_unsigned sp) + -96)) gp tp y5 y6 y7 (Z_to_bv 64 A_GSTATS) (Z_to_bv 64 A_SECONDARY) a y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 (smapsize n)) (Z_to_bv 64 (needed n)) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x36928) fc None m2 (seg_rom asegs))
      (mm_add_map a (Z_to_bv 64 (smapsize n)) mo) (mkG G (R - smapsize n)).
  Proof.
    intros until m2. intros GR MI2 MU2 WM2 ST2 ZNEW.
    pose proof (smapsize_facts n Hn HP HN) as SF. pose proof (pa_range st WF) as PR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    pose proof (nsec_room st mo (mkG G R) n WF HM HBINV DEP Hn) as ROOM.
    pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. cbn in RA.
    (nelimp GR 4%nat; intros GA GP GC GF). idtac. rewrite page_size_eq in GA.
    pose proof (grant_fresh st mo a (smapsize n) HOK HM WF ltac:(lia) GR) as FRESH.
    pose proof (FRONTR_grant mo R a (smapsize n) HFR ltac:(unfold FR_MINGRANT; lia) ltac:(lia) ltac:(unfold SEC_ALLOC_COST, SEC_SLOT_TAX in DEP; pose proof (rt_prov_nonneg st WF); lia)) as HFR1.
    pose proof (grant_ablk st mo a (smapsize n) HOK HM ltac:(lia) GR) as HKH.   (* [comment removed for export] *)
    pose proof (grant_plain mo a (smapsize n) HOK ltac:(lia) GR) as PLN.
    set (mb := bv_unsigned a) in *.
    assert (SZR : smapsize n <= R) by (unfold SEC_ALLOC_COST, SEC_SLOT_TAX in DEP; pose proof (rt_prov_nonneg st WF); lia).
    assert (HMB : (AIMG_HI <= mb /\ bandf (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0).
    { apply hmb_of_ablk; [exact HKH| subst mb; lia]. }
    pose proof HKH as HKHk. fold mb in HKHk. olin HKHk.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (MU02 : munch [(lo, (bv_unsigned sp)); (mb, mb + smapsize n)] m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn; intros; lia|].
      eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn; intros; lia. }
    pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM02.
    destruct FR1 as [jf FR2]. eapply (rw_cells_transport asegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; lia].
    assert (FOK : fresh_ok st [(mb, mb + smapsize n)]).
    { intros f [<-|[]]. cbn [fst snd]. split; [exact (hmb_ablk _ _ HMB)|]. intros r Hr. destruct (FRESH r Hr); lia. }
    assert (HR2 : RTREP st m2).
    { eapply (RTREP_szi st _ [(mb, mb + smapsize n)] m m2 WF); [| exact FOK| intros f [<-|[]]; cbn; unfold CEIL; lia| | | exact MU02| exact WM02| exact HR].
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|]. constructor; [| constructor].
        eapply (sz_ok_fresh st _ (mb, mb + smapsize n)); [left; reflexivity| cbn; lia| cbn; lia].
      - unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn. unfold KHIGHMEM_BEG, AIMG_HI in *. repeat split; lia.
      - split.
        + intros i Hi. cbn. unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in *.
          pose proof (FRESH (st_pa st, st_pa st + PTRARR_RES_SIZE) ltac:(unfold rt_ranges; right; left; reflexivity)) as D. cbn [fst snd] in D.
          unfold PTRARR_RES_SIZE in D. lia.
        + intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
          pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. olin ER.
          pose proof (FRESH (fst e, fst e + smapsize (snd e))) as D. cbn [fst snd] in D.
          cbn. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *.
          assert (IR : In (fst e, fst e + smapsize (snd e)) (rt_ranges st)).
          { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right. left. apply in_map_iff. exists e. split; [reflexivity| exact HE]. }
          specialize (D IR). pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8g _]. lia. }
    (* [comment removed for export] *)
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
    assert (CP2 : cli_pres st (bv_unsigned sp) m m2).
    { unfold cli_pres. eapply cj_pres_of_munch; [exact MU02| exact WM02|]. intros x Hx HC. cbn. split; [| split; [| exact I]].
      - intros Hin. exact (below_sp_not_client st WF (bv_unsigned sp) x ltac:(unfold CEIL in *; lia) HC).
      - intros Hin. exact (fresh_not_client st WF (bv_unsigned sp) HSPc mb (smapsize n) FRESH (hmb_ablk _ _ HMB) x Hin HC). }
    assert (RF2 : rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m2).
    { eapply rt_frame_of_munch; [exact MU02|]. intros iv [<-|[<-|[]]]; [left; cbn; lia|]. right. exists (mb, mb + smapsize n). split; [| cbn; lia].
      unfold secondary_fp. cbn. tauto. }
    (* [comment removed for export] *)
    assert (SHB : SH 0 <= SH mb /\ SH (mb + smapsize n) <= SH CEIL /\ SH mb + smapsize n / 8 = SH (mb + smapsize n) /\ (SH mb) mod 512 = 0 /\ (smapsize n / 8) mod 512 = 0).
    { split; [apply SH_mono; lia|]. split; [apply SH_mono; lia|]. rewrite !SH_def. unfold SHADOW_OFFSET. (nelim SF 4%nat; intros _ _ SM _). Z.div_mod_to_equations. lia. }
    change (SH 0) with 0x7fff8000 in SHB. rewrite SH_CEIL in SHB.   (* [comment removed for export] *)
    set (wlo := SH mb / 4096 * 4096). set (whi := (SH (mb + smapsize n) + 4095) / 4096 * 4096).
    assert (WB : wlo <= SH mb /\ SH mb < wlo + 4096 /\ SH (mb + smapsize n) <= whi /\ whi < SH (mb + smapsize n) + 4096
                 /\ wlo mod 4096 = 0 /\ whi mod 4096 = 0 /\ whi - wlo <= smapsize n / 8 + 7168).
    { subst wlo whi. Z.div_mod_to_equations. lia. }
    eapply (lscps_open asegs _ _ _ G (R - smapsize n) wlo whi).
    { unfold win_ok. cbn [fst snd]. (lia_on SF RA SHB WB). }
    { replace (4096 * ((whi - wlo) / 4096)) with (whi - wlo) by (Z.div_mod_to_equations; lia).
      unfold SEC_ALLOC_COST, SEC_SLOT_TAX in DEP. pose proof (rt_prov_nonneg st WF). lia. }
    intros mv' Emv ZFN FRZ. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS msw] in Emv |- *.
    replace (4096 * ((whi - wlo) / 4096)) with (whi - wlo) by (Z.div_mod_to_equations; lia).
    set (R1 := R - smapsize n - (whi - wlo)) in *.
    (* [comment removed for export] *)
    pose proof HM as HM'. (nelim HM' 8%nat; intros _ _ _ _ _ _ LZS _).
    assert (VNN : forall x : word, wlo <= bv_unsigned x < whi -> lzf mo x = true -> mv' x <> None).
    { intros x Hx Hz. destruct (in_winb G x) eqn:EW.
      - assert (V0 : m x <> None).
        { apply (GWIN_win st m mo _ HG x); [exact EW| exact Hz|].
          (* [comment removed for export] *)
          (nelim WB 7%nat; intros W1 W2 W3 W4 W5 W6 _). rewrite !SH_def in W1, W2, W3, W4. unfold SHADOW_OFFSET in W1, W2, W3, W4.
          unfold RTSH, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG. change (SH AIMG_LO) with 0x7fffa000.
          pose proof (ablk_lin _ _ HKHk) as KL. pose proof (ablk_disj_band _ _ HKHk) as KD. unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in KL, KD.
          clear - Hx W1 W2 W3 W4 W5 W6 KL KD. destruct KD as [ADl|ADh]; [left| right; left]; Z.div_mod_to_equations; lia. }
        assert (V2 : m2 x <> None).
        { rewrite (MU02 x); [exact V0|]. cbn. unfold KHIGHMEM_BEG, AIMG_HI in *. lia. }
        rewrite Emv, (open_mem_mono _ _ _ _ _ V2). exact V2.
      - rewrite (FRZ x Hx); [discriminate| rewrite mm_add_map_lzf; exact Hz| exact EW]. }
    assert (VSH : stk asegs mv' (SH mb) (SH (mb + smapsize n))).
    { apply stk_of_some; [lia| lia|]. intros x Hx. apply VNN; [lia|]. apply LZS. unfold KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI. rewrite !SH_def in Hx. unfold SHADOW_OFFSET in Hx.
      pose proof (ablk_lin _ _ HKHk) as KL. pose proof (ablk_disj_band _ _ HKHk) as KD. unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in KL, KD.
      clear - Hx KL KD. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    pose proof (RTREP_open (owf (mm_add_map a (Z_to_bv 64 (smapsize n)) mo) G) wlo whi ZFN ltac:(unfold AIMG_HI; lia) st m2 HR2) as HRv. rewrite <- Emv in HRv.
    pose proof (rw_cells_open asegs _ wlo whi m2 _ _ ZFN FR2) as FRv. rewrite <- Emv in FRv.
    pose proof (rw_cells_open asegs _ wlo whi m2 _ _ ZFN ZNEW) as ZNv. rewrite <- Emv in ZNv.
    pose proof (stk_open asegs _ wlo whi m2 _ _ ZFN ST2) as STv. rewrite <- Emv in STv.
    pose proof (mem_inv_open asegs _ wlo whi m2 ZFN MI2) as MIv. rewrite <- Emv in MIv.
    pose proof (wmono_open asegs (owf (mm_add_map a (Z_to_bv 64 (smapsize n)) mo) G) wlo whi m2 m2 (wmono_refl asegs m2)) as WM2v. rewrite <- Emv in WM2v.
    assert (CPv : cli_pres st (bv_unsigned sp) m mv').
    { eapply cli_pres_trans; [exact CP2|]. unfold cli_pres. rewrite Emv. apply cj_pres_open.
      intros x Hx HC Hw. (nelim WB 5%nat; intros W1 W2 W3 W4 _). (nelim SHB 3%nat; intros SB1 SB2 _).
      destruct (Z_lt_le_dec x (SH alloc_ceiling)) as [LTc|GEc].
      - apply (client_highshadow_vis st WF (bv_unsigned sp) HSPc mb (smapsize n) (hmb_ablk _ _ HMB) m2 x HR2 Hx HC).
        unfold KLOWSHADOW_BEG, CEIL. clear - LTc Hw W1 W2 SB1. lia.
      - (* [comment removed for export] *)
        pose proof (GWIN_mem st m m2 mo _ HG HOK WM02) as GW2c.
        assert (XB : SH alloc_ceiling <= x < SH alloc_ceiling + 4096) by (rewrite SH_def in *; unfold SHADOW_OFFSET in *; clear - GEc Hw W4 SB2; lia).
        assert (XU : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).
        apply (GWIN_ceilpage st m2 mo _ GW2c (wa x)); [rewrite XU; exact XB| | ].
        + apply LZS. rewrite XU. right. rewrite SH_def in XB. unfold SHADOW_OFFSET, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *. pose proof (@alloc_ceiling_lo ACEIL). pose proof (@alloc_ceiling_hi ACEIL). clear - XB H H0. Z.div_mod_to_equations. lia.
        + rewrite XU. right. left. rewrite SH_def in XB. unfold SHADOW_OFFSET, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *. pose proof (@alloc_ceiling_lo ACEIL). pose proof (@alloc_ceiling_hi ACEIL). clear - XB H H0. Z.div_mod_to_equations. lia. }
    assert (RFv : rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m mv').
    { eapply rt_frame_trans; [exact RF2|]. rewrite Emv. apply rt_frame_open. intros x Hx.
      exists (SH mb - 4096), (SH (mb + smapsize n) + 4096). split; [| lia]. unfold secondary_fp. cbn. tauto. }
    assert (GWv : GWIN st mv' (mm_add_map a (Z_to_bv 64 (smapsize n)) mo) (mkG ((wlo, whi) :: G) R1)).
    { pose proof (GWIN_mem st m mv' mo (mkG G R) HG HOK (wmono_trans asegs _ _ _ WM02 WM2v)) as GW2.
      apply (GWIN_open st mv' _ G (R - smapsize n)).
      - intros x Hw Hz HRS. apply (GW2 x Hw); [rewrite mm_add_map_lzf in Hz; exact Hz| exact HRS].
      - intros x Hx Hz _. apply VNN; [exact Hx|]. rewrite mm_add_map_lzf in Hz. exact Hz. }
    clear FR2 ZNEW ST2 MI2.
    lazymatch goal with |- LSCPS _ _ (msw (MS ?RR ?FF ?p ?c ?v ?mm ?ro) ?mv) _ _ => change (msw (MS RR FF p c v mm ro) mv) with (MS RR FF p c v mv ro) end.
    (* [comment removed for export] *)
    assert (Ea : a = Z_to_bv 64 mb) by (subst mb; symmetry; apply Z_to_bv_bv_unsigned).
    clearbody mb. subst a. clear GR GF.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR.
    assert (HMBn : 0x5ff000 <= mb /\ mb + smapsize n <= alloc_ceiling) by (unfold AIMG_HI, CEIL in HMB; lia).   (* [comment removed for export] *)
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHBk. pose proof (rt_SH_bounds (mb + smapsize n) ltac:(lia)) as SHBk2.
    pose proof (hmb_ablk _ _ HMB) as HBKk. olin HBKk.
    pose proof (t_range st WF) as TRk. olin TRk. pose proof (pa_range st WF) as PRk. olin PRk.   (* [comment removed for export] *)
    pose proof PR as PRn. unfold KHIGHMEM_BEG, AIMG_HI, PTRARR_RES_SIZE in PRn.
    assert (DJT : st_t st + 4096 <= mb \/ mb + smapsize n <= st_t st).
    { destruct (FRESH (st_t st, st_t st + 4096)) as [D|D]; [| cbn [fst snd] in D; lia| cbn [fst snd] in D; lia].
      unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (st_t st, 4096). split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))]. }
    assert (DJP : st_pa st + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= st_pa st).
    { destruct (FRESH (st_pa st, st_pa st + PTRARR_RES_SIZE) ltac:(unfold rt_ranges; right; left; reflexivity)) as [D|D]; cbn [fst snd] in D; lia. }
    pose proof (SH_mono mb (mb + smapsize n) ltac:(lia)) as SHle. pose proof (SH_mono (mb + smapsize n) (@CEIL ACEIL) ltac:(lia)) as SHC. rewrite SH_CEIL in SHC.
    pose proof (rt_SH_bounds mb ltac:(lia)) as SHlo.
    (* [comment removed for export] *)
    assert (RTT : forall mx, munch [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n))] mv' mx -> wmono asegs mv' mx -> RTREP st mx).
    { intros mx MUx WMx.
      eapply (RTREP_szi st _ [(mb, mb + smapsize n)] mv' mx WF); [| exact FOK| intros f [<-|[]]; cbn; unfold CEIL; lia| | | exact MUx| exact WMx| exact HRv].
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|]. constructor; [| constructor].
        eapply (sz_ok_fresh_sh st _ (mb, mb + smapsize n)); [left; reflexivity| cbn; lia| cbn; lia].
      - unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn [disjoint_from]. repeat split; (lia_on SF CEIL' RA SHB SHBk2).
      - split; [intros i Hi| intros e He]; cbn [disjoint_from fst snd].
        + repeat split; lia.
        + destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
          pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. olin ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
          pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8k _]. repeat split; lia. }
    pose proof (vis_of_CB mv' mb (smapsize n) _ ltac:(lia) ZNv) as VMv.
    (* [comment removed for export] *)
    (nelimp (sec_obj_cells st mv' HRv) 5%nat; intros j1 j2 j3 SECv MUTv). rewrite A_SECONDARY_val in SECv, MUTv. cbv beta delta [wz] in SECv.
    pose proof (rtrep_artcells st mv' HRv) as AC. pose proof (artcells_icpt mv' AC) as ICv. pose proof (artcells_poison mv' AC) as PCv. clear AC.
    destruct (stk_split asegs mv' (SH mb) (SH mb + 512) (SH (mb + smapsize n)) VSH ltac:(lia)) as [VS1 VS2].
    destruct (vis_carve mv' _ _ (SH mb) 512 VS1 ltac:(lia) ltac:(cbn; lia)) as [junk1 SH1].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply lscps_step_evt.
    eapply (la_A1 sp gp tp s4 s6 s7 s9 s10 s11 F fc n Hn HP HN _ mv' mb); [exact MIv| unfold AIMG_HI; lia| unfold CEIL; lia| lia| exact SECv|].
    intros z5 z6 z7 z13 z14 z15 z16 z17. unfold APOISON_SHADOW. cbv beta delta [wz].
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply poison_shadow_ok; [exact ICv| exact PCv| exact MIv| rewrite unsigned_lit by lia; exact STv| exact HCEIL| rewrite unsigned_lit by lia; unfold APOISON_STACK; lia
        | reflexivity| reflexivity| reflexivity| (lia_on SF RA HMB SHB SHBk2 SHlo)| reflexivity| lia| unfold app_range, lowmem_range, highmem_range, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; lia| lia| lia| ].
      change (Z.to_nat (4096 / 8)) with 512%nat. exact SH1. }
    cbv beta. intros ms4 PO4. (nelim PO4 22%nat; intros w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m4 -> MU4c WM4c MI4 PSH1 ST4).
    rewrite unsigned_lit in MU4c, ST4 by lia. change (Z.to_nat (4096 / 8)) with 512%nat in PSH1. change (4096 / 8) with 512 in MU4c.
    replace (ret_pc (Z_to_bv 64 0x36980)) with (Z_to_bv 64 0x36980 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    sepM. assert (MT4 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n))] mv' m4) by (eapply munch_weaken; [| exact MU4c]; subfp).
    sepM. assert (MU4 : munch (Wv mb) mv' m4) by (eapply munch_weaken; [| exact MU4c]; subfp).
    pose proof WM4c as WM4.
    pose proof FRv as FR4. eapply (rw_cells_transport asegs _ mv' m4) in FR4; [| exact MU4c| exact WM4| djs].
    pose proof VS2 as VS2'. eapply (stk_transport_disjoint asegs _ mv' m4) in VS2'; [| exact MU4c| exact WM4| djs].
    clear MU4c WM4c.
    pose proof (RTT m4 MT4 WM4) as HR4.
    pose proof (rtrep_artcells st m4 HR4) as AC. pose proof (artcells_icpt m4 AC) as IC4. pose proof (artcells_poison m4 AC) as PC4. clear AC.
    (* [comment removed for export] *)
    eapply (la_A2 sp gp tp s10 s11 F fc m4 n mb Hn HP HN HMB). unfold APOISON_SHADOW. cbv beta delta [wz].
    pose proof (tail_facts mb n Hn HP HN (proj2 (proj2 HMB)) ltac:(lia)) as TF. cbv zeta in TF.
    set (T := mb + smapsize n - (sec_alloc_beg mb + needed n)) in *.
    (nelim TF 7%nat; intros HT1 HT2 HT3 HT4 HT5 HT6 HT7).
    assert (A2Z : pz_range (sec_alloc_beg mb + needed n)).
    { (nelimp (ablk_lin _ _ HKHk) 4%nat; intros AL1 AL2 AL3 AL4). pose proof (smapsize_pos n Hn) as [SP8 _].
      pose proof alloc_ceiling_range as ACR. unfold pz_range.
      destruct (ablk_disj_band _ _ HKHk) as [BL|BH]; [left; clear - AL1 AL2 AL3 AL4 SP8 BL HT1 HT6 ACR| right; clear - AL1 AL2 AL3 AL4 SP8 BH HT1 HT6 ACR];
        unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG, KHIGHMEM_END in *; lia. }
    assert (A2A : 8 <= T -> app_range (sec_alloc_beg mb + needed n) T).
    { intros T8. (nelimp (ablk_lin _ _ HKHk) 4%nat; intros AL1 AL2 AL3 AL4). pose proof (smapsize_pos n Hn) as [SP8 _].
      pose proof alloc_ceiling_range as ACR. unfold app_range, lowmem_range, highmem_range.
      destruct (ablk_disj_band _ _ HKHk) as [BL|BH]; [left; clear - AL1 AL2 AL3 AL4 SP8 BL HT1 HT6 ACR T8| right; clear - AL1 AL2 AL3 AL4 SP8 BH HT1 HT6 ACR T8];
        unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG, KHIGHMEM_END in *; lia. }
    assert (PS2 : evt asegs (fun ms5 => exists (u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 : word) m5,
               ms5 = MS (mkR (Z_to_bv 64 0x36990) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u5 u6 u7 (Z_to_bv 64 A_GSTATS) (Z_to_bv 64 A_SECONDARY) u10 u11 u12 u13 u14 u15 u16 u17
                            (Z_to_bv 64 (smapsize n)) (Z_to_bv 64 (needed n)) (Z_to_bv 64 mb) (Z_to_bv 64 (sec_alloc_beg mb + needed n)) (Z_to_bv 64 (mb + smapsize n))
                            (Z_to_bv 64 (sec_alloc_beg mb + needed n)) (Z_to_bv 64 7) (Z_to_bv 64 (sec_alloc_beg mb)) s10 s11 u28 u29 u30 u31)
                        F (Z_to_bv 64 0x36990) fc None m5 (seg_rom asegs)
               /\ munch [(SH (sec_alloc_beg mb + needed n), SH (sec_alloc_beg mb + needed n) + T / 8); (bv_unsigned sp + -96 - APOISON_STACK, bv_unsigned sp + -96)] m4 m5
               /\ wmono asegs m4 m5 /\ mem_inv asegs m5
               /\ rw_cells asegs m5 (SH (sec_alloc_beg mb + needed n)) [CB (Z.to_nat (T / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (T / 8)))]
               /\ stk asegs m5 lo (bv_unsigned sp + -96))
             (MS (mkR (Z_to_bv 64 0x36990) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp w5 w6 w7 (Z_to_bv 64 A_GSTATS) (Z_to_bv 64 A_SECONDARY)
                      (Z_to_bv 64 (sec_alloc_beg mb + needed n)) (Z_to_bv 64 T) (Z_to_bv 64 250) w13 w14 w15 w16 w17
                      (Z_to_bv 64 (smapsize n)) (Z_to_bv 64 (needed n)) (Z_to_bv 64 mb) (Z_to_bv 64 (sec_alloc_beg mb + needed n)) (Z_to_bv 64 (mb + smapsize n))
                      (Z_to_bv 64 (sec_alloc_beg mb + needed n)) (Z_to_bv 64 7) (Z_to_bv 64 (sec_alloc_beg mb)) s10 s11 w28 w29 w30 w31)
                 F (Z_to_bv 64 0x5567c) fc None m4 (seg_rom asegs))).
    { destruct (Z.eq_dec T 0) as [T0|Tnz].
      - (* [comment removed for export] *)
        rewrite T0. eapply evt_mono; [eapply poison_shadow_zero_ok; [exact IC4| exact PC4| exact MI4| rewrite unsigned_lit by lia; exact ST4| exact HCEIL
             | rewrite unsigned_lit by lia; unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity| lia| exact A2Z| lia]|].
        cbv beta. intros ms5 nelH_; (nelim nelH_ 21%nat; intros u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m5 -> MU5c WM5c MI5 ST5).
        rewrite unsigned_lit in MU5c, ST5 by lia.
        replace (ret_pc (Z_to_bv 64 0x36990)) with (Z_to_bv 64 0x36990 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        nexists 15%nat. exists m5. split; [reflexivity|]. split; [| split; [exact WM5c| split; [exact MI5| split; [| exact ST5]]]].
        + eapply munch_weaken; [| exact MU5c]. unfold sub_fp. cbn [outside fst snd app]. intros; (lia_on H).
        + change (Z.to_nat (0 / 8)) with 0%nat. cbn [repeat]. apply rw_cells_CB_nil; lia.
      - (* [comment removed for export] *)
        destruct (vis_carve m4 _ _ (SH (sec_alloc_beg mb + needed n)) (Z.to_nat (T / 8)) VS2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as [junk2 SH2].
        eapply evt_mono; [eapply poison_shadow_ok; [exact IC4| exact PC4| exact MI4| rewrite unsigned_lit by lia; exact ST4| exact HCEIL
             | rewrite unsigned_lit by lia; unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity| lia| lia| (lia_on HT1 HT2 Tnz)
             | apply A2A; clear - HT1 HT2 Tnz; lia| lia| lia| exact SH2]|].
        cbv beta. intros ms5 nelH_; (nelim nelH_ 22%nat; intros u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m5 -> MU5c WM5c MI5 PSH2 ST5).
        rewrite unsigned_lit in MU5c, ST5 by lia.
        replace (ret_pc (Z_to_bv 64 0x36990)) with (Z_to_bv 64 0x36990 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        nexists 15%nat. exists m5. split; [reflexivity|]. split; [exact MU5c| split; [exact WM5c| split; [exact MI5| split; [exact PSH2| exact ST5]]]]. }
    eapply evt_cut; [exact PS2|]. clear PS2. cbv beta.
    intros ms5 nelH_; (nelim nelH_ 22%nat; intros u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m5 -> MU5c WM5c MI5 PSH2 ST5).
    sepM. assert (MT5 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n))] mv' m5) by (eapply munch_trans; [exact MT4|]; eapply munch_weaken; [| exact MU5c]; subfp).
    sepM. assert (MU5 : munch (Wv mb) mv' m5) by (eapply munch_trans; [exact MU4|]; eapply munch_weaken; [| exact MU5c]; subfp).
    pose proof (wmono_trans asegs _ _ _ WM4 WM5c) as WM5.
    pose proof FR4 as FR5. eapply (rw_cells_transport asegs _ m4 m5) in FR5; [| exact MU5c| exact WM5c| djs].
    pose proof PSH1 as PSH1'. eapply (rw_cells_transport asegs _ m4 m5) in PSH1'; [| exact MU5c| exact WM5c| djs].
    clear MU5c WM5c FR4 PSH1 VS2' IC4 PC4 HR4 MI4 ST4.
    pose proof (RTT m5 MT5 WM5) as HR5.
    (* [comment removed for export] *)
    eapply (la_A2c sp gp tp s10 s11 F fc m5 n mb).
    eapply evt_cut.
    { eapply get_thread_stats_c; [exact (leafc_of_RTREP st m5 HR5)| exact WF| exact MI5| exact TP| rewrite unsigned_lit by lia; exact ST5| exact HCEIL| rewrite unsigned_lit by lia; lia]. }
    cbv beta delta [leaf_post]. intros ms6 nelH_; (nelim nelH_ 22%nat; intros u5' u6' u7' u10' u11' u12' u13' u14' u15' u16' u17' u28' u29' u30' u31' m6 -> MU6c WM6c MI6 ST6 ->).
    rewrite unsigned_lit in MU6c, ST6 by lia.
    replace (ret_pc (wz 0x36994)) with (Z_to_bv 64 0x36994 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MT6 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + smapsize n))] mv' m6) by (eapply munch_trans; [exact MT5|]; eapply munch_weaken; [| exact MU6c]; subfp).
    assert (MU6 : munch (Wv mb) mv' m6) by (eapply munch_trans; [exact MU5|]; eapply munch_weaken; [| exact MU6c]; subfp).
    pose proof (wmono_trans asegs _ _ _ WM5 WM6c) as WM6.
    pose proof FR5 as FR6. eapply (rw_cells_transport asegs _ m5 m6) in FR6; [| exact MU6c| exact WM6c| djs].
    pose proof PSH1' as PSH1_6. eapply (rw_cells_transport asegs _ m5 m6) in PSH1_6; [| exact MU6c| exact WM6c| djs].
    pose proof PSH2 as PSH2_6. eapply (rw_cells_transport asegs _ m5 m6) in PSH2_6; [| exact MU6c| exact WM6c| djs].
    clear MU6c WM6c FR5 PSH1' PSH2 HR5 MI5 ST5 MT5 MU5 WM5.
    apply evt_done.
    eapply (la_mid mb mv' m6 wlo whi R1 T jf); [exact HMB| exact FRESH| exact HRv| exact VMv| exact VSH| exact CPv| exact RFv| exact GWv| exact HFR1| exact PLN| reflexivity| lia
      | exact MT6| exact MU6| exact WM6| exact MI6| exact FR6| exact ST6| exact PSH1_6| reflexivity| exact PSH2_6| split; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma la_refuse : forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2,
    mem_inv asegs m2 -> munch [(lo, bv_unsigned sp + -96)] m1 m2 -> wmono asegs m1 m2 -> stk asegs m2 lo (bv_unsigned sp + -96) ->
    LSCPS asegs (sec_alloc2_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m (mkG G R))
      (MS (mkR (Z_to_bv 64 0x36928) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp y5 y6 y7 (Z_to_bv 64 A_GSTATS) (Z_to_bv 64 A_SECONDARY) (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
               (Z_to_bv 64 (smapsize n)) (Z_to_bv 64 (needed n)) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x36928) fc None m2 (seg_rom asegs)) mo (mkG G R).
  Proof.
    intros until m2. intros MI2 MU2 WM2 ST2.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    destruct FR1 as [jf FR2]. eapply (rw_cells_transport asegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; lia].
    eapply lscps_step_evt.
    eapply (la_R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo); [unfold ALARGE_ALLOC_STACK; lia| eexists; exact FR2| exact ST2| exact MI2|].
    intros m3 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ST3 MI3 MU3 WM3.
    assert (MU03 : munch [(lo, bv_unsigned sp)] m m3).
    { eapply munch_trans; [exact MU1|]. eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn; intros; lia. }
    pose proof (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) as WM03.
    apply evt_done. apply lscps_assume. intros _ HOK0 _. apply lscps_done.
    unfold sec_alloc2_post_null, rt_post_std. nexists 15%nat. exists m3, st. split; [reflexivity|]. split; [exact MI3|].
    split; [reflexivity|]. split; [reflexivity|].
    split. { pose proof HR as HR3. rtrep_high HR3 WF MU03 WM03. exact (RTS_intro _ _ _ _ HR3 WF HM (GWIN_mem _ _ _ _ _ HG HOK WM03) HFR HSW). }
    split; [exact ST3|].
    split. { eapply (cli_pres_tpz st WF (bv_unsigned sp)); [unfold CEIL; lia| exact MU03| exact WM03|].
             constructor; [right; cbn; unfold CEIL; lia| constructor]. }
    split. { eapply rt_frame_of_munch; [exact MU03|]. intros iv [<-|[]]. left. cbn. lia. }
    split; [unfold budget_ok; lia|].
    intros w Hw. exact Hw.
  Qed.
End LA2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MAIN.

  Lemma blk_post_to_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g',
    sec_alloc2_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g' ->
    sec_alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g'.
  Proof.
    intros until g'. intros H. unfold sec_alloc2_post_blk, sec_alloc_post, rt_post_std in *.
    (nelim H 32%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st' -> MI' mb -> REL HB RTS' ST' CP RF BUD P1 P2 SW GM).
    nexists 15%nat. exists m', st'. split; [reflexivity|]. split; [exact MI'|]. exists (sec_alloc_beg mb).
    split; [reflexivity|]. split; [exact REL|]. split; [exact RTS'|]. split; [exact ST'|]. split; [exact CP|].
    split; [intros E; exfalso; (nelimp (ablk_lin _ _ HB) 3%nat; intros HB1 HB2 _); clear - E HB1 HB2; unfold sec_alloc_beg, SEC_HDR, AIMG_HI in *; lia|].
    split; [| exact GM]. intros mb' E HB'. assert (mb' = mb) by (unfold sec_alloc_beg in E; lia). subst mb'.
    split; [exact RF|]. split; [exact BUD|]. split; [exact P1|]. split; [exact P2| exact SW].
  Qed.

  Lemma null_post_to_post : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g',
    sec_alloc2_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g' ->
    sec_alloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g'.
  Proof.
    intros until g'. intros H. unfold sec_alloc2_post_null, sec_alloc_post, rt_post_std in *.
    (nelim H 27%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st' -> MI' -> -> RTS' ST' CP RF BUD GM).
    nexists 15%nat. exists m', st. split; [reflexivity|]. split; [exact MI'|]. exists 0.
    split; [reflexivity|]. split.
    { split; [repeat split; reflexivity|]. split; [reflexivity|]. left. repeat split; reflexivity. }
    split; [exact RTS'|]. split; [exact ST'|]. split; [exact CP|].
    split; [intros _; split; [exact RF| exact BUD]|].
    split; [| exact GM]. intros mb E HB. exfalso. (nelimp (ablk_lin _ _ HB) 3%nat; intros HB1 HB2 _). clear - E HB1 HB2. unfold sec_alloc_beg, SEC_HDR, AIMG_HI in *. lia.
  Qed.

  Theorem large_alloc_proof : large_alloc_spec.
  Proof.
    unfold large_alloc_spec. intros until lo. intros RTS0 Hn HP HN -> -> -> -> TP DEP ST HCEIL LO MI.
    (nelim RTS0 6%nat; intros HR WF HM HG HFR HSW).
    pose proof (smapsize_facts n Hn HP HN) as SF.
    pose proof (mmap_cells st m HR) as MC.
    pose proof (rr_link st m HR) as HL.
    destruct (sec_name_cell m) as [nmv NAME]. (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ALARGE_ALLOC_STACK in LO. pose proof HCEIL as CEIL'. idtac.
    apply lscps_assume. intros NWX HOK HBINV.
    destruct g as [G R]. cbn [g_res g_win] in *.
    eapply lscps_step_evt.
    eapply (la_A0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st n lo); try eassumption.
    intros m1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR1 ST1 MI1 MU1 WM1.
    apply evt_done. cbv beta delta [wz].
    pose proof MC as MC1. eapply (mmap_consts_munch _ m m1) in MC1; [| exact MU1| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia].
    unfold A_MMAP_ONFATAL.
    pose proof (bv_unsigned_in_range 64 nmv) as RNM. unfold bv_modulus in RNM. cbn in RNM.
    replace nmv with (Z_to_bv 64 (bv_unsigned nmv)) by apply Z_to_bv_bv_unsigned.
    eapply (mmap_onfatal_spec (Z_to_bv 64 0x36928) (Z_to_bv 64 (bv_unsigned sp + -96)));
      [exact MC1| exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; idtac; lia| lia
      | lia| unfold SEC_ALLOC_COST, SEC_SLOT_TAX in DEP; pose proof (rt_prov_nonneg st WF); lia| |].
    - intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2.
      rewrite unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 223528)) with (Z_to_bv 64 223528 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply lscps_mono; [eapply (la_refuse ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mo G R st n lo); eassumption|].
      intros ms' mo' g'. apply null_post_to_post.
    - intros a y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 GR MI2 MU2 WM2 ST2 ZNEW.
      rewrite unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 223528)) with (Z_to_bv 64 223528 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply lscps_mono; [eapply (la_grant ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mo G R st n lo); eassumption|].
      intros ms' mo' g' H'. apply blk_post_to_post, blkW_to_blk, H'.
  Qed.

  (* [comment removed for export] *)
End MAIN.


End CeilWrap.
(* [comment removed for export] *)
Ltac djs := cbn [disjoint_from cells_size Cells.csize fst snd length app]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; unfold PTRARR_RES_SIZE, APOISON_STACK in *; lia.
End RTW_sec_alloc.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_specs.
Module RTW_sec_allocW.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artO OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_mmapN OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_name OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_lib.RTW_sec_alloc1 RTW_sec_mapfix RTW_sec_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma blkW_to_postW : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g',
  sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g' ->
  sec_alloc_postW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g'.
Proof.
  intros until g'. intros H. unfold sec_alloc2_post_blkW, sec_alloc_postW, rt_post_std in *.
  destruct H as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & -> & MI' & mb & -> & REL & HB & RTS' & ST' & CP & RF & BUD & P1 & P2 & SW & GM).
  do 15 eexists. exists m', st'. split; [reflexivity|]. split; [exact MI'|]. exists (sec_alloc_beg mb).
  split; [reflexivity|]. split; [exact REL|]. split; [exact RTS'|]. split; [exact ST'|]. split; [exact CP|].
  split; [intros E; exfalso; pose proof (ablk_lin _ _ HB) as (HB1 & HB2 & _); clear - E HB1 HB2; unfold sec_alloc_beg, SEC_HDR, AIMG_HI in *; lia|].
  split; [| exact GM]. intros mb' E HB'. assert (mb' = mb) by (unfold sec_alloc_beg in E; lia). subst mb'.
  split; [exact RF|]. split; [exact BUD|]. split; [exact P1|]. split; [exact P2| exact SW].
Qed.

Lemma null_to_postW : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g',
  sec_alloc2_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g' ->
  sec_alloc_postW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g'.
Proof.
  intros until g'. intros H. unfold sec_alloc2_post_null, sec_alloc_postW, rt_post_std in *.
  destruct H as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & -> & MI' & -> & -> & RTS' & ST' & CP & RF & BUD & GM).
  do 15 eexists. exists m', st. split; [reflexivity|]. split; [exact MI'|]. exists 0.
  split; [reflexivity|]. split.
  { split; [repeat split; reflexivity|]. split; [reflexivity|]. left. repeat split; reflexivity. }
  split; [exact RTS'|]. split; [exact ST'|]. split; [exact CP|].
  split; [intros _; split; [exact RF| exact BUD]|].
  split; [| exact GM]. intros mb E HB. exfalso. pose proof (ablk_lin _ _ HB) as (HB1 & HB2 & _). clear - E HB1 HB2. unfold sec_alloc_beg, SEC_HDR, AIMG_HI in *. lia.
Qed.

Section MAINW.

  Theorem large_alloc_proofW : large_alloc_specW.
  Proof.
    unfold large_alloc_specW. intros until lo. intros RTS0 Hn HP HN -> -> -> -> TP DEP ST HCEIL LO MI.
    destruct RTS0 as (HR & WF & HM & HG & HFR & HSW).
    pose proof (smapsize_facts n Hn HP HN) as SF.
    pose proof (mmap_cells st m HR) as MC.
    pose proof (rr_link st m HR) as HL.
    destruct (sec_name_cell m) as [nmv NAME].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ALARGE_ALLOC_STACK in LO. pose proof HCEIL as CEIL'. idtac.
    apply lscps_assume. intros NWX HOK HBINV.
    destruct g as [G R]. cbn [g_res g_win] in *.
    eapply lscps_step_evt.
    eapply (la_A0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st n lo); try eassumption.
    intros m1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR1 ST1 MI1 MU1 WM1.
    apply evt_done. cbv beta delta [wz].
    pose proof MC as MC1. eapply (mmap_consts_munch _ m m1) in MC1; [| exact MU1| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia].
    unfold A_MMAP_ONFATAL.
    pose proof (bv_unsigned_in_range 64 nmv) as RNM. unfold bv_modulus in RNM. cbn in RNM.
    replace nmv with (Z_to_bv 64 (bv_unsigned nmv)) by apply Z_to_bv_bv_unsigned.
    eapply (mmap_onfatal_spec (Z_to_bv 64 0x36928) (Z_to_bv 64 (bv_unsigned sp + -96)));
      [exact MC1| exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; idtac; lia| lia
      | lia| unfold SEC_ALLOC_COST, SEC_SLOT_TAX in DEP; pose proof (rt_prov_nonneg st WF); lia| |].
    - intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2.
      rewrite unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 223528)) with (Z_to_bv 64 223528 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply lscps_mono; [eapply (la_refuse ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mo G R st n lo); eassumption|].
      intros ms' mo' g'. apply null_to_postW.
    - intros a y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 GR MI2 MU2 WM2 ST2 ZNEW.
      rewrite unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 223528)) with (Z_to_bv 64 223528 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply lscps_mono; [eapply (la_grant ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mo G R st n lo); eassumption|].
      intros ms' mo' g'. apply blkW_to_postW.
  Qed.
  (* [comment removed for export] *)
  Theorem large_alloc_nn_proofW : large_alloc_nn_specW.
  Proof.
    unfold large_alloc_nn_specW. intros until lo. intros RTS0 Hn HP HN -> -> -> -> TP DEP HPL ST HCEIL LO MI.
    destruct RTS0 as (HR & WF & HM & HG & HFR & HSW).
    pose proof (smapsize_facts n Hn HP HN) as SF.
    pose proof (mmap_cells st m HR) as MC.
    pose proof (rr_link st m HR) as HL.
    destruct (sec_name_cell m) as [nmv NAME].
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold ALARGE_ALLOC_STACK in LO. pose proof HCEIL as CEIL'. idtac.
    apply lscps_assume. intros NWX HOK HBINV.
    destruct g as [G R]. cbn [g_res g_win] in *.
    eapply lscps_step_evt.
    eapply (la_A0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st n lo); try eassumption.
    intros m1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR1 ST1 MI1 MU1 WM1.
    apply evt_done. cbv beta delta [wz].
    pose proof MC as MC1. eapply (mmap_consts_munch _ m m1) in MC1; [| exact MU1| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia| cbn; lia].
    unfold A_MMAP_ONFATAL.
    pose proof (bv_unsigned_in_range 64 nmv) as RNM. unfold bv_modulus in RNM. cbn in RNM.
    replace nmv with (Z_to_bv 64 (bv_unsigned nmv)) by apply Z_to_bv_bv_unsigned.
    eapply (mmap_onfatal_nn_spec (Z_to_bv 64 0x36928) (Z_to_bv 64 (bv_unsigned sp + -96)));
      [exact MC1| exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; idtac; lia| lia
      | lia| unfold SEC_ALLOC_COST, SEC_SLOT_TAX in DEP; pose proof (rt_prov_nonneg st WF); lia| exact HPL|].
    intros a y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 GR MI2 MU2 WM2 ST2 ZNEW.
    rewrite unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 223528)) with (Z_to_bv 64 223528 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_mono; [eapply (la_grant ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mo G R st n lo); eassumption|].
    intros ms' mo' g' H'. exact H'.
  Qed.
End MAINW.


End CeilWrap.
End RTW_sec_allocW.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
Module RTW_m_callocN.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_m_c0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec RTW_sec_allocW OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma refill2_1_nz : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g ms' mo' g',
  refill2_post 1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g ms' mo' g' ->
  nz_post (refill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st cls lo m g) ms' mo' g'.
Proof.
  intros until g'. intros H. unfold refill2_post, refill_post, nz_post, rt_post_std in *.
  (nelim H 21%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st' -> MI' -> REST).
  split; [| rewrite ms_a0_MS; apply wz_nz; lia].
  nexists 15%nat. exists m', st'. split; [reflexivity|]. split; [exact MI'|]. exists 1. split; [reflexivity| exact REST].
Qed.

Lemma blkW_nz : forall n, 0 <= n -> forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m g ms' mo' g',
  sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g ms' mo' g' ->
  nz_post (sec_alloc_postW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g) ms' mo' g'.
Proof.
  intros n Hn0. intros until g'. intros H. split; [apply blkW_to_postW; exact H|].
  unfold sec_alloc2_post_blkW, rt_post_std in H.
  (nelim H 24%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st' -> MI' mb -> REL HB _).
  rewrite ms_a0_MS. apply wz_nz. (nelimp (ablk_lin _ _ HB) 4%nat; intros B1 B2 B3 B4). pose proof (smapsize_pos n Hn0) as [SP _].
  unfold sec_alloc_beg, SEC_HDR, AIMG_HI in *. lia.
Qed.

(* [comment removed for export] *)
Ltac nz_cptr st WF c k HcK EC :=
  let CV := fresh "CV" in
  assert (CV : carved_cptr st c k)
    by (apply (wc_used_carved st c (wf_class_ok st WF c HcK)); unfold used_cptrs, avail_cptrs; rewrite !in_app_iff; left; right; rewrite EC;
        apply in_or_app; right; left; reflexivity);
  let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in
  (nelim (carved_chunk st WF c k HcK ltac:(lia) CV) 3%nat; intros C1 C2 C3);
  let RF := fresh "RF" in pose proof (region_facts st WF c HcK) as RF; cbn zeta in RF;
  let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in let X5 := fresh "X" in let X6 := fresh "X" in
  (nelim RF 7%nat; intros X1 X2 X3 X4 X5 X6 _);
  apply wz_nz; unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, PRIM_RES_SIZE, KFREEARRAY_OFF in *;
  pose proof alloc_ceiling_range; lia.

Section CALLOCN.
Hypothesis refill_nn_proof : refill_nn_stmt.
Hypothesis large_alloc_nn_proof : large_alloc_nn_specW.

Lemma zlen_pos_split : forall (l : list Z), 0 < zlen l -> exists pre k, l = pre ++ [k].
Proof.
  intros l H. destruct l as [|x l']; [cbn in H; unfold zlen in H; cbn in H; lia|].
  destruct (exists_last (l := x :: l') ltac:(discriminate)) as (pre & k & E). exists pre, k. exact E. (* [comment removed for export] *)
Qed.

Lemma nrefill_pos : forall c, 1 <= nrefill c <= 8.
Proof. intros c. unfold nrefill, cmaxcount, clampz. rewrite (Z.mul_comm 2), Z.div_mul by lia. lia. Qed.

(* [comment removed for export] *)
Lemma calloc_rel_pop : forall st n k pre, bprim n = true ->
  calloc_rel st (st_pop st (pclass n) k pre) n (cptr_addr st (pclass n) k).
Proof.
  intros st n k pre HP. pose proof (st_pop_same st (pclass n) k pre) as E.
  destruct E as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28). (* [comment removed for export] *)
  unfold calloc_rel, same_client. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]). right. left. split; [exact HP|]. exists k. auto.
Qed.

Lemma calloc_rel_refill_pop : forall st st1 n k pre, bprim n = true -> refill_rel st st1 (pclass n) 1 ->
  calloc_rel st (st_pop st1 (pclass n) k pre) n (cptr_addr st (pclass n) k).
Proof.
  intros st st1 n k pre HP nelH_; (nelim nelH_ 5%nat; intros SBP AP _ _ _). pose proof (st_pop_same st1 (pclass n) k pre) as E.
  destruct E as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28). (* [comment removed for export] *)
  destruct SBP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24). (* [comment removed for export] *)
  unfold calloc_rel, same_client. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18.
  rewrite P1, P3, P2, P4, P6, P7, P8, P9, P10, P12, P14, P15, P20, P21, P22, P23, P24, AP.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]). right. left. split; [exact HP|]. exists k. auto.
Qed.

Lemma calloc_rel_refill0 : forall st st1 n, refill_rel st st1 (pclass n) 0 -> calloc_rel st st1 n 0.
Proof.
  intros st st1 n nelH_; (nelim nelH_ 5%nat; intros SBP AP _ _ _).
  (nelim SBP 24%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24).
  unfold calloc_rel, same_client.
  rewrite P1, P3, P2, P4, P6, P7, P8, P9, P10, P12, P14, P15, P20, P21, P22, P23, P24, AP.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]). left. auto.
Qed.

Lemma calloc_rel_sec : forall st st1 n r, bprim n = false -> sec_alloc_rel st st1 n r -> calloc_rel st st1 n r.
Proof.
  intros st st1 n r HP nelH_; (nelim nelH_ 3%nat; intros SBS QC RES).
  (nelim SBS 24%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24).
  unfold calloc_rel, same_client.
  rewrite P1, P3, P2, P7, P8, P9, P10, P11, P13, P15, P16, P21, P22, P23, P24, QC.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]).
  destruct RES as [(-> & S1 & S2 & S3)|(mb & -> & M1 & M2 & M3 & S1 & S2 & S3)].
  - left. auto.
  - right. right. split; [exact HP|]. exists mb. repeat (split; [first [reflexivity| assumption]|]). exact P6.
Qed.

Theorem combined_alloc_nn_proof : combined_alloc_nn_spec.
Proof.
  unfold combined_alloc_nn_spec. intros until lo. intros (HR & WF & HM & HG & HFR & HSWR) HTPX HAP0 Hn -> -> -> -> TP HDEP HNN ST HCL LO SPS MI. unfold cnn_ok in HNN.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold ACALLOC_STACK, AREFILL_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  apply lscps_assume. intros NWX HO HB.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  destruct (bprim n) eqn:HP.
  - (* [comment removed for export] *)
    try rewrite HP in HNN.
    pose proof (prim_facts n HP) as (PC & _). set (c := pclass n) in *.
    assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
    assert (DEP : calloc_deposit n = 2 * csize c) by (unfold calloc_deposit; rewrite HP; reflexivity). rewrite DEP in HDEP.
    pose proof (csize_pos c ltac:(lia)) as CSP.
    eapply lscps_step_evt.
    callx ltac:(eapply calloc_c0p_spec with (lo := lo) (st := st) (n := n);
                [exact HR| exact WF| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn| exact HP| exact ST| idtac; lia| lia]).
    fold c. cbv beta delta [wz]. rename PC0 into ST. rename POST into FR. rename MI0 into MI.
    rtrep_high HR WF MU WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (CP0 : cli_pres st (bv_unsigned sp) m mA).
    { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
    assert (HG0 : GWIN st mA mo g) by (eapply GWIN_mem; eauto).
    assert (ES0 : errno_same m mA).
    { eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. left. unfold AERRNO, ATP. lia. }
    clear MU WM.
    pose proof (zlen_nonneg (cch st c)) as CZ.
    destruct (Z.eq_dec (zlen (cch st c)) 0) as [Z0|NZ].
    + (* [comment removed for export] *)
      assert (EC : cch st c = []) by (destruct (cch st c) as [|x' l']; [reflexivity| rewrite zlen_cons in Z0; pose proof (zlen_nonneg l'); lia]).
      rewrite Z0. lstep; if_lia.
      do 7 lstep. lstep. (* [comment removed for export] *)
      apply evt_done.
      eapply lscps_bind.
      { eapply lscps_mono; [pose proof refill_nn_proof as RP; unfold refill_nn_stmt in RP; eapply RP with (lo := lo) (cls := c); try reflexivity
                            | intros msx mox gx PX; exact (refill2_1_nz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PX)].
        - exact (RTS_intro _ _ _ _ HR WF HM HG0 HFR HSWR).
        - lia. - exact EC. - exact TP. - lia. - exact HNN.
        - rewrite unsigned_lit by lia. exact ST. - idtac; lia. - rewrite unsigned_lit by lia. unfold AREFILL_STACK. lia. - exact MI. }
      cbv beta. intros ms1 mo1 g1 [PO NZ1].
      (nelim PO 28%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 st1 -> MI1 r -> RR RTS1 ST1 CP1 RF1 GM1 BO1).
      rewrite unsigned_lit in ST1, CP1 by lia.
      replace (ret_pc (Z_to_bv 64 0x36844)) with (Z_to_bv 64 0x36844) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in FR; [| left; cbn; lia].
      (nelim RTS1 6%nat; intros HR1 WF1 HM1 HG1 HF1 HSW1).
      pose proof RR as RR0. (nelim RR 5%nat; intros SBP AP1 CI1 OTH RES).
      assert (Et : st_t st1 = st_t st) by ((nelim SBP 16%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ E _); exact E).
      assert (Esp0 : st_sp0 st1 = st_sp0 st) by (destruct SBP as (E & _); exact E).
      assert (Esb : st_spacebeg st1 = st_spacebeg st) by ((nelim SBP 4%nat; intros _ _ E _); exact E).
      assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
      { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|]. eapply cj_pres_weaken; [exact CP1| lia| auto| auto]. }
      clear ST MI CP0 CP1.
      apply lscps_assume. intros _ HO1 HB1.
      destruct RES as [[-> LEN1]|[-> EC1]].
      * (* [comment removed for export] *)
        pose proof (nrefill_pos c) as NP1.
        (nelim (zlen_pos_split (cch st1 c) ltac:(lia)) 3%nat; intros pre k EC1).
        assert (LENp : zlen pre + 1 = nrefill c) by (rewrite <- LEN1, EC1, zlen_app, zlen_cons, zlen_nil; lia).
        pose proof (proj1 (rr_cache st1 m1 HR1 c HcK)) as CC1.
        replace (pcaddr st1 c) with (pcaddr st c) in CC1 by (unfold pcaddr, acache; rewrite Et; reflexivity). rewrite LEN1 in CC1.
        pose proof (munch_refl [(pcaddr st1 c, pcaddr st1 c + 4); (st_t st1 + 2784, st_t st1 + 2792)] m1) as MU2. pose proof (wmono_refl asegs m1) as WM2.
        eapply lscps_step_evt. cbv beta delta [wz] in *.
        lstep; if_lia. (* [comment removed for export] *)
        lstep. rewrite (sx32_lit (nrefill c)) by lia. (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. (* [comment removed for export] *)
        rewrite <- LENp.
        sepM. callxp ltac:(eapply calloc_c1_spec with (lo := lo) (st := st1) (c := c) (k := k) (pre := pre) (vra := ra) (vs0 := s0) (vs1 := s1) (vs2 := s2) (vs3 := s3) (vs4 := s4);
          [ exact HR1| exact WF1| exact MI1| lia| exact EC1| reflexivity| unfold acache; rewrite Et; reflexivity| reflexivity| reflexivity| reflexivity
          | unfold pcaddr, acache; rewrite Et; reflexivity
          | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; exact FR ]) ltac:(clear CC1 FR).
        rewrite unsigned_lit in * by lia. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end. rename MI into MI2.
        apply evt_done. apply lscps_done. split; [| rewrite ms_a0_MS; nz_cptr st1 WF1 c k HcK EC1].
        unfold calloc_post, rt_post_std. nexists 15%nat. exists m2, (st_pop st1 c k pre). split; [reflexivity|]. split; [exact MI2|].
        exists (cptr_addr st c k).
        (* [comment removed for export] *)
        assert (CV : carved_cptr st1 c k).
        { apply (wc_used_carved st1 c (wf_class_ok st1 WF1 c HcK)). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. right. rewrite EC1. apply in_or_app. right. left. reflexivity. }
        (nelim (carved_chunk st1 WF1 c k HcK ltac:(lia) CV) 3%nat; intros C1 C2 C3).
        pose proof (region_facts st1 WF1 c HcK) as RF. cbn zeta in RF. (nelim RF 7%nat; intros X1 X2 X3 X4 X5 X6 _).
        assert (ECP : cptr_addr st1 c k = cptr_addr st c k) by (unfold cptr_addr, rbeg; rewrite Esb; reflexivity).
        unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, PRIM_RES_SIZE, KFREEARRAY_OFF in X1, X3, X4, X6.
        split; [rewrite ECP; reflexivity|]. split; [rewrite <- ECP; lia|].
        split; [apply calloc_rel_refill_pop; [exact HP| exact RR0]|].
        split.
        { apply RTS_intro.
          - eapply RTREP_pop'; [exact WF1| apply HTPX; exact WF1| lia| exact EC1| exact MU2| exact WM2| exact HR1| exact POST].
          - apply RTWF_pop'; [exact WF1| lia| exact EC1| rewrite AP1; exact HAP0].
          - apply RTMODEL_pop'. exact HM1.
          - apply GWIN_pop'. eapply GWIN_mem; [exact HG1| exact HO1| exact WM2].
          - exact HF1.
          - apply SWIN_pop'. exact HSW1. }
        split; [assumption|].
        split.
        { unfold cli_pres in *. eapply cj_pres_trans; [exact CP01|].
          eapply (cli_pres_tpz st1 WF1 (bv_unsigned sp) ltac:(unfold CEIL; lia)) in MU2; [| exact WM2|].
          - unfold cli_pres in MU2. rewrite Esp0 in MU2. (nelim SBP 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ P14 _ _ _ _ _ P20 _). rewrite P14, P20 in MU2. exact MU2.
          - constructor; [| constructor; [| constructor]]; cbn [fst snd]; left; unfold pcaddr, acache, T_ACACHE; lia. }
        split.
        { eapply errno_same_trans; [exact ES0|]. eapply errno_same_trans.
          - eapply errno_same_rt_frame; [exact RF1| unfold AERRNO, ATP; lia| intros a Ha; apply notin_ivs_app; [apply (errno_notin_primary_fp st c a WF HcK Ha)| apply (errno_notin_fp_emb st1 a WF1 Ha)]]   (* [comment removed for export] *).
          - eapply errno_same_munch; [exact MU2|]. pose proof (t_range st1 WF1) as TRx. olin TRx.
            constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold pcaddr, acache, T_ACACHE, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI in *; lia. }
        split; [exact GM1|].
        split.
        { replace (cptr_addr st c k =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite <- ECP; lia).
          pose proof (rt_prov_pop' st1 c k pre WF1 ltac:(lia) EC1 ltac:(rewrite AP1; exact HAP0)). rewrite DEP. unfold budget_ok in *. lia. }
        intros HF. rewrite HP in HF. discriminate.
      * (* [comment removed for export] *)
        exfalso. apply NZ1. reflexivity.
    + (* [comment removed for export] *)
      (nelim (zlen_pos_split (cch st c) ltac:(lia)) 3%nat; intros pre k EC).
      assert (LENp : zlen (cch st c) = zlen pre + 1) by (rewrite EC, zlen_app, zlen_cons, zlen_nil; lia).
      pose proof (munch_refl [(pcaddr st c, pcaddr st c + 4); (st_t st + 2784, st_t st + 2792)] mA) as MU2. pose proof (wmono_refl asegs mA) as WM2.
      pose proof (zlen_nonneg pre). pose proof (wc_cache_max st c (wf_class_ok st WF c HcK)) as CM. pose proof (cmaxcount_le16 c) as CM16. rewrite LENp in CM.
      rewrite LENp. lstep; if_lia. (* [comment removed for export] *)
      callxp ltac:(eapply calloc_c1_spec with (lo := lo) (st := st) (c := c) (k := k) (pre := pre) (vra := ra) (vs0 := s0) (vs1 := s1) (vs2 := s2) (vs3 := s3) (vs4 := s4);
        [ exact HR| exact WF| exact MI| lia| exact EC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; exact FR ]) ltac:(clear FR).
      rewrite unsigned_lit in * by lia. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end. rename MI0 into MI2.
      apply evt_done. apply lscps_done. split; [| rewrite ms_a0_MS; nz_cptr st WF c k HcK EC].
      unfold calloc_post, rt_post_std. nexists 15%nat. exists m2, (st_pop st c k pre). split; [reflexivity|]. split; [exact MI2|].
      exists (cptr_addr st c k).
      assert (CV : carved_cptr st c k).
      { apply (wc_used_carved st c (wf_class_ok st WF c HcK)). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. right. rewrite EC. apply in_or_app. right. left. reflexivity. }
      (nelim (carved_chunk st WF c k HcK ltac:(lia) CV) 3%nat; intros C1 C2 C3).
      pose proof (region_facts st WF c HcK) as RF. cbn zeta in RF. (nelim RF 7%nat; intros X1 X2 X3 X4 X5 X6 _).
      unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, PRIM_RES_SIZE, KFREEARRAY_OFF in X1, X3, X4, X6.
      split; [reflexivity|]. split; [lia|].
      split; [apply calloc_rel_pop; exact HP|].
      split.
      { apply RTS_intro.
        - eapply RTREP_pop'; [exact WF| apply HTPX; exact WF| lia| exact EC| exact MU2| exact WM2| exact HR| exact POST].
        - apply RTWF_pop'; [exact WF| lia| exact EC| exact HAP0].
        - apply RTMODEL_pop'. exact HM.
        - apply GWIN_pop'. eapply GWIN_mem; [exact HG0| exact HO| exact WM2].
        - exact HFR.
        - apply SWIN_pop'. exact HSWR. }
      split; [assumption|].
      split.
      { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|].
        eapply (cli_pres_tpz st WF (bv_unsigned sp) ltac:(unfold CEIL; lia)) in MU2; [| exact WM2|].
        - exact MU2.
        - constructor; [| constructor; [| constructor]]; cbn [fst snd]; left; unfold pcaddr, acache, T_ACACHE; lia. }
      split.
      { eapply errno_same_trans; [exact ES0|]. eapply errno_same_munch; [exact MU2|]. pose proof (t_range st WF) as TRx. olin TRx.
        constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold pcaddr, acache, T_ACACHE, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI in *; lia. }
      split; [intros w Hw; exact Hw|].
      split.
      { replace (cptr_addr st c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        pose proof (rt_prov_pop' st c k pre WF ltac:(lia) EC HAP0). rewrite DEP. unfold budget_ok in *. lia. }
      intros HF. rewrite HP in HF. discriminate.
  - (* [comment removed for export] *)
    try rewrite HP in HNN.
    (nelimp (sec_facts n HP) 6%nat; intros S1 S2 S3 S4 S5 S6). pose proof (rounded8_range n Hn) as R8. unfold usz in S4.
    assert (DEP : calloc_deposit n = SEC_ALLOC_COST n + SEC_SLOT_TAX) by (unfold calloc_deposit; rewrite HP; reflexivity). rewrite DEP in HDEP.
    eapply lscps_step_evt.
    callx ltac:(eapply calloc_c0s_spec with (lo := lo) (n := n);
                [exact MI| reflexivity| reflexivity| exact Hn| exact HP| exact ST| idtac; lia| lia]).
    cbv beta delta [wz].
    match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
    match goal with H : rw_cells _ _ _ (calloc_frame _ _ _ _ _ _) |- _ => rename H into FR end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    rtrep_high HR WF MU WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (CP0 : cli_pres st (bv_unsigned sp) m mA).
    { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
    assert (HG0 : GWIN st mA mo g) by (eapply GWIN_mem; eauto).
    assert (ES0 : errno_same m mA).
    { eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. left. unfold AERRNO, ATP. lia. }
    clear MU WM.
    unfold A_ALLOC. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    apply evt_done.
    eapply lscps_bind.
    { eapply lscps_mono; [pose proof large_alloc_nn_proof as LP; unfold large_alloc_nn_specW in LP; eapply LP with (lo := lo) (n := n); try reflexivity
                          | intros msx mox gx PX; exact (blkW_nz n (proj1 Hn) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PX)].
      - exact (RTS_intro _ _ _ _ HR WF HM HG0 HFR HSWR).
      - lia. - exact HP. - rewrite S6. lia. - exact TP. - lia. - exact HNN.
      - rewrite unsigned_lit by lia. exact ST. - idtac; lia. - rewrite unsigned_lit by lia. unfold ALARGE_ALLOC_STACK. lia. - exact MI. }
    cbv beta. intros ms1 mo1 g1 [PO NZ1].
    (nelim PO 28%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 st1 -> MI1 r -> SR RTS1 ST1 CP1 R0 RS GM1).
    rewrite unsigned_lit in ST1, CP1, R0, RS by lia.
    replace (ret_pc (Z_to_bv 64 0x3663c)) with (Z_to_bv 64 0x3663c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in FR; [| left; cbn; lia].
    (nelim RTS1 6%nat; intros HR1 WF1 HM1 HG1 HF1 HSW1).
    assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
    { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|]. eapply cj_pres_weaken; [exact CP1| lia| auto| auto]. }
    clear ST MI CP0 CP1.
    eapply lscps_step_evt. cbv beta delta [wz] in *. unfold calloc_frame in FR.
    lstep. lstep. lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    do 7 lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
    release_frame FR ST1 (bv_unsigned sp).
    apply evt_done. apply lscps_done. split; [| rewrite ms_a0_MS in *; exact NZ1].
    unfold calloc_post, rt_post_std. nexists 15%nat. exists m1, st1. split; [reflexivity|]. split; [exact MI1|].
    exists r.
    (nelimp SR 3%nat; intros _ _ RES).
    split; [reflexivity|].
    split.
    { destruct RES as [(-> & _)|(mb & -> & M1 & M2 & M3 & _)]; [lia|]. unfold sec_alloc_beg, SEC_HDR, KHIGHMEM_BEG, AIMG_HI in *. idtac. blia. }
    split; [apply calloc_rel_sec; [exact HP| exact SR]|].
    split; [exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HF1 HSW1)|].
    split; [exact ST1|]. split; [exact CP01|].
    split.
    { eapply errno_same_trans; [exact ES0|]. destruct RES as [(-> & _)|(mb & -> & M1 & M2 & M3 & _)].
      - eapply errno_same_rt_frame; [exact (proj1 (R0 eq_refl))| unfold AERRNO, ATP; lia|].
        intros a Ha. apply (errno_notin_secondary_fp0 st a WF Ha).
      - eapply errno_same_rt_frame; [exact (proj1 (RS mb eq_refl M1))| unfold AERRNO, ATP; lia|].
        intros a Ha. apply (errno_notin_secondary_fp st mb n a WF M1 Ha). }
    split; [exact GM1|].
    split.
    { destruct RES as [(-> & _)|(mb & -> & M1 & M2 & M3 & _)].
      - cbn [Z.eqb]. apply R0. reflexivity.
      - replace (sec_alloc_beg mb =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (ablk_img _ _ M1); unfold sec_alloc_beg, SEC_HDR, KHIGHMEM_BEG, AIMG_HI in *; lia).
        rewrite DEP. apply (RS mb eq_refl M1). }
    intros _ mb Hr Hmb. (nelim (RS mb Hr Hmb) 5%nat; intros _ _ P1 P2 P3). split; [exact P1| split; [exact P2| exact P3]].
Qed.
End CALLOCN.

End CeilWrap.
End RTW_m_callocN.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_quarantine_iface RTW_quarantine_iface2 RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_iface2 RTW_nn_specs.
Import RTW_sec_allocW.
Import RTW_m_callocN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_allocN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_mallocN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_realloc0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_realloc0.RTW_m_freeN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_asec RT_drv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.

Section DINST.
Variable AI : art_iface.
Hypothesis HART : CJ_iface.ART AI = ARTd.

(* [comment removed for export] *)
Hypothesis try_asan_init_proof : try_asan_init_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis internal_allocator_proof : internal_allocator_spec.
Hypothesis asan_inited_proof : asan_inited_spec.
Hypothesis rss_exceeded_proof : rss_exceeded_spec.
Hypothesis rzsize2log_proof : rzsize2log_spec.
Hypothesis get_current_thread_proof : get_current_thread_spec.
Hypothesis set_oom_proof : set_oom_spec.
Hypothesis may_return_null_proof : may_return_null_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis depot_put_proof : depot_put_specS.
(* [comment removed for export] *)
Hypothesis refill_nn_proof : refill_nn_stmt.
Hypothesis quarantine_put_proof : quarantine_put_spec2.   (* [comment removed for export] *)

Lemma alloc_sec_case : alloc_sec_stmt.
Proof. apply alloc_sec_proof; first [exact poison_shadow_ok| assumption]. Qed.

Lemma combined_alloc_nn_ok : combined_alloc_nn_spec.
Proof. apply combined_alloc_nn_proof; first [exact large_alloc_nn_proofW| assumption]. Qed.

Lemma allocate_nn_ok : allocate_nn_spec.
Proof.
  apply allocate_nn_proof; first [exact combined_alloc_nn_ok| exact alloc_sec_case| exact poison_shadow_ok| assumption].
Qed.

Lemma art2_malloc_ok : malloc_nn_stmt (CJ_iface.ART AI) ADRVd.
Proof. rewrite HART. apply art_malloc_nn_proof; first [exact allocate_nn_ok| assumption]. Qed.

Lemma art2_free_ok : forall k, free_lscps_stmt (fun sp0 SPB LB LF TRS B m mo g => CJ_iface.ART AI sp0 SPB LB LF TRS B m mo g /\ ADRVd k m mo g).
Proof.
  intros k. rewrite HART.
  apply art2_free_proof; assumption.
Qed.

Lemma adrv_frame_ok : forall k sp0 SPB LB LF TRS B m m' mo g W,
  CJ_iface.ART AI sp0 SPB LB LF TRS B m mo g -> ADRVd k m mo g -> munch W m m' -> wmono asegs m m' ->
  Forall (cj_write_ok sp0 SPB LB LF) W -> ADRVd k m' mo g.
Proof. rewrite HART. exact adrvd_frame. Qed.

Definition DINST : drv_iface2 AI :=
  mkDI2 AI ADRVd adrvd_weaken adrv_frame_ok adrvd_model art2_free_ok art2_malloc_ok.

End DINST.

End CeilWrap.
