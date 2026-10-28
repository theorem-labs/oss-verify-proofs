From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_callsA Atp_kitA Atp_objkA.
Import ListNotations.
Open Scope Z_scope.

Section AtkmCmp.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable E : aenvA.
Hypothesis OK : aenvA_ok E.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RC2 : rt_contracts2 RT.

Lemma atkm_cmp_call : forall (Σ : rts RT) (K : config -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (sp o P L : Z) (key : list Z)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  a_live RT Σ E -> AINV_A E m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m (ae_lo E) sp -> ae_lo E + RT_STACK <= sp -> sp + 16 <= USTACK_TOP -> sp mod 16 = 0 ->
  ptr_atA E P key -> L = zlength key -> 0 <= o -> o + 4 + L < ae_sn E ->
  (forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ sp (ae_lo E) m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 L)
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_memcmp) fc None m (seg_rom asegs)).
Proof using AF OK FDO MST RC2.
  intros Σ K m F fc sp o P L key ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    LV AI ART0 MI0 ST SPL SPT SPA PAT EL O0 OL HK.
  pose proof (ok_lo E OK) as LOW. pose proof (ok_hi E OK) as [HL HT].
  pose proof (ok_sbuf E OK) as (SB16 & NS8 & SN & SS & SL).
  pose proof (call_ok_lvl RT E OK Σ m sp LV ST SPL SPT SPA) as COK.
  assert (SPU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK in *; lia).
  assert (HK' : forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ (bv_unsigned (Z_to_bv 64 sp)) (ae_lo E) m m' ->
     rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 sp)) 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))).
  { intros r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PR. rewrite SPU in RA, PR.
    exact (HK r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PR). }
  pose proof (zlength_nonneg key) as KL0.
  destruct (Z.eq_dec L 0) as [L0|LP].
  - eapply (aevt_memcmp0 RT PMc FDO MST RC2 Σ); [rewrite L0; reflexivity| exact ART0| exact MI0| exact COK|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PR.
    exact (HK' (Z_to_bv 64 0) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PR).
  - assert (LPOS : 0 < L) by lia.
    assert (NE : key <> []) by (intros E0; rewrite E0 in EL; unfold zlength in EL; cbn [length] in EL; lia).
    destruct AI as (_ & SBB & PTB & _).
    pose proof (ptr_atA_facts E P key m OK PAT PTB) as (KB & KR & _ & _ & KL26).
    pose proof (lvl_ptr_range E OK P key PAT NE) as (PB0 & PB1 & PB2 & PB3).
    pose proof (lvl_live_ptr RT E Σ P key LV PAT NE) as INPB.
    pose proof LV as (_ & LVS & _ & _ & LWIN).
    assert (QB : bytes_at asegs m (ae_SBUF E + o + 4) (map (Z_to_bv 8) (firstn (Z.to_nat L) (skipn (Z.to_nat (o + 4)) (ae_sbs E))))).
    { rewrite <- firstn_map, <- skipn_map.
      replace (ae_SBUF E + o + 4) with (ae_SBUF E + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact SBB|]. rewrite length_map. lia. }
    assert (QL : Z.of_nat (length (map (Z_to_bv 8) (firstn (Z.to_nat L) (skipn (Z.to_nat (o + 4)) (ae_sbs E))))) = L).
    { rewrite length_map, firstn_length_le; [lia| rewrite length_skipn; lia]. }
    assert (KPL : Z.of_nat (length (map (Z_to_bv 8) key)) = L) by (rewrite length_map; unfold zlength in EL; lia).
    eapply (aevt_memcmpW RT PMc FDO MST RC2 Σ K ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1
              (Z_to_bv 64 P) (Z_to_bv 64 (ae_SBUF E + o + 4)) (Z_to_bv 64 L) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m P (ae_SBUF E + o + 4) (map (Z_to_bv 8) key)
              (map (Z_to_bv 8) (firstn (Z.to_nat L) (skipn (Z.to_nat (o + 4)) (ae_sbs E)))) (ae_lo E));
      [reflexivity| reflexivity| rewrite KPL; reflexivity| lia| unfold USTACK_TOP in *; lia| unfold USTACK_TOP in *; lia
      | lia| lia| exact KB| exact QB| | | exact ART0| exact MI0| exact COK| ].
    + rewrite KPL. apply (checked_src_live RT AF Σ m _ (ae_lo E) (ae_PB E) (ae_NPB E) _ _ ART0 INPB); [lia| lia| exact LWIN].
    + rewrite KPL. apply (checked_src_live RT AF Σ m _ (ae_lo E) (ae_SBUF E) (ae_NS E) _ _ ART0 LVS); [lia| lia| exact LWIN].
    + intros r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' _ RA PR.
      exact (HK' r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PR).
Qed.

End AtkmCmp.
