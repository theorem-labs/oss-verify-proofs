(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 696 of its 743 lines of code are new or changed and 357 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: the operation-loop arm op_decide (operation byte mod 6 = 4, entry +0x648).
   Offsets from 0x827d4; listing
   (internal path) (internal record, sha256 e84d6f0c6974).

     +0x648 text_of(&cursor, s1 + 0x130)      0x82e24  (Txo.v lf_text_of_call, Txa.v lf_text_of_after)
     +0x658 text_of(&cursor, s1 + 0x128)      0x82e34
     +0x668 reac_served_decide(t1, t2)        0x82e44  (ArmR.v ar_leaf_call, Txa.v lf_leaf_after)
     +0x678 model_decide(t1, t2)              0x82e54
     +0x688 check_verdict(v_rsd, v_md)        0x82e64  (s5 := [s1 + 0x98] restores md + MD_N_MARK)
     +0x698 free([s1 + 0x130])                0x82e6c  (Txa.v lf_free_tx_step: NULL or the fresh block)
     +0x6a0 free([s1 + 0x128])                0x82e74
     +0x6a4 j +0x1110                         LF_tail

   lf_op4 : forall POST i, 0 <= i <= 47 -> lf_from POST (lf_tail_inv i) -> lf_from POST (lf_arm_inv 4 i)
   (LLVMFuzzerTestOneInput.v's LF_ARM at op = 4). Each callee's contract is a named Section hypothesis.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c model_decide_c check_verdict_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxo.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis TXO_RO : forall i, (i < 11)%nat ->
  text_of_ro SEGS PCAP_RLO PCAP_RHI B (fst (nth i KP_TEXTS (0, [])))
    (Z.of_nat (length (snd (nth i KP_TEXTS (0, [])))) + 1).
Hypothesis TXO_TR : text_of_traces B.
Hypothesis TXO_C : forall fy : YK11.FPState, text_of_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B MT LF_CTX.
Hypothesis RSD_C : forall fy : YK11.FPState, reac_served_decide_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis MDC_C : forall fy : YK11.FPState, model_decide_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis CV_C : forall fy : YK11.FPState, check_verdict_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis AFREENULL4W : forall fy : YK11.FPState, afree_null04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Lemma lf_op4 : forall POST i, 0 <= i <= 47 ->
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP 4 i).
Proof.
  intros POST i Hi HT cx fy fp k2 ly3 S3 W3 ms3 md3 HB HFX HJ HFR GI.
  destruct GI as (md & mk & P & N & kbs & mbs & gbs & T3 & bop & _ & _ & HSH & HCORE & HLR & HSAV & HHDR & HFSH &
    HSLOTS & HN1 & Hbop & Hbm & HCUR & Hq & HJBK & HBLK & HDATA & HOPN).
  pose proof HB as (HPRE & HFRM & HGX & HLAN & HMSE & HE0 & HE0sp & HCTXA & HMO).
  pose proof (lf_env_agree0 (ms_regs ms3)) as HA.
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HCORE as (R2 & R8 & R9 & R3 & R4).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  assert (HC0 : ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 [(md, MD_SIZE); (mk, MK_SIZE)]
    (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD k2 ly3 S3 W3 ms3 md3)
    by (repeat (split; [eassumption|]); exact HDATA).
  clear HSAV HHDR HFSH HSLOTS HJBK HBLK HDATA.
  change (lf_op_pc 4) with LF_op4 in HSH.
  rewrite (lf_shape_eta fy LF_op4 ms3 HSH).
  (* ---- +0x648 .. +0x650: a0 := s1 + 0x118, a1 := s1 + 0x130, text_of ---- *)
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LF_op4) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op4)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) [] D4R HS EL D4R_low ltac:(d4chk)) as KR1.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (mdA := mdB) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC0 HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA (P + 1) (N - 1) KA (fun a _ H => H) HCUR) as HCURA.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  ew_reg EL 2%nat (2%bv : bv 5) Q2. ew_reg EL 3%nat (3%bv : bv 5) Q3. ew_reg EL 4%nat (4%bv : bv 5) Q4.
  ew_reg EL 8%nat (8%bv : bv 5) Q8. ew_reg EL 9%nat (9%bv : bv 5) Q9.
  ew_reg EL 9%nat (9%bv : bv 5) Q10. ew_reg EL 9%nat (9%bv : bv 5) Q11. rewrite R9 in Q10, Q11.
  rewrite R2 in Q2. rewrite R3 in Q3. rewrite R4 in Q4. rewrite R8 in Q8. rewrite R9 in Q9.
  rewrite HBASE in Q1.
  unfold w64 in Q2, Q8, Q9, Q10, Q11.
  rewrite unsigned_lit_small in Q10, Q11 by (unfold LLVMF_STK in *; lia).
  pose proof HCA as (HJA & HFRA & HSAVA & HHDRA & HFSHA & HSLA & HJBKA & HBLKA & HDATAA).
  pose proof HJBKA as (Hkev & Hbb & Hfa & Hnin & Hfd & Hfs & Hmo & Hwl & Hgi & Henv & Hbl & Hinc & Hla & Hro & Hpl & Hpv).
  destruct (lf_saved_ra_s0 cx W3 msA HSAVA) as (HR8 & HR16).
  pose proof HCURA as (HPA & HNA & _).
  destruct Hq as (q & Hq0 & HPq & HNq).
  assert (HspA : spZ (ms_regs msA) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Hs0A : s0Z (ms_regs msA) = spZ (c_regs cx))
    by (unfold s0Z; rewrite Q8; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Ha0A : aarg (ms_regs msA) 0 = lf_sp1 cx + LS_P)
    by (rewrite ar_aarg0, Q10; apply unsigned_lit_small; unfold LS_P, LLVMF_STK in *; lia).
  assert (Ha1A : aarg (ms_regs msA) 1 = lf_sp1 cx + LS_T130)
    by (rewrite ar_aarg1, Q11; apply unsigned_lit_small; unfold LS_T130, LLVMF_STK in *; lia).
  eapply SRr_bind.
  { replace (pa_sigma LS_text_of) with TEXT_OF_A by (rewrite (lv_sigma LV); reflexivity).
    change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 TEXT_OF_A) (ms_mem msA) (seg_rom SEGS)) mdA)
      with (cfg_at (fx := fy) SEGS TEXT_OF_A (ms_regs msA) (ms_mem msA) mdA).
    apply (lf_text_of_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS TXO_RO
      TXO_TR MT_OK TXO_C fy cx fp k2 (lf_ev i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 (ms_mem msA) mdA (ms_regs msA)
      (P + 1) (N - 1) LS_T130 3164 HB HJA Hkev
      ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB; lia) Hbb
      ltac:(pose proof LF_LIVE_HELD_room; unfold TEXT_OF_LIVE; lia) Hwl
      ltac:(unfold lf_wl, LF_WILD_OP, LINK_WILD_PER_CALL; lia) Hro Hpl HR8 HR16 HPA HNA
      ltac:(exists (q + 1); lia) (or_intror eq_refl) HspA Hs0A Ha0A Ha1A Q3 Q4 HBASE Q1
      ltac:(unfold LF_TEXT_OF_SITES; left; reflexivity)). }
  intros W4 c4 Hle4 HPOST.
  destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HPRES4 & HFR4 & HFD4 & HFS4 & HKEPT4 & HSHK4 &
    HMO4 & HLED4 & HPA4).
  pose proof (d4_keep_pres D4R _ _ D4R_saved HPRES4) as KT1.
  set (ms4 := @mkst fy regs4 (getr (ms_regs msA) 1) mem4 (seg_rom SEGS)).
  destruct (lf_text_of_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 msA mdA (ms_regs msA) (P + 1) (N - 1) LS_T130 ly4 S4 W4 regs4
    mem4 md4 ms4 (lf_mo LF_MO_SET LF_MO_OP i) HB HJA HCA HPA HNA ltac:(exists (q + 1); lia) (or_intror eq_refl)
    HspA Ha0A Ha1A eq_refl HJ4 HFR4 HFD4 HFS4 HKEPT4 HSHK4 HLED4 HPA4)
    as (own1 & s1v & t1 & adv1 & nb1 & HA10 & Hs1v & HC4 & HRO4 & HP4 & HN4 & Hq4 & HSL4 & Hnb1 & Hnb1a & Hnb1b &
        Hsub4 & Hap4 & HCALL4 & HD1 & _).
  (* ---- +0x654 .. +0x660: s2 := a0, a0 := s1 + 0x118, a1 := s1 + 0x128, text_of ---- *)
  pose proof HC4 as (HJ4' & HFR4' & HSAV4 & _ & _ & _ & HJBK4 & HBLK4 & _).
  unfold ms4. rewrite Q1, <- HBASE.
  clear HS SHOK.
  pose proof (lf_env_agree0 regs4) as HA4.
  assert (HEI4 : img_env pa_val A_LIM (Eimg (Ereg regs4 []))) by apply Eimg_env.
  pose proof (d4_entry fy W4 regs4 mem4 3164) as HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs4 []))
    (mrestrict (w_H W4) (ms_mem (@mkst fy regs4 (Z_to_bv 64 (BASE + 3164)) mem4 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  remember (Eimg (Ereg regs4 [])) as E4 eqn:HEdef.
  assert (EL4 : forall n, (n < A_TEXT)%nat -> ew E4 n = ew (Ereg regs4 []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ4 SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (d4_keep_run fy W4 _ _ msB regs4 [] D4R HS EL4 D4R_low ltac:(d4chk)) as KR2.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
  assert (FdB : m_fds mdB = m_fds md4) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
  assert (FsB : m_fs mdB = m_fs md4) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1) ly4 S4 W4 ms4 msB md4 mdB HC4
    HJ4 KB (fun x Hx => HGB x Hx) FdB FsB) as HCB.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1B. prreg HS (2%bv : bv 5) Q2B. prreg HS (3%bv : bv 5) Q3B. prreg HS (4%bv : bv 5) Q4B.
  prreg HS (8%bv : bv 5) Q8B. prreg HS (9%bv : bv 5) Q9B. prreg HS (10%bv : bv 5) Q10B. prreg HS (11%bv : bv 5) Q11B.
  prreg HS (18%bv : bv 5) Q18B.
  ew_reg EL4 2%nat (2%bv : bv 5) Q2B. ew_reg EL4 3%nat (3%bv : bv 5) Q3B. ew_reg EL4 4%nat (4%bv : bv 5) Q4B.
  ew_reg EL4 8%nat (8%bv : bv 5) Q8B. ew_reg EL4 9%nat (9%bv : bv 5) Q9B.
  ew_reg EL4 9%nat (9%bv : bv 5) Q10B. ew_reg EL4 9%nat (9%bv : bv 5) Q11B. ew_reg EL4 10%nat (10%bv : bv 5) Q18B.
  preg HPRES4 2 (2%bv : bv 5) P42. preg HPRES4 3 (3%bv : bv 5) P43. preg HPRES4 4 (4%bv : bv 5) P44.
  preg HPRES4 8 (8%bv : bv 5) P48. preg HPRES4 9 (9%bv : bv 5) P49.
  rewrite P42, Q2 in Q2B. rewrite P43, Q3 in Q3B. rewrite P44, Q4 in Q4B. rewrite P48, Q8 in Q8B.
  rewrite P49, Q9 in Q9B, Q10B, Q11B. rewrite HA10 in Q18B. rewrite HBASE in Q1B.
  rewrite unsigned_lit_small in Q10B, Q11B by (unfold LLVMF_STK in *; lia).
  pose proof HCB as (HJB & HFRB & HSAVB & _ & _ & _ & HJBKB & HBLKB & _).
  pose proof HJBKB as (HkevB & HbbB & _ & _ & _ & _ & _ & HwlB & _ & _ & _ & _ & _ & HroB & HplB & _).
  destruct (lf_saved_ra_s0 cx W4 msB HSAVB) as (HR8B & HR16B).
  pose proof (lf_at_keep (fun _ => False) W4 ms4 W4 msB _ _ KB (fun _ _ H => H) HP4) as HPB.
  pose proof (lf_at_keep (fun _ => False) W4 ms4 W4 msB _ _ KB (fun _ _ H => H) HN4) as HNB.
  pose proof (lf_at_keep (fun _ => False) W4 ms4 W4 msB _ _ KB (fun _ _ H => H) HSL4) as HSLB.
  assert (HspB : spZ (ms_regs msB) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2B; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Hs0B : s0Z (ms_regs msB) = spZ (c_regs cx))
    by (unfold s0Z; rewrite Q8B; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Ha0B : aarg (ms_regs msB) 0 = lf_sp1 cx + LS_P)
    by (rewrite ar_aarg0, Q10B; apply unsigned_lit_small; unfold LS_P, LLVMF_STK in *; lia).
  assert (Ha1B : aarg (ms_regs msB) 1 = lf_sp1 cx + LS_T128)
    by (rewrite ar_aarg1, Q11B; apply unsigned_lit_small; unfold LS_T128, LLVMF_STK in *; lia).
  eapply SRr_bind.
  { replace (pa_sigma LS_text_of) with TEXT_OF_A by (rewrite (lv_sigma LV); reflexivity).
    change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 TEXT_OF_A) (ms_mem msB) (seg_rom SEGS)) mdB)
      with (cfg_at (fx := fy) SEGS TEXT_OF_A (ms_regs msB) (ms_mem msB) mdB).
    apply (lf_text_of_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS TXO_RO
      TXO_TR MT_OK TXO_C fy cx fp (k2 + 1) (lf_ev i + 1) (S (lf_wl i)) (LF_LIVE_HELD + TEXT_OF_LIVE) ly4 S4 W4
      (ms_mem msB) mdB (ms_regs msB) (P + 1 + adv1) (N - 1 - adv1) LS_T128 3180 HB HJB HkevB
      ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB; lia) HbbB
      ltac:(pose proof LF_LIVE_HELD_room; unfold TEXT_OF_LIVE; lia) HwlB
      ltac:(unfold lf_wl, LF_WILD_OP, LINK_WILD_PER_CALL; lia) HroB HplB HR8B HR16B HPB HNB Hq4 (or_introl eq_refl)
      HspB Hs0B Ha0B Ha1B Q3B Q4B HBASE Q1B ltac:(unfold LF_TEXT_OF_SITES; right; left; reflexivity)). }
  intros W5 c5 Hle5 HPOST.
  destruct HPOST as (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HPRES5 & HFR5 & HFD5 & HFS5 & HKEPT5 & HSHK5 &
    HMO5 & HLED5 & HPA5).
  pose proof (d4_keep_pres D4R _ _ D4R_saved HPRES5) as KT2.
  set (ms5 := @mkst fy regs5 (getr (ms_regs msB) 1) mem5 (seg_rom SEGS)).
  destruct (lf_text_of_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1) ly4 S4 W4 msB mdB (ms_regs msB) (P + 1 + adv1) (N - 1 - adv1) LS_T128
    ly5 S5 W5 regs5 mem5 md5 ms5 (lf_mo LF_MO_SET LF_MO_OP i) HB HJB HCB HPB HNB Hq4 (or_introl eq_refl)
    HspB Ha0B Ha1B eq_refl HJ5 HFR5 HFD5 HFS5 HKEPT5 HSHK5 HLED5 HPA5)
    as (own2 & s2v & t2 & adv2 & nb2 & HA20 & Hs2v & HC5 & HRO5 & HP5 & HN5 & Hq5 & HSL5 & Hnb2 & Hnb2a & Hnb2b &
        Hsub5 & Hap5 & HCALL5 & HD2 & _).
  (* the first answer, carried to the return of the second text_of *)
  pose proof HC4 as (HJ4x & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly4 S4 W4
    (ms_mem ms4) md4 (k2 + 1) HB HJ4x) as (_ & _ & _ & _ & _ & _ & HAR4).
  assert (HD1B : dec_ans B ly4 S4 (rdW W4 (ms_mem msB)) s1v t1) by exact (d4_dec_run B ly4 S4 _ _ s1v t1 KB HD1).
  assert (HD1C5 : dec_ans B ly5 S5 (rdW W5 mem5) s1v t1).
  { apply (dec_ans_callee B cx TEXT_OF_AK ly4 S4 ly5 S5 W4 (ms_mem msB) W5 mem5 _ s1v t1 HCALL5); [|exact (fun b m H => Hsub5 (b, m) H)|exact HD1B].
    intros b m a Hb Ha (r & Hr & Hra). destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR4 Hb) as (_ & _ & Hc & _).
    unfold text_of_awr in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; rewrite ?Ha0B, ?Ha1B in Hra;
      unfold req_size, LS_P, LS_T128 in *; destruct (m =? 0) eqn:Em; unfold LLVMF_STK in *; lia. }
  (* ---- +0x664 .. +0x670: s4 := a0, a0 := s2, a1 := s4, reac_served_decide ---- *)
  unfold ms5. rewrite Q1B, <- HBASE.
  clear HS SHOK.
  pose proof (lf_env_agree0 regs5) as HA5.
  assert (HEI5 : img_env pa_val A_LIM (Eimg (Ereg regs5 []))) by apply Eimg_env.
  pose proof (d4_entry fy W5 regs5 mem5 3180) as HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs5 []))
    (mrestrict (w_H W5) (ms_mem (@mkst fy regs5 (Z_to_bv 64 (BASE + 3180)) mem5 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  remember (Eimg (Ereg regs5 [])) as E5 eqn:HEdef.
  assert (EL5 : forall n, (n < A_TEXT)%nat -> ew E5 n = ew (Ereg regs5 []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ5 SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
  pose proof (d4_keep_run fy W5 _ _ msC regs5 [] D4R HS EL5 D4R_low ltac:(d4chk)) as KR3.
  pose proof (kagree_frame_nil _ _ _ HFrC) as KC.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdC := mdx) in * end.
  assert (FdC : m_fds mdC = m_fds md5) by (subst mdC; rewrite !lf_wvb_fds; reflexivity).
  assert (FsC : m_fs mdC = m_fs md5) by (subst mdC; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1 + 1) ly5 S5 W5 ms5 msC md5 mdC
    HC5 HJ5 KC (fun x Hx => HGC x Hx) FdC FsC) as HCC.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1C. prreg HS (2%bv : bv 5) Q2C. prreg HS (3%bv : bv 5) Q3C. prreg HS (4%bv : bv 5) Q4C.
  prreg HS (8%bv : bv 5) Q8C. prreg HS (9%bv : bv 5) Q9C. prreg HS (10%bv : bv 5) Q10C. prreg HS (11%bv : bv 5) Q11C.
  prreg HS (18%bv : bv 5) Q18C. prreg HS (20%bv : bv 5) Q20C.
  ew_reg EL5 2%nat (2%bv : bv 5) Q2C. ew_reg EL5 3%nat (3%bv : bv 5) Q3C. ew_reg EL5 4%nat (4%bv : bv 5) Q4C.
  ew_reg EL5 8%nat (8%bv : bv 5) Q8C. ew_reg EL5 9%nat (9%bv : bv 5) Q9C.
  ew_reg EL5 18%nat (18%bv : bv 5) Q10C. ew_reg EL5 10%nat (10%bv : bv 5) Q11C.
  ew_reg EL5 18%nat (18%bv : bv 5) Q18C. ew_reg EL5 10%nat (10%bv : bv 5) Q20C.
  preg HPRES5 2 (2%bv : bv 5) P52. preg HPRES5 3 (3%bv : bv 5) P53. preg HPRES5 4 (4%bv : bv 5) P54.
  preg HPRES5 8 (8%bv : bv 5) P58. preg HPRES5 9 (9%bv : bv 5) P59. preg HPRES5 18 (18%bv : bv 5) P518.
  rewrite P52, Q2B in Q2C. rewrite P53, Q3B in Q3C. rewrite P54, Q4B in Q4C. rewrite P58, Q8B in Q8C.
  rewrite P59, Q9B in Q9C. rewrite P518, Q18B in Q10C, Q18C. rewrite HA20 in Q11C, Q20C. rewrite HBASE in Q1C.
  pose proof HCC as (HJC & HFRC & HSAVC & _ & _ & _ & HJBKC & HBLKC & _).
  pose proof HJBKC as (HkevC & HbbC & _ & _ & _ & _ & _ & HwlC & _ & _ & _ & _ & _ & HroC & HplC & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly5 S5 W5
    (ms_mem msC) mdC (k2 + 1 + 1) HB HJC) as (_ & _ & _ & _ & _ & _ & HARC).
  assert (HD1C : dec_ans B ly5 S5 (rdW W5 (ms_mem msC)) s1v t1) by exact (d4_dec_run B ly5 S5 _ _ s1v t1 KC HD1C5).
  assert (HD2C : dec_ans B ly5 S5 (rdW W5 (ms_mem msC)) s2v t2) by exact (d4_dec_run B ly5 S5 _ _ s2v t2 KC HD2).
  assert (HspC : spZ (ms_regs msC) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2C; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Ha0C : aarg (ms_regs msC) 0 = s1v).
  { rewrite ar_aarg0, Q10C. apply unsigned_lit_small.
    destruct (dec_rt_ok B LAWS TB HSEGS ly5 S5 W5 (ms_mem msC) mdC (ms_regs msC) DECIDE_AK s1v t1 HARC HroC
      ltac:(rewrite HspC; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia) HD1C) as (((Hab & Hae & _) & _) & _). rewrite length_app in Hae. cbn [length] in Hae. lia. }
  assert (Ha1C : aarg (ms_regs msC) 1 = s2v).
  { rewrite ar_aarg1, Q11C. apply unsigned_lit_small.
    destruct (dec_rt_ok B LAWS TB HSEGS ly5 S5 W5 (ms_mem msC) mdC (ms_regs msC) DECIDE_AK s2v t2 HARC HroC
      ltac:(rewrite HspC; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia) HD2C) as (((Hab & Hae & _) & _) & _). rewrite length_app in Hae. cbn [length] in Hae. lia. }
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  (* reac_served_decide (0x82e44) *)
  replace (pa_sigma LS_reac_served_decide) with REAC_SERVED_DECIDE_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msC) (Z_to_bv 64 REAC_SERVED_DECIDE_A) (ms_mem msC) (seg_rom SEGS)) mdC)
    with (cfg_at (fx := fy) SEGS REAC_SERVED_DECIDE_A (ms_regs msC) (ms_mem msC) mdC).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy REAC_SERVED_DECIDE_A
    DECIDE_AK 0 [] (decide_apre SEGS LA_RSD_PREFIX LA_RSD_VLAN) (decide_ard SEGS) decide_awr (decide_apost SEGS)
    (RSD_C fy) cx fp ly5 S5 W5 (ms_mem msC) mdC (k2 + 1 + 1) (ms_regs msC) (POST cx) HB HJC HroC);
    [ rewrite Q1C, <- HBASE; apply ret_ok_codeptr_v; [lia | reflexivity]
    | unfold raZ; rewrite Q1C; rewrite unsigned_lit_small by (unfold link_text; lia); unfold link_text; lia
    | rewrite Q3C; exact HGP
    | rewrite Q4C; exact HTP
    | exact HspC
    | pose proof DECIDE_AK_val; unfold LLVMF_STK; lia
    | lia
    | unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia
    | apply Forall_nil
    | intros a (r & [] & _)
    | intros a (r & [] & _)
    | intros a Ha; exact (dec_decide_ard B TB HSEGS ly5 S5 W5 (ms_mem msC) mdC (ms_regs msC) s1v t1 s2v t2
        _ _ HARC HroC Ha0C Ha1C HD1C HD2C a Ha)
    | exact (dec_decide_apre B LAWS TB HSEGS ly5 S5 W5 (ms_mem msC) mdC (ms_regs msC) s1v t1 s2v t2 LA_RSD_PREFIX
        LA_RSD_VLAN HARC HroC ltac:(rewrite HspC; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia)
        (or_intror (conj eq_refl eq_refl)) Ha0C Ha1C HD1C HD2C)
    | ].
  intros W6 ly6 S6 regs6 mem6 md6 Hle6 HJ6 HPRES6 HFR6 HFD6 HFS6 HKEPT6 HSHK6 HS6 HPERM6 HPOST6.
  pose proof (d4_keep_pres D4R _ _ D4R_saved HPRES6) as KT3.
  set (ms6 := @mkst fy regs6 (getr (ms_regs msC) 1) mem6 (seg_rom SEGS)).
  destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1 + 1) ly5 S5 W5 msC mdC DECIDE_AK
    (fun a => inFP (decide_awr (ms_regs msC) (rdW W5 (ms_mem msC))) a) ly6 S6 W6 ms6 md6 (k2 + 1 + 1 + 0)
    HB HJC HCC ltac:(pose proof DECIDE_AK_val; unfold LLVMF_STK; lia) ltac:(intros a (r & [] & _)) HJ6
    ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR6 HFD6 HFS6 HKEPT6 HSHK6 HS6 HPERM6)
    as (HC6 & HRO6 & HCALL6).
  (* the decide value *)
  destruct (dec_rt_ok B LAWS TB HSEGS ly5 S5 W5 (ms_mem msC) mdC (ms_regs msC) DECIDE_AK s1v t1 HARC HroC
    ltac:(rewrite HspC; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia) HD1C) as (HCS1C & _ & _ & HNZ1).
  destruct (dec_rt_ok B LAWS TB HSEGS ly5 S5 W5 (ms_mem msC) mdC (ms_regs msC) DECIDE_AK s2v t2 HARC HroC
    ltac:(rewrite HspC; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia) HD2C) as (HCS2C & _ & _ & HNZ2).
  pose proof (HPOST6 (Some t1) (Some t2) ltac:(rewrite Ha0C; split; [exact HNZ1 | exact HCS1C])
    ltac:(rewrite Ha1C; split; [exact HNZ2 | exact HCS2C])) as HV6.
  set (dval := decide (Some t1) (Some t2)) in HV6.
  assert (Hsub6 : forall b m, In (b, m) (ablocks B ly5 S5) -> In (b, m) (ablocks B ly6 S6))
    by (intros b m Hb; exact (Permutation_in _ (Permutation_sym HPERM6) Hb)).
  assert (HD1_6 : dec_ans B ly6 S6 (rdW W6 mem6) s1v t1)
    by exact (dec_ans_callee B cx DECIDE_AK ly5 S5 ly6 S6 W5 (ms_mem msC) W6 mem6 _ s1v t1 HCALL6
                (fun b m a _ _ H => match H with ex_intro _ r (conj Hr _) => match Hr with end end) Hsub6 HD1C).
  assert (HD2_6 : dec_ans B ly6 S6 (rdW W6 mem6) s2v t2)
    by exact (dec_ans_callee B cx DECIDE_AK ly5 S5 ly6 S6 W5 (ms_mem msC) W6 mem6 _ s2v t2 HCALL6
                (fun b m a _ _ H => match H with ex_intro _ r (conj Hr _) => match Hr with end end) Hsub6 HD2C).
  (* ---- +0x674 .. +0x680: s5 := a0, a0 := s2, a1 := s4, model_decide ---- *)
  unfold ms6. rewrite Q1C, <- HBASE.
  clear HS SHOK.
  pose proof (lf_env_agree0 regs6) as HA6.
  assert (HEI6 : img_env pa_val A_LIM (Eimg (Ereg regs6 []))) by apply Eimg_env.
  pose proof (d4_entry fy W6 regs6 mem6 3196) as HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs6 []))
    (mrestrict (w_H W6) (ms_mem (@mkst fy regs6 (Z_to_bv 64 (BASE + 3196)) mem6 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  remember (Eimg (Ereg regs6 [])) as E6 eqn:HEdef.
  assert (EL6 : forall n, (n < A_TEXT)%nat -> ew E6 n = ew (Ereg regs6 []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ6 SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msD, HF into HFD, HFr into HFrD, HG into HGD.
  pose proof (d4_keep_run fy W6 _ _ msD regs6 [] D4R HS EL6 D4R_low ltac:(d4chk)) as KR4.
  pose proof (kagree_frame_nil _ _ _ HFrD) as KD.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdD := mdx) in * end.
  assert (FdD : m_fds mdD = m_fds md6) by (subst mdD; rewrite !lf_wvb_fds; reflexivity).
  assert (FsD : m_fs mdD = m_fs md6) by (subst mdD; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly6 S6 W6 ms6 msD md6 mdD
    HC6 HJ6 KD (fun x Hx => HGD x Hx) FdD FsD) as HCD.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1D. prreg HS (2%bv : bv 5) Q2D. prreg HS (3%bv : bv 5) Q3D. prreg HS (4%bv : bv 5) Q4D.
  prreg HS (8%bv : bv 5) Q8D. prreg HS (9%bv : bv 5) Q9D. prreg HS (10%bv : bv 5) Q10D. prreg HS (11%bv : bv 5) Q11D.
  prreg HS (18%bv : bv 5) Q18D. prreg HS (20%bv : bv 5) Q20D. prreg HS (21%bv : bv 5) Q21D.
  ew_reg EL6 2%nat (2%bv : bv 5) Q2D. ew_reg EL6 3%nat (3%bv : bv 5) Q3D. ew_reg EL6 4%nat (4%bv : bv 5) Q4D.
  ew_reg EL6 8%nat (8%bv : bv 5) Q8D. ew_reg EL6 9%nat (9%bv : bv 5) Q9D.
  ew_reg EL6 18%nat (18%bv : bv 5) Q10D. ew_reg EL6 20%nat (20%bv : bv 5) Q11D.
  ew_reg EL6 18%nat (18%bv : bv 5) Q18D. ew_reg EL6 20%nat (20%bv : bv 5) Q20D. ew_reg EL6 10%nat (10%bv : bv 5) Q21D.
  preg HPRES6 2 (2%bv : bv 5) P62. preg HPRES6 3 (3%bv : bv 5) P63. preg HPRES6 4 (4%bv : bv 5) P64.
  preg HPRES6 8 (8%bv : bv 5) P68. preg HPRES6 9 (9%bv : bv 5) P69. preg HPRES6 18 (18%bv : bv 5) P618.
  preg HPRES6 20 (20%bv : bv 5) P620.
  rewrite P62, Q2C in Q2D. rewrite P63, Q3C in Q3D. rewrite P64, Q4C in Q4D. rewrite P68, Q8C in Q8D.
  rewrite P69, Q9C in Q9D. rewrite P618, Q18C in Q10D, Q18D. rewrite P620, Q20C in Q11D, Q20D. rewrite HV6 in Q21D.
  rewrite HBASE in Q1D.
  pose proof HCD as (HJD & HFRD & HSAVD & _ & _ & _ & HJBKD & HBLKD & _).
  pose proof HJBKD as (HkevD & HbbD & _ & _ & _ & _ & _ & HwlD & _ & _ & _ & _ & _ & HroD & HplD & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly6 S6 W6
    (ms_mem msD) mdD _ HB HJD) as (_ & _ & _ & _ & _ & _ & HARD).
  assert (HD1D : dec_ans B ly6 S6 (rdW W6 (ms_mem msD)) s1v t1) by exact (d4_dec_run B ly6 S6 _ _ s1v t1 KD HD1_6).
  assert (HD2D : dec_ans B ly6 S6 (rdW W6 (ms_mem msD)) s2v t2) by exact (d4_dec_run B ly6 S6 _ _ s2v t2 KD HD2_6).
  assert (HspD : spZ (ms_regs msD) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2D; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Ha0D : aarg (ms_regs msD) 0 = s1v) by (rewrite ar_aarg0, Q10D; exact (proj1 (proj1 (proj1 HCS1C)) ) || (rewrite ar_aarg0 in Ha0C; rewrite Q10C in Ha0C; exact Ha0C)).
  assert (Ha1D : aarg (ms_regs msD) 1 = s2v) by (rewrite ar_aarg1, Q11D; rewrite ar_aarg1, Q11C in Ha1C; exact Ha1C).
  (* model_decide (0x82e54) *)
  replace (pa_sigma LS_model_decide) with MODEL_DECIDE_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msD) (Z_to_bv 64 MODEL_DECIDE_A) (ms_mem msD) (seg_rom SEGS)) mdD)
    with (cfg_at (fx := fy) SEGS MODEL_DECIDE_A (ms_regs msD) (ms_mem msD) mdD).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy MODEL_DECIDE_A
    DECIDE_AK 0 [] (decide_apre SEGS LA_MD_PREFIX LA_MD_VLAN) (decide_ard SEGS) decide_awr (decide_apost SEGS)
    (MDC_C fy) cx fp ly6 S6 W6 (ms_mem msD) mdD _ (ms_regs msD) (POST cx) HB HJD HroD);
    [ rewrite Q1D, <- HBASE; apply ret_ok_codeptr_v; [lia | reflexivity]
    | unfold raZ; rewrite Q1D; rewrite unsigned_lit_small by (unfold link_text; lia); unfold link_text; lia
    | rewrite Q3D; exact HGP
    | rewrite Q4D; exact HTP
    | exact HspD
    | pose proof DECIDE_AK_val; unfold LLVMF_STK; lia
    | lia
    | unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia
    | apply Forall_nil
    | intros a (r & [] & _)
    | intros a (r & [] & _)
    | intros a Ha; exact (dec_decide_ard B TB HSEGS ly6 S6 W6 (ms_mem msD) mdD (ms_regs msD) s1v t1 s2v t2
        _ _ HARD HroD Ha0D Ha1D HD1D HD2D a Ha)
    | exact (dec_decide_apre B LAWS TB HSEGS ly6 S6 W6 (ms_mem msD) mdD (ms_regs msD) s1v t1 s2v t2 LA_MD_PREFIX
        LA_MD_VLAN HARD HroD ltac:(rewrite HspD; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia)
        (or_introl (conj eq_refl eq_refl)) Ha0D Ha1D HD1D HD2D)
    | ].
  intros W7 ly7 S7 regs7 mem7 md7 Hle7 HJ7 HPRES7 HFR7 HFD7 HFS7 HKEPT7 HSHK7 HS7 HPERM7 HPOST7.
  pose proof (d4_keep_pres D4R _ _ D4R_saved HPRES7) as KT4.
  set (ms7 := @mkst fy regs7 (getr (ms_regs msD) 1) mem7 (seg_rom SEGS)).
  destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly6 S6 W6 msD mdD DECIDE_AK
    (fun a => inFP (decide_awr (ms_regs msD) (rdW W6 (ms_mem msD))) a) ly7 S7 W7 ms7 md7 _
    HB HJD HCD ltac:(pose proof DECIDE_AK_val; unfold LLVMF_STK; lia) ltac:(intros a (r & [] & _)) HJ7
    ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR7 HFD7 HFS7 HKEPT7 HSHK7 HS7 HPERM7)
    as (HC7 & HRO7 & HCALL7).
  destruct (dec_rt_ok B LAWS TB HSEGS ly6 S6 W6 (ms_mem msD) mdD (ms_regs msD) DECIDE_AK s1v t1 HARD HroD
    ltac:(rewrite HspD; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia) HD1D) as (HCS1D & _ & _ & _).
  destruct (dec_rt_ok B LAWS TB HSEGS ly6 S6 W6 (ms_mem msD) mdD (ms_regs msD) DECIDE_AK s2v t2 HARD HroD
    ltac:(rewrite HspD; pose proof DECIDE_AK_val; unfold LLVMF_STK in *; lia) HD2D) as (HCS2D & _ & _ & _).
  pose proof (HPOST7 (Some t1) (Some t2) ltac:(rewrite Ha0D; split; [exact HNZ1 | exact HCS1D])
    ltac:(rewrite Ha1D; split; [exact HNZ2 | exact HCS2D])) as HV7.
  fold dval in HV7.
  (* ---- +0x684 .. +0x690: a1 := a0, a0 := s5, s5 := [s1 + 0x98], check_verdict ---- *)
  pose proof HC7 as (HJ7x & HFR7x & HSAV7 & _ & _ & HSL7 & HJBK7 & HBLK7 & _).
  pose proof HSL7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNM7 & _).
  preg HPRES7 9 (9%bv : bv 5) P79. rewrite Q9D in P79.
  pose proof HBLK7 as (Hmd7 & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly7 S7 W7
    (ms_mem ms7) md7 _ HB HJ7x) as (_ & _ & _ & _ & _ & _ & HAR7).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR7 Hmd7) as (_ & Hmd4096 & Hmdc & _).
  assert (HU9 : bv_unsigned (getr regs7 9) = lf_sp1 cx)
    by (rewrite P79; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  unfold ms7. rewrite Q1D, <- HBASE.
  clear HS SHOK.
  pose proof (d4_entry_l fy W7 regs7 mem7 3212 LS_NMARK (md + MD_N_MARK) ltac:(rewrite HU9; unfold LLVMF_STK in *; lia)
    ltac:(rewrite HU9; exact Hs32) ltac:(unfold LS_NMARK; lia)
    ltac:(unfold req_size, MD_SIZE, MD_N_MARK in *; cbn in Hmdc; lia) ltac:(vm_compute; reflexivity)
    ltac:(rewrite HU9; exact (val_mem_of_rdword SEGS (w_H W7) mem7 _ _ HNM7))) as HS.
  pose proof (lf_env_agree0 regs7) as HA7.
  assert (HEI7 : img_env pa_val A_LIM (Eimg (Ereg regs7 [Z_to_bv 64 (md + MD_N_MARK)]))) by apply Eimg_env.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs7 [Z_to_bv 64 (md + MD_N_MARK)]))
    (mrestrict (w_H W7) (ms_mem (@mkst fy regs7 (Z_to_bv 64 (BASE + 3212)) mem7 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  remember (Eimg (Ereg regs7 [Z_to_bv 64 (md + MD_N_MARK)])) as E7 eqn:HEdef.
  assert (EL7 : forall n, (n < A_TEXT)%nat -> ew E7 n = ew (Ereg regs7 [Z_to_bv 64 (md + MD_N_MARK)]) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  assert (E732 : ew E7 32 = Z_to_bv 64 (md + MD_N_MARK))
    by (rewrite EL7 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs7 _ 0)).
  clear HEdef.
  paj_run_tok RUN HS HJ7 SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
  rename ms into msE, HF into HFE, HFr into HFrE, HG into HGE.
  pose proof (d4_keep_run fy W7 _ _ msE regs7 _ D4R HS EL7 D4R_low ltac:(d4chk)) as KR5.
  assert (KE : kagree SEGS (fun _ => False) (rdW W7 (ms_mem ms7)) (rdW W7 (ms_mem msE))).
  { intros a _. unfold mbyte. rewrite (HFrE (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
    lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdE := mdx) in * end.
  assert (FdE : m_fds mdE = m_fds md7) by (subst mdE; rewrite !lf_wvb_fds; reflexivity).
  assert (FsE : m_fs mdE = m_fs md7) by (subst mdE; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly7 S7 W7 ms7 msE md7 mdE
    HC7 HJ7 KE (fun x Hx => HGE x Hx) FdE FsE) as HCE.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1E. prreg HS (2%bv : bv 5) Q2E. prreg HS (3%bv : bv 5) Q3E. prreg HS (4%bv : bv 5) Q4E.
  prreg HS (8%bv : bv 5) Q8E. prreg HS (9%bv : bv 5) Q9E. prreg HS (10%bv : bv 5) Q10E. prreg HS (11%bv : bv 5) Q11E.
  prreg HS (21%bv : bv 5) Q21E.
  ew_reg EL7 2%nat (2%bv : bv 5) Q2E. ew_reg EL7 3%nat (3%bv : bv 5) Q3E. ew_reg EL7 4%nat (4%bv : bv 5) Q4E.
  ew_reg EL7 8%nat (8%bv : bv 5) Q8E. ew_reg EL7 9%nat (9%bv : bv 5) Q9E.
  ew_reg EL7 21%nat (21%bv : bv 5) Q10E. ew_reg EL7 10%nat (10%bv : bv 5) Q11E.
  try rewrite E732 in Q21E.
  preg HPRES7 2 (2%bv : bv 5) P72. preg HPRES7 3 (3%bv : bv 5) P73. preg HPRES7 4 (4%bv : bv 5) P74.
  preg HPRES7 8 (8%bv : bv 5) P78. preg HPRES7 21 (21%bv : bv 5) P721.
  rewrite P72, Q2D in Q2E. rewrite P73, Q3D in Q3E. rewrite P74, Q4D in Q4E. rewrite P78, Q8D in Q8E.
  rewrite P79 in Q9E. rewrite P721, Q21D in Q10E. rewrite HV7 in Q11E. rewrite HBASE in Q1E.
  pose proof HCE as (HJE & HFRE & HSAVE & _ & _ & _ & HJBKE & HBLKE & _).
  pose proof HJBKE as (HkevE & HbbE & _ & _ & _ & _ & _ & HwlE & _ & _ & _ & _ & _ & HroE & HplE & _).
  assert (HspE : spZ (ms_regs msE) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2E; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  (* check_verdict (0x82e64) *)
  replace (pa_sigma LS_check_verdict) with CHECK_VERDICT_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msE) (Z_to_bv 64 CHECK_VERDICT_A) (ms_mem msE) (seg_rom SEGS)) mdE)
    with (cfg_at (fx := fy) SEGS CHECK_VERDICT_A (ms_regs msE) (ms_mem msE) mdE).
  apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy CHECK_VERDICT_A
    CHECK_VERDICT_AK 0 [] check_verdict_apre (fun _ _ _ => False) check_verdict_awr check_verdict_apost
    (proj2 (aleaf_rd_none (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B CHECK_VERDICT_A CHECK_VERDICT_AK 0 []
      check_verdict_apre check_verdict_awr check_verdict_apost) (CV_C fy))
    cx fp ly7 S7 W7 (ms_mem msE) mdE _ (ms_regs msE) (POST cx) HB HJE HroE);
    [ rewrite Q1E, <- HBASE; apply ret_ok_codeptr_v; [lia | reflexivity]
    | unfold raZ; rewrite Q1E; rewrite unsigned_lit_small by (unfold link_text; lia); unfold link_text; lia
    | rewrite Q3E; exact HGP
    | rewrite Q4E; exact HTP
    | exact HspE
    | unfold CHECK_VERDICT_AK, CHECK_VERDICT_AFRAME, LLVMF_STK; lia
    | lia
    | unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia
    | apply Forall_nil
    | intros a (r & [] & _)
    | intros a (r & [] & _)
    | intros a []
    | unfold check_verdict_apre; rewrite Q10E, Q11E; reflexivity
    | ].
  intros W8 ly8 S8 regs8 mem8 md8 Hle8 HJ8 HPRES8 HFR8 HFD8 HFS8 HKEPT8 HSHK8 HS8 HPERM8 _.
  pose proof (d4_keep_pres D4R _ _ D4R_saved HPRES8) as KT5.
  pose proof (d4_keep_pres [21] _ _ D4S5_saved HPRES8) as KS5.
  pose proof (d4_keep_trans D4R _ _ _ (d4_keep_trans D4R _ _ _ (d4_keep_trans D4R _ _ _ (d4_keep_trans D4R _ _ _
    (d4_keep_trans D4R _ _ _ (d4_keep_trans D4R _ _ _ (d4_keep_trans D4R _ _ _ (d4_keep_trans D4R _ _ _
    (d4_keep_trans D4R _ _ _ KR1 KT1) KR2) KT2) KR3) KT3) KR4) KT4) KR5) KT5) as K8.
  set (ms8 := @mkst fy regs8 (getr (ms_regs msE) 1) mem8 (seg_rom SEGS)).
  destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly7 S7 W7 msE mdE CHECK_VERDICT_AK
    (fun a => inFP (check_verdict_awr (ms_regs msE) (rdW W7 (ms_mem msE))) a) ly8 S8 W8 ms8 md8 _
    HB HJE HCE ltac:(unfold CHECK_VERDICT_AK, CHECK_VERDICT_AFRAME, LLVMF_STK; lia) ltac:(intros a (r & [] & _)) HJ8
    ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia) HFR8 HFD8 HFS8 HKEPT8 HSHK8 HS8 HPERM8)
    as (HC8 & HRO8 & HCALL8).
  (* ---- the words of the cursor and the out slots at the return of check_verdict ---- *)
  assert (Hhi : lf_sp1 cx + LS_T130 + 8 <= spZ (c_regs cx)) by (unfold LS_T130; lia).
  assert (SL5 : d4_sl4 cx W5 mem5 (P + 1 + adv1 + adv2) (N - 1 - adv1 - adv2) own1 own2).
  { split; [exact HP5|]. split; [replace (N - 1 - adv1 - adv2) with (N - 1 - adv1 - adv2) by lia; exact HN5|].
    split; [|exact HSL5].
    apply (d4_slot_callee B cx TEXT_OF_AK ly4 S4 ly5 S5 W4 (ms_mem msB) W5 mem5 _ _ own1 HCALL5);
      [unfold LS_T130; lia | unfold LS_T130; lia | | exact HSLB].
    intros j Hj (r & Hr & Hra). unfold text_of_awr in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; rewrite ?Ha0B, ?Ha1B in Hra;
      unfold LS_P, LS_T128, LS_T130 in *; lia. }
  pose proof (d4_sl4_run cx W5 mem5 (ms_mem msC) _ _ _ _ KC SL5) as SLC.
  pose proof (d4_sl4_callee B cx DECIDE_AK ly5 S5 ly6 S6 W5 (ms_mem msC) W6 mem6 _ _ _ _ _ HCALL6
    ltac:(intros a (r & [] & _)) Hhi SLC) as SL6.
  pose proof (d4_sl4_run cx W6 mem6 (ms_mem msD) _ _ _ _ KD SL6) as SLD.
  pose proof (d4_sl4_callee B cx DECIDE_AK ly6 S6 ly7 S7 W6 (ms_mem msD) W7 mem7 _ _ _ _ _ HCALL7
    ltac:(intros a (r & [] & _)) Hhi SLD) as SL7.
  pose proof (d4_sl4_run cx W7 mem7 (ms_mem msE) _ _ _ _ KE SL7) as SLE.
  pose proof (d4_sl4_callee B cx CHECK_VERDICT_AK ly7 S7 ly8 S8 W7 (ms_mem msE) W8 mem8 _ _ _ _ _ HCALL8
    ltac:(intros a (r & [] & _)) Hhi SLE) as SL8.
  (* ---- the blocks of the two answers ---- *)
  pose proof HJBKA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HblA & HincA & _).
  pose proof HBLKA as (HmdA & HmkA & _).
  pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
    (ms_mem msA) mdA k2 HB HJA) as HPBA.
  pose proof (d4_fresh_ok B cx md mk T3 _ ly3 S3 nb1 HblA HmdA HmkA HincA HPBA
    (fun c b Hc Hb => Hap4 c b Hc Hb) (d4_nb_req own1 nb1 Hnb1)) as FR1.
  pose proof HC4 as (_ & _ & _ & _ & _ & _ & HJBK4c & HBLK4c & _).
  pose proof HJBK4c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbl4 & Hinc4 & _).
  pose proof HBLK4c as (Hmd4 & Hmk4 & _).
  pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly4 S4 W4
    (ms_mem ms4) md4 (k2 + 1) HB HJ4x) as HPB4.
  pose proof (d4_fresh_ok B cx md mk T3 _ ly4 S4 nb2 Hbl4 Hmd4 Hmk4 Hinc4 HPB4
    (fun c b Hc Hb => Hap5 c b Hc Hb) (d4_nb_req own2 nb2 Hnb2)) as FR2.
  assert (Hsub58 : forall c, In c (ablocks B ly5 S5) -> In c (ablocks B ly8 S8)).
  { intros c Hc. apply (Permutation_in c (Permutation_sym HPERM8)). apply (Permutation_in c (Permutation_sym HPERM7)).
    exact (Permutation_in c (Permutation_sym HPERM6) Hc). }
  assert (NB1in8 : forall b, In b nb1 -> In b (ablocks B ly8 S8)).
  { intros b Hb. apply Hsub58, Hsub5. exact (d4_nb_in B own1 nb1 ly3 S3 ly4 S4 Hnb1
      (fun E => proj1 (Hnb1b E)) b Hb). }
  assert (NB2in8 : forall b, In b nb2 -> In b (ablocks B ly8 S8)).
  { intros b Hb. apply Hsub58. exact (d4_nb_in B own2 nb2 ly4 S4 ly5 S5 Hnb2
      (fun E => proj1 (Hnb2b E)) b Hb). }
  assert (NB21 : forall b, In b nb2 -> ~ In b nb1).
  { intros b Hb2 Hb1.
    pose proof (Hap5 b b (d4_nb_in B own1 nb1 ly3 S3 ly4 S4 Hnb1 (fun E => proj1 (Hnb1b E)) b Hb1) Hb2) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. pose proof (d4_nb_req own2 nb2 Hnb2 b Hb2). lia. }
  (* ---- +0x694 .. +0x698: a0 := [s1 + 0x130], free ---- *)
  kreg K8 9 (9%bv : bv 5) K89. rewrite R9 in K89.
  assert (HU98 : bv_unsigned (getr regs8 9) = lf_sp1 cx)
    by (rewrite K89; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof SL8 as (_ & _ & S130 & _).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W8) mem8) S130) as Rown1.
  unfold ms8. rewrite Q1E, <- HBASE.
  clear HS SHOK.
  pose proof (d4_entry_l fy W8 regs8 mem8 3228 LS_T130 own1 ltac:(rewrite HU98; unfold LLVMF_STK in *; lia)
    ltac:(rewrite HU98; exact Hs32) ltac:(unfold LS_T130; lia) Rown1 ltac:(vm_compute; reflexivity)
    ltac:(rewrite HU98; exact (val_mem_of_rdword SEGS (w_H W8) mem8 _ _ S130))) as HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs8 [Z_to_bv 64 own1]))
    (mrestrict (w_H W8) (ms_mem (@mkst fy regs8 (Z_to_bv 64 (BASE + 3228)) mem8 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEIx8 : img_env pa_val A_LIM (Eimg (Ereg regs8 [Z_to_bv 64 own1]))) by apply Eimg_env.
  remember (Eimg (Ereg regs8 [Z_to_bv 64 own1])) as E8 eqn:HEdef.
  assert (EL8 : forall n, (n < A_TEXT)%nat -> ew E8 n = ew (Ereg regs8 [Z_to_bv 64 own1]) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  assert (E832 : ew E8 32 = Z_to_bv 64 own1)
    by (rewrite EL8 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs8 _ 0)).
  clear HEdef.
  paj_run_tok RUN HS HJ8 SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
  rename ms into msF, HF into HFF, HFr into HFrF, HG into HGF.
  pose proof (d4_keep_run fy W8 _ _ msF regs8 _ D4R HS EL8 D4R_low ltac:(d4chk)) as KR6.
  pose proof (d4_keep_run fy W8 _ _ msF regs8 _ [21] HS EL8 D4S5_low ltac:(d4chk)) as KR6s.
  assert (KF : kagree SEGS (fun _ => False) (rdW W8 (ms_mem ms8)) (rdW W8 (ms_mem msF))).
  { intros a _. unfold mbyte. rewrite (HFrF (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
    lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdF := mdx) in * end.
  assert (FdF : m_fds mdF = m_fds md8) by (subst mdF; rewrite !lf_wvb_fds; reflexivity).
  assert (FsF : m_fs mdF = m_fs md8) by (subst mdF; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly8 S8 W8 ms8 msF md8 mdF
    HC8 HJ8 KF (fun x Hx => HGF x Hx) FdF FsF) as HCF.
  pose proof (d4_sl4_run cx W8 mem8 (ms_mem msF) _ _ _ _ KF SL8) as SLF.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1F. prreg HS (10%bv : bv 5) Q10F.
  try rewrite E832 in Q10F. rewrite HBASE in Q1F.
  pose proof (d4_keep_trans D4R _ _ _ K8 KR6) as KF6.
  kreg KF6 2 (2%bv : bv 5) F2. kreg KF6 3 (3%bv : bv 5) F3. kreg KF6 4 (4%bv : bv 5) F4. kreg KF6 8 (8%bv : bv 5) F8.
  rewrite R2 in F2. rewrite R8 in F8.
  pose proof HCF as (HJF & _).
  apply (lf_free_tx_step SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE LV MT_OK
    AFREE4W AFREENULL4W LF_TRACE_FREE fy cx fp md mk kbs mbs gbs T3 nb2 nb1 [(md, MD_SIZE); (mk, MK_SIZE)] own1 _ _ _ _ _
    ly8 S8 W8 msF mdF (ms_regs msF) 3236 (lf_mo LF_MO_SET LF_MO_OP i) (POST cx) HB HCF Hnb1
    (fun b Hb => conj (NB1in8 b Hb) (FR1 b Hb))).
  { unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. pose proof HJBKA as (HkA & _). lia. }
  { exact Q10F. }
  { unfold spZ. rewrite F2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { unfold s0Z. rewrite F8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { rewrite F3. exact R3. }
  { rewrite F4. exact R4. }
  { exact Q1F. }
  { unfold LF_FREE_RAS, link_text. left. reflexivity. }
  intros W9 ly9 S9 regs9 mem9 md9 Hle9 HP9 HC9 HRO9 (E9 & HCALL9 & HE9) Hsub9.
  pose proof (d4_keep_pres D4R _ _ D4R_saved HP9) as KT6.
  pose proof (d4_keep_pres [21] _ _ D4S5_saved HP9) as KS6.
  pose proof (d4_keep_trans D4R _ _ _ KF6 KT6) as K9.
  assert (Hlo1 : alloc_ceiling <= lf_sp1 cx) by (unfold LLVMF_STK in *; lia).
  pose proof (d4_sl4_callee B cx ASTACK ly8 S8 ly9 S9 W8 (ms_mem msF) W9 mem9 E9 _ _ _ _ HCALL9
    ltac:(intros a Ha Hr; pose proof (HE9 a Ha); unfold LS_P in *; lia) Hhi SLF) as SL9.
  (* ---- +0x69c .. +0x6a0: a0 := [s1 + 0x128], free ---- *)
  kreg K9 9 (9%bv : bv 5) K99. rewrite R9 in K99.
  assert (HU99 : bv_unsigned (getr regs9 9) = lf_sp1 cx)
    by (rewrite K99; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  pose proof SL9 as (_ & _ & _ & S128).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W9) mem9) S128) as Rown2.
  pose proof HC9 as (HJ9 & _).
  change (ms_mem (@mkst fy regs9 (getr (ms_regs msF) 1) mem9 (seg_rom SEGS))) with mem9 in HJ9.
  rewrite Q1F, <- HBASE.
  clear HS SHOK.
  pose proof (d4_entry_l fy W9 regs9 mem9 3236 LS_T128 own2 ltac:(rewrite HU99; unfold LLVMF_STK in *; lia)
    ltac:(rewrite HU99; exact Hs32) ltac:(unfold LS_T128; lia) Rown2 ltac:(vm_compute; reflexivity)
    ltac:(rewrite HU99; exact (val_mem_of_rdword SEGS (w_H W9) mem9 _ _ S128))) as HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs9 [Z_to_bv 64 own2]))
    (mrestrict (w_H W9) (ms_mem (@mkst fy regs9 (Z_to_bv 64 (BASE + 3236)) mem9 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEIx9 : img_env pa_val A_LIM (Eimg (Ereg regs9 [Z_to_bv 64 own2]))) by apply Eimg_env.
  remember (Eimg (Ereg regs9 [Z_to_bv 64 own2])) as E9x eqn:HEdef.
  assert (EL9 : forall n, (n < A_TEXT)%nat -> ew E9x n = ew (Ereg regs9 [Z_to_bv 64 own2]) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  assert (E932 : ew E9x 32 = Z_to_bv 64 own2)
    by (rewrite EL9 by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs9 _ 0)).
  clear HEdef.
  paj_run_tok RUN HS HJ9 SHOK (0, 0);
    [apply awr_ok_x_cons; [cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                          | apply awr_ok_x_nil] |].
  rename ms into msG, HF into HFG, HFr into HFrG, HG into HGG.
  pose proof (d4_keep_run fy W9 _ _ msG regs9 _ D4R HS EL9 D4R_low ltac:(d4chk)) as KR7.
  pose proof (d4_keep_run fy W9 _ _ msG regs9 _ [21] HS EL9 D4S5_low ltac:(d4chk)) as KR7s.
  assert (KG : kagree SEGS (fun _ => False) (rdW W9 mem9) (rdW W9 (ms_mem msG))).
  { intros a _. unfold mbyte. rewrite (HFrG (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [d4_ssl d4_slot ss_mem YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
    lia. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdG := mdx) in * end.
  assert (FdG : m_fds mdG = m_fds md9) by (subst mdG; rewrite !lf_wvb_fds; reflexivity).
  assert (FsG : m_fs mdG = m_fs md9) by (subst mdG; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly9 S9 W9 _ msG md9 mdG
    HC9 HJ9 KG (fun x Hx => HGG x Hx) FdG FsG) as HCG.
  pose proof (d4_sl4_run cx W9 mem9 (ms_mem msG) _ _ _ _ KG SL9) as SLG.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1G. prreg HS (10%bv : bv 5) Q10G.
  try rewrite E932 in Q10G. rewrite HBASE in Q1G.
  pose proof (d4_keep_trans D4R _ _ _ K9 KR7) as KG7.
  kreg KG7 2 (2%bv : bv 5) G2. kreg KG7 3 (3%bv : bv 5) G3. kreg KG7 4 (4%bv : bv 5) G4. kreg KG7 8 (8%bv : bv 5) G8.
  rewrite R2 in G2. rewrite R8 in G8.
  apply (lf_free_tx_step SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE LV MT_OK
    AFREE4W AFREENULL4W LF_TRACE_FREE fy cx fp md mk kbs mbs gbs T3 [] nb2 [(md, MD_SIZE); (mk, MK_SIZE)] own2 _ _ _ _ _
    ly9 S9 W9 msG mdG (ms_regs msG) 3244 (lf_mo LF_MO_SET LF_MO_OP i) (POST cx) HB HCG Hnb2
    (fun b Hb => conj (Hsub9 b (NB2in8 b Hb) (NB21 b Hb)) (FR2 b Hb))).
  { unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. pose proof HJBKA as (HkA & _). lia. }
  { exact Q10G. }
  { unfold spZ. rewrite G2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { unfold s0Z. rewrite G8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  { rewrite G3. exact R3. }
  { rewrite G4. exact R4. }
  { exact Q1G. }
  { unfold LF_FREE_RAS, link_text. right. left. reflexivity. }
  intros W10 ly10 S10 regs10 mem10 md10 Hle10 HP10 HC10 HRO10 (E10 & HCALL10 & HE10) Hsub10.
  pose proof (d4_keep_pres D4R _ _ D4R_saved HP10) as KT7.
  pose proof (d4_keep_pres [21] _ _ D4S5_saved HP10) as KS7.
  pose proof (d4_keep_trans D4R _ _ _ KG7 KT7) as K10.
  pose proof (d4_sl4_callee B cx ASTACK ly9 S9 ly10 S10 W9 (ms_mem msG) W10 mem10 E10 _ _ _ _ HCALL10
    ltac:(intros a Ha Hr; pose proof (HE10 a Ha); unfold LS_P in *; lia) Hhi SLG) as SL10.
  (* ---- +0x6a4: j +0x1110 ---- *)
  pose proof HC10 as (HJ10 & _).
  change (ms_mem (@mkst fy regs10 (getr (ms_regs msG) 1) mem10 (seg_rom SEGS))) with mem10 in HJ10.
  rewrite Q1G, <- HBASE.
  clear HS SHOK.
  pose proof (d4_entry fy W10 regs10 mem10 3244) as HS.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs10 []))
    (mrestrict (w_H W10) (ms_mem (@mkst fy regs10 (Z_to_bv 64 (BASE + 3244)) mem10 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEIx10 : img_env pa_val A_LIM (Eimg (Ereg regs10 []))) by apply Eimg_env.
  remember (Eimg (Ereg regs10 [])) as E10x eqn:HEdef.
  assert (EL10 : forall n, (n < A_TEXT)%nat -> ew E10x n = ew (Ereg regs10 []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_to_tok RUNTO HS HJ10 SHOK (0, 0) LF_tail; [apply awr_ok_x_nil|].
  rename ms into msZ, HF into HFZ, HFr into HFrZ, HG into HGZ.
  pose proof (d4_keep_run_pi fy W10 _ _ msZ regs10 [] D4R HS EL10 D4R_low ltac:(d4chk)) as KR8.
  pose proof (d4_keep_run_pi fy W10 _ _ msZ regs10 [] [21] HS EL10 D4S5_low ltac:(d4chk)) as KR8s.
  pose proof (kagree_frame_nil _ _ _ HFrZ) as KZ.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdZ := mdx) in * end.
  assert (FdZ : m_fds mdZ = m_fds md10) by (subst mdZ; rewrite !lf_wvb_fds; reflexivity).
  assert (FsZ : m_fs mdZ = m_fs md10) by (subst mdZ; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly10 S10 W10 _ msZ md10 mdZ
    HC10 HJ10 KZ (fun x Hx => HGZ x Hx) FdZ FsZ) as HCZ.
  pose proof (d4_sl4_run cx W10 mem10 (ms_mem msZ) _ _ _ _ KZ SL10) as SLZ.
  (* ---- the cut at LF_tail ---- *)
  pose proof HCZ as (_ & _ & _ & _ & _ & _ & HJBKZ & _).
  pose proof HJBKZ as (HkZ & _ & _ & _ & _ & _ & _ & HwlZ & _ & _ & HblZ & _).
  pose proof HJBKA as (HkA & HbbA & _).
  pose proof (ak_cut_counters SK B MT MS la_nul MT_LE cx fp md mk kbs mbs gbs T3 _ _ _ _ _ _ ly10 S10 W10 msZ mdZ
    (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD HCZ) as HCZ'.
  specialize (HCZ' ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP in *; lia)
    ltac:(rewrite (lf_bl_bytes_eq B cx _ T3 ly3 S3 ly10 S10 HblA HblZ); exact HbbA)
    ltac:(unfold lf_wl, LF_WILD_OP in *; rewrite Z2Nat.inj_add by lia; cbn [Z.to_nat Pos.to_nat]; lia)).
  clear HCZ.
  destruct HCZ' as (HJZ & HFRZ & HSAVZ & HHDRZ & HFSHZ & HSLZ & HJBKZ' & HBLKZ & HDATAZ).
  pose proof (d4_keep_trans D4R _ _ _ K10 KR8) as KZ8.
  pose proof (d4_keep_trans [21] _ _ _ (d4_keep_trans [21] _ _ _ (d4_keep_trans [21] _ _ _ (d4_keep_trans [21] _ _ _
    (d4_keep_trans [21] _ _ _ KS5 KR6s) KS6) KR7s) KS7) KR8s) as KZ21.
  kreg KZ8 2 (2%bv : bv 5) Z2. kreg KZ8 3 (3%bv : bv 5) Z3. kreg KZ8 4 (4%bv : bv 5) Z4.
  kreg KZ8 8 (8%bv : bv 5) Z8. kreg KZ8 9 (9%bv : bv 5) Z9.
  kreg KZ8 19 (19%bv : bv 5) Z19. kreg KZ8 22 (22%bv : bv 5) Z22. kreg KZ8 23 (23%bv : bv 5) Z23.
  kreg KZ8 24 (24%bv : bv 5) Z24. kreg KZ8 25 (25%bv : bv 5) Z25. kreg KZ8 26 (26%bv : bv 5) Z26.
  kreg KZ8 27 (27%bv : bv 5) Z27. kreg KZ21 21 (21%bv : bv 5) Z21.
  rewrite Q21E in Z21.
  pose proof HLR as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  pose proof SLZ as (SZP & SZN & _ & _).
  apply (HT cx fy fp _ ly10 S10 W10 msZ mdZ HB HFX HJZ HFRZ).
  exists md, mk, (P + 1 + adv1 + adv2), (N - 1 - adv1 - adv2), kbs, mbs, gbs, T3.
  split; [exact Hi|].
  split; [exact (lf_shape_of_st_ok fy W10 _ _ msZ HS eq_refl)|].
  split; [split; [rewrite Z2; exact R2|]; split; [rewrite Z8; exact R8|]; split; [rewrite Z9; exact R9|];
          split; [rewrite Z3; exact R3 | rewrite Z4; exact R4]|].
  split; [split; [rewrite Z19; exact L19|]; split; [rewrite Z21; reflexivity|];
          split; [rewrite Z22; exact L22|]; split; [rewrite Z23; exact L23|]; split; [rewrite Z24; exact L24|];
          split; [rewrite Z25; exact L25|]; split; [rewrite Z26; exact L26 | rewrite Z27; exact L27]|].
  split; [exact HSAVZ|]. split; [exact HHDRZ|]. split; [exact HFSHZ|]. split; [exact HSLZ|].
  split; [split; [exact SZP|]; split; [exact SZN | exact Hq5]|].
  split; [exact HJBKZ'|]. split; [exact HBLKZ|]. split; [exact HDATAZ|].
  lia.
Qed.

End a.
