(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 295 of its 342 lines of code are new or changed and 357 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write from the selector's join (+0xffc) to kernel's return (+0x1014).
   Offsets from 0x827d4; listing
   (internal path) (internal record, sha256 e84d6f0c6974).

     +0xffc  a0 := s1 + 0x118, a1 := s1 + 0x130, text_of        0x837d8 (Txo.v lf_text_of_call, Txa.v lf_text_of_after)
     +0x1008 s6 := a0, a0 := s1 + 0x118, kernel                  0x837e4 (ArmR.v ar_leaf_call, Kpre.v, Kpost.v)

   w_tk : forall POST i, 0 <= i <= 47 -> FROM POST (w_k_inv i) -> FROM POST (sel_join .. LF_wj 21%bv i).
   kernel's application at 0x837e4 is OPEN under kernel_c.v's read set (open item W2).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxo.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1S.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma w_bv5_ne : forall a b : bv 5, bv_unsigned a <> bv_unsigned b -> a <> b.
Proof. intros a b H E. subst. exact (H eq_refl). Qed.

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
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Lemma w_tk : forall POST i, 0 <= i <= 47 ->
  FROM POST (w_k_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (sel_join SK B MT MS la_nul LF_MO_SET LF_MO_OP LF_wj 21%bv i).
Proof.
  intros POST i Hi HT cx fy fp k2 ly3 S3 W3 ms3 md3 HB HFX HJ HFR GI.
  destruct GI as (md & mk & P & N & s & nm & kbs & mbs & gbs & T3 & _ & HSH & HCORE & HLR & HS21 & HNM & HC0 & HCUR
    & HOPN).
  pose proof HB as (HPRE & HFRM & HGX & HLAN & HMSE & HE0 & HE0sp & HCTXA & HMO).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HCORE as (R2 & R8 & R9 & R3 & R4).
  pose proof HLR as (L19 & _ & L22 & L23 & L24 & L25 & L26 & L27).
  destruct L19 as [Habs | L19]; [apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs|].
  destruct L22 as [Habs | L22]; [apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs|].
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (HGP & HTP).
  rewrite (lf_shape_eta fy LF_wj ms3 HSH).
  (* ---- +0xffc .. +0x1004: a0 := s1 + 0x118, a1 := s1 + 0x130, text_of ---- *)
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LF_wj) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_wj)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) [] D4R HS EL D4R_low ltac:(d4chk)) as KR1.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) [] [21] HS EL D4S5_low ltac:(d4chk)) as KS1.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (mdA := mdB) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC0 HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) HCUR) as HCURA.
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
  pose proof HJBKA as (Hkev & Hbb & Hfa & Hnin & Hfd & Hfs & Hmo & Hwl & Hgi & Henv & HblA & HincA & Hla & Hro & Hpl & Hpv).
  destruct (lf_saved_ra_s0 cx W3 msA HSAVA) as (HR8 & HR16).
  pose proof HCURA as (HPA & HNA & Hq).
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
      P N LS_T130 5648 HB HJA Hkev
      ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB; lia) Hbb
      ltac:(pose proof LF_LIVE_HELD_room; unfold TEXT_OF_LIVE; lia) Hwl
      ltac:(unfold lf_wl, LF_WILD_OP, LINK_WILD_PER_CALL; lia) Hro Hpl HR8 HR16 HPA HNA
      Hq (or_intror eq_refl) HspA Hs0A Ha0A Ha1A Q3 Q4 HBASE Q1
      ltac:(unfold LF_TEXT_OF_SITES; right; right; left; reflexivity)). }
  intros W4 c4 Hle4 HPOST.
  destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HPRES4 & HFR4 & HFD4 & HFS4 & HKEPT4 & HSHK4 &
    HMO4 & HLED4 & HPA4).
  pose proof (d4_keep_pres D4R _ _ D4R_saved HPRES4) as KT1.
  pose proof (d4_keep_pres [21] _ _ D4S5_saved HPRES4) as KU1.
  set (ms4 := @mkst fy regs4 (getr (ms_regs msA) 1) mem4 (seg_rom SEGS)).
  destruct (lf_text_of_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 msA mdA (ms_regs msA) P N LS_T130 ly4 S4 W4 regs4
    mem4 md4 ms4 (lf_mo LF_MO_SET LF_MO_OP i) HB HJA HCA HPA HNA Hq (or_intror eq_refl)
    HspA Ha0A Ha1A eq_refl HJ4 HFR4 HFD4 HFS4 HKEPT4 HSHK4 HLED4 HPA4)
    as (own1 & s1v & t1 & adv1 & nb1 & HA10 & Hs1v & HC4 & HRO4 & HP4 & HN4 & Hq4 & HSL4 & Hnb1 & Hnb1a & Hnb1b &
        Hsub4 & Hap4 & HCALL4 & HD1 & HTX1).
  pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
    (ms_mem msA) mdA k2 HB HJA) as HPBA.
  pose proof HBLKA as (HmdA & HmkA & _).
  pose proof (d4_fresh_ok B cx md mk T3 _ ly3 S3 nb1 HblA HmdA HmkA HincA HPBA
    (fun c b Hc Hb => Hap4 c b Hc Hb) (d4_nb_req own1 nb1 Hnb1)) as FR1.
  (* ---- +0x1008 .. +0x1010: s6 := a0, a0 := s1 + 0x118, kernel ---- *)
  unfold ms4. rewrite Q1, <- HBASE.
  clear HS SHOK.
  assert (HEI4 : img_env pa_val A_LIM (Eimg (Ereg regs4 []))) by apply Eimg_env.
  pose proof (d4_entry fy W4 regs4 mem4 5648) as HS.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg regs4 []))
    (mrestrict (w_H W4) (ms_mem (@mkst fy regs4 (Z_to_bv 64 (BASE + 5648)) mem4 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  remember (Eimg (Ereg regs4 [])) as E4 eqn:HEdef.
  assert (EL4 : forall n, (n < A_TEXT)%nat -> ew E4 n = ew (Ereg regs4 []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ4 SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (d4_keep_run fy W4 _ _ msB regs4 [] [2; 3; 4; 8; 9; 19; 23; 24; 25; 26; 27] HS EL4
    ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk)) as KR2.
  pose proof (d4_keep_run fy W4 _ _ msB regs4 [] [21] HS EL4 D4S5_low ltac:(d4chk)) as KS2.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
  assert (FdB : m_fds mdB = m_fds md4) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
  assert (FsB : m_fs mdB = m_fs md4) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1) ly4 S4 W4 ms4 msB md4 mdB HC4
    HJ4 KB (fun x Hx => HGB x Hx) FdB FsB) as HCB.
  assert (HCUR4 : lf_cur cx W4 ms4 (P + adv1) (N - adv1)) by (split; [exact HP4|]; split; [exact HN4 | exact Hq4]).
  pose proof (lf_cur_keep (fun _ => False) cx W4 ms4 W4 msB _ _ KB (fun a _ H => H) HCUR4) as HCURB.
  pose proof (d4_slot_run W4 _ _ _ _ KB HSL4) as HSLB4.
  assert (HD1B : dec_ans B ly4 S4 (rdW W4 (ms_mem msB)) s1v t1) by exact (d4_dec_run B ly4 S4 _ _ s1v t1 KB HD1).
  assert (HTX1B : tx_ans B SEGS own1 nb1 ly4 S4 (rdW W4 (ms_mem msB)) s1v t1)
    by exact (tx_ans_keep B own1 nb1 ly4 S4 ly4 S4 _ _ _ s1v t1 HTX1 (fun c H => H) KB (fun _ _ _ _ H => H)).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1B. prreg HS (2%bv : bv 5) Q2B. prreg HS (3%bv : bv 5) Q3B. prreg HS (4%bv : bv 5) Q4B.
  prreg HS (9%bv : bv 5) Q9B. prreg HS (10%bv : bv 5) Q10B. prreg HS (22%bv : bv 5) Q22B.
  ew_reg EL4 2%nat (2%bv : bv 5) Q2B. ew_reg EL4 3%nat (3%bv : bv 5) Q3B. ew_reg EL4 4%nat (4%bv : bv 5) Q4B.
  ew_reg EL4 9%nat (9%bv : bv 5) Q9B. ew_reg EL4 9%nat (9%bv : bv 5) Q10B. ew_reg EL4 10%nat (10%bv : bv 5) Q22B.
  preg HPRES4 2 (2%bv : bv 5) P42. preg HPRES4 3 (3%bv : bv 5) P43. preg HPRES4 4 (4%bv : bv 5) P44.
  preg HPRES4 9 (9%bv : bv 5) P49.
  rewrite P42, Q2 in Q2B. rewrite P43, Q3 in Q3B. rewrite P44, Q4 in Q4B.
  rewrite P49, Q9 in Q9B, Q10B. rewrite HA10 in Q22B. rewrite HBASE in Q1B.
  rewrite unsigned_lit_small in Q10B by (unfold LLVMF_STK in *; lia).
  pose proof HCB as (HJB & HFRB & HSAVB & HHDRB & HFSHB & HSLB & HJBKB & HBLKB & HDATAB).
  pose proof HJBKB as (HkevB & HbbB & _ & _ & _ & _ & _ & HwlB & _ & _ & HblB & HincB & _ & HroB & HplB & _).
  pose proof HCURB as (HcPB & HcNB & HcqB).
  assert (HspB : spZ (ms_regs msB) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2B; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Ra0 : aarg (ms_regs msB) 0 = lf_sp1 cx + LS_P)
    by (rewrite ar_aarg0, Q10B; apply unsigned_lit_small; unfold LS_P, LLVMF_STK in *; lia).
  replace (pa_sigma LS_kernel) with KERNEL_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 KERNEL_A) (ms_mem msB) (seg_rom SEGS)) mdB)
    with (@cfg_at fy SEGS KERNEL_A (ms_regs msB) (ms_mem msB) mdB).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (KERNEL fy).
  - exact HB.
  - exact HJB.
  - exact HroB.
  - rewrite Q1B, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1B. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite Q3B. exact HGP.
  - rewrite Q4B. exact HTP.
  - exact HspB.
  - rewrite KERNEL_AK_val. unfold LLVMF_STK. lia.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia.
  - apply (ar_side_room S4 fp _ HFRB). vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold kernel_awr in Hin. rewrite Ra0 in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply ar_ajw_G. unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold NK_CHUNK, NK_OPEN in Hr. lia.
    + apply ar_ajw_G. unfold inG, G_HARNESS. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. unfold LONG_ALIAS_SIZE in Hr. lia.
    + apply ar_ajw_stack. unfold LS_P, LLVMF_STK in *. lia.
  - intros a (r & Hin & Hr). unfold kernel_awr in Hin. rewrite Ra0 in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply (ar_not_ro_G HSEGS). unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold NK_CHUNK, NK_OPEN in Hr. lia.
    + apply (ar_not_ro_G HSEGS). unfold inG, G_HARNESS. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. unfold LONG_ALIAS_SIZE in Hr. lia.
    + apply (ar_not_ro_high HSEGS). unfold LS_P, LLVMF_STK in *. lia.
  - intros a Ha.
    pose proof (lf_kernel_ard SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp ly4 S4 W4 (ms_mem msB) mdB (k2 + 1) md mk kbs mbs gbs (ms_regs msB) (P + adv1) (N - adv1) HB HJB HroB
      HDATAB HcPB HcNB HcqB Ra0 HspB a Ha) as Hk. rewrite HspB in Hk. exact Hk.
  - exact (lf_kernel_apre SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp ly4 S4 W4 (ms_mem msB) mdB (k2 + 1) md mk kbs mbs gbs (ms_regs msB) (P + adv1) (N - adv1) HB HJB HroB
      HDATAB HplB HcPB HcNB HcqB Ra0 HspB).
  - intros W5 ly5 S5 regs5 mem5 md5 Hle5 HJ5 Hpr Hfr5 Hfd5 Hfs5 Hkp Hsk Hs5 Hperm Hpost.
    rewrite Z.add_0_r in HJ5.
    set (ms5 := @mkst fy regs5 (getr (ms_regs msB) 1) mem5 (seg_rom SEGS)).
    change mem5 with (ms_mem ms5) in HJ5, Hkp, Hsk, Hpost.
    destruct (lf_kernel_post SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp (k2 + 1) _ _ _ _ md mk kbs mbs gbs T3 _ (P + adv1) (N - adv1) ly4 S4 W4 msB mdB ly5 S5 W5 ms5 md5
      (ms_regs msB) regs5 HB HFRB HJB HJ5 Ra0 Hkp Hsk Hs5 Hperm Hfd5 Hfs5 Hpost HSAVB HHDRB HFSHB HSLB HCURB HJBKB
      HBLKB HDATAB)
      as (kbs' & adv & Hadv & Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & Hnx & Hch & Hend & Hsock
        & Hsend & Hopd & _ & _ & _).
    pose proof (d4_keep_pres [2; 3; 4; 8; 9; 19; 23; 24; 25; 26; 27] _ _
      ltac:(intros r Hr; unfold acallee_saved; cbn in Hr; lia) Hpr) as KT2.
    pose proof (d4_keep_pres [21] _ _ D4S5_saved Hpr) as KU2.
    pose proof (d4_keep_trans [2; 3; 4; 8; 9; 19; 23; 24; 25; 26; 27] _ _ _
      (d4_keep_trans [2; 3; 4; 8; 9; 19; 23; 24; 25; 26; 27] _ _ _
        (d4_keep_trans [2; 3; 4; 8; 9; 19; 23; 24; 25; 26; 27] _ _ _
          (fun r Hr => KR1 r ltac:(cbn in Hr |- *; tauto)) (fun r Hr => KT1 r ltac:(cbn in Hr |- *; tauto))) KR2) KT2)
      as K5.
    pose proof (d4_keep_trans [21] _ _ _ (d4_keep_trans [21] _ _ _ (d4_keep_trans [21] _ _ _ KS1 KU1) KS2) KU2) as K21.
    preg Hpr 22 (22%bv : bv 5) P522. rewrite Q22B in P522.
    (* the kernel's call, as lf_call *)
    assert (HCALLK : lf_call B cx KERNEL_AK ly4 S4 ly5 S5 W4 (ms_mem msB) W5 (ms_mem ms5)
              (fun a => inFP (kernel_awr (ms_regs msB) (rdW W4 (ms_mem msB))) a)).
    { split; [rewrite KERNEL_AK_val; unfold LLVMF_STK in *; lia|].
      split; [rewrite KERNEL_AK_val; unfold LLVMF_STK in *; lia|]. split; [exact Hkp | exact Hsk]. }
    destruct (lf_img_facts B MS la_nul HSEGS TB HMSE HLAN) as (HIMG & _).
    destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly4 S4 W4
      (ms_mem msB) mdB (k2 + 1) HB HJB) as (_ & _ & _ & _ & _ & _ & HAR4).
    assert (HEK : forall a, inFP (kernel_awr (ms_regs msB) (rdW W4 (ms_mem msB))) a ->
              lf_img_fp MS la_nul a \/ lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_P + 16).
    { intros a (r & Hin & Hr). unfold kernel_awr in Hin. rewrite Ra0 in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
      - left. unfold lf_img_fp. left. unfold NK_CHUNK, NK_OPEN, NK_SIZE in *. lia.
      - left. unfold lf_img_fp. right; right; left. unfold LONG_ALIAS_SIZE in Hr. lia.
      - right. lia. }
    assert (HBK : forall b m a, In (b, m) (ablocks B ly4 S4) -> b <= a < b + m ->
              ~ inFP (kernel_awr (ms_regs msB) (rdW W4 (ms_mem msB))) a).
    { intros b m a Hb Ha HE. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR4 Hb) as (_ & _ & Hc & _).
      destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR4 ltac:(left; exists b, m; split; [exact Hb | unfold req_size; destruct (m =? 0) eqn:Em'; lia])) as (_ & Hni).
      destruct (HEK a HE) as [Hf | Hf].
      - exact (Hni (proj1 (HIMG a Hf))).
      - unfold req_size in Hc. destruct (m =? 0) eqn:Em; unfold LS_P, LLVMF_STK in *; lia. }
    assert (Hsub5 : forall c, In c (ablocks B ly4 S4) -> In c (ablocks B ly5 S5))
      by (intros c Hc; exact (Permutation_in c (Permutation_sym Hperm) Hc)).
    apply (HT cx fy fp (k2 + 1) ly5 S5 W5 ms5 md5 HB HFX HJ5 ltac:(rewrite Hfr5; exact HFRB)).
    exists md, mk, (P + adv1 + adv), (N - adv1 - adv), s, s1v, own1, nm, t1, kbs', mbs, gbs, T3, nb1.
    split; [exact Hi|].
    split.
    { unfold lf_shape, ms5. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1B, <- HBASE. unfold LW_kret, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    split.
    { unfold lf_core, ms5. cbn [ms_regs mkst].
      kreg K5 2 (2%bv : bv 5) Z2. kreg K5 8 (8%bv : bv 5) Z8. kreg K5 9 (9%bv : bv 5) Z9.
      kreg K5 3 (3%bv : bv 5) Z3. kreg K5 4 (4%bv : bv 5) Z4.
      rewrite Z2, Z8, Z9, Z3, Z4. repeat split; assumption. }
    split.
    { unfold w_regs, ms5. cbn [ms_regs mkst].
      kreg K5 19 (19%bv : bv 5) Z19. kreg K21 21 (21%bv : bv 5) Z21. kreg K5 23 (23%bv : bv 5) Z23.
      kreg K5 24 (24%bv : bv 5) Z24. kreg K5 25 (25%bv : bv 5) Z25. kreg K5 26 (26%bv : bv 5) Z26.
      kreg K5 27 (27%bv : bv 5) Z27.
      rewrite Z19, Z21, P522, Z23, Z24, Z25, Z26, Z27. repeat split; assumption. }
    split; [exact HNM|].
    split.
    { split; [exact HJ5|]. split; [rewrite Hfr5; exact HFRB|]. split; [exact Hsv2|]. split; [exact Hhd2|].
      split; [exact Hfs2'|]. split; [exact Hsl2|]. split; [exact Hjbk2|]. split; [exact Hblk2 | exact Hdat2]. }
    split; [replace (P + adv1 + adv) with (P + adv1 + adv) by reflexivity;
            replace (N - adv1 - adv) with (N - adv1 - adv) by reflexivity; exact Hcur2|].
    split; [rewrite Hopd; exact HOPN|].
    split.
    { exact (dec_ans_callee B cx KERNEL_AK ly4 S4 ly5 S5 W4 (ms_mem msB) W5 (ms_mem ms5) _ s1v t1 HCALLK
        HBK (fun b m Hb => Hsub5 (b, m) Hb) HD1B). }
    split.
    { exact (tx_ans_keep B own1 nb1 ly4 S4 ly5 S5 _ _ _ s1v t1 HTX1B Hsub5 (lf_call_kagree B cx KERNEL_AK ly4 S4 ly5 S5
        W4 (ms_mem msB) W5 (ms_mem ms5) _ HCALLK) (fun k a Hb Ha => lfx_blk B ly4 S4 ly5 S5 _ _ _ own1 k a Hb Ha
        (HBK own1 k a Hb Ha))). }
    split.
    { apply (d4_slot_callee B cx KERNEL_AK ly4 S4 ly5 S5 W4 (ms_mem msB) W5 (ms_mem ms5) _ _ own1 HCALLK);
        [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLB4].
      intros j Hj HE. destruct (HEK _ HE) as [Hf | Hf].
      - pose proof (proj1 (HIMG _ Hf)) as Hi'. pose proof (pa_segs_low _ Hi') as L.
        unfold LS_T130, kLowMemEnd, LLVMF_STK in *. lia.
      - unfold LS_T130, LS_P in *. lia. }
    split; [exact Hnb1|].
    split; [intros E1; exact (proj2 (Hnb1b E1))|].
    split.
    { split; [|exists ly3, S3; split; [exact HblA | exact Hbb]].
      intros b Hb. destruct (FR1 b Hb) as (Hne & Hd). split; [|split; [exact Hne | exact Hd]].
      apply Hsub5. exact (d4_nb_in B own1 nb1 ly3 S3 ly4 S4 Hnb1 (fun E1 => proj1 (Hnb1b E1)) b Hb). }
    split; [exact Hnx|]. split; [exact Hch|]. split; [exact Hend|]. split; [exact Hsock | exact Hsend].
Qed.

End a.
