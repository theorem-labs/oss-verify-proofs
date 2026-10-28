(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface Sj_tables. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA El_sitesA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
#[warnings="-notation-for-abbreviation"] Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition EL_CJTAB_B : Z := 0x23694.
Definition CJT_TAB : list Z := [585764; 586672; 586176; 586328; 585984; 586892; 587084; 586480].
Definition cjt (i : Z) : Z := nth (Z.to_nat i) CJT_TAB 0.
Definition CJT_WORDS : list word := map (Z_to_bv 64) CJT_TAB.
Lemma cjt_image : ro_bytes_b asegs EL_CJTAB_B (u32s CJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cjt_at : forall m, mem_inv asegs m -> bytes_at asegs m EL_CJTAB_B (u32s CJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_CJTAB_B; lia | rewrite u32s_length; unfold EL_CJTAB_B, CJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact cjt_image.
Qed.
Lemma cjt_read : forall (m : word -> option byte) i a, mem_inv asegs m -> 0 <= i < 8 -> a = wa (EL_CJTAB_B + 4 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 (Z_to_bv 64 (cjt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EL_CJTAB_B CJT_WORDS i); [apply cjt_at; exact MI| | lia | reflexivity].
  unfold CJT_WORDS, cjt. rewrite nth_error_map. rewrite (nth_error_nth' CJT_TAB 0); [reflexivity|].
  change (length CJT_TAB) with 8%nat. lia.
Qed.
Lemma cjt_range : forall i, 0 <= i < 8 -> 0 <= cjt i < 2 ^ 31.
Proof.
  intros i Hi. unfold cjt.
  assert (F : forallb (fun x => (0 <=? x) && (x <? 2 ^ 31)) CJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length CJT_TAB)%nat) by (change (length CJT_TAB) with 8%nat; lia).
  specialize (F _ (nth_In CJT_TAB 0 L)). apply andb_true_iff in F. destruct F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
Qed.

Lemma cjt_mod4 : forall i, 0 <= i < 8 -> cjt i mod 4 = 0.
Proof.
  intros i Hi. unfold cjt.
  assert (F : forallb (fun x => x mod 4 =? 0) CJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length CJT_TAB)%nat) by (change (length CJT_TAB) with 8%nat; lia).
  specialize (F _ (nth_In CJT_TAB 0 L)). apply Z.eqb_eq in F. exact F.
Qed.

Definition EL_H22RET_B : Z := 0xb2c44.

Definition h22_W (q : Z) : list ivl := [(q + -48, q)].

Section H22.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variables (q node SELA sel : Z) (mA : mem).

  Hypothesis LO : ae_lo E + 48 <= q.
  Hypothesis GLO : SEGTOP_A <= ae_lo E.
  Hypothesis QH : q <= ae_hi E.
  Hypothesis HI47 : ae_hi E < 2^47.
  Hypothesis Q16 : q mod 16 = 0.
  Hypothesis N0 : 0 < node.
  Hypothesis NQ : node + 16 <= q - 48.
  Hypothesis N8 : node mod 8 = 0.
  Hypothesis SEL : 0 <= sel < 8.
  Hypothesis QS : q <= SELA.
  Hypothesis SH : SELA + 8 < 2^47.
  Hypothesis S84 : SELA mod 8 = 4.
  Hypothesis SHBM : forall m', munch (h22_W q) mA m' -> wmono asegs mA m' -> shb_cells m'.
  Hypothesis SZS : forall m', munch (h22_W q) mA m' -> wmono asegs mA m' -> shz m' (SELA - 4) 8.
  Hypothesis SZN : forall m', munch (h22_W q) mA m' -> wmono asegs mA m' -> shz m' node 16.
  Hypothesis AIM : forall m', munch (h22_W q) mA m' -> AINV_A E m'.
  Hypothesis SZD : forall m', munch (h22_W q) mA m' -> wmono asegs mA m' -> shz m' (ae_DOC E) 16.
  Hypothesis SZT : forall m', munch (h22_W q) mA m' -> wmono asegs mA m' -> shz m' (ae_TAPE E) (8 * ae_n E).

  Definition h22_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : machine_state -> Prop :=
    fun ms => exists (m0 : mem) (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      munch (h22_W q) mA m0 /\ wmono asegs mA m0 /\ mem_inv asegs m0 /\ frm0 fc' /\
      ( (stk asegs m0 (ae_lo E) q /\
           ms = MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m0 (seg_rom asegs))
     \/ (exists (pcs : Z) (j0 : list byte) (xra xs0 xs2 xs3 : word),
           In pcs (el_site_pcsB 22) /\ length j0 = 8%nat /\ stk asegs m0 (ae_lo E) (q + -48) /\
           rw_cells asegs m0 (q + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
           ms = MS (mkR xra (wz (q + -48)) gp (wz TPV_A) t0' t1' t2' xs0 (wz SHB) a0' a1' a2' a3' a4' a5' a6' a7' xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (wz pcs) fc' None m0 (seg_rom asegs)) ).

  Local Ltac ok_facts :=
    pose proof OK as OK'; destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SNS & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]];
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia);
    pose proof (ael_root_elem E OK) as [EL NR];
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia);
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR;
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia);
    unfold SEGTOP_A, USTACK_TOP, EL_H22_A, EL_H22RET_B, SHB, h22_W in *;
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.

  Lemma h22_pre : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    munch (h22_W q) mA m -> wmono asegs mA m -> stk asegs m (ae_lo E) q -> rw_cells asegs m SELA [C4 (wz sel)] ->
    rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> mem_inv asegs m ->
    evt asegs (fun ms => exists (m0 : mem) (j0 : list byte),
        munch (h22_W q) mA m0 /\ wmono asegs mA m0 /\ mem_inv asegs m0 /\ stk asegs m0 (ae_lo E) (q + -48) /\ length j0 = 8%nat /\
        rw_cells asegs m0 (q + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
        rw_cells asegs m0 node [C8 (wz (ae_DOC E)); C8 (wz 1)] /\
        ms = MS (mkR ra (wz (q + -48)) gp (wz TPV_A) t0 t1 t2 s0 (wz SHB) (wz (cjt sel + EL_CJTAB_B)) (wz node) (wz EL_CJTAB_B) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz (cjt sel + EL_CJTAB_B)) fc None m0 (seg_rom asegs))
      (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz SELA) (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H22_A) fc None m (seg_rom asegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH QS S84 SEL SH SHBM SZD SZN SZS SZT GLO.
    intros until m. intros MU WM ST XSEL NODE MI. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    zstep. carve_frame 48%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 5 lstep.
    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step. shz_pose SZS (SELA - 4). zstep. rewrite ?shr3_div.
    replace (SELA / 8) with ((SELA - 4) / 8) by (clear - S84 QS GLO LO; Z.div_mod_to_equations; lia). zstep. zstep. shz_norm. step. if_false.
    zstep. rewrite (a_sx32_small sel) by lia. zstep. step.
    if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (cjt_read mx sel (wa (Z.shiftl sel 2 + EL_CJTAB_B)) ltac:(assumption) SEL ltac:(unfold wa, EL_CJTAB_B; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ end.
    unfold EL_CJTAB_B in RJ. pose proof (cjt_range sel SEL) as CJR.
    zstep. zstep. rewrite (a_swrap32_small (cjt sel)) by lia.
    zstep. pose proof (cjt_mod4 sel SEL) as CJ4. rewrite (ret_pc_even (cjt sel + 0x23694)) by (clear - CJ4 CJR; Z.div_mod_to_equations; lia).
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?ja :: _) => exists ja end.
    pose proof FR as [[WFj _] _]. cbn [cells_wf cell_wf] in WFj.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [tauto|]. split; [exact FR|]. split; [exact NODE|].
    unfold EL_CJTAB_B. atp_st_eq_goal.
  Qed.

  Lemma h22_ret : forall (gp t0 t1 t2 xra xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    munch (h22_W q) mA m -> wmono asegs mA m -> stk asegs m (ae_lo E) (q + -48) -> mem_inv asegs m -> frm0 fc ->
    rw_cells asegs m (q + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt asegs (h22_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR xra (wz (q + -48)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H22RET_B) fc None m (seg_rom asegs)).
  Proof using HI47 LO OK Q16 QH GLO.
    clear SEL S84 QS SH N0 NQ N8 SHBM SZS SZN AIM SZD SZT.
    intros until j0. intros MU WM ST MI FRM FR. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    step. step. step. step. step. zstep.
    pose proof (stk_release asegs m (ae_lo E) _ _ ST FR ltac:(lia)) as STq. cbn [cells_size csize Nat.add] in STq.
    replace (q + -48 + Z.of_nat 48) with q in STq by lia.
    step.
    apply evt_done. exists m. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. left.
    split; [exact STq|]. replace (q + -48 + 48) with q by lia. atp_st_eq_goal.
  Qed.

  Definition h22_case (pc : Z) : Prop := forall (ra gp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    munch (h22_W q) mA m -> wmono asegs mA m -> stk asegs m (ae_lo E) (q + -48) -> mem_inv asegs m -> frm0 fc ->
    length j0 = 8%nat -> rw_cells asegs m (q + -48) [CB 8 j0; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
    evt asegs (h22_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR ra (wz (q + -48)) gp (wz TPV_A) t0 t1 t2 s0 (wz SHB) a0 (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom asegs)).

  Local Ltac fin_ret :=
    try change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A);
    lazymatch goal with |- evt _ (h22_post ?ra ?gp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11) (MS _ ?F _ ?fc _ ?mx _) =>
      eapply (h22_ret gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 F fc mx _); eassumption end.
  Local Ltac fin_site pcs :=
    apply evt_done; lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end; do 17 eexists;
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; right;
    exists pcs; eexists; do 4 eexists;
    split; [cbn; repeat (first [left; reflexivity | right])|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    try change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A); atp_st_eq_goal.

  Lemma h22_c0 : h22_case 0xb26b8.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. step. if_cases K1; [fin_ret|].
    step. step. step. if_cases K2; [fin_ret| fin_site 0xb272c].
  Qed.
  Lemma h22_c1 : h22_case 0xb2a44.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. step. if_cases K1; [fin_ret|].
    step. step. step. if_cases K2; [fin_ret|].
    step. step. step. if_cases K3; [fin_ret| fin_site 0xb2ac4].
  Qed.
  Lemma h22_c2 : h22_case 0xb2854.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. step. if_cases K1; [fin_ret|].
    step. step. step. if_cases K2; [step; fin_site 0xb2c64|].
    pose proof (AIM m MU) as AI2. pose proof AI2 as (TAPEB & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2. replace (8 * 2) with 16 in RDT2 by lia.
    clear TAPEB AI2.
    step. chk0 SZT (ae_TAPE E + 16). step. if_false. astep.
    step. if_cases K3; [fin_ret|].
    step. step. fin_site 0xb2c64.
  Qed.
  Lemma h22_c3 : h22_case 0xb28ec.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 2 TAPEB ltac:(lia)) as RDT2.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. step. if_cases K1; [fin_ret|].
    astep. step. step. if_cases K2; [step; fin_site 0xb2cc0|].
    step. chk0 SZT (ae_TAPE E + 16). step. if_false.
    step. step. if_cases K3; [fin_ret|].
    step. step. fin_site 0xb2cc0.
  Qed.
  Lemma h22_c4 : h22_case 0xb2794.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY. rewrite Z.mul_1_r in RDTY.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. if_cases K1; [fin_ret| fin_site 0xb27f8].
  Qed.
  Lemma h22_c5 : h22_case 0xb2b20.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY. rewrite Z.mul_1_r in RDTY.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. if_cases K1; [fin_ret| fin_site 0xb2b84].
  Qed.
  Lemma h22_c6 : h22_case 0xb2be0.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY. rewrite Z.mul_1_r in RDTY.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. if_cases K1; [fin_site 0xb2d2c| fin_ret].
  Qed.
  Lemma h22_c7 : h22_case 0xb2984.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j0. intros MU WM ST MI FRM J8 FR NODE. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -48)) = q + -48) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. chk0 SZN (node + 8). step. if_false.
    pose proof (AIM m MU) as AI1. pose proof AI1 as (TAPEB & _ & _ & DOCC & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia)) as RDT. rewrite Z.mul_1_r in RDT.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDTY. rewrite Z.mul_1_r in RDTY.
    clear TAPEB AI1.
    step. chk0 SZD (ae_DOC E). step. if_false.
    step. step. astep. step. chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. astep. step. if_cases K1; [fin_ret| fin_site 0xb29e8].
  Qed.

  Lemma h22_walk : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    munch (h22_W q) mA m -> wmono asegs mA m -> stk asegs m (ae_lo E) q -> mem_inv asegs m -> frm0 fc ->
    rw_cells asegs m SELA [C4 (wz sel)] -> rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
    0 <= bv_unsigned ra < 2^64 -> bv_unsigned ra mod 2 = 0 ->
    evt asegs (h22_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz SELA) (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H22_A) fc None m (seg_rom asegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH QS S84 SEL SH SHBM SZD SZN SZS SZT GLO.
    intros until m. intros MU WM ST MI FRM XSEL NODE _ _.
    eapply evt_cut; [exact (h22_pre ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MU WM ST XSEL NODE MI)|].
    cbv beta. intros ms1 (m0 & j0 & MU0 & WM0 & MI0 & ST0 & J8 & FR0 & NODE0 & ->).
    assert (CASES8 : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by lia.
    destruct CASES8 as [EQS|[EQS|[EQS|[EQS|[EQS|[EQS|[EQS|EQS]]]]]]]; rewrite EQS.
    - change (cjt 0 + EL_CJTAB_B) with 0xb26b8. exact (h22_c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
    - change (cjt 1 + EL_CJTAB_B) with 0xb2a44. exact (h22_c1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
    - change (cjt 2 + EL_CJTAB_B) with 0xb2854. exact (h22_c2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
    - change (cjt 3 + EL_CJTAB_B) with 0xb28ec. exact (h22_c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
    - change (cjt 4 + EL_CJTAB_B) with 0xb2794. exact (h22_c4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
    - change (cjt 5 + EL_CJTAB_B) with 0xb2b20. exact (h22_c5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
    - change (cjt 6 + EL_CJTAB_B) with 0xb2be0. exact (h22_c6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
    - change (cjt 7 + EL_CJTAB_B) with 0xb2984. exact (h22_c7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU0 WM0 ST0 MI0 FRM J8 FR0 NODE0).
  Qed.
End H22.

Section Arm22.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH in *; lia.

Theorem arm22_okA : forall W, (forall pcs, throw_siteB RT PMc W 22 pcs) -> arm_cpsA RT PMc W 22.
Proof using AF RC.
  intros W SITE Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED48 : lf_lo X + 16 <= lf_S1 X - 48) by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 22 sel idx jr jos t m 48 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED48) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof (arm_ctx_below RT AF X E Σ 22 sel idx jr jos t m) as CTX.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof AL as (ALT & ALS & ALP & ALF & WLO). rewrite ELO in WLO.
  assert (SZS : forall m', munch (h22_W sp') m m' -> wmono asegs m m' -> shz m' (sp' + 124 - 4) 8).
  { intros m' MU WM. apply (shz_stack RT AF Σ m' (sp' + 124 - 4) 8 (ARTM m' MU WM)); [clear - WLO NEED48; ul| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  change (el_arm_pcA 22) with 728116. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO48 : f + 1024 <= sp' - 48) by (clear - FLO NEED48; lia).
  apply (aevt_evt RT AF PMc MST).

  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply h22_walk with (E := E) (q := sp') (node := f + 208) (SELA := sp' + 124) (sel := sel) (mA := m).
    all: first
      [ exact OKE | apply munch_refl | apply wmono_refl | rewrite ELO; exact STg | exact MIg | exact FRM | exact C100 | exact CE
      | exact SHBM | exact SZS | exact SZN | exact AIM | exact SZD | exact SZT | exact SEL
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; reflexivity
      | rewrite ?ELO, ?EHI; clear - NEED48 LLO SPR SPT SPA' FPOS F64 FLO48; ul
      | rewrite ?ELO, ?EHI; clear - NEED48 LLO SPR SPT SPA' FPOS F64 FLO48; Z.div_mod_to_equations; ul ]. }
  cbv beta. intros ms1 (m0 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & F' & fc' & MU0 & WM0 & MI0 & FRM0 &
                         [(ST0 & ->) | (pcs & j0 & xra & xs0 & xs2 & xs3 & IN & LJ & ST0 & FR0 & ->)]).
  -
    rewrite ret_pc_even by lia. zstep. apply evt_done.
    rewrite ELO in ST0.
    apply (POST false (rt_credit RT Σ) Σ m0 fc' F').
    exact (arm_post_below_le RT AF W 22 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m0 fc' 48 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED48
             MU0 WM0 MI0 ST0 FRM0 ltac:(unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; pose proof (mcost_nonneg EXC_SIZE ltac:(unfold EXC_SIZE; lia)); lia)).
  -
    destruct (CTX m0 48 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED48 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    rewrite ELO in ST0.
    assert (B12 : (pcs =? EL_SITE_END_B) = false /\ (pcs =? hd 0 (el_site_pcsB 23)) = false)
      by (clear - IN; simpl in IN; repeat destruct IN as [<-|IN]; (contradiction || (split; reflexivity))).
    destruct B12 as [B1 B2]. cbn [hd el_site_pcsB Z.eqb Pos.eqb] in B2.
    pose proof (SITE pcs) as S. unfold throw_siteB, site_fszB, site_frameB, site_regsB in S. rewrite B1, B2 in S. cbn [orb] in S.
    apply evt_done. replace (sp' + -48) with (sp' - 48) by lia.
    eapply (S Σ K {| lf_usp := usp; lf_S1 := sp'; lf_F := f; lf_lo := lo |} E sel idx jr jos t j0 0
              xra gp t0' t1' t2' xs0 (wz SHB) a0' a1' a2' a3' a4' a5' a6' a7' xs2 xs3 (wz (f + 32))
              (wz (f + 208)) (wz 0) (wz f) s9 s10 (wz (f + 120)) t3' t4' t5' t6' F' fc' m0);
      cbn [lf_usp lf_S1 lf_F lf_lo site_jlenB site_cvB];
      [exact IN| exact FDO| exact MST| exact LK| exact OKE| exact LE| exact SEL| exact IDX| exact AL| exact FRS| exact LPA
      | clear - LVB; unfold arm_xliveA in LVB; cbn [Z.eqb Pos.eqb orb] in LVB; lia
      | clear - CRB; unfold arm_costA in CRB; cbn [Z.eqb Pos.eqb orb] in CRB; lia
      | exact ART0| exact MI0| replace (sp' - 48) with (sp' + -48) by lia; exact ST0
      | clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul
      | exact AM0| exact FRM0| exact XD0| exact AUX0| exact SPB| exact LJ| exact I
      | replace (sp' - 48) with (sp' + -48) by lia; exact FR0| repeat split|].
    intros c Σ' m' fc'' F'' ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s6' s7' s8' s9' s10' s11' t3'' t4'' t5'' t6'' LP.
    unfold lf_st, EL_LRET_A. cbn [lf_usp lf_S1 lf_F lf_lo].
    destruct LP as (AX & MI' & ST' & FRM' & LV' & FRS' & SP' & CR' & PRES' & MEM' & _). cbn [lf_usp lf_S1 lf_F lf_lo] in ST', PRES', MEM'.
    apply (aevt_evt RT AF PMc MST). zstep. apply evt_done.
    apply (POST true c Σ' m' fc'' F''). unfold arm_postA. cbn [lf_usp lf_S1 lf_F lf_lo].
    split; [exact AX|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|]. split; [exact LV'|]. split; [exact FRS'|]. split; [exact SP'|].
    split; [exact CR'|].
    split; [intros a Ha Ho; rewrite (PRES' a Ha Ho); apply MU0; cbn [outside h22_W]; split; [exact (NBELOW _ Ha)| exact I]|].
    split; [exact MEM'| intros _; right; lia].
Qed.
End Arm22.
