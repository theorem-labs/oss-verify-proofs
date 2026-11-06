(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Sj_tables Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA
     Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA Atp_arrlA Atp_arratA El_sitesA
     El_haccA El_h6A El_h7A El_h8A Atp_h_gstrA El_gstrA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
#[warnings="-notation-for-abbreviation"] Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition EL_CJTAB_B : Z := 0x23884.
Definition CJT_TAB : list Z := [595088; 596004; 595520; 595660; 595368; 596144; 596192; 595800].
Definition cjt (i : Z) : Z := nth (Z.to_nat i) CJT_TAB 0.
Definition CJT_WORDS : list word := map (Z_to_bv 64) CJT_TAB.
Lemma cjt_image : ro_bytes_b bsegs EL_CJTAB_B (u32s CJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cjt_at : forall m, mem_inv bsegs m -> bytes_at bsegs m EL_CJTAB_B (u32s CJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_CJTAB_B; lia | rewrite u32s_length; unfold EL_CJTAB_B, CJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact cjt_image.
Qed.
Lemma cjt_read : forall (m : word -> option byte) i a, mem_inv bsegs m -> 0 <= i < 8 -> a = wa (EL_CJTAB_B + 4 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 (Z_to_bv 64 (cjt i))).
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

Definition EL_H22RET_B : Z := 0xb51c8.
Definition EL_CSTR_B : Z := 0xb8228.

Definition h22_W (q : Z) : list ivl := [(q + -176, q)].

Definition cast_frameB (j0 : list byte) (res : list cell) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0] ++ res ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section H22.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variables (q node SELA sel : Z) (mA : mem).

  Hypothesis LO : ae_lo E + 176 <= q.
  Hypothesis GLO : SEGTOP_A <= ae_lo E.
  Hypothesis QH : q <= ae_hi E.
  Hypothesis HI47 : ae_hi E < 2^47.
  Hypothesis Q16 : q mod 16 = 0.
  Hypothesis N0 : 0 < node.
  Hypothesis NQ : node + 16 <= q - 176.
  Hypothesis N8 : node mod 8 = 0.
  Hypothesis SEL : 0 <= sel < 8.
  Hypothesis QS : q <= SELA.
  Hypothesis SH : SELA + 8 < 2^47.
  Hypothesis S84 : SELA mod 8 = 4.
  Hypothesis SHBM : forall m', munch (h22_W q) mA m' -> wmono bsegs mA m' -> shb_cells m'.
  Hypothesis SZS : forall m', munch (h22_W q) mA m' -> wmono bsegs mA m' -> shz m' (SELA - 4) 8.
  Hypothesis SZN : forall m', munch (h22_W q) mA m' -> wmono bsegs mA m' -> shz m' node 16.
  Hypothesis AIM : forall m', munch (h22_W q) mA m' -> AINV_A E m'.
  Hypothesis SZD : forall m', munch (h22_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_DOC E) 16.
  Hypothesis SZT : forall m', munch (h22_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_TAPE E) (8 * ae_n E).

  Definition h22_post (j0 : list byte) (res : list cell) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : machine_state -> Prop :=
    fun ms => exists (m0 : mem) (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      munch (h22_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ frm0 fc' /\
      ( (stk bsegs m0 (ae_lo E) q /\
           ms = MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m0 (seg_rom bsegs))
     \/ (exists (pcs : Z) (res' : list cell) (xra xs0 xs1 xs3 xs4 : word) (cv : Z),
           In pcs (el_site_pcsB 22) /\ pcs <> EL_SITE_CSTR_B /\ stk bsegs m0 (ae_lo E) (q + -80) /\
           rw_cells bsegs m0 (q + -80) (cast_frameB j0 res' s4 s3 s2 s1 s0 ra) /\ cells_size res' = 24%nat /\
           (pcs = EL_SITE_SV_B -> exists b16 g20, res' = [CB 16 b16; C4 (wz cv); CB 4 g20] /\ 0 < cv < 64) /\
           ms = MS (mkR xra (wz (q + -80)) gp (wz TPV_A) t0' t1' t2' xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7' (wz SHB) xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (wz pcs) fc' None m0 (seg_rom bsegs))
     \/ (stk bsegs m0 (ae_lo E) (q + -48) /\
           rw_cells bsegs m0 (q + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
           ms = MS (mkR (wz 0xb8290) (wz (q + -48)) gp (wz TPV_A) t0' t1' t2' (wz node) (wz (node + 8)) a0' a1' a2' a3' a4' a5' a6' a7'
                        (wz SHB) (wz (shad node)) (wz (shad (node + 8))) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (wz EL_SITE_CSTR_B) fc' None m0 (seg_rom bsegs)) ).

  Local Ltac ok_facts :=
    pose proof OK as OK'; destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SNS & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]];
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia);
    pose proof (ael_root_elem E OK) as [EL NR];
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia);
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR;
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia);
    unfold SEGTOP_A, USTACK_TOP, EL_H22_A, EL_H22RET_B, EL_CSTR_B, SHB, h22_W in *;
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.

  Lemma h22_pre : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    munch (h22_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) q -> rw_cells bsegs m SELA [C4 (wz sel)] -> mem_inv bsegs m ->
    evt bsegs (fun ms => exists (m0 : mem) (j0 j8 : list byte) (a0' a1' a2' : word),
        munch (h22_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ stk bsegs m0 (ae_lo E) (q + -80) /\
        rw_cells bsegs m0 (q + -80) (cast_frameB j0 [CB 24 j8] s4 s3 s2 s1 s0 ra) /\
        ms = MS (mkR ra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 a0' a1' a2' a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz (cjt sel + EL_CJTAB_B)) fc None m0 (seg_rom bsegs))
      (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz SELA) (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H22_A) fc None m (seg_rom bsegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH QS S84 SEL SH SHBM SZD SZN SZS SZT GLO.
    intros until m. intros MU WM ST XSEL MI. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

    zstep. carve_frame 80%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 24; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 6 lstep.

    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step.

    shz_pose SZS (SELA - 4). zstep. rewrite ?shr3_div.
    replace (SELA / 8) with ((SELA - 4) / 8) by (clear - S84 QS GLO LO; Z.div_mod_to_equations; lia). zstep. zstep. shz_norm. step. step. if_false.
    zstep. rewrite (a_sx32_small sel) by lia.
    zstep. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.

    zstep. step. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (cjt_read mx sel (wa (Z.shiftl sel 2 + EL_CJTAB_B)) ltac:(assumption) SEL ltac:(unfold wa, EL_CJTAB_B; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ end.
    unfold EL_CJTAB_B in RJ. pose proof (cjt_range sel SEL) as CJR.
    zstep. zstep. rewrite (a_swrap32_small (cjt sel)) by lia.
    zstep. pose proof (cjt_mod4 sel SEL) as CJ4. rewrite (ret_pc_even (cjt sel + 145540)) by (clear - CJ4 CJR; Z.div_mod_to_equations; lia).
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?ja :: CB 24 ?jb :: _) => exists ja, jb end.
    do 3 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|].
    unfold EL_CJTAB_B. atp_st_eq_goal.
  Qed.

  Local Ltac rebase m1 m2 MU2 WM2 SUB :=
    repeat match goal with
    | H : rw_cells bsegs m1 ?a ?cs |- _ =>
        let H2 := fresh H in
        assert (H2 : rw_cells bsegs m2 a cs)
          by (eapply (rw_cells_agree bsegs m1 m2); [exact H| apply (agree_of_munch _ _ _ _ MU2); intros ?x ?Hx; cbn [cells_size csize Nat.add app] in Hx; cbn [outside]; lia| exact WM2]);
        clear H; rename H2 into H
    end;
    lazymatch goal with
    | MU : munch ?W mA m1, WM : wmono bsegs mA m1 |- _ =>
        let MU' := fresh "MU" in let WM' := fresh "WM" in
        assert (MU' : munch W mA m2) by exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU2));
        assert (WM' : wmono bsegs mA m2) by exact (wmono_trans _ _ _ _ WM WM2);
        clear MU WM MU2 WM2; rename MU' into MU; rename WM' into WM
    end.

  Local Ltac tape_facts m RDT RDTY :=
    let AI2 := fresh "AI" in let TB := fresh "TAPEB" in
    assert (AI2 : AINV_A E m) by (apply AIM; assumption);
    pose proof AI2 as (TB & _ & _ & _ & _);
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia)) as RDT; rewrite Z.mul_1_r in RDT;
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TB ltac:(lia) ltac:(assumption)) as RDTY; rewrite Z.mul_1_r in RDTY;
    clear TB AI2.

  Lemma h22_ret : forall (gp t0 t1 t2 xra xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte) (res : list cell),
    munch (h22_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (cast_frameB j0 res s4 s3 s2 s1 s0 ra) -> cells_size res = 24%nat ->
    evt bsegs (h22_post j0 res ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR xra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H22RET_B) fc None m (seg_rom bsegs)).
  Proof using HI47 LO OK Q16 QH GLO.
    clear SEL S84 QS SH N0 NQ N8 SHBM SZS SZN AIM SZD SZT.
    intros until res. intros MU WM ST MI FRM FR SZ. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    unfold cast_frameB in FR.
    apply (proj1 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ res) _)) in FR. destruct FR as [FR1 FR2].
    rewrite cells_size_app, SZ in FR2. cbn [cells_size csize Nat.add] in FR2. replace (q + -80 + Z.of_nat 32) with (q + -48) in FR2 by lia.

    step. step. step. step. step. step. zstep.
    assert (FR' : rw_cells bsegs m (q + -80) (([CB 8 j0] ++ res) ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply (proj2 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ res) _)). split; [exact FR1|].
      rewrite cells_size_app, SZ. cbn [cells_size csize Nat.add]. replace (q + -80 + Z.of_nat 32) with (q + -48) by lia. exact FR2. }
    pose proof (stk_release bsegs m (ae_lo E) _ _ ST FR' ltac:(lia)) as STq. rewrite !cells_size_app, SZ in STq. cbn [cells_size csize Nat.add] in STq.
    replace (q + -80 + Z.of_nat 80) with q in STq by lia.
    step.
    apply evt_done. exists m. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. left.
    split; [exact STq|]. replace (q + -80 + 80) with q by lia. atp_st_eq_goal.
  Qed.

  Lemma h22_c0 : forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 j8 : list byte),
    munch (h22_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
    rw_cells bsegs m (q + -80) (cast_frameB j0 [CB 24 j8] s4 s3 s2 s1 s0 ra) ->
    evt bsegs (h22_post j0 [CB 24 j8] ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR ra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb4d14) fc None m (seg_rom bsegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS.
    intros until j8. intros MU WM ST MI FRM NODE FR. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (SUB : sub_fp [(q + -80 + -16, q + -80)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].

    astep. replace (node mod 8) with 0 by lia. step. if_lia. step. if_lia.
    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_false.
    step. zstep.
    name_mem m1.
    eapply (tix_cps E OK _ m1 F fc (q + -80) 1 0xb4d5c);
      [exact (AIM m1 MU)| lia| exact (SHBM m1 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2. rebase m1 m2 MU2 WM2 SUB. clear MI.
    tape_facts m2 RDT2 RDTY2. replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. astep. step. if_cases K1.
    { change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A).
      apply (h22_ret gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 F fc m2 j0 [CB 24 j8] MU WM ST2 MI2 FRM FR eq_refl). }

    shz_pose SZN node. step. shz_norm. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    shz_pose SZN (node + 8). step. shz_norm. step. if_false.
    step. zstep.
    clear RDT2 RDTY2.
    eapply (tix_cps E OK _ m2 F fc (q + -80) 1 0xb4da4);
      [exact (AIM m2 MU)| lia| exact (SHBM m2 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m3 ya1 ya3 ya4 MU3 WM3 MI3 ST3. rebase m2 m3 MU3 WM3 SUB. clear MI2 ST2.
    tape_facts m3 RDT3 RDTY3. replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. astep. step. if_cases K2.
    { change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A).
      apply (h22_ret gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 F fc m3 j0 [CB 24 j8] MU WM ST3 MI3 FRM FR eq_refl). }
    apply evt_done. exists m3. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM|]. right; left.
    exists 0xb4dc4, [CB 24 j8]. do 5 eexists. exists 0.
    split; [cbn; left; reflexivity|]. split; [unfold EL_SITE_CSTR_B; lia|]. split; [exact ST3|]. split; [exact FR|]. split; [reflexivity|].
    split; [intros X; exfalso; unfold EL_SITE_SV_B in X; lia|]. unfold shad. atp_st_eq_goal.
  Qed.

  Definition h22_case (pc : Z) : Prop := forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 j8 : list byte),
    munch (h22_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
    rw_cells bsegs m (q + -80) (cast_frameB j0 [CB 24 j8] s4 s3 s2 s1 s0 ra) ->
    evt bsegs (h22_post j0 [CB 24 j8] ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR ra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom bsegs)).

  Local Ltac case67 RA :=
    clear SEL S84 QS SH SZS; unfold h22_case;
    intros until j8; intros MU WM ST MI FRM NODE FR; ok_facts;
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia);
    assert (SUB : sub_fp [(q + -80 + -16, q + -80)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia);
    pose proof (SHBM _ MU WM) as [G1 G2];

    astep; replace (node mod 8) with 0 by lia; step; if_lia; step; if_lia;
    chk0 SZN node; step; if_false;
    step; step; if_lia; astep; replace (ae_DOC E mod 8) with 0 by lia; step; if_lia;
    astep; chk0 SZN (node + 8); step; if_false;
    step; zstep;
    let m1 := fresh "m1" in let m2 := fresh "m2" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let MI2 := fresh "MI2" in let ST2 := fresh "ST2" in
    name_mem m1;
    eapply (tix_cps E OK _ m1 _ _ (q + -80) 1 RA);
      [apply AIM; assumption| lia| apply SHBM; assumption
      | intros m' MU' WM'; apply (SZD m'); [eapply munch_trans; [eassumption| exact (munch_weaken _ _ _ _ SUB MU')]| eapply wmono_trans; [eassumption| exact WM']]
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|];
    intros m2 ?xa1 ?xa3 ?xa4 MU2 WM2 MI2 ST2; rebase m1 m2 MU2 WM2 SUB;
    let RDT2 := fresh "RDT" in let RDTY2 := fresh "RDTY" in
    tape_facts m2 RDT2 RDTY2; replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia;

    chk0 SZT (ae_TAPE E + 8); step; if_false;
    step; step.
  Local Ltac fin_ret mx STx MIx FR :=
    change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A);
    lazymatch goal with |- evt _ (h22_post ?j0 _ ?ra ?gp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11) (MS _ ?F _ ?fc _ _ _) =>
      apply (h22_ret gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 F fc mx j0 _);
        [ lazymatch goal with H : munch _ mA mx |- _ => exact H end
        | lazymatch goal with H : wmono bsegs mA mx |- _ => exact H end
        | exact STx| exact MIx
        | lazymatch goal with H : frm0 fc |- _ => exact H end
        | exact FR| reflexivity] end.
  Local Ltac fin_site mx STx MIx FR pcs :=
    apply evt_done; exists mx; do 17 eexists;
    split; [lazymatch goal with H : munch _ mA mx |- _ => exact H end|];
    split; [lazymatch goal with H : wmono bsegs mA mx |- _ => exact H end|];
    split; [exact MIx|];
    split; [lazymatch goal with H : frm0 _ |- _ => exact H end|]; right; left;
    exists pcs; eexists; do 5 eexists; exists 0;
    split; [cbn; tauto|]; split; [unfold EL_SITE_CSTR_B; lia|]; split; [exact STx|]; split; [exact FR|]; split; [reflexivity|];
    split; [intros X; exfalso; unfold EL_SITE_SV_B in X; lia|]; unfold shad; change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A); atp_st_eq_goal.

  Lemma h22_c7 : h22_case 0xb4fdc.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    case67 0xb5024.
    step. if_cases K1; [fin_ret m2 ST2 MI2 FR| fin_site m2 ST2 MI2 FR 0xb5040].
  Qed.
  Lemma h22_c6 : h22_case 0xb5164.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    case67 0xb51ac.
    step. if_cases K1; [fin_site m2 ST2 MI2 FR 0xb51f8| fin_ret m2 ST2 MI2 FR].
  Qed.

  Local Ltac caseacc SPEC RA :=
    clear SEL S84 QS SH SZS; unfold h22_case;
    intros until j8; intros MU WM ST MI FRM NODE FR; ok_facts;
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia);
    assert (SUB : sub_fp [(q + -80 - 64, q + -80)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia);

    astep; replace (node mod 8) with 0 by lia; step; if_lia; step; if_lia;
    step; zstep;
    let m1 := fresh "m1" in name_mem m1;
    change (Z_to_bv 64 TPV_A) with (Z_to_bv 64 TPV);
    eapply evt_cut;
    [ eapply (SPEC E OK (wz RA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (q + -80) node);
      [exact ST| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI| exact FRM| exact NODE| lia| left; lia| lia
      | intros m' MU'; apply AIM; exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))
      | intros m' MU' WM'; apply SHBM; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
      | intros m' MU' WM'; apply SZN; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
      | intros m' MU' WM'; apply SZD; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
      | intros m' MU' WM'; apply SZT; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')] ]
    | ];
    cbv beta; let m2 := fresh "m2" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
    intros ?ms (?u0 & ?u1 & ?u2 & ?b2 & ?b3 & ?b4 & ?b5 & ?b6 & ?b7 & ?u3 & ?u4 & ?u5 & ?u6 & ?F' & ?fc' & m2 & ?c0 & ?c1 & -> & ?FRM' & MU2 & WM2 & ?MI2 & ?ST2 & ?HG);
    rebase m1 m2 MU2 WM2 SUB; clear MI FRM;
    rewrite (ret_pc_even RA) by lia; change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A).

  Lemma h22_c2 : h22_case 0xb4ec4.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    caseacc gu64_specB 0xb4ed8. unfold G_int in HG.

    step. astep. rewrite ?Z.add_0_r. step. step. if_lia.
    step. if_cases K1; [fin_ret m2 ST2 MI2 FR| fin_site m2 ST2 MI2 FR 0xb4eec].
  Qed.
  Lemma h22_c3 : h22_case 0xb4f50.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    caseacc gi64_specB 0xb4f64. unfold G_int in HG.
    step. astep. rewrite ?Z.add_0_r. step. step. if_lia.
    step. if_cases K1; [fin_ret m2 ST2 MI2 FR| fin_site m2 ST2 MI2 FR 0xb4f78].
  Qed.
  Lemma h22_c1 : h22_case 0xb50a8.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    caseacc gdbl_specB 0xb50bc. unfold G_dbl in HG.

    step. astep. rewrite ?Z.add_0_r. step. step. if_lia.
    step. if_cases K1; [fin_ret m2 ST2 MI2 FR| fin_site m2 ST2 MI2 FR 0xb50d0].
  Qed.

  Lemma h22_c5 : h22_case 0xb5134.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO.
    clear SEL S84 QS SH SZS. unfold h22_case.
    intros until j8. intros MU WM ST MI FRM NODE FR. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (EQq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    assert (SUB : sub_fp [(q + -48 + -16, q + -48)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia).
    unfold cast_frameB in FR. cbn [app] in FR.

    astep. replace (node mod 8) with 0 by lia. step. if_lia. step. if_lia.
    step. step. step. step. step. step. step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (STq : stk bsegs mx (ae_lo E) q)
        by (pose proof (stk_release bsegs mx (ae_lo E) _ _ ST FR ltac:(lia)) as X; cbn [cells_size csize Nat.add] in X; replace (q + -80 + Z.of_nat 80) with q in X by lia; exact X) end.
    clear FR ST. zstep. replace (q + -80 + 80) with q by lia.

    zstep. carve_frame 48%nat STq.
    apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 6 lstep.
    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step. step.

    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_false.
    step. zstep.
    name_mem m1.
    eapply (tix_cps E OK _ m1 _ _ (q + -48) 1 0xb8290);
      [exact (AIM m1 MU)| lia| exact (SHBM m1 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2. rebase m1 m2 MU2 WM2 SUB. clear MI.
    tape_facts m2 RDT2 RDTY2. replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. step. if_cases K1.
    {
      apply evt_done. exists m2. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact FRM|]. right; right.
      split; [exact ST2|]. split; [exact FR|]. unfold shad. change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A). atp_st_eq_goal. }

    shz_pose SZN node. step. shz_norm. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    shz_pose SZN (node + 8). step. shz_norm. step. if_false.
    step. zstep.
    clear RDT2 RDTY2.
    eapply (tix_cps E OK _ m2 _ _ (q + -48) 1 0xb82d4);
      [exact (AIM m2 MU)| lia| exact (SHBM m2 MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|].
    intros m3 ya1 ya3 ya4 MU3 WM3 MI3 ST3. rebase m2 m3 MU3 WM3 SUB. clear MI2 ST2.
    tape_facts m3 RDT3 RDTY3. replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.
    pose proof (AIM m3 MU) as (_ & _ & _ & DOCC3 & _).

    shz_pose SZN node. step. shz_norm. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    chk0 SZT (ae_TAPE E + 8). step. if_false.
    astep. chk0 SZD (ae_DOC E + 8). step. if_false.
    step. step. if_dead1 by SS.

    step. astep. astep. pose proof (land_le_r (ae_T E 1) 72057594037927935 ltac:(lia)) as TV.
    astep. astep. step. if_dead1 by SS TV. step. if_dead1 by SS TV SL LOW HL HT.

    step. step. step. step. step. step. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (STr : stk bsegs mx (ae_lo E) q)
        by (pose proof (stk_release bsegs mx (ae_lo E) _ _ ST3 FR ltac:(lia)) as X; cbn [cells_size csize Nat.add] in X; replace (q + -48 + Z.of_nat 48) with q in X by lia; exact X) end.
    step.
    apply evt_done. exists m3. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM|]. left.
    split; [exact STr|]. replace (q + -48 + 48) with q by lia. change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A). atp_st_eq_goal.
  Qed.

  Lemma h22_c4a : forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    evt bsegs (fun ms => exists a0', ms = MS (mkR (wz 0xb4e44) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 (wz (q + -72)) (wz node) a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                            F (wz ATP_GETSTR_A) fc None m (seg_rom bsegs) /\ a0' = a0)
      (MS (mkR ra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb4e2c) fc None m (seg_rom bsegs)).
  Proof using HI47 LO N0 N8 NQ OK Q16 QH GLO.
    clear SEL S84 QS SH SZS SHBM SZN AIM SZD SZT. intros. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).

    astep. replace (node mod 8) with 0 by lia. step. if_lia. step. if_lia.
    astep. step. zstep.
    apply evt_done. exists a0. split; [| reflexivity]. replace (q + -80 + 8) with (q + -72) by lia. unfold ATP_GETSTR_A. atp_st_eq_goal.
  Qed.

  Lemma h22_c4b : forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs0 xs1 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 b16 g20 : list byte) (code : Z),
    munch (h22_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (cast_frameB j0 [CB 16 b16; C4 (wz code); CB 4 g20] s4 s3 s2 s1 s0 ra) -> (code = 0 \/ code = 17) ->
    evt bsegs (h22_post j0 [CB 16 b16; C4 (wz code); CB 4 g20] ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR (wz 0xb4e44) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb4e44) fc None m (seg_rom bsegs)).
  Proof using HI47 LO OK Q16 QH GLO.
    clear SEL S84 QS SH SZS SHBM SZN AIM SZD SZT N0 NQ N8. intros until code. intros MU WM ST MI FRM FR HC. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    unfold cast_frameB in FR. cbn [app] in FR.

    step. rewrite (a_sx32_small code) by lia. step. step. if_lia.
    step. if_cases K1.
    { fin_ret m ST MI FR. }
    zify_cond K1. rewrite ?unsigned_lit in K1 by lia.
    apply evt_done. exists m. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. right; left.
    exists EL_SITE_SV_B, [CB 16 b16; C4 (wz code); CB 4 g20]. do 5 eexists. exists code.
    split; [cbn; tauto|]. split; [unfold EL_SITE_CSTR_B, EL_SITE_SV_B; lia|]. split; [exact ST|]. split; [exact FR|]. split; [reflexivity|].
    split; [intros _; exists b16, g20; split; [reflexivity| lia]|]. unfold EL_SITE_SV_B. atp_st_eq_goal.
  Qed.
End H22.

Section Arm22.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH, GSTR_STACK_A in *; lia.

Lemma wf_len1 : forall (m : mem) A (ja : list byte) (na : nat) (rest : list cell),
  rw_cells bsegs m A (CB na ja :: rest) -> length ja = na.
Proof. intros m A ja na rest [[WF _] _]. cbn [cells_wf cell_wf] in WF. tauto. Qed.
Lemma wf_len2 : forall (m : mem) A (ja : list byte) (na : nat) c2 (jb : list byte) (nb : nat) (rest : list cell),
  rw_cells bsegs m A (CB na ja :: c2 :: CB nb jb :: rest) -> length ja = na /\ length jb = nb.
Proof. intros m A ja na c2 jb nb rest [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct c2; cbn [cell_wf] in WF; tauto. Qed.

Theorem arm22_okA : forall W, (forall pcs, throw_siteB RT PMc W 22 pcs) -> arm_cpsA RT PMc W 22.
Proof using AF RC.
  intros W SITE Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED176 : lf_lo X + 16 <= lf_S1 X - 176) by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 22 sel idx jr jos t m 176 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED176) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof (arm_ctx_below RT AF X E Σ 22 sel idx jr jos t m) as CTX.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof AL as (ALT & ALS & ALP & ALF & WLO). rewrite ELO in WLO.
  change (el_arm_pcA 22) with 0xb23f4. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO176 : f + 1024 <= sp' - 176) by (clear - FLO NEED176; lia).
  assert (COSTP : 0 <= arm_costA 22 (ae_n E) (ae_sn E) (zlength (ae_p1 E)))
    by (unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; pose proof (mcost_nonneg EXC_SIZE ltac:(unfold EXC_SIZE; lia)); lia).
  pose proof (ael_root_elem E OKE) as [ELR NR].

  assert (SZSk : forall mx, ART RT Σ mx -> shz mx (sp' + 100 - 4) 8).
  { intros mx ARTx. apply (shz_stack RT AF Σ mx (sp' + 100 - 4) 8 ARTx); [clear - WLO NEED176; ul| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  assert (TAIL : forall (mB : mem) (j0 : list byte) (res : list cell) (ms : machine_state),
    (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> mB x = m x) ->
    (forall m', munch (h22_W sp') mB m' -> wmono bsegs mB m' -> ART RT Σ m') ->
    arm_memA (mkLF usp sp' f lo) E 22 sel idx jr jos t mB -> el_xdataA mB -> el_auxvA usp mB ->
    h22_post E sp' (f + 208) mB j0 res (wz 0xb2400) gp (wz usp) (wz sp') (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) ms ->
    evt bsegs (fun ms' => aevt RT PMc Σ K ms') ms).
  { intros mB j0 res ms AGB ARTMB AMB XDB AUXB (m0 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u0 & u1 & u2 & u3 & u4 & u5 & u6 & F' & fc' & MU0 & WM0 & MI0 & FRM0 & CASES).
    destruct (arm_ctx_below RT AF (mkLF usp sp' f lo) E Σ 22 sel idx jr jos t mB m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS
                (ARTMB mB (munch_refl _ mB) (wmono_refl bsegs mB)) AMB ltac:(lia) NEED176 XDB AUXB MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    assert (PRES0 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m0 x = m x).
    { intros x Hx. rewrite (MU0 x); [exact (AGB x Hx)|]. cbn [outside]. split; [exact (NBELOW _ Hx)| exact I]. }
    destruct CASES as [(ST0 & ->)|[(pcs & res' & xra & xs0 & xs1 & xs3 & xs4 & cv & HIN & NCS & ST0 & FR0 & SZ0 & SV & ->)|(ST0 & FR0 & ->)]].
    -
      rewrite (ret_pc_even 0xb2400) by lia. rewrite ELO in ST0. zstep. apply evt_done.
      apply (POST false (rt_credit RT Σ) Σ m0 fc' F').
      exact (arm_post_agree RT AF W 22 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m0 fc' LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART0 AM XD AUX
               PRES0 MI0 ST0 FRM0 COSTP).
    -
      rewrite ELO in ST0.
      assert (NEND : pcs <> EL_SITE_END_B)
        by (clear - HIN; cbn [el_site_pcsB Z.eqb Pos.eqb] in HIN; unfold EL_SITE_END_B, EL_SITE_CSTR_B in *; destruct HIN as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; lia).
      assert (N53 : pcs <> 0xb5420)
        by (clear - HIN; cbn [el_site_pcsB Z.eqb Pos.eqb] in HIN; unfold EL_SITE_END_B, EL_SITE_CSTR_B in *; destruct HIN as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; lia).
      assert (TE : (pcs =? EL_SITE_END_B) = false) by (apply Z.eqb_neq; exact NEND).
      assert (T53 : (pcs =? 0xb5420) = false) by (apply Z.eqb_neq; exact N53).
      assert (TC : (pcs =? EL_SITE_CSTR_B) = false) by (apply Z.eqb_neq; exact NCS).
      assert (P80 : site_fszB pcs = 80) by (unfold site_fszB; rewrite TE, TC, T53; reflexivity).
      pose proof (wf_len1 _ _ _ _ _ FR0) as LJ0.
      assert (SFR : exists j, length j = site_jlenB pcs /\ site_cvB pcs cv /\
                rw_cells bsegs m0 (sp' - site_fszB pcs) (site_frameB pcs (mkLF usp sp' f lo) j cv)).
      { unfold cast_frameB in FR0. rewrite P80. replace (sp' - 80) with (sp' + -80) by lia.
        destruct (Z.eq_dec pcs EL_SITE_SV_B) as [EQ|NE].
        + destruct (SV EQ) as (b16 & g20 & -> & CVR). cbn [app] in FR0.
          assert (L16 : length b16 = 16%nat) by (destruct FR0 as [[WF _] _]; cbn [cells_wf cell_wf] in WF; tauto).
          assert (L4 : length g20 = 4%nat) by (destruct FR0 as [[WF _] _]; cbn [cells_wf cell_wf] in WF; tauto).
          exists (j0 ++ b16 ++ g20). rewrite EQ. split; [| split].
          * unfold site_jlenB, EL_SITE_END_B, EL_SITE_SV_B, EL_SITE_CSTR_B. cbn [Z.eqb Pos.eqb orb]. rewrite !length_app, LJ0, L16, L4. reflexivity.
          * unfold site_cvB. rewrite Z.eqb_refl. cbn [orb EL_SITE_END_B EL_SITE_SV_B Z.eqb Pos.eqb]. exact CVR.
          * rewrite (site_frame_svB_intro (mkLF usp sp' f lo) j0 b16 g20 cv LJ0 L16). cbn [lf_usp lf_S1 lf_F lf_lo lftoi_savedB app]. exact FR0.
        + assert (TS : (pcs =? EL_SITE_SV_B) = false) by (apply Z.eqb_neq; exact NE).
          pose proof (rw_cells_merge bsegs m0 (sp' + -80) [] ([CB 8 j0] ++ res') [C8 (wz (f + 32)); C8 (wz (shad f)); C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb2400)]) as M.
          cbn [app] in M. cbn [app] in FR0. specialize (M FR0). cbn [cells_size csize] in M. rewrite SZ0 in M. change (8 + 24)%nat with 32%nat in M.
          pose proof (wf_len1 _ _ _ _ _ M) as LJ.
          exists (cells_bytes (CB 8 j0 :: res')). split; [| split].
          * unfold site_jlenB. rewrite TE, TS, TC, T53. cbn [orb]. exact LJ.
          * unfold site_cvB. rewrite TE, TS. cbn [orb]. exact I.
          * unfold site_frameB. rewrite TE, T53, TC, TS. cbn [lf_usp lf_S1 lf_F lf_lo lftoi_savedB app]. exact M. }
      destruct SFR as (j & LJ & CVj & SFRj).
      apply evt_done. replace (sp' + -80) with (sp' - site_fszB pcs) by lia.
      eapply (SITE pcs Σ K {| lf_usp := usp; lf_S1 := sp'; lf_F := f; lf_lo := lo |} E sel idx jr jos t j cv
                xra gp u0 u1 u2 xs0 xs1 a0' a1' a2' a3' a4' a5' a6' a7' (wz SHB) xs3 xs4
                s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) u3 u4 u5 u6 F' fc' m0);
        cbn [lf_usp lf_S1 lf_F lf_lo];
        [exact HIN| exact FDO| exact MST| exact LK| exact OKE| exact LE| exact SEL| exact IDX| exact AL| exact FRS| exact LPA
        | clear - LVB; unfold arm_xliveA in LVB; cbn [Z.eqb Pos.eqb orb] in LVB; lia
        | clear - CRB; unfold arm_costA in CRB; cbn [Z.eqb Pos.eqb orb] in CRB; lia
        | exact ART0| exact MI0| rewrite P80; replace (sp' - 80) with (sp' + -80) by lia; exact ST0
        | clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; lia
        | exact AM0| exact FRM0| exact XD0| exact AUX0| exact SPB| exact LJ| exact CVj
        | exact SFRj| unfold site_regsB; rewrite TE; reflexivity|].
      intros c Σ' m' fc'' F'' ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s6' s7' s8' s9' s10' s11' t3'' t4'' t5'' t6'' LP.
      unfold lf_st, EL_LRET_A. cbn [lf_usp lf_S1 lf_F lf_lo].
      destruct LP as (AX & MI' & ST' & FRM' & LV' & FRS' & SP' & CR' & PRES' & MEM' & _). cbn [lf_usp lf_S1 lf_F lf_lo] in ST', PRES', MEM'.
      apply (aevt_evt RT AF PMc MST). zstep. apply evt_done.
      apply (POST true c Σ' m' fc'' F''). unfold arm_postA. cbn [lf_usp lf_S1 lf_F lf_lo].
      split; [exact AX|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|]. split; [exact LV'|]. split; [exact FRS'|]. split; [exact SP'|].
      split; [exact CR'|].
      split; [intros a Ha Ho; rewrite (PRES' a Ha Ho); exact (PRES0 a Ha)|].
      split; [exact MEM'| intros _; right; lia].
    -
      rewrite ELO in ST0.
      apply evt_done. replace (f + 208 + 8) with (f + 216) by lia. replace (sp' + -48) with (sp' - 48) by lia.
      eapply (SITE EL_SITE_CSTR_B Σ K {| lf_usp := usp; lf_S1 := sp'; lf_F := f; lf_lo := lo |} E sel idx jr jos t [] 0
                (wz 0xb8290) gp u0 u1 u2 (wz (f + 208)) (wz (f + 216)) a0' a1' a2' a3' a4' a5' a6' a7' (wz SHB) (wz (shad (f + 208))) (wz (shad (f + 216)))
                s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) u3 u4 u5 u6 F' fc' m0);
        cbn [lf_usp lf_S1 lf_F lf_lo site_fszB site_frameB site_jlenB site_cvB site_regsB lftoi_savedB el_site_pcsB EL_SITE_END_B EL_SITE_CSTR_B EL_SITE_SV_B Z.eqb Pos.eqb orb andb app];
        [right; right; right; right; right; right; right; left; reflexivity| exact FDO| exact MST| exact LK| exact OKE| exact LE| exact SEL| exact IDX| exact AL| exact FRS| exact LPA
        | clear - LVB; unfold arm_xliveA in LVB; cbn [Z.eqb Pos.eqb orb] in LVB; lia
        | clear - CRB; unfold arm_costA in CRB; cbn [Z.eqb Pos.eqb orb] in CRB; lia
        | exact ART0| exact MI0| replace (sp' - 48) with (sp' + -48) by lia; exact ST0
        | clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; lia
        | exact AM0| exact FRM0| exact XD0| exact AUX0| exact SPB| reflexivity| exact I
        | replace (sp' - 48) with (sp' + -48) by lia; exact FR0| reflexivity|].
      intros c Σ' m' fc'' F'' ra' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s6' s7' s8' s9' s10' s11' t3'' t4'' t5'' t6'' LP.
      unfold lf_st, EL_LRET_A. cbn [lf_usp lf_S1 lf_F lf_lo].
      destruct LP as (AX & MI' & ST' & FRM' & LV' & FRS' & SP' & CR' & PRES' & MEM' & _). cbn [lf_usp lf_S1 lf_F lf_lo] in ST', PRES', MEM'.
      apply (aevt_evt RT AF PMc MST). zstep. apply evt_done.
      apply (POST true c Σ' m' fc'' F''). unfold arm_postA. cbn [lf_usp lf_S1 lf_F lf_lo].
      split; [exact AX|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FRM'|]. split; [exact LV'|]. split; [exact FRS'|]. split; [exact SP'|].
      split; [exact CR'|].
      split; [intros a Ha Ho; rewrite (PRES' a Ha Ho); exact (PRES0 a Ha)|].
      split; [exact MEM'| intros _; right; lia]. }

  apply (aevt_evt RT AF PMc MST).
  astep. zstep. zstep.
  eapply evt_cut.
  { eapply (h22_pre E OKE sp' (f + 208) (sp' + 100) sel m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SEL| clear; lia| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia
      | exact SHBM| intros m' MU' WM'; exact (SZSk m' (ARTM m' MU' WM'))| exact SZN| exact AIM| exact SZD| exact SZT
      | apply munch_refl| apply wmono_refl| rewrite ELO; exact STg| exact C100| exact MIg]. }
  cbv beta. intros ms1 (m0 & j0 & j8 & a0' & a1' & a2' & MU0 & WM0 & MI0 & ST0 & FR0 & ->).
  assert (CE0 : rw_cells bsegs m0 (f + 208) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
  { eapply (rw_cells_agree bsegs m m0); [exact CE| | exact WM0]. apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold h22_W. cbn [outside].
    clear - Hx FLO176. lia. }
  assert (CASES8 : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by (clear - SEL; lia).

  destruct CASES8 as [EQS|[EQS|[EQS|[EQS|[EQS|[EQS|[EQS|EQS]]]]]]]; subst sel.
  - change (cjt 0 + EL_CJTAB_B) with 0xb4d14. eapply evt_cut;
    [ eapply (h22_c0 E OKE sp' (f + 208) m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m j0 [CB 24 j8] ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - change (cjt 1 + EL_CJTAB_B) with 0xb50a8. eapply evt_cut;
    [ eapply (h22_c1 E OKE sp' (f + 208) m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m j0 [CB 24 j8] ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - change (cjt 2 + EL_CJTAB_B) with 0xb4ec4. eapply evt_cut;
    [ eapply (h22_c2 E OKE sp' (f + 208) m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m j0 [CB 24 j8] ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - change (cjt 3 + EL_CJTAB_B) with 0xb4f50. eapply evt_cut;
    [ eapply (h22_c3 E OKE sp' (f + 208) m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m j0 [CB 24 j8] ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  -
    change (cjt 4 + EL_CJTAB_B) with 0xb4e2c.
    eapply evt_cut.
    { eapply (h22_c4a E OKE sp' (f + 208));
        [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia]. }
    cbv beta. intros ms2 (a0x & -> & _).
    destruct (CTX m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED176 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.

    unfold cast_frameB in FR0. cbn [app] in FR0.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -80) [CB 8 j0] _) FR0) as [FRa FRbc]. cbn [cells_size csize Nat.add] in FRbc.
    replace (sp' + -80 + Z.of_nat 8) with (sp' + -72) in FRbc by lia.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -72) [CB 24 j8] _) FRbc) as [FRb FRc]. cbn [cells_size csize Nat.add] in FRc.
    replace (sp' + -72 + Z.of_nat 24) with (sp' + -48) in FRc by lia.
    assert (SUB4 : sub_fp (gstr_W (sp' + -80) (sp' + -72)) (h22_W sp')) by (unfold gstr_W, h22_W; intros x Hx; cbn [outside] in *; lia).
    assert (SZE4 : forall m', munch (gstr_W (sp' + -80) (sp' + -72)) m0 m' -> wmono bsegs m0 m' -> shz m' (f + 208) 16).
    { intros m' MU' WM'. exact (SZN m' (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ SUB4 MU')) (wmono_trans _ _ _ _ WM0 WM')). }
    apply evt_done. change (Z_to_bv 64 TPV_A) with (Z_to_bv 64 TPV).
    eapply (aevt_rt RT PMc Σ K _ _
             (gstr_cps_elB RT AF E OKE RC Σ PMc (sp' + -80) (sp' + -72) (f + 208) 1 (ae_n E - 1) TAPE_MAX_DEPTH
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 j8
                FDO MST AL (AIM m0 MU0) ELR ltac:(clear; lia) CE0 ltac:(left; clear - FLO176; lia) ltac:(clear - FPOS FLO176 SPT SPR; ul)
                ltac:(clear - F64; Z.div_mod_to_equations; lia)
                FRb ltac:(clear; lia) ltac:(rewrite EHI; clear - SPR; lia) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) ltac:(left; clear - FLO176; lia)
                (ARTM m0 MU0 WM0) MI0 ST0
                ltac:(rewrite ELO; clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold EL_THROW_STACK_A, NORET_DEPTH, GSTR_STACK_A, RT_STACK in *; lia)
                ltac:(clear - SPA'; Z.div_mod_to_equations; lia) FRM SZE4));
      [exact FRM|].
    intros c Hc; eexists Σ, _; split; [exact Hc|].
    intros ms' (v & m1 & b16 & g20 & code & RS & (ART1 & MI1 & ST1) & PRES1 & RC1 & CODE) FRM1.
    destruct RS as (w0 & w1 & w2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & F1 & fc1 & ->). cbn [ms_fcsr MS] in FRM1.
    rewrite ret_pc_even by (clear; lia). change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A).

    assert (AG1 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) -> agree_on P m0 m1).
    { intros P HP x Px. pose proof (HP _ Px) as Hx. apply (PRES1 x).
      - destruct Hx as [H|H]; [left; clear - H; lia| right; exact H].
      - cbn [outside]. split; [| exact I]. pose proof (NBELOW _ Hx) as NB. clear - NB. lia. }
    destruct (arm_mem_agree RT AF (mkLF usp sp' f lo) E Σ 22 4 idx jr jos t m0 m1 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM0 XD0 AUX0 AG1)
      as (AM1 & XD1 & AUX1). cbn [lf_usp lf_S1 lf_F lf_lo] in AM1, AUX1.
    assert (AGB1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m1 x = m x).
    { intros x Hx. rewrite (AG1 (fun y => aclient (rt_live RT Σ) (rt_frames RT Σ) sp' y) (fun y Hy => Hy) x Hx).
      apply MU0. cbn [outside]. split; [exact (NBELOW _ Hx)| exact I]. }

    assert (FRa1 : rw_cells bsegs m1 (sp' + -80) [CB 8 j0]).
    { eapply rw_cells_agree_nw; [exact FRa|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (PRES1 x); [left; clear - Hx SPT SPR; ul| cbn [outside]; split; [clear - Hx; lia| exact I]]. }
    assert (FRc1 : rw_cells bsegs m1 (sp' + -48) [C8 (wz (f + 32)); C8 (wz (shad f)); C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb2400)]).
    { eapply rw_cells_agree_nw; [exact FRc|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (PRES1 x); [left; clear - Hx SPT SPR; ul| cbn [outside]; split; [clear - Hx; lia| exact I]]. }
    assert (FR1 : rw_cells bsegs m1 (sp' + -80) (cast_frameB j0 [CB 16 b16; C4 (wz code); CB 4 g20] (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb2400))).
    { unfold cast_frameB. apply (proj2 (rw_cells_app bsegs m1 (sp' + -80) [CB 8 j0] _)). split; [exact FRa1|]. cbn [cells_size csize Nat.add].
      replace (sp' + -80 + Z.of_nat 8) with (sp' + -72) by lia.
      apply (proj2 (rw_cells_app bsegs m1 (sp' + -72) [CB 16 b16; C4 (wz code); CB 4 g20] _)). split; [exact RC1|]. cbn [cells_size csize Nat.add].
      replace (sp' + -72 + Z.of_nat 24) with (sp' + -48) by lia. exact FRc1. }
    pose proof (arm_entry_kit RT AF (mkLF usp sp' f lo) E Σ 22 4 idx jr jos t m1 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM1 ltac:(lia) NEED176)
      as (ARTM1 & SZN1 & AIM1 & SZD1 & SZT1 & SHBM1). cbn [lf_usp lf_S1 lf_F lf_lo] in ARTM1, SZN1, AIM1, SZD1, SZT1, SHBM1.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { eapply (h22_c4b E OKE sp' (f + 208) m1);
        [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia
        | apply munch_refl| apply wmono_refl| exact ST1| exact MI1| exact FRM1| exact FR1| exact CODE]. }
    cbv beta. intros ms3 HP3. exact (TAIL m1 j0 [CB 16 b16; C4 (wz code); CB 4 g20] ms3 AGB1 ARTM1 AM1 XD1 AUX1 HP3).
  - change (cjt 5 + EL_CJTAB_B) with 0xb5134. eapply evt_cut;
    [ eapply (h22_c5 E OKE sp' (f + 208) m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m j0 [CB 24 j8] ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - change (cjt 6 + EL_CJTAB_B) with 0xb5164. eapply evt_cut;
    [ eapply (h22_c6 E OKE sp' (f + 208) m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m j0 [CB 24 j8] ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - change (cjt 7 + EL_CJTAB_B) with 0xb4fdc. eapply evt_cut;
    [ eapply (h22_c7 E OKE sp' (f + 208) m);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m j0 [CB 24 j8] ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
Qed.
End Arm22.
