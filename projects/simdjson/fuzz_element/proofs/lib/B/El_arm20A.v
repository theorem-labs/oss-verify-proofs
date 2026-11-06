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

Definition EL_GJTAB_B : Z := 0x23844.
Definition GJT_TAB : list Z := [593112; 593452; 593284; 593332; 593256; 593500; 593768; 593380].
Definition gjt (i : Z) : Z := nth (Z.to_nat i) GJT_TAB 0.
Definition GJT_WORDS : list word := map (Z_to_bv 64) GJT_TAB.
Lemma gjt_image : ro_bytes_b bsegs EL_GJTAB_B (u32s GJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gjt_at : forall m, mem_inv bsegs m -> bytes_at bsegs m EL_GJTAB_B (u32s GJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_GJTAB_B; lia | rewrite u32s_length; unfold EL_GJTAB_B, GJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact gjt_image.
Qed.
Lemma gjt_read : forall (m : word -> option byte) i a, mem_inv bsegs m -> 0 <= i < 8 -> a = wa (EL_GJTAB_B + 4 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 (Z_to_bv 64 (gjt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EL_GJTAB_B GJT_WORDS i); [apply gjt_at; exact MI| | lia | reflexivity].
  unfold GJT_WORDS, gjt. rewrite nth_error_map. rewrite (nth_error_nth' GJT_TAB 0); [reflexivity|].
  change (length GJT_TAB) with 8%nat. lia.
Qed.
Lemma gjt_range : forall i, 0 <= i < 8 -> 0 <= gjt i < 2 ^ 31.
Proof.
  intros i Hi. unfold gjt.
  assert (F : forallb (fun x => (0 <=? x) && (x <? 2 ^ 31)) GJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length GJT_TAB)%nat) by (change (length GJT_TAB) with 8%nat; lia).
  specialize (F _ (nth_In GJT_TAB 0 L)). apply andb_true_iff in F. destruct F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
Qed.
Lemma gjt_mod4 : forall i, 0 <= i < 8 -> gjt i mod 4 = 0.
Proof.
  intros i Hi. unfold gjt.
  assert (F : forallb (fun x => x mod 4 =? 0) GJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length GJT_TAB)%nat) by (change (length GJT_TAB) with 8%nat; lia).
  specialize (F _ (nth_In GJT_TAB 0 L)). apply Z.eqb_eq in F. exact F.
Qed.

Definition EL_H20_B : Z := 0xb44b8.
Definition EL_H20RET_B : Z := 0xb478c.
Definition EL_H20TTX_B : Z := 0xb47f0.

Definition h20_W (q : Z) : list ivl := [(q + -176, q)].

Definition h20_frameB (j0 : list byte) (res : list cell) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0] ++ res ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section H20.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variables (q node SELA sel : Z) (mA : mem) (RA : Z).

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
  Hypothesis RA0 : 0 <= RA < 2^64.
  Hypothesis RA2 : RA mod 2 = 0.
  Hypothesis SHBM : forall m', munch (h20_W q) mA m' -> wmono bsegs mA m' -> shb_cells m'.
  Hypothesis SZS : forall m', munch (h20_W q) mA m' -> wmono bsegs mA m' -> shz m' (SELA - 4) 8.
  Hypothesis SZN : forall m', munch (h20_W q) mA m' -> wmono bsegs mA m' -> shz m' node 16.
  Hypothesis AIM : forall m', munch (h20_W q) mA m' -> AINV_A E m'.
  Hypothesis SZD : forall m', munch (h20_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_DOC E) 16.
  Hypothesis SZT : forall m', munch (h20_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_TAPE E) (8 * ae_n E).

  Definition h20_post (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : machine_state -> Prop :=
    fun ms => exists (m0 : mem) (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      munch (h20_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ frm0 fc' /\ stk bsegs m0 (ae_lo E) q /\
      ms = MS (mkR (wz RA) (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (wz RA) fc' None m0 (seg_rom bsegs).

  Local Ltac ok_facts :=
    pose proof OK as OK'; destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SNS & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]];
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia);
    pose proof (ael_root_elem E OK) as [EL NR];
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia);
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR;
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia);
    unfold SEGTOP_A, USTACK_TOP, EL_H20_B, EL_H20RET_B, EL_H20TTX_B, SHB, h20_W in *;
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.

  Lemma h20_pre : forall (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    munch (h20_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) q -> rw_cells bsegs m SELA [C4 (wz sel)] -> mem_inv bsegs m ->
    evt bsegs (fun ms => exists (m0 : mem) (j0 j8 : list byte) (a0' a1' a2' : word),
        munch (h20_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ stk bsegs m0 (ae_lo E) (q + -80) /\
        rw_cells bsegs m0 (q + -80) (h20_frameB j0 [CB 24 j8] s4 s3 s2 s1 s0 (wz RA)) /\
        ms = MS (mkR (wz RA) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 a0' a1' a2' a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz (gjt sel + EL_GJTAB_B)) fc None m0 (seg_rom bsegs))
      (MS (mkR (wz RA) (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz SELA) (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H20_B) fc None m (seg_rom bsegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH QS S84 SEL SH SHBM SZD SZN SZS SZT GLO RA0 RA2.
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
      pose proof (gjt_read mx sel (wa (Z.shiftl sel 2 + EL_GJTAB_B)) ltac:(assumption) SEL ltac:(unfold wa, EL_GJTAB_B; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ end.
    unfold EL_GJTAB_B in RJ. pose proof (gjt_range sel SEL) as CJR.
    zstep. zstep. rewrite (a_swrap32_small (gjt sel)) by lia.
    zstep. pose proof (gjt_mod4 sel SEL) as CJ4. rewrite (ret_pc_even (gjt sel + 145476)) by (clear - CJ4 CJR; Z.div_mod_to_equations; lia).
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?ja :: CB 24 ?jb :: _) => exists ja, jb end.
    do 3 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|].
    unfold EL_GJTAB_B. atp_st_eq_goal.
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

  Lemma h20_ret : forall (gp t0 t1 t2 xra xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte) (res : list cell),
    munch (h20_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (h20_frameB j0 res s4 s3 s2 s1 s0 (wz RA)) -> cells_size res = 24%nat ->
    evt bsegs (h20_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR xra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H20RET_B) fc None m (seg_rom bsegs)).
  Proof using HI47 LO OK Q16 QH GLO RA0 RA2.
    clear SEL S84 QS SH N0 NQ N8 SHBM SZS SZN AIM SZD SZT.
    intros until res. intros MU WM ST MI FRM FR SZ. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    unfold h20_frameB in FR.
    apply (proj1 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ res) _)) in FR. destruct FR as [FR1 FR2].
    rewrite cells_size_app, SZ in FR2. cbn [cells_size csize Nat.add] in FR2. replace (q + -80 + Z.of_nat 32) with (q + -48) in FR2 by lia.

    step. step. step. step. step. step. zstep.
    assert (FR' : rw_cells bsegs m (q + -80) (([CB 8 j0] ++ res) ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (wz RA)])).
    { apply (proj2 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ res) _)). split; [exact FR1|].
      rewrite cells_size_app, SZ. cbn [cells_size csize Nat.add]. replace (q + -80 + Z.of_nat 32) with (q + -48) by lia. exact FR2. }
    pose proof (stk_release bsegs m (ae_lo E) _ _ ST FR' ltac:(lia)) as STq. rewrite !cells_size_app, SZ in STq. cbn [cells_size csize Nat.add] in STq.
    replace (q + -80 + Z.of_nat 80) with q in STq by lia.
    step. rewrite (ret_pc_even RA) by lia.
    apply evt_done. exists m. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact STq|].
    replace (q + -80 + 80) with q by lia. atp_st_eq_goal.
  Qed.

  Lemma h20_ttx : forall (gp t0 t1 t2 xra xs0 xs1 a2 a3 a4 a5 a6 a7 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte) (res : list cell),
    munch (h20_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (h20_frameB j0 res s4 s3 s2 s1 s0 (wz RA)) -> cells_size res = 24%nat ->
    evt bsegs (h20_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR xra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 (wz (ae_DOC E)) (wz 1) a2 a3 a4 a5 a6 a7 (wz SHB) xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H20TTX_B) fc None m (seg_rom bsegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    clear SEL S84 QS SH SZS.
    intros until res. intros MU WM ST MI FRM FR SZ. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (SUB : sub_fp [(q + -16, q)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia).
    unfold h20_frameB in FR.
    apply (proj1 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ res) _)) in FR. destruct FR as [FR1 FR2].
    rewrite cells_size_app, SZ in FR2. cbn [cells_size csize Nat.add] in FR2. replace (q + -80 + Z.of_nat 32) with (q + -48) in FR2 by lia.

    step. step. step. step. step. step. zstep.
    assert (FR' : rw_cells bsegs m (q + -80) (([CB 8 j0] ++ res) ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (wz RA)])).
    { apply (proj2 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ res) _)). split; [exact FR1|].
      rewrite cells_size_app, SZ. cbn [cells_size csize Nat.add]. replace (q + -80 + Z.of_nat 32) with (q + -48) by lia. exact FR2. }
    pose proof (stk_release bsegs m (ae_lo E) _ _ ST FR' ltac:(lia)) as STq. rewrite !cells_size_app, SZ in STq. cbn [cells_size csize Nat.add] in STq.
    replace (q + -80 + Z.of_nat 80) with q in STq by lia. clear FR' FR1 FR2 ST.
    zstep. replace (q + -80 + 80) with q by lia.
    change (Z_to_bv 64 TPV_A) with (Z_to_bv 64 TPV).
    eapply (tix_cps E OK _ m F fc q 1 RA);
      [exact (AIM m MU)| lia| exact (SHBM m MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | exact STq| lia| lia| exact Q16| exact MI| exact RA0| exact RA2|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2. rebase m m2 MU2 WM2 SUB.
    apply evt_done. exists m2. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
    change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A). atp_st_eq_goal.
  Qed.

  Definition h20_case (pc : Z) : Prop := forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 j8 : list byte),
    munch (h20_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
    rw_cells bsegs m (q + -80) (h20_frameB j0 [CB 24 j8] s4 s3 s2 s1 s0 (wz RA)) ->
    evt bsegs (h20_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR (wz RA) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom bsegs)).

  Local Ltac fin_ret :=
    change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A);
    lazymatch goal with |- evt _ (h20_post ?gp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11) (MS _ ?F _ ?fc _ ?mx _) =>
      lazymatch goal with FR : rw_cells bsegs mx (q + -80) (h20_frameB ?j0 ?res _ _ _ _ _ _) |- _ =>
      apply (h20_ret gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 s3 s4 F fc mx j0 res);
        [ lazymatch goal with H : munch _ mA mx |- _ => exact H end
        | lazymatch goal with H : wmono bsegs mA mx |- _ => exact H end
        | lazymatch goal with H : stk bsegs mx _ _ |- _ => exact H end
        | lazymatch goal with H : mem_inv bsegs mx |- _ => exact H end
        | lazymatch goal with H : frm0 fc |- _ => exact H end
        | exact FR| reflexivity] end end.
  Local Ltac fin_ttx :=
    change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A);
    lazymatch goal with |- evt _ (h20_post ?gp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11) (MS _ ?F _ ?fc _ ?mx _) =>
      lazymatch goal with FR : rw_cells bsegs mx (q + -80) (h20_frameB ?j0 ?res _ _ _ _ _ _) |- _ =>
      apply (h20_ttx gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 s3 s4 F fc mx j0 res);
        [ lazymatch goal with H : munch _ mA mx |- _ => exact H end
        | lazymatch goal with H : wmono bsegs mA mx |- _ => exact H end
        | lazymatch goal with H : stk bsegs mx _ _ |- _ => exact H end
        | lazymatch goal with H : mem_inv bsegs mx |- _ => exact H end
        | lazymatch goal with H : frm0 fc |- _ => exact H end
        | exact FR| reflexivity] end end.

  Local Ltac case_open :=
    clear SEL S84 QS SH SZS; unfold h20_case;
    intros until j8; intros MU WM ST MI FRM NODE FR; ok_facts;
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia);
    astep; replace (node mod 8) with 0 by lia; step; if_lia; step; if_lia.

  Local Ltac call_tix RET :=
    let SUB := fresh "SUB" in
    assert (SUB : sub_fp [(q + -80 + -16, q + -80)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia);
    let m1 := fresh "m1" in name_mem m1;
    eapply (tix_cps E OK _ m1 _ _ (q + -80) 1 RET);
      [apply AIM; assumption| lia| apply SHBM; assumption
      | intros m' MU' WM'; apply (SZD m'); [eapply munch_trans; [eassumption| exact (munch_weaken _ _ _ _ SUB MU')]| eapply wmono_trans; [eassumption| exact WM']]
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|];
    let m2 := fresh "m2" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let MI2 := fresh "MI2" in let ST2 := fresh "ST2" in
    intros m2 ?xa1 ?xa3 ?xa4 MU2 WM2 MI2 ST2; rebase m1 m2 MU2 WM2 SUB; clear SUB;
    repeat match goal with H : mem_inv bsegs m1 |- _ => clear H | H : stk bsegs m1 _ _ |- _ => clear H end;
    let RDT2 := fresh "RDT" in let RDTY2 := fresh "RDTY" in
    tape_facts m2 RDT2 RDTY2; replace (ae_TAPE E + 8 * 1) with (ae_TAPE E + 8) by lia.

  Lemma h20_c0 : h20_case 0xb451c.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open. pose proof (SHBM _ MU WM) as [G1 G2].

    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_false.
    step. zstep.
    call_tix 0xb4564.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. astep. step. if_cases K1.
    { fin_ret. }

    shz_pose SZN node. step. shz_norm. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    shz_pose SZN (node + 8). step. shz_norm. step. if_false.
    step. zstep. fin_ttx.
  Qed.

  Lemma h20_c6 : h20_case 0xb47ac.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open. pose proof (SHBM _ MU WM) as [G1 G2].

    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_false.
    step. fin_ttx.
  Qed.
  Lemma h20_c7 : h20_case 0xb4628.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open. pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_true.
    step. fin_ttx.
  Qed.

  Local Ltac case_tacc SPEC :=
    clear SEL S84 QS SH SZS; unfold h20_case;
    intros until j8; intros MU WM ST MI FRM NODE FR; ok_facts;
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia);
    assert (SUB : sub_fp [(q - 64, q)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia);

    astep; replace (node mod 8) with 0 by lia; step; if_lia; step; if_lia; step;
    lazymatch type of FR with rw_cells bsegs ?mx (q + -80) (h20_frameB ?j0 ?res ?s4 ?s3 ?s2 ?s1 ?s0 ?ra) =>
      unfold h20_frameB in FR;
      apply (proj1 (rw_cells_app bsegs mx (q + -80) ([CB 8 j0] ++ res) _)) in FR;
      let FR1 := fresh "FR1" in let FR2 := fresh "FR2" in destruct FR as [FR1 FR2];
      cbn [cells_size csize Nat.add app] in FR2; replace (q + -80 + Z.of_nat 32) with (q + -48) in FR2 by lia;

      step; step; step; step; step; step; zstep;
      let FR' := fresh "FR'" in
      assert (FR' : rw_cells bsegs mx (q + -80) (([CB 8 j0] ++ res) ++ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
        by (apply (proj2 (rw_cells_app bsegs mx (q + -80) ([CB 8 j0] ++ res) _)); split; [exact FR1|]; cbn [cells_size csize Nat.add app];
            replace (q + -80 + Z.of_nat 32) with (q + -48) by lia; exact FR2);
      let STq := fresh "STq" in
      pose proof (stk_release bsegs mx (ae_lo E) _ _ ST FR' ltac:(lia)) as STq; cbn [cells_size csize Nat.add app] in STq;
      replace (q + -80 + Z.of_nat 80) with q in STq by lia; clear FR' FR1 FR2 ST;
      zstep; replace (q + -80 + 80) with q by lia;
      change (Z_to_bv 64 TPV_A) with (Z_to_bv 64 TPV);
      eapply evt_cut;
      [ eapply (SPEC E OK (wz RA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx q node);
        [exact STq| lia| lia| exact Q16| exact MI| exact FRM| exact NODE| lia| left; lia| lia
        | intros m' MU'; apply AIM; exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))
        | intros m' MU' WM'; apply SHBM; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
        | intros m' MU' WM'; apply SZN; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
        | intros m' MU' WM'; apply SZD; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
        | intros m' MU' WM'; apply SZT; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')] ]
      | ];
      cbv beta; let m2 := fresh "m2" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let FRM2 := fresh "FRM2" in let MI2 := fresh "MI2" in let ST2 := fresh "ST2" in
      intros ?ms (?u0 & ?u1 & ?u2 & ?b2 & ?b3 & ?b4 & ?b5 & ?b6 & ?b7 & ?u3 & ?u4 & ?u5 & ?u6 & ?F' & ?fc' & m2 & ?c0 & ?c1 & -> & FRM2 & MU2 & WM2 & MI2 & ST2 & ?HG);
      rebase mx m2 MU2 WM2 SUB; clear MI FRM SUB;
      rewrite (ret_pc_even RA) by lia; change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A);
      apply evt_done; exists m2; do 17 eexists;
      split; [lazymatch goal with H : munch _ mA m2 |- _ => exact H end|];
      split; [lazymatch goal with H : wmono bsegs mA m2 |- _ => exact H end|];
      split; [exact MI2|]; split; [exact FRM2|]; split; [exact ST2|]; atp_st_eq_goal
    end.

  Lemma h20_c1 : h20_case 0xb4670.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2. case_tacc gdbl_specB. Qed.
  Lemma h20_c2 : h20_case 0xb45c8.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2. case_tacc gu64_specB. Qed.
  Lemma h20_c3 : h20_case 0xb45f8.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2. case_tacc gi64_specB. Qed.

  Lemma h20_c5 : h20_case 0xb46a0.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open. pose proof (SHBM _ MU WM) as [G1 G2].

    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_false.
    step. zstep.
    call_tix 0xb46e8.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. step. if_cases K1.
    { fin_ret. }

    shz_pose SZN node. step. shz_norm. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    shz_pose SZN (node + 8). step. shz_norm. step. if_false.
    step. zstep.
    repeat match goal with H : bytes_at bsegs m2 _ _ |- _ => clear H | H : ov_read_bytes bsegs m2 _ _ = _ |- _ => clear H end.
    call_tix 0xb472c.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (AIM mx ltac:(assumption)) as (_ & _ & _ & DOCC3 & _) end.

    shz_pose SZN node. step. shz_norm. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    chk0 SZT (ae_TAPE E + 8). step. if_false.
    astep. chk0 SZD (ae_DOC E + 8). step. if_false.
    step. step. if_dead1 by SS.

    step. astep. astep. pose proof (land_le_r (ae_T E 1) 72057594037927935 ltac:(lia)) as TV.
    astep. astep. step. if_dead1 by SS TV. step. if_dead1 by SS TV SL LOW HL HT.
    fin_ret.
  Qed.

  Lemma h20_c4a : forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    evt bsegs (fun ms => exists a0', ms = MS (mkR (wz 0xb45c4) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 (wz (q + -72)) (wz node) a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                            F (wz ATP_GETSTR_A) fc None m (seg_rom bsegs) /\ a0' = a0)
      (MS (mkR ra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 (wz node) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb45ac) fc None m (seg_rom bsegs)).
  Proof using HI47 LO N0 N8 NQ OK Q16 QH GLO.
    clear SEL S84 QS SH SZS SHBM SZN AIM SZD SZT RA0 RA2. intros. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).

    astep. replace (node mod 8) with 0 by lia. step. if_lia. step. if_lia.
    astep. step. zstep.
    apply evt_done. exists a0. split; [| reflexivity]. replace (q + -80 + 8) with (q + -72) by lia. unfold ATP_GETSTR_A. atp_st_eq_goal.
  Qed.

  Lemma h20_c4b : forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs0 xs1 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 b16 g20 : list byte) (code : Z),
    munch (h20_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (h20_frameB j0 [CB 16 b16; C4 (wz code); CB 4 g20] s4 s3 s2 s1 s0 (wz RA)) -> (code = 0 \/ code = 17) ->
    evt bsegs (h20_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR (wz 0xb45c4) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) xs3 xs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb45c4) fc None m (seg_rom bsegs)).
  Proof using HI47 LO OK Q16 QH GLO RA0 RA2.
    clear SEL S84 QS SH SZS SHBM SZN AIM SZD SZT N0 NQ N8. intros until code. intros MU WM ST MI FRM FR HC. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).

    zstep. fin_ret.
  Qed.
End H20.

Section Arm20.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH, GSTR_STACK_A in *; lia.

Theorem arm20_okA : forall W, arm_cpsA RT PMc W 20.
Proof using AF RC.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED176 : lf_lo X + 16 <= lf_S1 X - 176) by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 20 sel idx jr jos t m 176 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED176) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof (arm_ctx_below RT AF X E Σ 20 sel idx jr jos t m) as CTX.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof AL as (ALT & ALS & ALP & ALF & WLO). rewrite ELO in WLO.
  change (el_arm_pcA 20) with 0xb2670. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO176 : f + 1024 <= sp' - 176) by (clear - FLO NEED176; lia).
  assert (COSTP : 0 <= arm_costA 20 (ae_n E) (ae_sn E) (zlength (ae_p1 E))) by (unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; lia).
  pose proof (ael_root_elem E OKE) as [ELR NR].

  assert (SZSk : forall mx, ART RT Σ mx -> shz mx (sp' + 100 - 4) 8).
  { intros mx ARTx. apply (shz_stack RT AF Σ mx (sp' + 100 - 4) 8 ARTx); [clear - WLO NEED176; ul| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  assert (TAIL : forall (mB : mem) (ms : machine_state),
    (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> mB x = m x) ->
    (forall m', munch (h20_W sp') mB m' -> wmono bsegs mB m' -> ART RT Σ m') ->
    arm_memA (mkLF usp sp' f lo) E 20 sel idx jr jos t mB -> el_xdataA mB -> el_auxvA usp mB ->
    h20_post E sp' mB 0xb267c gp (wz usp) (wz sp') (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) ms ->
    evt bsegs (fun ms' => aevt RT PMc Σ K ms') ms).
  { intros mB ms AGB ARTMB AMB XDB AUXB (m0 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u0 & u1 & u2 & u3 & u4 & u5 & u6 & F' & fc' & MU0 & WM0 & MI0 & FRM0 & ST0 & ->).
    destruct (arm_ctx_below RT AF (mkLF usp sp' f lo) E Σ 20 sel idx jr jos t mB m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS
                (ARTMB mB (munch_refl _ mB) (wmono_refl bsegs mB)) AMB ltac:(lia) NEED176 XDB AUXB MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    assert (PRES0 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m0 x = m x).
    { intros x Hx. rewrite (MU0 x); [exact (AGB x Hx)|]. cbn [outside]. split; [exact (NBELOW _ Hx)| exact I]. }
    rewrite ELO in ST0. zstep. apply evt_done.
    apply (POST false (rt_credit RT Σ) Σ m0 fc' F').
    exact (arm_post_agree RT AF W 20 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m0 fc' LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART0 AM XD AUX
             PRES0 MI0 ST0 FRM0 COSTP). }

  apply (aevt_evt RT AF PMc MST).
  astep. zstep. zstep.
  eapply evt_cut.
  { eapply (h20_pre E OKE sp' (f + 208) (sp' + 100) sel m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SEL| clear; lia| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| clear; lia| reflexivity
      | exact SHBM| intros m' MU' WM'; exact (SZSk m' (ARTM m' MU' WM'))| exact SZN| exact AIM| exact SZD| exact SZT
      | apply munch_refl| apply wmono_refl| rewrite ELO; exact STg| exact C100| exact MIg]. }
  cbv beta. intros ms1 (m0 & j0 & j8 & a0' & a1' & a2' & MU0 & WM0 & MI0 & ST0 & FR0 & ->).
  assert (CE0 : rw_cells bsegs m0 (f + 208) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
  { eapply (rw_cells_agree bsegs m m0); [exact CE| | exact WM0]. apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold h20_W. cbn [outside].
    clear - Hx FLO176. lia. }
  assert (CASES8 : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by (clear - SEL; lia).
  destruct CASES8 as [EQS|[EQS|[EQS|[EQS|[EQS|[EQS|[EQS|EQS]]]]]]].
  - subst sel. change (gjt 0 + EL_GJTAB_B) with 0xb451c. eapply evt_cut;
    [ eapply (h20_c0 E OKE sp' (f + 208) m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (gjt 1 + EL_GJTAB_B) with 0xb4670. eapply evt_cut;
    [ eapply (h20_c1 E OKE sp' (f + 208) m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (gjt 2 + EL_GJTAB_B) with 0xb45c8. eapply evt_cut;
    [ eapply (h20_c2 E OKE sp' (f + 208) m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (gjt 3 + EL_GJTAB_B) with 0xb45f8. eapply evt_cut;
    [ eapply (h20_c3 E OKE sp' (f + 208) m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  -
    subst sel. change (gjt 4 + EL_GJTAB_B) with 0xb45ac.
    eapply evt_cut.
    { eapply (h20_c4a E OKE sp' (f + 208));
        [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia]. }
    cbv beta. intros ms2 (a0x & -> & _).
    destruct (CTX m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED176 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.

    pose proof FR0 as FRw. unfold h20_frameB in FRw. cbn [app] in FRw.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -80) [CB 8 j0] _) FRw) as [FRa FRbc]. cbn [cells_size csize Nat.add] in FRbc.
    replace (sp' + -80 + Z.of_nat 8) with (sp' + -72) in FRbc by lia.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -72) [CB 24 j8] _) FRbc) as [FRb FRc]. cbn [cells_size csize Nat.add] in FRc.
    replace (sp' + -72 + Z.of_nat 24) with (sp' + -48) in FRc by lia. clear FRw FRbc.
    assert (SUB4 : sub_fp (gstr_W (sp' + -80) (sp' + -72)) (h20_W sp')) by (unfold gstr_W, h20_W; intros x Hx; cbn [outside] in *; lia).
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
    destruct (arm_mem_agree RT AF (mkLF usp sp' f lo) E Σ 20 4 idx jr jos t m0 m1 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM0 XD0 AUX0 AG1)
      as (AM1 & XD1 & AUX1). cbn [lf_usp lf_S1 lf_F lf_lo] in AM1, AUX1.
    assert (AGB1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m1 x = m x).
    { intros x Hx. rewrite (AG1 (fun y => aclient (rt_live RT Σ) (rt_frames RT Σ) sp' y) (fun y Hy => Hy) x Hx).
      apply MU0. cbn [outside]. split; [exact (NBELOW _ Hx)| exact I]. }

    assert (FRa1 : rw_cells bsegs m1 (sp' + -80) [CB 8 j0]).
    { eapply rw_cells_agree_nw; [exact FRa|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (PRES1 x); [left; clear - Hx SPT SPR; ul| cbn [outside]; split; [clear - Hx; lia| exact I]]. }
    assert (FRc1 : rw_cells bsegs m1 (sp' + -48) [C8 (wz (f + 32)); C8 (wz (shad f)); C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb267c)]).
    { eapply rw_cells_agree_nw; [exact FRc|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (PRES1 x); [left; clear - Hx SPT SPR; ul| cbn [outside]; split; [clear - Hx; lia| exact I]]. }
    assert (FR1 : rw_cells bsegs m1 (sp' + -80) (h20_frameB j0 [CB 16 b16; C4 (wz code); CB 4 g20] (wz (f + 32)) (wz (shad f)) (wz f) (wz sp') (wz usp) (wz 0xb267c))).
    { unfold h20_frameB. apply (proj2 (rw_cells_app bsegs m1 (sp' + -80) [CB 8 j0] _)). split; [exact FRa1|]. cbn [cells_size csize Nat.add].
      replace (sp' + -80 + Z.of_nat 8) with (sp' + -72) by lia.
      apply (proj2 (rw_cells_app bsegs m1 (sp' + -72) [CB 16 b16; C4 (wz code); CB 4 g20] _)). split; [exact RC1|]. cbn [cells_size csize Nat.add].
      replace (sp' + -72 + Z.of_nat 24) with (sp' + -48) by lia. exact FRc1. }
    pose proof (arm_entry_kit RT AF (mkLF usp sp' f lo) E Σ 20 4 idx jr jos t m1 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM1 ltac:(lia) NEED176)
      as (ARTM1 & SZN1 & AIM1 & SZD1 & SZT1 & SHBM1). cbn [lf_usp lf_S1 lf_F lf_lo] in ARTM1, SZN1, AIM1, SZD1, SZT1, SHBM1.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { eapply (h20_c4b E OKE sp' m1 0xb267c);
        [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia| clear; lia| reflexivity
        | apply munch_refl| apply wmono_refl| exact ST1| exact MI1| exact FRM1| exact FR1| exact CODE]. }
    cbv beta. intros ms3 HP3. exact (TAIL m1 ms3 AGB1 ARTM1 AM1 XD1 AUX1 HP3).
  - subst sel. change (gjt 5 + EL_GJTAB_B) with 0xb46a0. eapply evt_cut;
    [ eapply (h20_c5 E OKE sp' (f + 208) m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (gjt 6 + EL_GJTAB_B) with 0xb47ac. eapply evt_cut;
    [ eapply (h20_c6 E OKE sp' (f + 208) m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (gjt 7 + EL_GJTAB_B) with 0xb4628. eapply evt_cut;
    [ eapply (h20_c7 E OKE sp' (f + 208) m 0xb267c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
Qed.
End Arm20.
