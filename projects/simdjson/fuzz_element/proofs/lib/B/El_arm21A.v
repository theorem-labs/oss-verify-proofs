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

Definition EL_TJTAB_B : Z := 0x23864.
Definition TJT_TAB : list Z := [594060; 594524; 594204; 594352; 594172; 594580; 594764; 594464].
Definition tjt (i : Z) : Z := nth (Z.to_nat i) TJT_TAB 0.
Definition TJT_WORDS : list word := map (Z_to_bv 64) TJT_TAB.
Lemma tjt_image : ro_bytes_b bsegs EL_TJTAB_B (u32s TJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tjt_at : forall m, mem_inv bsegs m -> bytes_at bsegs m EL_TJTAB_B (u32s TJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_TJTAB_B; lia | rewrite u32s_length; unfold EL_TJTAB_B, TJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact tjt_image.
Qed.
Lemma tjt_read : forall (m : word -> option byte) i a, mem_inv bsegs m -> 0 <= i < 8 -> a = wa (EL_TJTAB_B + 4 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 (Z_to_bv 64 (tjt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EL_TJTAB_B TJT_WORDS i); [apply tjt_at; exact MI| | lia | reflexivity].
  unfold TJT_WORDS, tjt. rewrite nth_error_map. rewrite (nth_error_nth' TJT_TAB 0); [reflexivity|].
  change (length TJT_TAB) with 8%nat. lia.
Qed.
Lemma tjt_range : forall i, 0 <= i < 8 -> 0 <= tjt i < 2 ^ 31.
Proof.
  intros i Hi. unfold tjt.
  assert (F : forallb (fun x => (0 <=? x) && (x <? 2 ^ 31)) TJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length TJT_TAB)%nat) by (change (length TJT_TAB) with 8%nat; lia).
  specialize (F _ (nth_In TJT_TAB 0 L)). apply andb_true_iff in F. destruct F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
Qed.
Lemma tjt_mod4 : forall i, 0 <= i < 8 -> tjt i mod 4 = 0.
Proof.
  intros i Hi. unfold tjt.
  assert (F : forallb (fun x => x mod 4 =? 0) TJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length TJT_TAB)%nat) by (change (length TJT_TAB) with 8%nat; lia).
  specialize (F _ (nth_In TJT_TAB 0 L)). apply Z.eqb_eq in F. exact F.
Qed.

Definition EL_H21_B : Z := 0xb4898.
Definition EL_H21RET_B : Z := 0xb4ae0.
Definition EL_H21TTX_B : Z := 0xb4be8.

Definition h21_W (q : Z) : list ivl := [(q + -176, q)].

Definition h21_frameB (j0 : list byte) (loc res : list cell) (s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0] ++ loc ++ res ++ [C8 s2; C8 s1; C8 s0; C8 ra].

Section FobjSrc.
Variable RT : rt_sig.
Lemma el_fobj_src : forall (Σ : rts RT) (m : mem) (sp : word) (lo f a n ss nn : Z),
  fobj RT Σ m a n -> 0 <= a -> rt_frames RT Σ = [(f, 4%nat)] ->
  a <= ss -> ss + nn <= a + n -> f <= a -> a + n <= f + 1016 -> 0 < nn -> a + n <= lo ->
  checked_src RT Σ m sp lo ss nn.
Proof.
  intros Σ m sp lo f a n ss nn (A8 & N0 & _ & HB) A0 FRS S1 S2 F1 F2 NP ALO.
  assert (INF : In (f, 4%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  pose proof (acc_zero_run bsegs m a _ A8 A0 HB) as AC. rewrite Z2Nat.id in AC by (Z.div_mod_to_equations; lia).
  split.
  - intros _. split; [apply (acc_sub bsegs m a (8 * ((n + 7) / 8))); [exact AC| lia| Z.div_mod_to_equations; lia]|].
    right; left. exists f, 4%nat. change (fs_size 4) with 1024. split; [exact INF| lia].
  - left. lia.
Qed.
End FobjSrc.

Section H21.
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
  Hypothesis SHBM : forall m', munch (h21_W q) mA m' -> wmono bsegs mA m' -> shb_cells m'.
  Hypothesis SZS : forall m', munch (h21_W q) mA m' -> wmono bsegs mA m' -> shz m' (SELA - 4) 8.
  Hypothesis SZN : forall m', munch (h21_W q) mA m' -> wmono bsegs mA m' -> shz m' node 16.
  Hypothesis AIM : forall m', munch (h21_W q) mA m' -> AINV_A E m'.
  Hypothesis SZD : forall m', munch (h21_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_DOC E) 16.
  Hypothesis SZT : forall m', munch (h21_W q) mA m' -> wmono bsegs mA m' -> shz m' (ae_TAPE E) (8 * ae_n E).

  Hypothesis SZL : forall m', munch (h21_W q) mA m' -> wmono bsegs mA m' -> shz m' (q + -56) 16.

  Definition h21_post (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : machine_state -> Prop :=
    fun ms => exists (m0 : mem) (a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      munch (h21_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ frm0 fc' /\ stk bsegs m0 (ae_lo E) q /\
      ms = MS (mkR (wz RA) (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (wz RA) fc' None m0 (seg_rom bsegs).

  Local Ltac ok_facts :=
    pose proof OK as OK'; destruct OK' as [WF _ _ _ (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SNS & SS & SL) _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]];
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia);
    pose proof (ael_root_elem E OK) as [EL NR];
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia);
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) HSN) as TIR;
    assert (TTR : 0 <= ttype (ae_T E 1) < 256) by (unfold ttype; lia);
    unfold SEGTOP_A, USTACK_TOP, EL_H21_B, EL_H21RET_B, EL_H21TTX_B, SHB, h21_W in *;
    assert (DOCR : 0 < ae_DOC E < 2^47) by lia.

  Lemma h21_pre : forall (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    munch (h21_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) q -> rw_cells bsegs m SELA [C4 (wz sel)] -> mem_inv bsegs m ->
    evt bsegs (fun ms => exists (m0 : mem) (j0 j16 j24 : list byte) (a0' a2' : word),
        munch (h21_W q) mA m0 /\ wmono bsegs mA m0 /\ mem_inv bsegs m0 /\ stk bsegs m0 (ae_lo E) (q + -80) /\
        rw_cells bsegs m0 (q + -80) (h21_frameB j0 [CB 16 j16] [CB 24 j24] s2 s1 s0 (wz RA)) /\
        ms = MS (mkR (wz RA) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 s0 s1 a0' (wz node) a2' a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz (tjt sel + EL_TJTAB_B)) fc None m0 (seg_rom bsegs))
      (MS (mkR (wz RA) (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz SELA) (wz node) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H21_B) fc None m (seg_rom bsegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH QS S84 SEL SH SHBM SZD SZN SZS SZT GLO RA0 RA2.
    intros until m. intros MU WM ST XSEL MI. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

    zstep. carve_frame 80%nat ST.
    apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 16; 24; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 4 lstep.

    pose proof (SHBM _ MU WM) as [G1 G2].
    step. step. step.

    shz_pose SZS (SELA - 4). zstep. rewrite ?shr3_div.
    replace (SELA / 8) with ((SELA - 4) / 8) by (clear - S84 QS GLO LO; Z.div_mod_to_equations; lia). zstep. zstep. shz_norm. step. if_false.
    zstep. rewrite (a_sx32_small sel) by lia.
    step. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|]. clear KB.

    zstep. step. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (tjt_read mx sel (wa (Z.shiftl sel 2 + EL_TJTAB_B)) ltac:(assumption) SEL ltac:(unfold wa, EL_TJTAB_B; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ end.
    unfold EL_TJTAB_B in RJ. pose proof (tjt_range sel SEL) as CJR.
    zstep. zstep. rewrite (a_swrap32_small (tjt sel)) by lia.
    zstep. pose proof (tjt_mod4 sel SEL) as CJ4. rewrite (ret_pc_even (tjt sel + 145508)) by (clear - CJ4 CJR; Z.div_mod_to_equations; lia).
    apply evt_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?ja :: CB 16 ?jb :: CB 24 ?jc :: _) => exists ja, jb, jc end.
    do 2 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|].
    unfold EL_TJTAB_B. atp_st_eq_goal.
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

  Local Ltac tape_facts_i m i RDT RDTY :=
    let AI2 := fresh "AI" in let TB := fresh "TAPEB" in
    assert (AI2 : AINV_A E m) by (apply AIM; assumption);
    pose proof AI2 as (TB & _ & _ & _ & _);
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TB ltac:(lia)) as RDT;
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) i TB ltac:(lia) ltac:(first [assumption| unfold ttype; lia])) as RDTY;
    clear TB AI2.

  Lemma h21_ret : forall (gp t0 t1 t2 xra xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte) (loc res : list cell),
    munch (h21_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (h21_frameB j0 loc res s2 s1 s0 (wz RA)) -> cells_size loc = 16%nat -> cells_size res = 24%nat ->
    evt bsegs (h21_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR xra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H21RET_B) fc None m (seg_rom bsegs)).
  Proof using HI47 LO OK Q16 QH GLO RA0 RA2.
    clear SEL S84 QS SH N0 NQ N8 SHBM SZS SZN AIM SZD SZT SZL.
    intros until res. intros MU WM ST MI FRM FR SZl SZr. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    pose proof FR as FRw. unfold h21_frameB in FR.
    apply (proj1 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ loc) _)) in FR. destruct FR as [FR1 FR2].
    rewrite cells_size_app, SZl in FR2. cbn [cells_size csize Nat.add] in FR2. replace (q + -80 + Z.of_nat 24) with (q + -56) in FR2 by lia.
    apply (proj1 (rw_cells_app bsegs m (q + -56) res _)) in FR2. destruct FR2 as [FR2 FR3].
    rewrite SZr in FR3. replace (q + -56 + Z.of_nat 24) with (q + -32) in FR3 by lia.

    step. step. step. step. zstep.
    pose proof (stk_release bsegs m (ae_lo E) _ _ ST FRw ltac:(lia)) as STq. unfold h21_frameB in STq. rewrite !cells_size_app, SZl, SZr in STq.
    cbn [cells_size csize Nat.add] in STq. replace (q + -80 + Z.of_nat 80) with q in STq by lia.
    step. rewrite (ret_pc_even RA) by lia.
    apply evt_done. exists m. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact STq|].
    replace (q + -80 + 80) with q by lia. atp_st_eq_goal.
  Qed.

  Lemma h21_ttx : forall (gp t0 t1 t2 xra xs0 xs1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte) (loc res : list cell) (i : Z),
    munch (h21_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (h21_frameB j0 loc res s2 s1 s0 (wz RA)) -> cells_size loc = 16%nat -> cells_size res = 24%nat -> 0 <= i < ae_n E ->
    evt bsegs (h21_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR xra (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 (wz (ae_DOC E)) (wz i) a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz EL_H21TTX_B) fc None m (seg_rom bsegs)).
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    clear SEL S84 QS SH SZS SZL.
    intros until i. intros MU WM ST MI FRM FR SZl SZr IR. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (SUB : sub_fp [(q + -16, q)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia).
    pose proof FR as FRw. unfold h21_frameB in FR.
    apply (proj1 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ loc) _)) in FR. destruct FR as [FR1 FR2].
    rewrite cells_size_app, SZl in FR2. cbn [cells_size csize Nat.add] in FR2. replace (q + -80 + Z.of_nat 24) with (q + -56) in FR2 by lia.
    apply (proj1 (rw_cells_app bsegs m (q + -56) res _)) in FR2. destruct FR2 as [FR2 FR3].
    rewrite SZr in FR3. replace (q + -56 + Z.of_nat 24) with (q + -32) in FR3 by lia.

    step. step. step. step. zstep.
    pose proof (stk_release bsegs m (ae_lo E) _ _ ST FRw ltac:(lia)) as STq. unfold h21_frameB in STq. rewrite !cells_size_app, SZl, SZr in STq.
    cbn [cells_size csize Nat.add] in STq. replace (q + -80 + Z.of_nat 80) with q in STq by lia. clear FRw FR1 FR2 FR3 ST.
    zstep. replace (q + -80 + 80) with q by lia.
    change (Z_to_bv 64 TPV_A) with (Z_to_bv 64 TPV).
    eapply (tix_cps E OK _ m F fc q i RA);
      [exact (AIM m MU)| exact IR| exact (SHBM m MU WM)
      | intros m' MU' WM'; exact (SZD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU')) (wmono_trans _ _ _ _ WM WM'))
      | exact STq| lia| lia| exact Q16| exact MI| exact RA0| exact RA2|].
    intros m2 xa1 xa3 xa4 MU2 WM2 MI2 ST2. rebase m m2 MU2 WM2 SUB.
    apply evt_done. exists m2. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
    change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A). atp_st_eq_goal.
  Qed.

  Definition h21_case (pc : Z) : Prop := forall (gp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 j16 j24 : list byte),
    munch (h21_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
    rw_cells bsegs m (q + -80) (h21_frameB j0 [CB 16 j16] [CB 24 j24] s2 s1 s0 (wz RA)) ->
    evt bsegs (h21_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR (wz RA) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 s0 s1 a0 (wz node) a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom bsegs)).

  Local Ltac fin_ret :=
    change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A);
    lazymatch goal with |- evt _ (h21_post ?gp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11) (MS _ ?F _ ?fc _ ?mx _) =>
      lazymatch goal with FR : rw_cells bsegs mx (q + -80) (h21_frameB ?j0 ?loc ?res _ _ _ _) |- _ =>
      apply (h21_ret gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 F fc mx j0 loc res);
        [ lazymatch goal with H : munch _ mA mx |- _ => exact H end
        | lazymatch goal with H : wmono bsegs mA mx |- _ => exact H end
        | lazymatch goal with H : stk bsegs mx _ _ |- _ => exact H end
        | lazymatch goal with H : mem_inv bsegs mx |- _ => exact H end
        | lazymatch goal with H : frm0 fc |- _ => exact H end
        | exact FR| first [reflexivity| assumption]| first [reflexivity| assumption]] end end.
  Local Ltac fin_ttx :=
    change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A);
    lazymatch goal with |- evt _ (h21_post ?gp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11) (MS _ ?F _ ?fc _ ?mx _) =>
      lazymatch goal with FR : rw_cells bsegs mx (q + -80) (h21_frameB ?j0 ?loc ?res _ _ _ _) |- _ =>
      apply (h21_ttx gp _ _ _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 F fc mx j0 loc res);
        [ lazymatch goal with H : munch _ mA mx |- _ => exact H end
        | lazymatch goal with H : wmono bsegs mA mx |- _ => exact H end
        | lazymatch goal with H : stk bsegs mx _ _ |- _ => exact H end
        | lazymatch goal with H : mem_inv bsegs mx |- _ => exact H end
        | lazymatch goal with H : frm0 fc |- _ => exact H end
        | exact FR| first [reflexivity| assumption]| first [reflexivity| assumption]| lia] end end.

  Local Ltac call_tix RET i :=
    let SUB := fresh "SUB" in
    assert (SUB : sub_fp [(q + -80 + -16, q + -80)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia);
    let m1 := fresh "m1" in name_mem m1;
    eapply (tix_cps E OK _ m1 _ _ (q + -80) i RET);
      [apply AIM; assumption| lia| apply SHBM; assumption
      | intros m' MU' WM'; apply (SZD m'); [eapply munch_trans; [eassumption| exact (munch_weaken _ _ _ _ SUB MU')]| eapply wmono_trans; [eassumption| exact WM']]
      | assumption| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| assumption| lia| reflexivity|];
    let m2 := fresh "m2" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in let MI2 := fresh "MI2" in let ST2 := fresh "ST2" in
    intros m2 ?xa1 ?xa3 ?xa4 MU2 WM2 MI2 ST2; rebase m1 m2 MU2 WM2 SUB; clear SUB;
    repeat match goal with H : mem_inv bsegs m1 |- _ => clear H | H : stk bsegs m1 _ _ |- _ => clear H
                         | H : bytes_at bsegs m1 _ _ |- _ => clear H | H : ov_read_bytes bsegs m1 _ _ = _ |- _ => clear H end;
    let RDT2 := fresh "RDT" in let RDTY2 := fresh "RDTY" in
    tape_facts_i m2 i RDT2 RDTY2; rewrite ?Z.mul_1_r in RDT2, RDTY2.

  Local Ltac case_open_tix RET :=
    clear SEL S84 QS SH SZS SZL; unfold h21_case;
    intros until j24; intros MU WM ST MI FRM NODE FR; ok_facts;
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia);
    pose proof (SHBM _ MU WM) as [G1 G2];
    chk0 SZN node; step; if_false;
    astep; chk0 SZN (node + 8); step; if_false;
    step; step; if_lia; astep; replace (ae_DOC E mod 8) with 0 by lia; step; if_lia;
    step; step; step; zstep;
    call_tix RET 1.

  Lemma h21_c0 : h21_case 0xb48f0.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open_tix 0xb4934.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. astep. step. if_cases K1.
    { fin_ret. }

    step. step. zstep. fin_ttx.
  Qed.

  Lemma h21_c6 : h21_case 0xb4bb0.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    clear SEL S84 QS SH SZS SZL. unfold h21_case. intros until j24. intros MU WM ST MI FRM NODE FR. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_false.
    step. fin_ttx.
  Qed.
  Lemma h21_c7 : h21_case 0xb4a84.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    clear SEL S84 QS SH SZS SZL. unfold h21_case. intros until j24. intros MU WM ST MI FRM NODE FR. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    pose proof (SHBM _ MU WM) as [G1 G2].
    chk0 SZN node. step. if_false.
    step. step. if_lia. astep. replace (ae_DOC E mod 8) with 0 by lia. step. if_lia.
    astep. chk0 SZN (node + 8). step. if_true.
    step. fin_ttx.
  Qed.

  Lemma h21_c2 : h21_case 0xb4980.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open_tix 0xb49c4.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. astep. step. if_cases K1.
    {
      astep. step. zstep. fin_ttx. }

    step. step. zstep.
    call_tix 0xb49f0 1.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. astep. step. if_cases K2.
    { astep. step. zstep. fin_ttx. }
    zstep. fin_ret.
  Qed.

  Lemma h21_c3 : h21_case 0xb4a14.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open_tix 0xb4a58.
    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. astep. step. if_cases K1.
    -
      step. step. zstep.
      call_tix 0xb4c0c 1.
      chk0 SZT (ae_TAPE E + 8). step. if_false.
      step. step. astep. step. if_cases K2.
      { astep. step. zstep. fin_ttx. }
      zstep. fin_ret.
    -
      astep. step. zstep. fin_ttx.
  Qed.

  Lemma h21_c5 : h21_case 0xb4af8.
  Proof using AIM HI47 LO N0 N8 NQ OK Q16 QH SHBM SZD SZN SZT GLO RA0 RA2.
    case_open_tix 0xb4b3c.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    step. step. step. if_cases K1.
    { fin_ret. }

    step. step. zstep.
    call_tix 0xb4b64 1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (AIM mx ltac:(assumption)) as (_ & _ & _ & DOCC3 & _) end.

    chk0 SZT (ae_TAPE E + 8). step. if_false.
    astep. chk0 SZD (ae_DOC E + 8). step. if_false.
    step. step. if_dead1 by SS.

    step. astep. astep. pose proof (land_le_r (ae_T E 1) 72057594037927935 ltac:(lia)) as TV.
    astep. astep. step. if_dead1 by SS TV. step. if_cases K2; [| exfalso; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - SS TV SL LOW HL HT; lia); clear - K2 SS TV SL LOW HL HT; lia].
    fin_ret.
  Qed.

  Lemma h21_c1b : forall (gp t0 t1 t2 xa0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 j16 j8 : list byte),
    munch (h21_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (h21_frameB j0 [CB 16 j16] [C8 (wz (ae_DOC E)); C8 (wz 1); CB 8 j8] s2 s1 s0 (wz RA)) ->
    evt bsegs (h21_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR (wz 0xb4acc) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 s0 s1 xa0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb4acc) fc None m (seg_rom bsegs)).
  Proof using AIM HI47 LO OK Q16 QH SHBM SZD SZL SZT GLO RA0 RA2.
    clear SEL S84 QS SH SZS SZN N0 NQ N8. intros until j8. intros MU WM ST MI FRM FR. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    assert (SUB : sub_fp [(q + -80 - 64, q + -80)] [(q + -176, q)]) by (intros x Hx; cbn [outside] in *; lia).

    pose proof FR as FRw. unfold h21_frameB in FRw. cbn [app] in FRw.
    apply (proj1 (rw_cells_app bsegs m (q + -80) [CB 8 j0; CB 16 j16] _)) in FRw. destruct FRw as [_ FRw]. cbn [cells_size csize Nat.add] in FRw.
    replace (q + -80 + Z.of_nat 24) with (q + -56) in FRw by lia.
    apply (proj1 (rw_cells_app bsegs m (q + -56) [C8 (wz (ae_DOC E)); C8 (wz 1)] _)) in FRw. destruct FRw as [REC _].

    astep. zstep. replace (q + -80 + 24) with (q + -56) by lia.
    name_mem m1.
    change (Z_to_bv 64 TPV_A) with (Z_to_bv 64 TPV).
    eapply evt_cut.
    { eapply (gdbl_specB E OK (wz 0xb4ad4) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (q + -80) (q + -56));
        [exact ST| lia| lia| clear - Q16; Z.div_mod_to_equations; lia| exact MI| exact FRM| exact REC| lia| right; lia| lia
        | intros m' MU'; apply AIM; exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))
        | intros m' MU' WM'; apply SHBM; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
        | intros m' MU' WM'; apply SZL; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
        | intros m' MU' WM'; apply SZD; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')]
        | intros m' MU' WM'; apply SZT; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))| exact (wmono_trans _ _ _ _ WM WM')] ]. }
    cbv beta. intros ms (u0 & u1 & u2 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m2 & c0 & c1 & -> & FRM' & MU2 & WM2 & MI2 & ST2 & HG).
    rebase m1 m2 MU2 WM2 SUB. clear MI FRM SUB REC. unfold G_dbl in HG.
    rewrite (ret_pc_even 0xb4ad4) by lia. change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A).

    astep. rewrite ?Z.add_0_r, ?(a_sx32_small c0) by lia. step. step. if_lia. fin_ret.
  Qed.

  Lemma h21_c4b : forall (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs0 xs1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte) (loc : list cell) (b16 g20 : list byte) (code : Z),
    munch (h21_W q) mA m -> wmono bsegs mA m -> stk bsegs m (ae_lo E) (q + -80) -> mem_inv bsegs m -> frm0 fc ->
    rw_cells bsegs m (q + -80) (h21_frameB j0 loc [CB 16 b16; C4 (wz code); CB 4 g20] s2 s1 s0 (wz RA)) -> cells_size loc = 16%nat -> (code = 0 \/ code = 17) ->
    evt bsegs (h21_post gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      (MS (mkR (wz 0xb4978) (wz (q + -80)) gp (wz TPV_A) t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 (wz SHB) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0xb4978) fc None m (seg_rom bsegs)).
  Proof using HI47 LO OK Q16 QH GLO RA0 RA2.
    clear SEL S84 QS SH SZS SHBM SZN AIM SZD SZT SZL N0 NQ N8. intros until code. intros MU WM ST MI FRM FR SZl HC. ok_facts.
    assert (EQ : bv_unsigned (Z_to_bv 64 (q + -80)) = q + -80) by (apply unsigned_lit; lia).
    pose proof FR as FRw. unfold h21_frameB in FRw.
    apply (proj1 (rw_cells_app bsegs m (q + -80) ([CB 8 j0] ++ loc) _)) in FRw. destruct FRw as [_ FRw].
    rewrite cells_size_app, SZl in FRw. cbn [cells_size csize Nat.add app] in FRw. replace (q + -80 + Z.of_nat 24) with (q + -56) in FRw by lia.

    step. rewrite (a_sx32_small code) by lia. zstep. step. step. if_lia.
    clear FRw. fin_ret.
  Qed.
End H21.

Section Arm21.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB, EL_THROW_STACK_A, NORET_DEPTH, GSTR_STACK_A in *; lia.

Theorem arm21_okA : forall W, arm_cpsA RT PMc W 21.
Proof using AF RC.
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST.
  assert (NEED176 : lf_lo X + 16 <= lf_S1 X - 176) by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul).
  pose proof (arm_entry_kit RT AF X E Σ 21 sel idx jr jos t m 176 LK OKE LE AL FRS ARTg AM ltac:(lia) NEED176) as (ARTM & SZN & AIM & SZD & SZT & SHBM).
  pose proof (arm_ctx_below RT AF X E Σ 21 sel idx jr jos t m) as CTX.
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)].
  destruct X as [usp sp' f lo]. cbn [lf_usp lf_S1 lf_F lf_lo] in *.
  pose proof LE as (EDOC & EFD & EKD & ELO & EHI). cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI.
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS). cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS.
  pose proof AL as (ALT & ALS & ALP & ALF & WLO). rewrite ELO in WLO.
  change (el_arm_pcA 21) with 0xb2390. unfold lf_st. cbn [lf_usp lf_S1 lf_F lf_lo].
  assert (ES : bv_unsigned (wz sp') = sp') by (apply unsigned_lit; ul).
  assert (FLO176 : f + 1024 <= sp' - 176) by (clear - FLO NEED176; lia).
  assert (COSTP : 0 <= arm_costA 21 (ae_n E) (ae_sn E) (zlength (ae_p1 E))) by (unfold arm_costA; cbn [Z.eqb Pos.eqb orb]; lia).
  pose proof (ael_root_elem E OKE) as [ELR NR].
  pose proof (af_sp0_range RT AF Σ m ARTg) as SP0R.

  assert (SZSk : forall mx, ART RT Σ mx -> shz mx (sp' + 100 - 4) 8).
  { intros mx ARTx. apply (shz_stack RT AF Σ mx (sp' + 100 - 4) 8 ARTx); [clear - WLO NEED176; ul| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  assert (SZLk : forall mx, ART RT Σ mx -> shz mx (sp' + -56) 16).
  { intros mx ARTx. apply (shz_stack RT AF Σ mx (sp' + -56) 16 ARTx); [clear - WLO NEED176; ul| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  assert (SZEk : forall mx, ART RT Σ mx -> shz mx (sp' + -72) 16).
  { intros mx ARTx. apply (shz_stack RT AF Σ mx (sp' + -72) 16 ARTx); [clear - WLO NEED176; ul| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| reflexivity| lia]. }

  assert (TAIL : forall (mB : mem) (ms : machine_state),
    (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> mB x = m x) ->
    (forall m', munch (h21_W sp') mB m' -> wmono bsegs mB m' -> ART RT Σ m') ->
    arm_memA (mkLF usp sp' f lo) E 21 sel idx jr jos t mB -> el_xdataA mB -> el_auxvA usp mB ->
    h21_post E sp' mB 0xb239c gp (wz usp) (wz sp') (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) ms ->
    evt bsegs (fun ms' => aevt RT PMc Σ K ms') ms).
  { intros mB ms AGB ARTMB AMB XDB AUXB (m0 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u0 & u1 & u2 & u3 & u4 & u5 & u6 & F' & fc' & MU0 & WM0 & MI0 & FRM0 & ST0 & ->).
    destruct (arm_ctx_below RT AF (mkLF usp sp' f lo) E Σ 21 sel idx jr jos t mB m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS
                (ARTMB mB (munch_refl _ mB) (wmono_refl bsegs mB)) AMB ltac:(lia) NEED176 XDB AUXB MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    assert (PRES0 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m0 x = m x).
    { intros x Hx. rewrite (MU0 x); [exact (AGB x Hx)|]. cbn [outside]. split; [exact (NBELOW _ Hx)| exact I]. }
    rewrite ELO in ST0. zstep. apply evt_done.
    apply (POST false (rt_credit RT Σ) Σ m0 fc' F').
    exact (arm_post_agree RT AF W 21 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m0 fc' LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART0 AM XD AUX
             PRES0 MI0 ST0 FRM0 COSTP). }

  assert (MCPY : forall (mB m0 : mem) (d : Z) (gp' t0' t1' t2' a3' a4' a5' a6' a7' : word) (s3' s4' t3' t4' t5' t6' : word) (F0 : bvmap 5 word) (fc0 : bv 32) (RET : Z)
      (Q : mem -> machine_state -> Prop),
    (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> mB x = m x) ->
    (forall m', munch (h21_W sp') mB m' -> wmono bsegs mB m' -> ART RT Σ m') ->
    arm_memA (mkLF usp sp' f lo) E 21 sel idx jr jos t mB -> el_xdataA mB -> el_auxvA usp mB ->
    munch (h21_W sp') mB m0 -> wmono bsegs mB m0 -> mem_inv bsegs m0 -> stk bsegs m0 lo (sp' + -80) -> frm0 fc0 ->
    (d = sp' + -56 \/ d = sp' + -72) -> wr_at bsegs m0 d 16 -> 0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall (m1 : mem) (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (F1 : bvmap 5 word),
       (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m1 x = m x) ->
       (forall m', munch (h21_W sp') m1 m' -> wmono bsegs m1 m' -> ART RT Σ m') ->
       arm_memA (mkLF usp sp' f lo) E 21 sel idx jr jos t m1 -> el_xdataA m1 -> el_auxvA usp m1 ->
       ART RT Σ m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (sp' + -80) ->
       (forall x : word, sp' + -80 <= bv_unsigned x -> ~ (d <= bv_unsigned x < d + 16) -> bv_unsigned x < USTACK_TOP -> m1 x = m0 x) -> wmono bsegs m0 m1 ->
       rw_cells bsegs m1 d [C8 (wz (ae_DOC E)); C8 (wz 1)] ->
       Q m1 (MS (mkR (wz RET) (wz (sp' + -80)) gp' (wz TPV_A) t0'' t1'' t2'' (wz usp) (wz sp') (wz d) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (wz SHB) s3' s4' (wz (f + 96))
                        s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3'' t4'' t5'' t6'') F1 (wz RET) fc0 None m1 (seg_rom bsegs))) ->
    (forall m1 ms1, Q m1 ms1 -> aevt RT PMc Σ K ms1) ->
    aevt RT PMc Σ K (MS (mkR (wz RET) (wz (sp' + -80)) gp' (wz TPV_A) t0' t1' t2' (wz usp) (wz sp') (wz d) (wz (f + 208)) (wz 16) a3' a4' a5' a6' a7' (wz SHB) s3' s4' (wz (f + 96))
                         s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3' t4' t5' t6') F0 (wz e_asan_memcpy) fc0 None m0 (seg_rom bsegs))).
  { intros mB m0 d gp' t0' t1' t2' a3' a4' a5' a6' a7' s3' s4' t3' t4' t5' t6' F0 fc0 RET Q AGB ARTMB AMB XDB AUXB MU0 WM0 MI0 ST0 FRM0 HD WRD RET0 RET2 HQ QK.
    destruct (arm_ctx_below RT AF (mkLF usp sp' f lo) E Σ 21 sel idx jr jos t mB m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS
                (ARTMB mB (munch_refl _ mB) (wmono_refl bsegs mB)) AMB ltac:(lia) NEED176 XDB AUXB MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    pose proof AM0 as (_ & _ & _ & CE0 & _ & CS0 & _). cbn [lf_usp lf_S1 lf_F lf_lo] in CE0, CS0.
    assert (EQ0 : bv_unsigned (Z_to_bv 64 (sp' + -80)) = sp' + -80) by (apply unsigned_lit; clear - SPR SPT LLO LOR NEED176; ul).
    assert (FOBJ : fobj RT Σ m0 (f + 208) 16) by (apply (el_elem_fobj RT Σ m0 f 0 0 (-8) t); [exact CS0| exact FRS| exact FPOS| exact F64]).
    assert (CSRC : checked_src RT Σ m0 (wz (sp' + -80)) lo (f + 208) 16)
      by (apply (el_fobj_src RT Σ m0 _ lo f (f + 208) 16 (f + 208) 16 FOBJ); [clear - FPOS; lia| exact FRS| lia| lia| lia| lia| lia| clear - FLO; lia]).
    assert (CDST : checked_dst RT Σ m0 (wz (sp' + -80)) d 16).
    { apply (checked_dst_stack RT AF Σ m0 _ d 16 ART0); [clear - HD WLO NEED176 SPB SP0R; ul| clear - HD SPT SPR; ul| rewrite EQ0; clear - HD; lia| exact WRD]. }
    assert (COK : call_ok RT Σ m0 (wz (sp' + -80)) lo).
    { unfold call_ok. rewrite EQ0. split; [exact ST0|]. split; [exact WLO|]. split; [clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; ul|].
      split; [clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia]. }
    pose proof CE0 as [[_ BYS] _].
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 m0 d (f + 208) (cells_bytes [C8 (wz (ae_DOC E)); C8 (wz 1)]) lo
              eq_refl eq_refl eq_refl ltac:(clear - HD SPT SPR LLO LOR NEED176; ul) ltac:(clear - FPOS FLO LLO LOR SPR SPT; ul) ltac:(cbn; clear; lia) BYS CSRC CDST
              ltac:(cbn; clear - HD FLO176; lia) ART0 MI0 COK).
    intros y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F1 m1 (ART1 & MI1 & WM1 & ST1) PRES1 BY1. rewrite EQ0 in ST1, PRES1.
    rewrite (ret_pc_even RET) by lia. change (Z.of_nat (length _)) with 16 in PRES1.
    assert (AG1 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) -> agree_on P m0 m1).
    { intros P HP x Px. pose proof (HP _ Px) as Hx. apply (PRES1 x).
      - destruct Hx as [H|H]; [left; clear - H; lia| right; exact H].
      - pose proof (NBELOW _ Hx) as NB. clear - NB HD. lia. }
    destruct (arm_mem_agree RT AF (mkLF usp sp' f lo) E Σ 21 sel idx jr jos t m0 m1 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM0 XD0 AUX0 AG1)
      as (AM1 & XD1 & AUX1). cbn [lf_usp lf_S1 lf_F lf_lo] in AM1, AUX1.
    assert (AGB1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m1 x = m x).
    { intros x Hx. rewrite (AG1 (fun y => aclient (rt_live RT Σ) (rt_frames RT Σ) sp' y) (fun y Hy => Hy) x Hx).
      rewrite (MU0 x); [exact (AGB x Hx)|]. cbn [outside]. split; [exact (NBELOW _ Hx)| exact I]. }
    pose proof (arm_entry_kit RT AF (mkLF usp sp' f lo) E Σ 21 sel idx jr jos t m1 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM1 ltac:(lia) NEED176)
      as (ARTM1 & _). cbn [lf_usp lf_S1 lf_F lf_lo] in ARTM1.
    apply (QK m1). apply HQ; [exact AGB1| exact ARTM1| exact AM1| exact XD1| exact AUX1| exact ART1| exact MI1| exact ST1| | exact WM1|].
    - intros x H1 H2 H3. apply (PRES1 x); [left; clear - H1 H3; unfold USTACK_TOP in *; lia| exact H2].
    - split; [split; [cbn; tauto| exact BY1]|]. cbn [cells_size csize Nat.add]. exact (wr_at_transport bsegs m0 m1 d 16 WRD WM1). }

  apply (aevt_evt RT AF PMc MST).
  astep. zstep. zstep.
  eapply evt_cut.
  { eapply (h21_pre E OKE sp' (f + 208) (sp' + 100) sel m 0xb239c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | exact SEL| clear; lia| clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia| clear; lia| reflexivity
      | exact SHBM| intros m' MU' WM'; exact (SZSk m' (ARTM m' MU' WM'))| exact SZN| exact AIM| exact SZD| exact SZT
      | apply munch_refl| apply wmono_refl| rewrite ELO; exact STg| exact C100| exact MIg]. }
  cbv beta. intros ms1 (m0 & j0 & j16 & j24 & a0' & a2' & MU0 & WM0 & MI0 & ST0 & FR0 & ->).
  assert (CE0 : rw_cells bsegs m0 (f + 208) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
  { eapply (rw_cells_agree bsegs m m0); [exact CE| | exact WM0]. apply (agree_of_munch _ _ _ _ MU0). intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold h21_W. cbn [outside].
    clear - Hx FLO176. lia. }
  assert (SZLm : forall m', munch (h21_W sp') m m' -> wmono bsegs m m' -> shz m' (sp' + -56) 16) by (intros m' MU' WM'; exact (SZLk m' (ARTM m' MU' WM'))).
  assert (CASES8 : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by (clear - SEL; lia).
  destruct CASES8 as [EQS|[EQS|[EQS|[EQS|[EQS|[EQS|[EQS|EQS]]]]]]].
  - subst sel. change (tjt 0 + EL_TJTAB_B) with 0xb48f0. eapply evt_cut;
    [ eapply (h21_c0 E OKE sp' (f + 208) m 0xb239c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  -
    subst sel. change (tjt 1 + EL_TJTAB_B) with 0xb4ac0.
    destruct (CTX m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED176 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    assert (EQ0 : bv_unsigned (Z_to_bv 64 (sp' + -80)) = sp' + -80) by (apply unsigned_lit; clear - SPR SPT LLO LOR NEED176; ul).

    astep. step. zstep. replace (sp' + -80 + 24) with (sp' + -56) by lia. apply evt_done.

    pose proof FR0 as FRw. unfold h21_frameB in FRw. cbn [app] in FRw.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -80) [CB 8 j0; CB 16 j16] _) FRw) as [FRa FRbc]. cbn [cells_size csize Nat.add] in FRbc.
    replace (sp' + -80 + Z.of_nat 24) with (sp' + -56) in FRbc by lia.
    apply (rw_cells_split_CB bsegs _ _ [] 24 j24 _ [16; 8]%nat) in FRbc; [| reflexivity]. cbn [mk_CB_cells app] in FRbc.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -56) [CB 16 (firstn 16 j24)] _) FRbc) as [FRr FRc]. cbn [cells_size csize Nat.add] in FRc.
    replace (sp' + -56 + Z.of_nat 16) with (sp' + -40) in FRc by lia.
    set (j8 := firstn 8 (skipn 16 j24)) in FRc. clearbody j8. clear FRw FRbc.
    apply (MCPY m m0 (sp' + -56) gp t0 t1 t2 a3 a4 a5 a6 a7 (wz (shad f)) (wz (f + 32)) t3 t4 t5 t6 F fc 0xb4acc
             (fun m1 ms1 => exists (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (F1 : bvmap 5 word),
                (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m1 x = m x) /\
                (forall m', munch (h21_W sp') m1 m' -> wmono bsegs m1 m' -> ART RT Σ m') /\
                arm_memA (mkLF usp sp' f lo) E 21 1 idx jr jos t m1 /\ el_xdataA m1 /\ el_auxvA usp m1 /\ ART RT Σ m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (sp' + -80) /\
                rw_cells bsegs m1 (sp' + -80) (h21_frameB j0 [CB 16 j16] [C8 (wz (ae_DOC E)); C8 (wz 1); CB 8 j8] (wz f) (wz sp') (wz usp) (wz 0xb239c)) /\
                ms1 = MS (mkR (wz 0xb4acc) (wz (sp' + -80)) gp (wz TPV_A) t0'' t1'' t2'' (wz usp) (wz sp') (wz (sp' + -56)) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (wz SHB) (wz (shad f)) (wz (f + 32)) (wz (f + 96))
                        s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3'' t4'' t5'' t6'') F1 (wz 0xb4acc) fc None m1 (seg_rom bsegs))
             (fun x _ => eq_refl) ARTM AM XD AUX MU0 WM0 MI0 ltac:(rewrite <- ELO; exact ST0) FRM ltac:(left; reflexivity)
             ltac:(apply (wr_at_sub m0 (sp' + -80) 80); [eapply rw_cells_wr_at; [exact FR0| unfold h21_frameB; cbn [cells_size csize Nat.add app]; lia]| lia| lia| lia])
             ltac:(clear; lia) ltac:(reflexivity)).
    { intros m1 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F1 AGB1 ARTM1 AM1 XD1 AUX1 ART1 MI1 ST1 PRES1 WM1 REC1.
      exists y0, y1, y2, e1, e2, e3, e4, e5, e6, e7, y3, y4, y5, y6, F1.
      split; [exact AGB1|]. split; [exact ARTM1|]. split; [exact AM1|]. split; [exact XD1|]. split; [exact AUX1|]. split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|].
      split; [| reflexivity].
      assert (AGa : agree_on (fun x => sp' + -80 <= x < sp' + -80 + Z.of_nat (cells_size [CB 8 j0; CB 16 j16])) m0 m1).
      { intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (PRES1 a); [clear - Ha; lia| clear - Ha; lia| clear - Ha SPT SPR; ul]. }
      assert (AGc : agree_on (fun x => sp' + -40 <= x < sp' + -40 + Z.of_nat (cells_size [CB 8 j8; C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb239c)])) m0 m1).
      { intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (PRES1 a); [clear - Ha; lia| clear - Ha; lia| clear - Ha SPT SPR; ul]. }
      pose proof (rw_cells_agree_nw bsegs m0 m1 _ _ FRa AGa) as FRa1. pose proof (rw_cells_agree_nw bsegs m0 m1 _ _ FRc AGc) as FRc1.
      unfold h21_frameB. cbn [app].
      apply (proj2 (rw_cells_app bsegs m1 (sp' + -80) [CB 8 j0; CB 16 j16] _)). split; [exact FRa1|]. cbn [cells_size csize Nat.add].
      replace (sp' + -80 + Z.of_nat 24) with (sp' + -56) by lia.
      apply (proj2 (rw_cells_app bsegs m1 (sp' + -56) [C8 (wz (ae_DOC E)); C8 (wz 1)] _)). split; [exact REC1|]. cbn [cells_size csize Nat.add].
      replace (sp' + -56 + Z.of_nat 16) with (sp' + -40) by lia. exact FRc1. }
    intros m1 ms1 (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F1 & AGB1 & ARTM1 & AM1 & XD1 & AUX1 & ART1 & MI1 & ST1 & FR1 & ->).
    pose proof (arm_entry_kit RT AF (mkLF usp sp' f lo) E Σ 21 1 idx jr jos t m1 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM1 ltac:(lia) NEED176)
      as (_ & SZN1 & AIM1 & SZD1 & SZT1 & SHBM1). cbn [lf_usp lf_S1 lf_F lf_lo] in SZN1, AIM1, SZD1, SZT1, SHBM1.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { eapply (h21_c1b E OKE sp' m1 0xb239c);
        [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia| clear; lia| reflexivity
        | exact SHBM1| exact AIM1| exact SZD1| exact SZT1| intros m' MU' WM'; exact (SZLk m' (ARTM1 m' MU' WM'))
        | apply munch_refl| apply wmono_refl| rewrite <- ELO in ST1; exact ST1| exact MI1| exact FRM| exact FR1]. }
    cbv beta. intros ms3 HP3. exact (TAIL m1 ms3 AGB1 ARTM1 AM1 XD1 AUX1 HP3).
  - subst sel. change (tjt 2 + EL_TJTAB_B) with 0xb4980. eapply evt_cut;
    [ eapply (h21_c2 E OKE sp' (f + 208) m 0xb239c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (tjt 3 + EL_TJTAB_B) with 0xb4a14. eapply evt_cut;
    [ eapply (h21_c3 E OKE sp' (f + 208) m 0xb239c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  -
    subst sel. change (tjt 4 + EL_TJTAB_B) with 0xb4960.
    destruct (CTX m0 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ltac:(lia) NEED176 XD AUX MU0 WM0) as (ART0 & AM0 & XD0 & AUX0 & NBELOW & AGM).
    cbn [lf_usp lf_S1 lf_F lf_lo] in AM0, AUX0, NBELOW, AGM.
    assert (EQ0 : bv_unsigned (Z_to_bv 64 (sp' + -80)) = sp' + -80) by (apply unsigned_lit; clear - SPR SPT LLO LOR NEED176; ul).

    astep. step. zstep. replace (sp' + -80 + 8) with (sp' + -72) by lia. apply evt_done.
    pose proof FR0 as FRw. unfold h21_frameB in FRw. cbn [app] in FRw.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -80) [CB 8 j0] _) FRw) as [FRa FRbc]. cbn [cells_size csize Nat.add] in FRbc.
    replace (sp' + -80 + Z.of_nat 8) with (sp' + -72) in FRbc by lia.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -72) [CB 16 j16] _) FRbc) as [_ FRrc]. cbn [cells_size csize Nat.add] in FRrc.
    replace (sp' + -72 + Z.of_nat 16) with (sp' + -56) in FRrc by lia.
    pose proof (proj1 (rw_cells_app bsegs m0 (sp' + -56) [CB 24 j24] _) FRrc) as [FRr FRc]. cbn [cells_size csize Nat.add] in FRc.
    replace (sp' + -56 + Z.of_nat 24) with (sp' + -32) in FRc by lia. clear FRw FRbc FRrc.
    apply (MCPY m m0 (sp' + -72) gp t0 t1 t2 a3 a4 a5 a6 a7 (wz (shad f)) (wz (f + 32)) t3 t4 t5 t6 F fc 0xb496c
             (fun m1 ms1 => exists (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word) (F1 : bvmap 5 word),
                (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m1 x = m x) /\
                (forall m', munch (h21_W sp') m1 m' -> wmono bsegs m1 m' -> ART RT Σ m') /\
                arm_memA (mkLF usp sp' f lo) E 21 4 idx jr jos t m1 /\ el_xdataA m1 /\ el_auxvA usp m1 /\ ART RT Σ m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (sp' + -80) /\
                rw_cells bsegs m1 (sp' + -80) [CB 8 j0] /\ rw_cells bsegs m1 (sp' + -72) [C8 (wz (ae_DOC E)); C8 (wz 1)] /\ rw_cells bsegs m1 (sp' + -56) [CB 24 j24] /\
                rw_cells bsegs m1 (sp' + -32) [C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb239c)] /\
                ms1 = MS (mkR (wz 0xb496c) (wz (sp' + -80)) gp (wz TPV_A) t0'' t1'' t2'' (wz usp) (wz sp') (wz (sp' + -72)) a1'' a2'' a3'' a4'' a5'' a6'' a7'' (wz SHB) (wz (shad f)) (wz (f + 32)) (wz (f + 96))
                        s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3'' t4'' t5'' t6'') F1 (wz 0xb496c) fc None m1 (seg_rom bsegs))
             (fun x _ => eq_refl) ARTM AM XD AUX MU0 WM0 MI0 ltac:(rewrite <- ELO; exact ST0) FRM ltac:(right; reflexivity)
             ltac:(apply (wr_at_sub m0 (sp' + -80) 80); [eapply rw_cells_wr_at; [exact FR0| unfold h21_frameB; cbn [cells_size csize Nat.add app]; lia]| lia| lia| lia])
             ltac:(clear; lia) ltac:(reflexivity)).
    { intros m1 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F1 AGB1 ARTM1 AM1 XD1 AUX1 ART1 MI1 ST1 PRES1 WM1 REC1.
      exists y0, y1, y2, e1, e2, e3, e4, e5, e6, e7, y3, y4, y5, y6, F1.
      split; [exact AGB1|]. split; [exact ARTM1|]. split; [exact AM1|]. split; [exact XD1|]. split; [exact AUX1|]. split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|].
      assert (AGa : agree_on (fun x => sp' + -80 <= x < sp' + -80 + Z.of_nat (cells_size [CB 8 j0])) m0 m1).
      { intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (PRES1 a); [clear - Ha; lia| clear - Ha; lia| clear - Ha SPT SPR; ul]. }
      assert (AGr : agree_on (fun x => sp' + -56 <= x < sp' + -56 + Z.of_nat (cells_size [CB 24 j24])) m0 m1).
      { intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (PRES1 a); [clear - Ha; lia| clear - Ha; lia| clear - Ha SPT SPR; ul]. }
      assert (AGc : agree_on (fun x => sp' + -32 <= x < sp' + -32 + Z.of_nat (cells_size [C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb239c)])) m0 m1).
      { intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (PRES1 a); [clear - Ha; lia| clear - Ha; lia| clear - Ha SPT SPR; ul]. }
      split; [exact (rw_cells_agree_nw bsegs m0 m1 _ _ FRa AGa)|]. split; [exact REC1|]. split; [exact (rw_cells_agree_nw bsegs m0 m1 _ _ FRr AGr)|].
      split; [exact (rw_cells_agree_nw bsegs m0 m1 _ _ FRc AGc)| reflexivity]. }
    intros m1 ms1 (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F1 & AGB1 & ARTM1 & AM1 & XD1 & AUX1 & ART1 & MI1 & ST1 & FRa1 & REC1 & FRr1 & FRc1 & ->).
    destruct (arm_ctx_below RT AF (mkLF usp sp' f lo) E Σ 21 4 idx jr jos t m1 m1 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM1 ltac:(lia) NEED176 XD1 AUX1
                (munch_refl _ m1) (wmono_refl bsegs m1)) as (_ & _ & _ & _ & NBELOW1 & _). cbn [lf_usp lf_S1 lf_F lf_lo] in NBELOW1.

    apply (aevt_evt RT AF PMc MST).
    astep. astep. zstep. replace (sp' + -80 + 24) with (sp' + -56) by lia. replace (sp' + -80 + 8) with (sp' + -72) by lia. apply evt_done.
    assert (SUB4 : sub_fp (gstr_W (sp' + -80) (sp' + -56)) (h21_W sp')) by (unfold gstr_W, h21_W; intros x Hx; cbn [outside] in *; lia).
    assert (SZE4 : forall m', munch (gstr_W (sp' + -80) (sp' + -56)) m1 m' -> wmono bsegs m1 m' -> shz m' (sp' + -72) 16).
    { intros m' MU' WM'. exact (SZEk m' (ARTM1 m' (munch_weaken _ _ _ _ SUB4 MU') WM')). }
    pose proof (arm_entry_kit RT AF (mkLF usp sp' f lo) E Σ 21 4 idx jr jos t m1 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART1 AM1 ltac:(lia) NEED176)
      as (_ & _ & AIM1 & _). cbn [lf_usp lf_S1 lf_F lf_lo] in AIM1.
    change (Z_to_bv 64 TPV_A) with (Z_to_bv 64 TPV).
    eapply (aevt_rt RT PMc Σ K _ _
             (gstr_cps_elB RT AF E OKE RC Σ PMc (sp' + -80) (sp' + -56) (sp' + -72) 1 (ae_n E - 1) TAPE_MAX_DEPTH
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m1 j24
                FDO MST AL (AIM1 m1 (munch_refl _ m1)) ELR ltac:(clear; lia) REC1 ltac:(right; clear; lia) ltac:(clear - SPT SPR LLO LOR NEED176; ul)
                ltac:(clear - SPA'; Z.div_mod_to_equations; lia)
                FRr1 ltac:(clear; lia) ltac:(rewrite EHI; clear - SPR; lia) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) ltac:(left; clear; lia)
                ART1 MI1 ltac:(rewrite ELO; exact ST1)
                ltac:(rewrite ELO; clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold EL_THROW_STACK_A, NORET_DEPTH, GSTR_STACK_A, RT_STACK in *; lia)
                ltac:(clear - SPA'; Z.div_mod_to_equations; lia) FRM SZE4));
      [exact FRM|].
    intros c Hc; eexists Σ, _; split; [exact Hc|].
    intros ms' (v & m2 & b16 & g20 & code & RS & (ART2 & MI2 & ST2) & PRES2 & RC2 & CODE) FRM2.
    destruct RS as (w0 & w1 & w2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->). cbn [ms_fcsr MS] in FRM2.
    rewrite ret_pc_even by (clear; lia). change (Z_to_bv 64 TPV) with (Z_to_bv 64 TPV_A).
    assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x) -> agree_on P m1 m2).
    { intros P HP x Px. pose proof (HP _ Px) as Hx. apply (PRES2 x).
      - destruct Hx as [H|H]; [left; clear - H; lia| right; exact H].
      - cbn [outside]. split; [| exact I]. pose proof (NBELOW1 _ Hx) as NB. clear - NB. lia. }
    destruct (arm_mem_agree RT AF (mkLF usp sp' f lo) E Σ 21 4 idx jr jos t m1 m2 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART2 AM1 XD1 AUX1 AG2)
      as (AM2 & XD2 & AUX2). cbn [lf_usp lf_S1 lf_F lf_lo] in AM2, AUX2.
    assert (AGB2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned x) -> m2 x = m x).
    { intros x Hx. rewrite (AG2 (fun y => aclient (rt_live RT Σ) (rt_frames RT Σ) sp' y) (fun y Hy => Hy) x Hx). exact (AGB1 x Hx). }
    assert (FRa2 : rw_cells bsegs m2 (sp' + -80) [CB 8 j0]).
    { eapply rw_cells_agree_nw; [exact FRa1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (PRES2 x); [left; clear - Hx SPT SPR; ul| cbn [outside]; split; [clear - Hx; lia| exact I]]. }
    assert (REC2 : rw_cells bsegs m2 (sp' + -72) [C8 (wz (ae_DOC E)); C8 (wz 1)]).
    { eapply rw_cells_agree_nw; [exact REC1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (PRES2 x); [left; clear - Hx SPT SPR; ul| cbn [outside]; split; [clear - Hx; lia| exact I]]. }
    assert (FRc2 : rw_cells bsegs m2 (sp' + -32) [C8 (wz f); C8 (wz sp'); C8 (wz usp); C8 (wz 0xb239c)]).
    { eapply rw_cells_agree_nw; [exact FRc1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (PRES2 x); [left; clear - Hx SPT SPR; ul| cbn [outside]; split; [clear - Hx; lia| exact I]]. }
    assert (FR2 : rw_cells bsegs m2 (sp' + -80) (h21_frameB j0 [C8 (wz (ae_DOC E)); C8 (wz 1)] [CB 16 b16; C4 (wz code); CB 4 g20] (wz f) (wz sp') (wz usp) (wz 0xb239c))).
    { unfold h21_frameB. cbn [app]. apply (proj2 (rw_cells_app bsegs m2 (sp' + -80) [CB 8 j0] _)). split; [exact FRa2|]. cbn [cells_size csize Nat.add].
      replace (sp' + -80 + Z.of_nat 8) with (sp' + -72) by lia.
      apply (proj2 (rw_cells_app bsegs m2 (sp' + -72) [C8 (wz (ae_DOC E)); C8 (wz 1)] _)). split; [exact REC2|]. cbn [cells_size csize Nat.add].
      replace (sp' + -72 + Z.of_nat 16) with (sp' + -56) by lia.
      apply (proj2 (rw_cells_app bsegs m2 (sp' + -56) [CB 16 b16; C4 (wz code); CB 4 g20] _)). split; [exact RC2|]. cbn [cells_size csize Nat.add].
      replace (sp' + -56 + Z.of_nat 24) with (sp' + -32) by lia. exact FRc2. }
    pose proof (arm_entry_kit RT AF (mkLF usp sp' f lo) E Σ 21 4 idx jr jos t m2 176 LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ART2 AM2 ltac:(lia) NEED176)
      as (ARTM2 & _). cbn [lf_usp lf_S1 lf_F lf_lo] in ARTM2.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { eapply (h21_c4b E OKE sp' m2 0xb239c);
        [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
        | clear - SPA'; Z.div_mod_to_equations; lia| clear; lia| reflexivity
        | apply munch_refl| apply wmono_refl| exact ST2| exact MI2| exact FRM2| exact FR2| reflexivity| exact CODE]. }
    cbv beta. intros ms3 HP3. exact (TAIL m2 ms3 AGB2 ARTM2 AM2 XD2 AUX2 HP3).
  - subst sel. change (tjt 5 + EL_TJTAB_B) with 0xb4af8. eapply evt_cut;
    [ eapply (h21_c5 E OKE sp' (f + 208) m 0xb239c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (tjt 6 + EL_TJTAB_B) with 0xb4bb0. eapply evt_cut;
    [ eapply (h21_c6 E OKE sp' (f + 208) m 0xb239c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
  - subst sel. change (tjt 7 + EL_TJTAB_B) with 0xb4a84. eapply evt_cut;
    [ eapply (h21_c7 E OKE sp' (f + 208) m 0xb239c);
      [rewrite ELO; clear - NEED176; lia| rewrite ELO; clear - LLO; ul| rewrite EHI; clear - SPR; lia| rewrite EHI; clear - SPT; ul
      | clear - SPA'; Z.div_mod_to_equations; lia| clear - FPOS; lia| clear - FLO176; lia| clear - F64; Z.div_mod_to_equations; lia
      | clear; lia| reflexivity
      | exact SHBM| exact SZN| exact AIM| exact SZD| exact SZT
      | exact MU0| exact WM0| exact ST0| exact MI0| exact FRM| exact CE0| exact FR0]
    | cbv beta; intros ms2 HP2; exact (TAIL m ms2 (fun x _ => eq_refl) ARTM AM XD AUX HP2) ].
Qed.
End Arm21.
