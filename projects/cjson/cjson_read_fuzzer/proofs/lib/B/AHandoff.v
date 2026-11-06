(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import
  PropExec AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit StartupHS2Both.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RealizesEqv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RealizesEqv.RegsEqv0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RealizesEqv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport AHandoffJ2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AHandoffTrim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AHandoffTrim.AHandoffSh.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AHandoffTrim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry.MainFactsBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import AMainEntry AHandoffCore.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Instance ahandoff_fx : AS.PropExec.FPState := AS.PropExec.fx0.

Lemma bsegs_BSEGS : BSEGS = bsegs. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition AHOLES (argv : list (list byte)) (h : nat) (E : env) (fs : Fs.Fs) : TSet := spec04 argv fs.

(* [comment removed for export] *)
Definition a_holes_stmt : Prop :=
  forall (sp brk0 mbase : word) (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word),
    valid_sp sp -> valid_brk BSEGS brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> valid_fs fs -> entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw ->
    holes_stmt BSEGS BOTH AsanInit.LIMIT HS_both2
      (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) (AHOLES argv) fs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition ABAND_LO : Z := 0x7fff7000.
Definition ABAND_LEN : Z := 0x100000001000.

(* [comment removed for export] *)
Definition sub_of (bn : zexp * zexp) (b' : zexp) (n' : Z) : bool :=
  match snd bn with
  | ZLit nn =>
      (zexp_eqb (fst bn) b' && (0 <=? nn) && (nn <=? n'))
      || match fst bn with
         | ZAdd b0 (ZLit k) => zexp_eqb b0 b' && (0 <=? k) && (0 <=? nn) && (k + nn <=? n')
         | _ => false
         end
  | _ => false
  end.

Lemma sub_of_sound : forall V bn b' n', sub_of bn b' n' = true ->
  zv V b' <= zv V (fst bn) /\ zv V (fst bn) + zv V (snd bn) <= zv V b' + n'.
Proof.
  intros V [b n] b' n' H. unfold sub_of in H. cbn [fst snd] in *. destruct n as [nn| | | | |]; try discriminate.
  apply orb_prop in H as [H|H].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply zexp_eqb_eq in H1. subst b'.
    apply Z.leb_le in H2. apply Z.leb_le in H3. cbn [zv]. lia.
  - destruct b as [| |b0 k| | |]; try discriminate. destruct k as [k| | | | |]; try discriminate.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [zv]. lia.
Qed.

(* [comment removed for export] *)
Definition band_fact (blo blen : Z) (PF : list pfact) (bn : zexp * zexp) : bool :=
  existsb (fun f => match f with
                    | PDisj b' n' (ZLit c) d => (c =? blo) && (d =? blen) && sub_of bn b' n'
                    | _ => false
                    end) PF.

Lemma band_fact_sound : forall V blo blen PF bn a, Forall (pfact_ok V) PF -> band_fact blo blen PF bn = true ->
  blo <= a < blo + blen -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
  intros V blo blen PF bn a HPF H Ha Hin. unfold band_fact in H. apply existsb_exists in H as (f & Hf & Hm).
  destruct f as [| |b' n' c d|]; try discriminate. destruct c as [c| | | | |]; try discriminate.
  apply andb_prop in Hm as [Hm H3]. apply andb_prop in Hm as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst c d.
  pose proof (sub_of_sound V bn b' n' H3) as [S1 S2].
  pose proof (proj1 (Forall_forall _ _) HPF _ Hf) as D. cbn [pfact_ok zv] in D. lia.
Qed.

(* [comment removed for export] *)
Definition shad_clear (VR : vranges) (PF : list pfact) (bn : zexp * zexp) : bool :=
  range_clear ASHADOWS VR bn || band_fact ABAND_LO ABAND_LEN PF bn.

Lemma shad_clear_sound : forall V VR PF bn a, vr_sound V VR -> Forall (pfact_ok V) PF -> shad_clear VR PF bn = true ->
  (exists s, In s ASHADOWS /\ fst s <= a < snd s) -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
  intros V VR PF bn a HV HPF H HS. unfold shad_clear in H. apply orb_prop in H as [H|H].
  - exact (range_clear_sound V VR ASHADOWS bn a HV H HS).
  - apply (band_fact_sound V ABAND_LO ABAND_LEN PF bn a HPF H).
    (nelim HS 3%nat; intros s Hs Ha). unfold ABAND_LO, ABAND_LEN. cbn in Hs. destruct Hs as [<-|[<-|[]]]; cbn in Ha; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_eqv_mkR_mkst : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte),
  ms_eqv (MS (mkR_of R) bvmap_empty pc (Z_to_bv 32 0) None m (seg_rom bsegs))
         (AS.PropExec.mkst R pc m (AS.PropExec.seg_rom BSEGS)).
Proof.
  intros R pc m. split; [| repeat split; try reflexivity; try apply regs_eqv_refl].
  intros r Hr. cbn [ms_regs MS AS.PropExec.mkst]. rewrite <- (getr_mkR_of R r Hr). apply getr_reg_get. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section J.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfs : valid_fs fs.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Abbreviation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Abbreviation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Abbreviation E0a := (AsanInit.E0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Abbreviation LIM := AsanInit.LIMIT.

  Let AH := argH0_high BPH sp rdraw argv envp uid hw Hsp Hva.
  Let AH2 := argH0_high2 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.

  (* [comment removed for export] *)
  Lemma run_ceil_lo : 0x7fff7f800000 <= bv_unsigned sp - 8388608.
  Proof. pose proof Hsp as (H & _). unfold sp_window_lo in H. lia. Qed.
  Lemma run_ceil_hi : bv_unsigned sp - 8388608 <= 0x7fffff800000.
  Proof. (nelimp Hsp 3%nat; intros _ H _). unfold sp_window_hi in H. lia. Qed.
  Lemma run_ceil_al : (bv_unsigned sp - 8388608) mod 16 = 0.
  Proof. (nelimp Hsp 3%nat; intros _ _ H). Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Definition run_ceil : Ceil := ceil_of_val (bv_unsigned sp - 8388608) run_ceil_lo run_ceil_hi run_ceil_al.
  #[local] Existing Instance run_ceil.

  Lemma run_ceil_val : alloc_ceiling = bv_unsigned sp - 8388608.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma sinv_usp : forall E M, SINV E M -> uE E e_sp0 = bv_unsigned sp.
  Proof.
    intros E M [HE _].
    transitivity (uE E0a e_sp0); [| exact (AsanInit.u_e_sp0 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit)].
    unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
    rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity.
  Qed.

  Section W.
  Variables (w : bool) (hs : acs).
  Hypothesis Hregs : s_regs (a_ss hs) = s_regs (a_ss HS_both2_1).
  Hypothesis Hpc : pc hs = AM_MAIN.
  Hypothesis Hfd : a_fd hs = FdStd.
  Hypothesis Hbrk0 : a_brk hs = EVar both_vmbrk.
  Hypothesis MJ : forallb (mjustify (kn hs) (var_ranges (kn hs)) AM_IMG_LO AM_IMG_HI) (both_mem_facts ++ both_mem_facts_w w) = true.
  Hypothesis PJ : forallb (pjustify (kn hs) (var_ranges (kn hs))) (both_pure_facts ++ both_pure_facts_w w) = true.
  Hypothesis VJ : vis_match (var_ranges (kn hs)) (a_vis hs) both_vis_app = true /\ vis_match (var_ranges (kn hs)) (a_ghost hs) both_ghost = true.
  Hypothesis LJ : ledger_xmatch (var_ranges (kn hs)) (a_maps hs) both_ledger = true.
  Hypothesis CONSTS : a_totsz hs = both_totsz /\ a_ylo hs = both_ylo /\ a_eager hs = both_eager /\ a_abytes hs = both_abytes.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
  Hypothesis HC : cs_ok BSEGS BOTH LIM SINV argH fs E hs R FULL mo.

  #[local] Abbreviation V := (uev E).

  Lemma HSINV : SINV E FULL. Proof. exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
  Lemma USP : uE E e_sp0 = bv_unsigned sp. Proof. exact (sinv_usp E FULL HSINV). Qed.
  Lemma ATOP : atop mo = bv_unsigned sp - 8388608.
  Proof. pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP. unfold atop. rewrite TOP. reflexivity. Qed.
  Lemma HTOP : atop mo = alloc_ceiling. Proof. rewrite ATOP. reflexivity. Qed.
  Lemma HargH_hi : forall a, argH E a = true -> alloc_ceiling <= bv_unsigned a.
  Proof. intros a Ha. pose proof (AH2 E FULL a HSINV Ha) as H. rewrite USP in H. rewrite run_ceil_val. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation mvj := (jvis argH E hs FULL mo).
  #[local] Abbreviation mv := (trim mvj).
  #[local] Abbreviation gg := (g0 LIM E hs).

  Lemma ceil_lt_top : alloc_ceiling < TOP47.
  Proof. rewrite run_ceil_val. pose proof run_ceil_hi. unfold TOP47. lia. Qed.

  Lemma LINV0 : LINV bsegs gg mo (m_vm_materialized mo) mv FULL.
  Proof.
    apply LINV_intro.
    - exact bsegs_no_wx.
    - exact (LOK_of_cs_ok LIM SINV argH fs E hs R FULL mo HC HTOP).
    - exact (BINV_of_cs_ok LIM SINV argH fs E hs R FULL mo HC).
    - exact (matok_of_cs_ok LIM SINV argH fs E hs R FULL mo HC).
    - intros x. destruct (Z.lt_ge_cases (bv_unsigned x) TOP47) as [Hlt|Hge].
      + pose proof (magree_of_cs_ok LIM SINV argH fs E hs R FULL mo HC HTOP HargH_hi x) as M. unfold lmem in *.
        rewrite (trim_below mvj x Hlt). exact M.
      + right. split; [unfold trim; destruct (Z.leb_spec0 TOP47 (bv_unsigned x)); [reflexivity| lia]|].
        split; [apply noseg_iff_hull; unfold TOP47 in Hge; lia|].
        left. destruct (lzf mo x) eqn:Ez; [|reflexivity]. exfalso.
        pose proof (lazy_below_ceil LIM SINV argH fs E hs R FULL mo HC HTOP x (lzf_lazy mo x Ez)). pose proof ceil_lt_top. lia.
    - intros x Hl Hw. apply trim_none. exact (hidden_of_cs_ok argH E hs FULL mo x Hl Hw).
    - intros x Hx. apply (vdom_of_cs_ok LIM SINV argH fs E hs R FULL mo HC HTOP HargH_hi x).
      intros Hn. apply Hx. apply trim_none. exact Hn.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vars_ok : amain_vars V sp brk0 rdraw argv envp uid hw.
  Proof.
    pose proof HSINV as [Hev _].
    (nelimp (AsanInit.uE0 BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) 7%nat; intros U0 U6 U1 U2 U3 U4 U5).
    pose proof (AsanInit.uE0_sp BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U10.
    pose proof (AsanInit.uE0_L1 BPH sp rdraw brk0 argv envp uid hw Hva) as U7.
    pose proof (AsanInit.uE0_uid BPH sp rdraw brk0 argv envp uid hw) as U8.
    pose proof (AsanInit.uE0_hw BPH sp rdraw brk0 argv envp uid hw) as U9.
    unfold APS.uE in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10. cbn [edenot] in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10.
    assert (PIN : forall n z, (n < 11)%nat -> bv_unsigned (ev E0a n) = z -> V n = z).
    { intros n z Hn Hz. unfold uev. rewrite (Hev n) by (unfold NX0; lia). exact Hz. }
    pose proof (PIN 0%nat _ ltac:(lia) U0) as P0. pose proof (PIN 6%nat _ ltac:(lia) U6) as P6.
    pose proof (PIN 1%nat _ ltac:(lia) U1) as P1. pose proof (PIN 2%nat _ ltac:(lia) U2) as P2.
    pose proof (PIN 3%nat _ ltac:(lia) U3) as P3. pose proof (PIN 4%nat _ ltac:(lia) U4) as P4.
    pose proof (PIN 5%nat _ ltac:(lia) U5) as P5. pose proof (PIN 7%nat _ ltac:(lia) U7) as P7.
    pose proof (PIN 8%nat _ ltac:(lia) U8) as P8. pose proof (PIN 9%nat _ ltac:(lia) U9) as P9.
    pose proof (PIN 10%nat _ ltac:(lia) U10) as P10.
    clear U0 U6 U1 U2 U3 U4 U5 U7 U8 U9 U10.
    assert (Hal : bv_unsigned sp mod 16 = 0) by ((nelimp Hsp 3%nat; intros _ _ H); exact H).
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    unfold amain_vars, IX_S1, IX_S2, IX_SP, IX_ARGC, IX_ENVC, IX_L0, IX_L1, IX_W, IX_BRK, IX_UID, IX_HW. cbv zeta.
    split; [intros n; apply uev_range|].
    split; [exact P0|]. split; [exact P6|]. split; [exact P10|].
    split. { rewrite P0, P6, P10. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hid_keep : forall a, APS.hid BOTH argH E hs mo a = false -> mvj a = FULL a.
  Proof.
    intros a Hh. unfold APS.hid in Hh. apply orb_false_iff in Hh as [Ea Ev]. apply negb_false_iff in Ev.
    unfold jvis, keepb. rewrite Ev, Ea. cbn [orb].
    destruct (in_rangesb (m_vm_lazy mo) a) eqn:El; [| reflexivity].
    rewrite (vis_lazy_win LIM SINV argH fs E hs R FULL mo HC HTOP a Ev El). reflexivity.
  Qed.

  Lemma Mr_mv : mrestrict (APS.hid BOTH argH E hs mo) mvj = mrestrict (APS.hid BOTH argH E hs mo) FULL.
  Proof.
    apply functional_extensionality. intros a. unfold mrestrict.
    destruct (APS.hid BOTH argH E hs mo a) eqn:Eh; [reflexivity | apply hid_keep; exact Eh].
  Qed.

  Lemma HIDrom : forall a, APS.hid BOTH argH E hs mo a = true -> seg_rom bsegs a = None.
  Proof.
    intros a Ha. apply (APS.seg_rom_off_hull BSEGS BOTH both_in_hull).
    unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
    - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold CEIL in Hc.
      apply andb_false_iff. right. apply Z.ltb_ge. lia.
    - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha.
  Qed.

  Lemma HULLvis : forall a, AM_IMG_LO <= bv_unsigned a < AM_IMG_HI -> APS.hid BOTH argH E hs mo a = false.
  Proof.
    intros a Ha. apply (APS.hid_hull BOTH both_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold AM_IMG_LO, AM_IMG_HI in Ha.
    apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  Qed.

  Lemma facts_okj : Forall (mfact_ok bsegs V mvj) (both_mem_facts ++ both_mem_facts_w w)
                   /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w).
  Proof.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as KOK. unfold APS.Mr in KOK. rewrite <- Mr_mv in KOK.
    exact (export_sound bsegs E (APS.hid BOTH argH E hs mo) mvj (kn hs) AM_IMG_LO AM_IMG_HI KOK HIDrom HULLvis _ _ MJ PJ).
  Qed.

  (* [comment removed for export] *)
  Lemma fit_BL : bv_unsigned sp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 8 * amain_W sp rdraw argv envp uid hw + 200 <= TOP47.
  Proof.
    pose proof (AsanInit.usp_fit BPH sp rdraw argv envp uid hw Hfit) as F.
    (nelimp (AsanInit.W_range BPH sp rdraw argv envp uid hw Hva Hve) 3%nat; intros W1 W2 W3).
    unfold amain_W. unfold BothPlanImages.BPH in *. unfold TOP47. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis FB : forallb (fbelow (pvranges both_pure_facts)) (both_mem_facts ++ both_mem_facts_w w) = true.

  Lemma facts_ok : Forall (mfact_ok bsegs V mv) (both_mem_facts ++ both_mem_facts_w w)
                   /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w).
  Proof.
    destruct facts_okj as [HMF HPF]. split; [| exact HPF].
    pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
    pose proof (pvranges_sound V both_pure_facts (fun n => uev_range E n) HPFc) as HVRp.
    apply (mfacts_trim bsegs V (pvranges both_pure_facts) HVRp (fun n => proj1 (uev_range E n))); [| exact HMF | exact FB].
    (nelimp vars_ok 8%nat; intros VR P0 P6 P10 PSP P1 P2 _). pose proof fit_BL as F.
    pose proof (AsanInit.W_range BPH sp rdraw argv envp uid hw Hva Hve) as (W1 & _).
    unfold IX_S1, IX_S2, IX_SP, IX_ARGC, IX_ENVC in *. unfold amain_W in F. unfold BothPlanImages.BPH in *.
    cbn [lden_l BLl]. unfold BLc. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma args_ok : amain_args sp rdraw argv envp uid hw mv.
  Proof.
    pose proof HSINV as [_ Hhid].
    intros a Ha.
    assert (Hg : argH E a = true).
    { pose proof (AsanInit.usp_fit BPH sp rdraw argv envp uid hw Hfit) as F.
      (nelimp (AsanInit.W_range BPH sp rdraw argv envp uid hw Hva Hve) 3%nat; intros W1 W2 W3).
      pose proof (AsanInit.len_av BPH sp rdraw argv envp uid hw Hva) as LA. pose proof (AsanInit.len_ev BPH sp rdraw argv envp uid hw Hve) as LE.
      unfold amain_argblock, amain_W in Ha. cbv zeta in Ha.
      unfold argH0. cbv zeta. unfold BothPlanImages.BPH in *.
      apply orb_true_intro. destruct Ha as [Ha|Ha]; [left|right]; apply andb_true_intro; split;
        first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    rewrite trim_below.
    2:{ pose proof fit_BL as F. unfold amain_argblock in Ha. cbv zeta in Ha.
        assert (W0 : 0 <= amain_W sp rdraw argv envp uid hw).
        { pose proof (AsanInit.W_range BPH sp rdraw argv envp uid hw Hva Hve) as (W1 & _). unfold amain_W. unfold BothPlanImages.BPH in *. exact W1. }
        pose proof (Zle_0_nat (length argv)). pose proof (Zle_0_nat (length envp)). lia. }
    rewrite (jvis_arg LIM SINV argH fs E hs R FULL mo HC HTOP HargH_hi a Hg). apply Hhid. exact Hg.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma regs_main : amain_regs V sp R.
  Proof.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR. unfold regs_ok in HR.
    (nelimp vars_ok 7%nat; intros VR P0 P6 P10 PSP P1 _).
    unfold IX_S1, IX_S2, IX_SP, IX_ARGC in *.
    assert (G : forall (r : Prelude.reg) ze, zexp_of (sr_get (s_regs (a_ss HS_both2_1)) r) = Some ze ->
                  forall z, zv V ze = z -> AS.PropExec.getr R r = Z_to_bv 64 z).
    { intros r ze Hz z Hv. rewrite (HR r), Hregs. rewrite <- (zexp_of_sound E _ ze Hz). f_equal. exact Hv. }
    unfold amain_regs. cbv zeta. unfold IX_ARGC, AM_RA, AM_GP, AM_TP, AM_MAIN.
    repeat split; (eapply G; [reflexivity | cbn [zv]; lia]).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma HVR : vr_sound V (var_ranges (kn hs)).
  Proof. exact (var_ranges_sound BSEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.

  Lemma HVISa : Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
             bv_unsigned (edenot E (fst p)) = zv V (fst bn) /\ bv_unsigned (edenot E (snd p)) = zv V (snd bn) /\ 0 <= zv V (snd bn))
             (a_vis hs) both_vis_app.
  Proof. exact (vis_match_sound E _ _ _ HVR (proj1 VJ)). Qed.
  Lemma HVISg : Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
             bv_unsigned (edenot E (fst p)) = zv V (fst bn) /\ bv_unsigned (edenot E (snd p)) = zv V (snd bn) /\ 0 <= zv V (snd bn))
             (a_ghost hs) both_ghost.
  Proof. exact (vis_match_sound E _ _ _ HVR (proj2 VJ)). Qed.

  Lemma HAL : allowA BOTH E hs = allow_of AM_SHOFF V both_vis.
  Proof.
    pose proof (Forall2_app HVISa HVISg) as HVIS. change (both_vis_app ++ both_ghost) with both_vis in HVIS.
    exact (allowA_allow_of BOTH E _ _ HVIS).
  Qed.

  Lemma HLD : ledger_den V both_ledger (vm_maps (m_vmmaps mo)).
  Proof. exact (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.
  Lemma HKD : Forall (lentry_kind_ok V mo) both_ledger.
  Proof. exact (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.

  Lemma model_ok : amodel V sp fs mo.
  Proof.
    (nelimp CONSTS 4%nat; intros Ct Cy Ce Ca).
    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
    pose proof ATOP as ATOP'. pose proof HLD as HLD'. pose proof HKD as HKD'.
    assert (Hal : bv_unsigned sp mod 16 = 0) by ((nelimp Hsp 3%nat; intros _ _ H); exact H).
    pose proof (AsanInit.usp_lo sp Hsp) as LO.
    pose proof (AsanInit.usp_hi BPH sp rdraw argv envp uid hw Hva Hve Hfit) as HI.
    destruct HC. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
    constructor.
    + exact co_halt0.
    + exact co_fds0.
    + exact co_fs0.
    + exact co_res0.
    + exact co_limit0.
    + rewrite co_brk0. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite co_brk0 in co_sbrk0. cbn [edenot] in co_sbrk0. exact co_sbrk0.
    + exact USPW.
    + split; [exact LO|]. split; [lia| exact Hal].
    + exact HLD'.
    + exact HKD'.
    + apply seps_ivs_sep. exact co_seps0.
    + eapply Forall_impl; [|exact co_bounds0]. cbv beta. intros iv nelH_; (nelim nelH_ 6%nat; intros B1 B2 B3 B4 B5 B6).
      unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP' in B6. unfold AM_IMG_LO, AM_IMG_HI. repeat split; assumption.
    + eapply Forall_impl; [|exact co_lazyb0]. cbv beta. intros iv (B5 & B6).
      unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP' in B6. unfold AM_IMG_LO, AM_IMG_HI. split; assumption.
    + (nelim co_wf0 3%nat; intros _ Wn _). apply Forall_forall. intros iv Hiv. exact (Wn iv Hiv).
    + intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_nasub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
    + rewrite <- Ct. exact co_totsz0.
    + eapply Forall_impl; [|exact co_naal0]. cbv beta. intros iv nelH_; (nelim nelH_ 3%nat; intros _ _ P). exact P.
  Qed.

  (* [comment removed for export] *)
  Lemma ghost_ok : gg = mkG (amain_windows V) AMAIN_R0.
  Proof.
    (nelimp CONSTS 4%nat; intros Ct Cy Ce Ca).
    unfold g0, G0, R0, amain_windows, AMAIN_R0. rewrite HAL, Ce, Ca. f_equal.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma win_eq : G0 E hs = amain_windows V.
  Proof. unfold G0, amain_windows. rewrite HAL. reflexivity. Qed.

  Lemma gwin_ok : amain_gwin V mv mo.
  Proof.
    intros x Hw Hz HD. rewrite <- win_eq in Hw.
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2^64) in Rx.
    pose proof (lzf_lazy mo x Hz) as Hl.
    rewrite trim_below
      by (pose proof (lazy_below_ceil LIM SINV argH fs E hs R FULL mo HC HTOP x Hl); pose proof ceil_lt_top; lia).
    destruct facts_okj as [HMF HPF].
    pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _]. pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
    assert (HD' : (exists s, In s ASHADOWS /\ fst s <= bv_unsigned x < snd s)
                  \/ 4096 * V IX_SSTORE <= bv_unsigned x < 4096 * V IX_SSTORE + 8388608).
    { destruct HD as [D|[D|D]]; [left; exists (0x7fff7000, 0x8fff7000) | left; exists (0x2008fff7000, 0x10007fff8000) | right; exact D];
        (split; [cbn; tauto | cbn [fst snd]; lia]). }
    clear HD. destruct HD' as [HSS | D3].
    2:{ (* [comment removed for export] *)
      pose proof (mwr_find bsegs V mvj both_mem_facts (ZMul (ZLit 4096) (ZV IX_SSTORE)) 8388608 HMFc ltac:(vm_compute; reflexivity)) as W.
      cbn [zv] in W. exact (gwin_wr LIM SINV argH fs E hs R FULL mo HC HTOP x _ _ W D3 Hl). }
    (* [comment removed for export] *)
    pose proof (pvranges_sound V both_pure_facts (fun n => uev_range E n) HPFc) as HVRp.
    assert (CLRv : forallb (shad_clear (pvranges both_pure_facts) both_pure_facts) both_vis_app = true) by (vm_compute; reflexivity).
    assert (CLRg : forallb (shad_clear (pvranges both_pure_facts) both_pure_facts) both_ghost = true) by (vm_compute; reflexivity).
    assert (SHC : forallb (sh_cover AM_SHOFF both_mem_facts) both_vis_app = true) by (vm_compute; reflexivity).
    destruct (APS.in_allow BOTH E hs (bv_unsigned x)) eqn:Ea.
    - unfold APS.in_allow in Ea. apply orb_prop in Ea as [Ea|Ea].
      + (* [comment removed for export] *)
        exfalso. unfold APS.in_vis in Ea. apply existsb_exists in Ea as (p & Hp & Xp).
        apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
        (nelim (Forall2_In_l _ _ _ _ HVISa Hp) 5%nat; intros bn Hbn E1 E2 E3). unfold APS.uE in X1, X2. rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
        apply (shad_clear_sound V _ both_pure_facts bn (bv_unsigned x) HVRp HPFc (proj1 (forallb_forall _ _) CLRv bn Hbn) HSS). lia.
      + (* [comment removed for export] *)
        unfold APS.in_sh in Ea. apply existsb_exists in Ea as (p & Hp & Xp).
        apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.sh_lo, APS.sh_hi, APS.uE in X1, X2.
        (nelim (Forall2_In_l _ _ _ _ HVISa Hp) 5%nat; intros bn Hbn E1 E2 E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
        change (shadow_off BOTH) with AM_SHOFF in X1, X2.
        (nelim (sh_cover_sound bsegs AM_SHOFF V mvj both_mem_facts bn (bv_unsigned x) HMFc (proj1 (forallb_forall _ _) SHC bn Hbn) (conj X1 X2)) 4%nat; intros lo len W Rg)
.
        exact (gwin_wr LIM SINV argH fs E hs R FULL mo HC HTOP x lo len W Rg Hl).
    - (* [comment removed for export] *)
      assert (Hg : APS.in_ghost E hs (bv_unsigned x) = false).
      { unfold APS.in_ghost. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
        apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.uE in X1, X2.
        (nelim (Forall2_In_l _ _ _ _ HVISg Hp) 5%nat; intros bn Hbn E1 E2 E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2.
        apply (shad_clear_sound V _ both_pure_facts bn (bv_unsigned x) HVRp HPFc (proj1 (forallb_forall _ _) CLRg bn Hbn) HSS). lia. }
      rewrite (gwin_hidden LIM SINV argH fs E hs R FULL mo HC HTOP x Hz Hw Ea Hg). discriminate.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma entry_ok : a_main_entry w V sp brk0 rdraw argv envp uid hw fs R mv mo gg.
  Proof.
    unfold a_main_entry. destruct facts_ok as [HMF HPF].
    split; [exact vars_ok|]. split; [exact regs_main|]. split; [exact HMF|]. split; [exact HPF|].
    split; [exact args_ok|]. split; [exact model_ok|]. split; [exact ghost_ok|]. split; [exact gwin_ok|].
    intros a Ha. unfold trim. destruct (Z.leb_spec0 TOP47 (bv_unsigned a)) as [_|N]; [reflexivity| unfold TOP47 in N; lia].
  Qed.

  Theorem hole_ok_of_main : a_main_stmt ->
    AS.SpinAlg.srealizes BSEGS (APS.cfg_of BSEGS R (pc hs) FULL mo) (AHOLES argv 0%nat E (m_fs mo)).
  Proof.
    intros HM.
    pose proof (HM run_ceil w V sp brk0 mbase rdraw argv envp uid hw fs R mv mo gg Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw run_ceil_val entry_ok) as HR.
    pose proof LINV0 as HL.
    specialize (HR FULL (m_vm_materialized mo)). cbn [ms_mem MS] in HR. specialize (HR HL).
    rewrite real_of_self, msw_MS in HR.
    unfold AHOLES. rewrite (co_fs _ _ _ _ _ _ _ _ _ _ _ HC).
    rewrite Hpc. unfold APS.cfg_of.
    apply srealizes_LRT_AS. eapply srealizes_ms_eqv; [apply ms_eqv_mkR_mkst| exact HR].
  Qed.

  End W.

  (* [comment removed for export] *)
  Theorem hole1_ok : a_main_stmt -> forall E R FULL mo,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both2_1 R FULL mo ->
    AS.SpinAlg.srealizes BSEGS (APS.cfg_of BSEGS R (pc HS_both2_1) FULL mo) (AHOLES argv 1%nat E (m_fs mo)).
  Proof.
    intros HM E R FULL mo HC.
    exact (hole_ok_of_main true HS_both2_1 eq_refl eq_refl eq_refl eq_refl both_mem_facts_justified_w1 both_pure_facts_justified_w1
             both_vis_justified_w1 both_ledger_justified_w1 both_consts_w1 E R FULL mo HC ltac:(vm_compute; reflexivity) HM).
  Qed.
  Theorem hole2_ok : a_main_stmt -> forall E R FULL mo,
    cs_ok BSEGS BOTH LIM SINV argH fs E HS_both2_2 R FULL mo ->
    AS.SpinAlg.srealizes BSEGS (APS.cfg_of BSEGS R (pc HS_both2_2) FULL mo) (AHOLES argv 2%nat E (m_fs mo)).
  Proof.
    intros HM E R FULL mo HC.
    exact (hole_ok_of_main false HS_both2_2 eq_refl eq_refl eq_refl eq_refl both_mem_facts_justified_w2 both_pure_facts_justified_w2
             both_vis_justified_w2 both_ledger_justified_w2 both_consts_w2 E R FULL mo HC ltac:(vm_compute; reflexivity) HM).
  Qed.
End J.

(* [comment removed for export] *)
Theorem a_holes_of : a_main_stmt -> a_holes_stmt.
Proof.
  intros HM sp brk0 mbase rdraw argv envp fs uid hw Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw h ch Hch E R FULL mo HC.
  destruct h as [|[|[|h]]]; cbn in Hch; try discriminate Hch; injection Hch as <-.
  - exact (hole1_ok sp brk0 mbase rdraw argv envp fs uid hw Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw HM E R FULL mo HC).
  - exact (hole2_ok sp brk0 mbase rdraw argv envp fs uid hw Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw HM E R FULL mo HC).
Qed.
