(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsHSTab AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk ASEGS brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Vfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Hh : HSF_asan h = Some ch.
  Hypothesis HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                        (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.
  #[local] Notation g := (hole_granted h).
  #[local] Notation cls := (hole_class h).
  #[local] Notation X := (Xof g E).
  #[local] Notation brk0z := (bv_unsigned brk0).
  #[local] Notation sp0z := (bv_unsigned sp0).
  #[local] Notation argc := (Z.of_nat (length (in_argv inp))).
  (* [comment removed for export] *)
  #[local] Notation VM := (pm_vmem (bv_unsigned sp0) (bv_unsigned brk0) (Xof g E) FULL).
  (* [comment removed for export] *)
  Let MC : PMC sp0 rdraw inp brk0z X FULL := PMC_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC.
  Let SOK : pm_syms_ok sp0z brk0z 0 X := pm_syms_ok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC.

  (* [comment removed for export] *)
  Ltac prepI :=
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP);
    let B := fresh "B" in let Bg := fresh "Bg" in let B13 := fresh "B13" in
    pose proof (KB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as B; cbv zeta in B; destruct B as [B B13];
    unfold pm_kernel_placed in B; rewrite Forall_app in B; destruct B as [B Bg];
    unfold GHZ, Xof in B, Bg, B13;
    cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_b24 ps_a1 ps_a2 ps_a3 ps_g1 ps_g2 ps_g3 ps_g4 ps_granted] in B, Bg, B13;
    repeat (apply Forall_cons_iff in B as [? B]);
    (let BG4 := fresh "BG4" in let BG3 := fresh "BG3" in let BG2 := fresh "BG2" in let BG1 := fresh "BG1" in
     apply Forall_cons_iff in B13 as [BG4 B13]; apply Forall_cons_iff in B13 as [BG3 B13]; apply Forall_cons_iff in B13 as [BG2 B13];
     apply Forall_cons_iff in B13 as [BG1 B13]; apply Forall_inv in B13);
    cbn [fst snd] in *;
    pose proof (u64_range brk0) as ?Hb0; pose proof (u64_range sp0) as ?Hs0;
    pose proof (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL) as ?HRIv.
  Ltac zlistsI :=
    unfold pm_vmem in *;
    unfold PM_LAZY, PM_S, PM_ZR, PM_NOACC, PM_MAPS, PM_REM, VISZ, VISZ0, GHZ, SW;
    rewrite ?(RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl) by assumption;
    unfold Xof in *; cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_b24 ps_a1 ps_a2 ps_a3 ps_g1 ps_g2 ps_g3 ps_g4 ps_granted map app fst snd] in *.

  (* [comment removed for export] *)
  #[local] Notation kp_apart := (AsMainIface.kp_apart sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_apart_ne := (AsMainIface.kp_apart_ne sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_facts := (AsMainIface.kp_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_align := (AsMainIface.kp_align sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pd_facts := (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b06 := (AsMainIface.kp_b06 h E) (only parsing).
  #[local] Notation kp_b08 := (AsMainIface.kp_b08 h E) (only parsing).
  #[local] Notation kp_b22 := (AsMainIface.kp_b22 h E) (only parsing).
  #[local] Notation vm_full := (AsMainIface.vm_full sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_img := (AsMainIface.vm_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_S := (AsMainIface.vm_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_obj := (AsMainIface.vm_obj sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_ri := (AsMainIface.vm_ri sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_stack := (AsMainIface.vm_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_brk := (AsMainIface.vm_brk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation seg_rom_above := (AsMainIface.seg_rom_above sp0 brk0 inp) (only parsing).
  #[local] Notation seg_rom_below := (AsMainIface.seg_rom_below sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_above := (AsMainIface.mrd_above sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_outside := (AsMainIface.mrd_outside sp0 brk0 inp) (only parsing).
  #[local] Notation vrange := (AsMainIface.vrange sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_sub := (AsMainIface.vr_sub sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_img := (AsMainIface.vr_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_stack := (AsMainIface.vr_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation G_cases := (AsMainIface.G_cases sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zinP_of_In := AsMainIface.zinP_of_In (only parsing).
  #[local] Notation vr_kobj_gen := (AsMainIface.vr_kobj_gen sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b04 := (AsMainIface.kp_b04 h E) (only parsing).
  #[local] Notation kp_b05 := (AsMainIface.kp_b05 h E) (only parsing).
  #[local] Notation kp_b09 := (AsMainIface.kp_b09 h E) (only parsing).
  #[local] Notation kp_b10 := (AsMainIface.kp_b10 h E) (only parsing).
  #[local] Notation kp_b11 := (AsMainIface.kp_b11 h E) (only parsing).
  #[local] Notation kp_b12 := (AsMainIface.kp_b12 h E) (only parsing).
  #[local] Notation kp_b16 := (AsMainIface.kp_b16 h E) (only parsing).
  #[local] Notation kp_b20 := (AsMainIface.kp_b20 h E) (only parsing).
  #[local] Notation kp_b21 := (AsMainIface.kp_b21 h E) (only parsing).
  #[local] Notation kp_b23 := (AsMainIface.kp_b23 h E) (only parsing).
  #[local] Notation kp_b24 := (AsMainIface.kp_b24 h E) (only parsing).
  #[local] Notation vr_b04 := (AsMainIface.vr_b04 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b05 := (AsMainIface.vr_b05 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b09 := (AsMainIface.vr_b09 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b10 := (AsMainIface.vr_b10 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b11 := (AsMainIface.vr_b11 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b12 := (AsMainIface.vr_b12 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b16 := (AsMainIface.vr_b16 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b20 := (AsMainIface.vr_b20 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b21 := (AsMainIface.vr_b21 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b23 := (AsMainIface.vr_b23 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b24 := (AsMainIface.vr_b24 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_sw := (AsMainIface.vm_sw sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_b22 := (AsMainIface.vm_b22 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation world_ok_X := (AsMainIface.world_ok_X sp0 h E) (only parsing).
  #[local] Notation bytes_main := (AsMainIface.bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation word_main := (AsMainIface.word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zero_main := (AsMainIface.zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fill_main := (AsMainIface.fill_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation bytes_at_const := (AsMainIface.bytes_at_const sp0 brk0 inp) (only parsing).
  #[local] Notation u8arr_const := (AsMainIface.u8arr_const sp0 brk0 inp) (only parsing).
  #[local] Notation bytes_at_constZ := (AsMainIface.bytes_at_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_img := (AsMainIface.rw_cells_img sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_above := (AsMainIface.rw_cells_above sp0 brk0 inp) (only parsing).
  #[local] Notation cellsZ := AsMainIface.cellsZ (only parsing).
  #[local] Notation cells_wfb := AsMainIface.cells_wfb (only parsing).
  #[local] Notation cells_wfb_sound := AsMainIface.cells_wfb_sound (only parsing).
  #[local] Notation map_b8_unsigned := AsMainIface.map_b8_unsigned (only parsing).
  #[local] Notation map_b8_cellsZ := AsMainIface.map_b8_cellsZ (only parsing).
  #[local] Notation length_cellsZ := AsMainIface.length_cellsZ (only parsing).
  #[local] Notation img_cells_check := AsMainIface.img_cells_check (only parsing).
  #[local] Notation img_cells_main := (AsMainIface.img_cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation lowsh_vm := (AsMainIface.lowsh_vm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation lowsh_vis := (AsMainIface.lowsh_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation u8arr_constZ := (AsMainIface.u8arr_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation fact_ivl := AsMainIface.fact_ivl (only parsing).
  #[local] Notation ivls_of := AsMainIface.ivls_of (only parsing).
  #[local] Notation cover_sweep := AsMainIface.cover_sweep (only parsing).
  #[local] Notation cover_check := AsMainIface.cover_check (only parsing).
  #[local] Notation cover_sweep_sound := (AsMainIface.cover_sweep_sound sp0 brk0 inp) (only parsing).
  #[local] Notation ivls_of_In := AsMainIface.ivls_of_In (only parsing).
  #[local] Notation Mr_some' := (AsMainIface.Mr_some' sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_nonnull := (AsMainIface.Mr_nonnull sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation uE_lit' := (AsMainIface.uE_lit' E) (only parsing).
  #[local] Notation estart_lit := (AsMainIface.estart_lit sp0 brk0 inp E) (only parsing).
  #[local] Notation fact_ivl_sound := (AsMainIface.fact_ivl_sound sp0 brk0 rdraw inp ch E R FULL model HC) (only parsing).
  #[local] Notation cover_main := (AsMainIface.cover_main sp0 brk0 rdraw inp h ch E R FULL model Hh HC) (only parsing).
  #[local] Notation lowsh_stk := (AsMainIface.lowsh_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_word_main := (AsMainIface.img_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zscanN := AsMainIface.zscanN (only parsing).
  #[local] Notation zscanN_sound := (AsMainIface.zscanN_sound sp0 brk0 inp) (only parsing).
  #[local] Notation segment_byte_at_zero1 := (AsMainIface.segment_byte_at_zero1 sp0 brk0 inp) (only parsing).
  #[local] Notation obj_word_main := (AsMainIface.obj_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_bytes_main := (AsMainIface.obj_bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_zero_main := (AsMainIface.obj_zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation world_uw := (AsMainIface.world_uw sp0 h) (only parsing).
  #[local] Notation rw_cells_cons1 := AsMainIface.rw_cells_cons1 (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation CXV a := (cx_val sp0z brk0z X a).

  (* [comment removed for export] *)
  Ltac csz := cbn [cells_size csize cells_bytes cbytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map] in *.
  Ltac cszl := rewrite ?length_cellsZ in * by (cbn; tauto); csz.

  (* [comment removed for export] *)
  Definition shw_cells_check (A : Z) (cs : list cell) : bool :=
    cells_wfb cs && forallb (fun b => Z.eqb (bv_unsigned b) 0) (cells_bytes cs)
    && Z.leb (SHOFF + 0x10000 / 8) A && Z.leb (A + Z.of_nat (cells_size cs)) (SHOFF + 0xc04000 / 8)
    && zero_check (CAbs, A) (Z.of_nat (cells_size cs)).
  Lemma shw_cells_main : forall A cs, shw_cells_check A cs = true -> rw_cells asegs VM A cs.
  Proof.
    intros A cs H. unfold shw_cells_check in H. apply andb_prop in H as [H HZ]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1].
    apply andb_prop in H as [H0 HB]. apply cells_wfb_sound in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (cells_bytes_length cs H0) as HL.
    assert (ZB : forall z, A <= z < A + Z.of_nat (cells_size cs) -> VM (wa z) = Some (b8 0)).
    { intros z Hz. refine (zero_main w_all (CAbs, A) (Z.of_nat (cells_size cs)) HZ (world_ok_all _ _) _ _ z _).
      - unfold SHOFF in *. lia.
      - intros y Hy. apply lowsh_vm. revert Hy. pmc_simpl. unfold SHOFF in *. lia.
      - pmc_simpl. lia. }
    apply rw_cells_above; [exact H0 | unfold SHOFF in *; lia | unfold SHOFF in *; lia |].
    apply bytes_at_of_nth; [unfold SHOFF in *; lia | rewrite HL; unfold SHOFF in *; lia |].
    intros i Hi. rewrite HL in Hi. unfold mrd. rewrite (ZB (A + Z.of_nat i) ltac:(lia)).
    destruct (nth_error (cells_bytes cs) i) as [b|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    pose proof (proj1 (forallb_forall _ _) HB b (nth_error_In _ _ Hn)) as Hb. apply Z.eqb_eq in Hb.
    f_equal. unfold b8. rewrite <- Hb. apply definitions.Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma cellrows_main : forall L : list (Z * list cell),
    forallb (fun ac => img_cells_check (fst ac) (snd ac) || shw_cells_check (fst ac) (snd ac)) L = true ->
    Forall (fun ac => rw_cells asegs VM (fst ac) (snd ac)) L.
  Proof.
    intros L HL. apply Forall_forall. intros ac Hin. pose proof (proj1 (forallb_forall _ _) HL ac Hin) as H. cbn beta in H.
    apply orb_prop in H as [H|H]; [apply img_cells_main; exact H | apply shw_cells_main; exact H].
  Qed.
  Lemma aconst_cells_check : forallb (fun ac => img_cells_check (fst ac) (snd ac) || shw_cells_check (fst ac) (snd ac)) aconst_cells = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  Lemma aconst_cells_main : Forall (fun ac => rw_cells asegs VM (fst ac) (snd ac)) aconst_cells.
  Proof. exact (cellrows_main aconst_cells aconst_cells_check). Qed.

  (* [comment removed for export] *)
  Definition gshadow_check (gl : Z * Z * Z) : bool :=
    let '(beg, sz, szrz) := gl in
    let S := SHOFF + beg / 8 in
    Z.leb 0x10000 beg && Z.leb (beg + szrz) 0xc04000 && Z.eqb (beg mod 8) 0 && Z.leb 0 sz && Z.leb (8 * nsh sz) szrz && Z.eqb (szrz mod 8) 0
    && (Z.eqb (sz / 8) 0 || zero_check (CAbs, S) (sz / 8))
    && (if Z.eqb (sz mod 8) 0 then true else bytes_check (CAbs, S + sz / 8) [sz mod 8])
    && (Z.eqb ((szrz - 8 * nsh sz) / 8) 0 || fill_check (CAbs, S + nsh sz) ((szrz - 8 * nsh sz) / 8) 0xf9).   (* [comment removed for export] *)

  Lemma gshadow_main : forall gl, gshadow_check gl = true -> AGLOBAL_SH VM gl.
  Proof.
    intros [[beg sz] szrz] H. unfold gshadow_check in H.
    apply andb_prop in H as [H HF]. apply andb_prop in H as [H HP]. apply andb_prop in H as [H HZ].
    apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.eqb_eq in H6.
    assert (HP' : sz mod 8 <> 0 -> bytes_check (CAbs, SHOFF + beg / 8 + sz / 8) [sz mod 8] = true).
    { revert HP. destruct (Z.eqb_spec (sz mod 8) 0) as [E8|E8]; intros HP NE; [lia | exact HP]. }
    clear HP. rename HP' into HP.
    assert (HZ' : sz / 8 <> 0 -> zero_check (CAbs, SHOFF + beg / 8) (sz / 8) = true).
    { revert HZ. destruct (Z.eqb_spec (sz / 8) 0) as [E8|E8]; intros HZ NE; [lia | exact HZ]. }
    clear HZ. rename HZ' into HZ.
    assert (HF' : (szrz - 8 * nsh sz) / 8 <> 0 -> fill_check (CAbs, SHOFF + beg / 8 + nsh sz) ((szrz - 8 * nsh sz) / 8) 0xf9 = true).
    { revert HF. destruct (Z.eqb_spec ((szrz - 8 * nsh sz) / 8) 0) as [E8|E8]; intros HF NE; [lia | exact HF]. }
    clear HF. rename HF' into HF.
    unfold AGLOBAL_SH, SHAD. split; [lia|]. split; [exact H3|]. unfold sh. rewrite ASHADOW_BASE_val. fold SHOFF.
    assert (VIS : forall z, SHOFF + beg / 8 <= z < SHOFF + (beg + szrz) / 8 -> VM (wa z) = FULL (wa z)) by (intros z Hz; apply lowsh_vm; unfold SHOFF in *; lia).
    assert (VSH : forall z, SHOFF + beg / 8 <= z < SHOFF + (beg + szrz) / 8 -> visibleZ sp0z brk0z argc X z) by (intros z Hz; apply lowsh_vis; unfold SHOFF in *; lia).
    assert (NSH : nsh sz = sz / 8 + (if Z.eqb (sz mod 8) 0 then 0 else 1)).
    { unfold nsh. destruct (Z.eqb_spec (sz mod 8) 0); lia. }
    assert (LSH : Z.of_nat (length (AsShadow.shadow_of sz)) = nsh sz) by (apply shadow_of_length; lia).
    unfold global_shadow, poison_bytes. split.
    - (* [comment removed for export] *)
      apply bytes_at_app. rewrite LSH. split; [unfold AsShadow.shadow_of; apply bytes_at_app; rewrite repeat_length, Z2Nat.id by lia; split|].
      + apply bytes_at_constZ; [unfold SHOFF; lia | lia | unfold SHOFF, nsh in *; lia |].
        intros z Hz. assert (NZ : sz / 8 <> 0) by lia.
        apply (zero_main w_all (CAbs, SHOFF + beg / 8) (sz / 8) (HZ NZ) (world_ok_all _ _) ltac:(unfold nsh in *; lia)); [|revert Hz; pmc_simpl; lia].
        intros y Hy. apply VIS. revert Hy. pmc_simpl. unfold nsh in *. lia.
      + destruct (Z.eqb_spec (sz mod 8) 0) as [E0|E0]; [apply bytes_at_nil; unfold SHOFF in *; lia|].
        pose proof (bytes_main w_all (CAbs, SHOFF + beg / 8 + sz / 8) [sz mod 8] (HP E0) (world_ok_all _ _)) as B. revert B. pmc_simpl. rewrite Z.add_0_l. intros B.
        apply B; [unfold SHOFF; lia | unfold SHOFF in *; lia |]. split; [apply VIS; unfold nsh in *; lia | apply VSH; unfold nsh in *; lia].
      + apply bytes_at_constZ; [unfold SHOFF; lia | unfold nsh in *; lia | unfold SHOFF, nsh in *; lia |].
        intros z Hz. assert (NF : (szrz - 8 * nsh sz) / 8 <> 0) by lia.
        apply (fill_main w_all (CAbs, SHOFF + beg / 8 + nsh sz) ((szrz - 8 * nsh sz) / 8) 249 (HF NF) (world_ok_all _ _)); [|revert Hz; pmc_simpl; lia].
        intros y Hy. apply VIS. revert Hy. pmc_simpl. unfold nsh in *. lia.
    - (* [comment removed for export] *)
      rewrite length_app, repeat_length, Nat2Z.inj_add, LSH, Z2Nat.id by lia.
      apply wr_at_of_some; [unfold SHOFF; lia | unfold SHOFF, nsh in *; lia |].
      intros i Hi.
      assert (Hi' : 0 <= i < szrz / 8) by (unfold nsh in *; lia). clear Hi.
      destruct (Z.lt_ge_cases i (sz / 8)) as [L|L].
      { exists (b8 0). assert (NZ : sz / 8 <> 0) by lia.
        apply (zero_main w_all (CAbs, SHOFF + beg / 8) (sz / 8) (HZ NZ) (world_ok_all _ _) ltac:(unfold nsh in *; lia)); [|pmc_simpl; lia].
        intros y Hy. apply VIS. revert Hy. pmc_simpl. unfold nsh in *. lia. }
      destruct (Z.lt_ge_cases i (nsh sz)) as [L2|L2].
      { assert (E0 : sz mod 8 <> 0) by (unfold nsh in *; intros E0; rewrite E0 in NSH; cbn in NSH; lia).
        rewrite (proj2 (Z.eqb_neq _ _) E0) in NSH.
        pose proof (bytes_main w_all (CAbs, SHOFF + beg / 8 + sz / 8) [sz mod 8] (HP E0) (world_ok_all _ _)) as B. revert B. pmc_simpl. rewrite Z.add_0_l. intros B.
        specialize (B ltac:(unfold SHOFF; lia) ltac:(unfold SHOFF in *; lia) ltac:(split; [apply VIS; unfold nsh in *; lia | apply VSH; unfold nsh in *; lia])).
        destruct B as (_ & _ & B). specialize (B 0%nat ltac:(cbn; lia)). cbn [nth_error] in B. rewrite Z.add_0_r in B.
        exists (b8 (sz mod 8)). replace (SHOFF + beg / 8 + i) with (SHOFF + beg / 8 + sz / 8) by lia.
        apply (mrd_above VM (SHOFF + beg / 8 + sz / 8) _ ltac:(unfold SHOFF, nsh in *; lia)). exact B. }
      assert (NF : (szrz - 8 * nsh sz) / 8 <> 0) by lia.
      exists (b8 249). apply (fill_main w_all (CAbs, SHOFF + beg / 8 + nsh sz) ((szrz - 8 * nsh sz) / 8) 249 (HF NF) (world_ok_all _ _)); [|pmc_simpl; lia].
      intros y Hy. apply VIS. revert Hy. pmc_simpl. unfold nsh in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition isKZ0 (K : kentry) : bool := match K with KZero (SA zb _) _ => expr_eqb zb (ELit 0) | _ => false end.
  Definition isKZF0 (K : kentry) : bool := match K with KZero (SA zb _) _ | KFill (SA zb _) _ _ => expr_eqb zb (ELit 0) | _ => false end.
  Definition gshadow_rest (gl : Z * Z * Z) : bool :=
    let '(beg, sz, szrz) := gl in
    let S := SHOFF + beg / 8 in
    Z.leb 0x10000 beg && Z.leb (beg + szrz) 0xc04000 && Z.eqb (beg mod 8) 0 && Z.leb 0 sz && Z.leb (8 * nsh sz) szrz && Z.eqb (szrz mod 8) 0
    && (if Z.eqb (sz mod 8) 0 then true else bytes_check (CAbs, S + sz / 8) [sz mod 8]).
  Definition gshadow_hole (h : nat) : bool :=
    if hole_sel w_all h then
      match HSF_asan h with
      | Some ch =>
          let g := hole_granted h in let cls := hole_class h in
          let bc := mkbc (kn ch) in let kz := List.filter isKZ0 (kn ch) in let kf := List.filter isKZF0 (kn ch) in
          forallb (fun gl : Z * Z * Z => let '(beg, sz, szrz) := gl in
             let S := SHOFF + beg / 8 in
             (Z.eqb (sz / 8) 0 || (let (b, k) := csym_base g cls CAbs in kzero_xB bc kz b (k + S) (ELit (sz / 8))))
             && (Z.eqb ((szrz - 8 * nsh sz) / 8) 0
                 || (let (b, k) := csym_base g cls CAbs in existsb (fill1 b (k + (S + nsh sz)) ((szrz - 8 * nsh sz) / 8) 0xf9) kf))) aglobals
      | None => true
      end
    else true.

  Lemma kzero_xB_filter_imp : forall bc p k b off n, kzero_xB bc (List.filter p k) b off n = true -> kzero_xB bc k b off n = true.
  Proof.
    intros bc p. induction k as [|K rest IH]; intros b off n H; [exact H|].
    cbn [List.filter] in H. destruct (p K).
    - destruct K as [a w v|[zb zk] zn|a zn kk|lo hi|e mm|e lo hi|a zn|a1 n1 a2 n2|a zn c|a zn]; cbn [kzero_xB] in H |- *; try (apply IH; exact H).
      repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; try reflexivity; try discriminate; apply IH; exact H.
    - destruct K as [a w v|[zb zk] zn|a zn kk|lo hi|e mm|e lo hi|a zn|a1 n1 a2 n2|a zn c|a zn]; cbn [kzero_xB]; try (apply IH; exact H).
      repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; try reflexivity; apply IH; exact H.
  Qed.
  Lemma existsb_filter_imp : forall (A : Type) (f p : A -> bool) l, existsb f (List.filter p l) = true -> existsb f l = true.
  Proof.
    intros A f p l H. apply existsb_exists in H as (a & Hin & Hf). apply filter_In in Hin as [Hin _].
    apply existsb_exists. exists a. split; assumption.
  Qed.
  Lemma aglobals_fast_imp : forallb gshadow_rest aglobals = true -> forallb gshadow_hole holes = true -> forallb gshadow_check aglobals = true.
  Proof.
    intros HR HH. apply forallb_forall. intros glq Hgl.
    pose proof (proj1 (forallb_forall _ _) HR glq Hgl) as Rg.
    assert (ZF : forall hq, In hq holes -> gshadow_hole hq = true) by (apply forallb_forall; exact HH).
    destruct glq as [[beg sz] szrz]. unfold gshadow_rest in Rg. unfold gshadow_check. cbv zeta in Rg |- *.
    apply andb_prop in Rg as [RA RB].
    assert (HZ : (Z.eqb (sz / 8) 0 || zero_check (CAbs, SHOFF + beg / 8) (sz / 8))%bool = true).
    { destruct (Z.eqb (sz / 8) 0) eqn:EQz; [reflexivity|]. cbn [orb]. unfold zero_check_w, all_holes_w. apply forallb_forall. intros hq Hhq.
      specialize (ZF hq Hhq). unfold gshadow_hole in ZF. destruct (hole_sel w_all hq); [|reflexivity]. destruct (HSF_asan hq) as [chq|]; [|reflexivity].
      cbv zeta in ZF. pose proof (proj1 (forallb_forall _ _) ZF _ Hgl) as G. cbv beta iota zeta in G. apply andb_prop in G as [GZ _].
      rewrite EQz in GZ. cbn [orb] in GZ. cbn [fst snd]. destruct (csym_base (hole_granted hq) (hole_class hq) CAbs) as [bq kq].
      exact (kzero_xB_filter_imp _ _ _ _ _ _ GZ). }
    assert (HF : (Z.eqb ((szrz - 8 * nsh sz) / 8) 0 || fill_check (CAbs, SHOFF + beg / 8 + nsh sz) ((szrz - 8 * nsh sz) / 8) 0xf9)%bool = true).
    { destruct (Z.eqb ((szrz - 8 * nsh sz) / 8) 0) eqn:EQf; [reflexivity|]. cbn [orb]. unfold fill_check_w, all_holes_w. apply forallb_forall. intros hq Hhq.
      specialize (ZF hq Hhq). unfold gshadow_hole in ZF. destruct (hole_sel w_all hq); [|reflexivity]. destruct (HSF_asan hq) as [chq|]; [|reflexivity].
      cbv zeta in ZF. pose proof (proj1 (forallb_forall _ _) ZF _ Hgl) as G. cbv beta iota zeta in G. apply andb_prop in G as [_ GF].
      rewrite EQf in GF. cbn [orb] in GF. cbn [fst snd]. destruct (csym_base (hole_granted hq) (hole_class hq) CAbs) as [bq kq].
      exact (existsb_filter_imp _ _ _ _ GF). }
    rewrite RA, HZ, RB, HF. reflexivity.
  Qed.

  Lemma aglobals_check : forallb gshadow_check aglobals = true.
  Proof. apply aglobals_fast_imp; vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  Lemma aglobals_main : Forall (AGLOBAL_SH VM) aglobals.
  Proof. apply Forall_forall. intros gl Hin. apply gshadow_main. exact (proj1 (forallb_forall _ _) aglobals_check gl Hin). Qed.

  (* [comment removed for export] *)
  Theorem aconst_main : ACONST VM.
  Proof. exact (conj aconst_cells_main (conj aglobals_main lowsh_stk)). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End AT_MAIN.
