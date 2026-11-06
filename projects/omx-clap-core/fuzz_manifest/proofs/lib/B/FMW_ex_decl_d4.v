(* G4.ExDecl, IMAGE B: dseg_D4 (FMW_ex_decl_base.v), expected 0x8163c..0x81664 on fm.asan-ubsan
   (fuzz_manifest.c:159-162). B twin of lib/A/FMW_ex_decl_d4.v (06d82004dc3); B's code (fm_b_expected_iface.out
   lines 254-275, 431-433): strchr (ns, '>') answered r (a0): r = 0 is DCut -> 0x81900 s7 = 0, 0x81904 a0 = s7 ->
   EX_R with a0 = 0 = the scan's answer; else a1 = r, s8 = r - s8 = ns_len (s8 = text + ns): ns_len >= n (0x8164c) ->
   0x81680..0x8168c (a6 = ld F+0x78 = text, a7 = 6, t0 = ':', t1 = ld F+0x70 = the mask) -> EX_JUMP with a1 = text +
   close (matches false); else close into F+0x40, strncmp (uri, text + ns, ns_len) -> dat_D5 at the return 0x81664.
   One symbolic state at EX_D4: the frame slots the run reads (atom 2 = F; uri, n, the mask, text) with the write
   window F+0x40; the difference the run takes (a0 - s8) as an alias atom. No UBSan guard on these paths. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_decl_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel expected_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the symbolic state at EX_D4 ---- *)
(* the frame (atom 2 = F): extra atoms 32 = uri (F+0x38), 33 = n (F+0x48), 34 = the mask (F+0x70), 35 = text (F+0x78);
   the window F+0x40 (close) is written on the strncmp path *)
Definition d4_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0x38 0x80 0x40 0x48
    (dd_slot_chunks [(0x38, 0%nat); (0x48, 1%nat); (0x70, 2%nat); (0x78, 3%nat)]).
(* 36 = a0 - s8 (ns_len) *)
Definition d4_alias : list (sv * sv) := [(SAlu ALU_SUB (SOff 10 0) (SOff 24 0), SOff 36 0)].
Definition ss_D4 : sstate :=
  mkSS EX_D4 sr_atoms [d4_frame] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] d4_alias).
Definition d4_extra (cx : ecx) (regs3 : bvmap 5 word) : list word :=
  map w64 [cx_u cx; cx_n cx; EX_MASK1; cx_t cx; bv_unsigned (getr regs3 10) - bv_unsigned (getr regs3 24)].

(* words (after G3's FMW_rd_c8.v c8_u64 / c8_u64s) *)
Lemma d4_u64 : forall z, bv_unsigned (w64 z) = z mod 2 ^ 64.
Proof. intros z. unfold w64. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma d4_u64s : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. rewrite d4_u64. apply Z.mod_small. exact Hz. Qed.

(* a callee-saved register survives a runtime call (after G3's FMW_g3kit.v g3_aregs_keep) *)
Lemma d4_keep : forall regs0 regs1 : bvmap 5 word,
  aregs_preserved regs0 regs1 -> forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs1 r = getr regs0 r.
Proof.
  intros regs0 regs1 HP r Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Ltac d4_cs HP HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    rewrite (d4_keep _ _ HP r ltac:(let v := eval vm_compute in (bv_unsigned r) in
                                     change (bv_unsigned r) with v; unfold acallee_saved; lia));
    dd_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma d4_entry : forall cx i d f name nl ns nl2 close r ly3 S3 W3 regs3 mem3 md3,
  dat_D4 B cx i d f name nl ns nl2 close r ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (d4_extra cx regs3)) ss_D4
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_D4) mem3 (seg_rom tfibsegs))).
Proof.
  intros cx i d f name nl ns nl2 close r ly3 S3 W3 regs3 mem3 md3 HD.
  destruct HD as ((HB & HC & HSL & _) & _).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HC as (HJ & _ & _ & Rsp & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  destruct HSL as (_ & _ & S38 & S48 & _ & _ & _ & S70 & S78 & _).
  assert (HSTK : STK_expected = 8464) by reflexivity.
  assert (HF : cx_F cx = cx_sp cx - 240) by reflexivity.
  assert (Hn : 0 <= cx_n cx <= 255).
  { destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hul & _). unfold cx_n. lia. }
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (d4_extra cx regs3)).
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hq; subst E; apply ew_Ereg_nat; exact Hq).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (rewrite (EE 2%nat 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E36 : ew E 36 = w64 (bv_unsigned (getr regs3 10) - bv_unsigned (getr regs3 24)))
    by exact (ew_Ereg_extra regs3 _ 4).
  pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as R10. pose proof (bv_unsigned_in_range 64 (getr regs3 24)) as R24.
  change (bv_modulus 64) with (2 ^ 64) in R10, R24.
  unfold ss_D4. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (d4_extra cx regs3)) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, d4_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. unfold cx_F in *. lia. }
    apply dd_chunks_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd Nat.add];
      lazymatch goal with |- val_mem _ _ _ _ (bv_unsigned (ew E ?k)) =>
        let j := eval vm_compute in (k - 32)%nat in
        replace (ew E k) with (nth j (d4_extra cx regs3) (Z_to_bv 64 0))
          by (subst E; symmetry; exact (ew_Ereg_extra regs3 _ j)) end;
      cbn [nth d4_extra map]; unfold w64; rewrite unsigned_lit_small by (first [lia | unfold EX_MASK1; lia]);
      assumption.
  - cbn. tauto.
  - split; [|split; [exact I|]].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2. change (2 ^ 4) with 16. split; [|exact I]. repeat split; first [exact HFm | lia].
    + cbn [f_alias alias_ok d4_alias]. split; [|exact I]. apply U_inj; rewrite U_SAlu; cbn [zalu_raw];
        rewrite !U_SOff, !Z.add_0_r.
      rewrite E36, d4_u64, (EE 10%nat 10%bv eq_refl), (EE 24%nat 24%bv eq_refl). unfold zcanon, M64.
      rewrite (Z.mod_small (bv_unsigned (getr regs3 10))), (Z.mod_small (bv_unsigned (getr regs3 24))) by lia.
      rewrite Zmod_mod. reflexivity.
Qed.

Hypothesis SD5 : dseg_D5 B.
Hypothesis SDJ : dseg_J B.
Hypothesis SEG_R : ex_seg_R B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Theorem decl_D4_holds : dseg_D4 B.
Proof.
  intros cx i d f name nl ns nl2 close r ly3 S3 W3 regs3 mem3 md3 HLf HD.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof (d4_entry cx i d f name nl ns nl2 close r ly3 S3 W3 regs3 mem3 md3 HD) as HS.
  destruct HD as ((HB & HC & HSL & HSR & HSC & Hi) & Hdc & R10 & R20 & R21 & R18 & R22 & R9 & R23 & R24 & R26).
  pose proof (dd_bounds B cx HB) as (HFm & HFlo & HFhi & Ht4 & Htc & Hu4 & Huc).
  pose proof HB as ((HPRE & HRO0) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_expected = 8464) by reflexivity.
  assert (HF : cx_F cx = cx_sp cx - 240) by reflexivity.
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HSC as (Hil & Hd16 & Hfl & Hu0 & Hres).
  pose proof HSR as (R19 & R27 & R8).
  set (E := Ereg regs3 (d4_extra cx regs3)) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hq; subst E; apply ew_Ereg_nat; exact Hq).
  assert (E32 : ew E 32 = w64 (cx_u cx)) by exact (ew_Ereg_extra regs3 _ 0).
  assert (E33 : ew E 33 = w64 (cx_n cx)) by exact (ew_Ereg_extra regs3 _ 1).
  assert (E34 : ew E 34 = w64 EX_MASK1) by exact (ew_Ereg_extra regs3 _ 2).
  assert (E35 : ew E 35 = w64 (cx_t cx)) by exact (ew_Ereg_extra regs3 _ 3).
  assert (E36 : ew E 36 = w64 (bv_unsigned (getr regs3 10) - bv_unsigned (getr regs3 24)))
    by exact (ew_Ereg_extra regs3 _ 4).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (rewrite (EE 2%nat 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E19 : ew E 19 = w64 5) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E27 : ew E 27 = w64 32) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  assert (E8 : ew E 8 = w64 (2 ^ 64 - 1)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
  clearbody E.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_D4) mem3 (seg_rom tfibsegs))))) by constructor.
  assert (AVw : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx + 0x40 <= a < cx_F cx + 0x48) ->
    aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by (intros; reflexivity).
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_D4) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_D4) with (Z_to_bv 64 EX_D4).
  destruct Hdc as [(Hdc & Hr0) | (Hdc & Hr)].
  - (* r = 0: DCut, 0x8163c beqz -> 0x81900 s7 = 0, 0x81904 a0 = s7 -> EX_R with a0 = 0 = the scan's answer *)
    assert (U10 : bv_unsigned (ew E 10) = 0) by (rewrite (EE 10%nat 10%bv eq_refl), R10, Hr0; reflexivity).
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    2:{ exfalso. rewrite branch_eq_U, U_SOff, U_SLit, U10 in Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_R.
    { dd_awr U2. }
    dd_avw W3 mem3 (cx_F cx + 0x40) (cx_F cx + 0x48) U2. dd_mk HS.
    apply (SEG_R cx ly3 S3 W3 _ _ _ HB).
    + eapply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ);
        [intros a Ha _ _ H3; exact (AVw a Ha H3) | ..]; dd_g HS; apply EE; reflexivity.
    + dd_g HS. rewrite (dd_res_cut cx i d f HSC Hi Hdc). reflexivity.
  - (* r = text + close: DFound *)
    pose proof (expected_m.decl_found _ _ _ _ _ _ _ Hdc) as (Dn & Di & Dc & Dcl & Db).
    assert (Hul : (length (cx_ub cx) <= 255)%nat) by (destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
    assert (U10 : bv_unsigned (ew E 10) = cx_t cx + Z.of_nat close)
      by (rewrite (EE 10%nat 10%bv eq_refl), R10, Hr; apply d4_u64s; lia).
    assert (U33 : bv_unsigned (ew E 33) = Z.of_nat (length (cx_ub cx))) by (rewrite E33; apply d4_u64s; unfold cx_n; lia).
    assert (U36 : bv_unsigned (ew E 36) = Z.of_nat nl2).
    { rewrite E36, R10, R24, Hr, (d4_u64s (cx_t cx + Z.of_nat close)), (d4_u64s (cx_t cx + Z.of_nat ns)) by lia.
      replace (cx_t cx + Z.of_nat close - (cx_t cx + Z.of_nat ns)) with (Z.of_nat nl2) by lia. apply d4_u64s. lia. }
    assert (G36 : ew E 36 = w64 (Z.of_nat nl2)).
    { rewrite E36, R10, R24, Hr, (d4_u64s (cx_t cx + Z.of_nat close)), (d4_u64s (cx_t cx + Z.of_nat ns)) by lia.
      unfold w64; f_equal; lia. }
    clear E36.
    assert (G10 : ew E 10 = w64 (cx_t cx + Z.of_nat close)) by (rewrite (EE 10%nat 10%bv eq_refl), R10, Hr; reflexivity).
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    { exfalso. rewrite branch_eq_U, U_SOff, U_SLit, U10, Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
      apply Z.eqb_eq in Hc. lia. }
    clear Hc.
    aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
    { dd_awr U2. }
    dd_avw W3 mem3 (cx_F cx + 0x40) (cx_F cx + 0x48) U2.
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    + (* ns_len >= n: 0x81680 .. 0x8168c -> EX_JUMP with a1 = text + close, matches false *)
      rewrite branch_geu_U, !U_SOff, U36, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
      apply Bool.negb_true_iff, Z.ltb_ge in Hc.
      assert (Hm : MM.matches (cx_tb cx) (cx_ub cx) ns nl2 = false)
        by (unfold MM.matches; rewrite (proj2 (Nat.ltb_ge nl2 (length (cx_ub cx))) ltac:(lia)); reflexivity).
      clear Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_JUMP.
      { dd_awr U2. }
      dd_avw W3 mem3 (cx_F cx + 0x40) (cx_F cx + 0x48) U2. dd_mk HS.
      lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
      assert (HK : dd_kept cx W3 mem3 (ms_mem msC)) by (intros a Ha _ _ H3; exact (AVw a Ha H3)).
      destruct (dd_scan_skip cx i d f name nl ns nl2 close HSC Hi Hdc Hm) as (HSC' & Hic).
      apply (SDJ cx i close d (pred f) ly3 S3 W3 _ _ _ HLf ltac:(lia)).
      split; [exact HB|].
      split; [eapply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ HK); dd_g HS; apply EE; reflexivity|].
      split; [apply (dd_slots_kept cx W3 mem3 _ d HSL); intros a Ha Hn; apply AVw; [lia | exact Hn]|].
      split; [split; [|split]; dd_regs HS EE|].
      split; [split; [|split; [|split]]; dd_regs HS EE|].
      split; [exact HSC' | dd_regs HS EE].
    + (* ns_len < n: close into F+0x40, strncmp (uri, text + ns, ns_len) *)
      rewrite branch_geu_U, !U_SOff, U36, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
      apply Bool.negb_false_iff, Z.ltb_lt in Hc.
      aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
      { dd_awr U2. }
      dd_avw W3 mem3 (cx_F cx + 0x40) (cx_F cx + 0x48) U2.
      lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
      (* the store 0x81650: F+0x40 = text + close *)
      lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
        let rg := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
        pose proof (fw_region_nth tfibsegs Ex ssx (restrict (w_H W3) msx) 0 rg HS ltac:(vm_compute; reflexivity))
          as HR0 end.
      rewrite restrict_mem in HR0.
      pose proof (fw_field tfibsegs E _ 2 (cx_F cx) _ _ _ _ _ 0x40 8%N (SOff 10 0) (cx_t cx + Z.of_nat close) HR0 U2
        ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite U10, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))
        as V40.
      cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V40. clear HR0.
      rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp'. rreg HS (3%bv : bv 5) Rgp'. rreg HS (4%bv : bv 5) Rtp'.
      rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
      assert (KL : fw_low tfibsegs (w_H W3) mem3 (ms_mem msC)) by (intros a Ha; apply AVw; lia).
      pose proof (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL HRO) as HRO1.
      pose proof (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL HCt) as HCt1.
      pose proof (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL HCu) as HCu1.
      assert (FR : STK_RT_STR = 8192) by reflexivity.
      dd_mk HS.
      eapply SRr_bind.
      { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strncmp STK_RT_STR
          (fun v => v = 0 <-> strn_eq (Z.to_nat (Z.of_nat nl2)) (cx_ub cx) (skipn ns (cx_tb cx)))
          W3 (ms_regs msC) (ms_mem msC) STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx)
          (cx_md cx) [] ly3 S3 _ 0 (-240) (Z_to_bv 64 0x81664) HJ).
        - unfold spZ. rewrite Rsp', U2. unfold cx_F. lia.
        - reflexivity.
        - lia.
        - unfold ESTACK. lia.
        - lia.
        - rewrite Rgp', (EE 3%nat 3%bv eq_refl), Rgp. exact Hgp.
        - rewrite Rtp', (EE 4%nat 4%bv eq_refl), Rtp. exact Htp.
        - exact Rra.
        - vm_compute. reflexivity.
        - intros HPK. apply (STRNCMP ly3 S3 W3 (ms_regs msC) (ms_mem msC) _ (cx_u cx) (cx_t cx + Z.of_nat ns)
            (Z.of_nat nl2) (cx_ub cx) (skipn ns (cx_tb cx)) HPK).
          + exact (proj1 (IMG ly3 S3 W3 (ms_mem msC) _ (proj1 HJ) HRO1)).
          + exact (proj1 (proj2 (IMG ly3 S3 W3 (ms_mem msC) _ (proj1 HJ) HRO1))).
          + rewrite Ra0, E32. reflexivity.
          + rewrite Ra1, (EE 23%nat 23%bv eq_refl), R23. reflexivity.
          + rewrite Ra2, G36. reflexivity.
          + lia.
          + exact HCu1.
          + exact (dd_cstr_suffix W3 (ms_mem msC) (cx_t cx) (cx_tb cx) ns HCt1 ltac:(lia)). }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
      change (mkCfg (mkst regs2 (Z_to_bv 64 0x81664) mem2 (seg_rom tfibsegs)) md2)
        with (cfg_at tfibsegs EX_D5 regs2 mem2 md2).
      assert (HK2 : dd_kept cx W3 mem3 mem2).
      { intros a Ha H1 _ H3. rewrite (Hfr2 a Ha) by lia. exact (AVw a Ha H3). }
      apply (SD5 cx i d f name nl ns nl2 close v ly3 S3 W3 regs2 mem2 md2 HLf).
      split.
      { split; [exact HB|].
        split; [eapply (dd_com_kept B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ2 HK2); d4_cs HP2 HS; apply EE;
                reflexivity|].
        split.
        { apply (dd_slots_kept cx W3 mem3 mem2 d HSL). intros a Ha Hn.
          rewrite (Hfr2 a ltac:(lia)) by lia. apply AVw; [lia | exact Hn]. }
        split; [split; [|split]; d4_cs HP2 HS; assumption|].
        split; [exact HSC | exact Hi]. }
      split; [exact Hdc|]. split; [lia|].
      split.
      { eapply dd_val_kept; [|exact V40]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hfr2; lia. }
      split; [exact Hv|]. split; [exact Hvr|].
      split; [rewrite Nat2Z.id in Hvl; refine (iff_trans Hvl (dm_strn (cx_tb cx) (cx_ub cx) ns nl2 _ _)); lia|].
      split; [d4_cs HP2 HS; rewrite (EE 20%nat 20%bv eq_refl); exact R20|].
      split; [d4_cs HP2 HS; rewrite (EE 21%nat 21%bv eq_refl); exact R21|].
      split; [d4_cs HP2 HS; rewrite (EE 18%nat 18%bv eq_refl); exact R18|].
      split; [d4_cs HP2 HS; rewrite (EE 22%nat 22%bv eq_refl); exact R22|].
      split; [d4_cs HP2 HS; rewrite (EE 9%nat 9%bv eq_refl); exact R9|].
      split.
      { lazymatch goal with |- getr _ ?r = _ =>
          rewrite (d4_keep _ _ HP2 r ltac:(let v := eval vm_compute in (bv_unsigned r) in
                                            change (bv_unsigned r) with v; unfold acallee_saved; lia)) end.
        dd_regs HS EE. }
      d4_cs HP2 HS. rewrite (EE 26%nat 26%bv eq_refl). exact R26.
Qed.
End W.

Check decl_D4_holds.
Print Assumptions decl_D4_holds.
