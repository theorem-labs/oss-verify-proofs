(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1 SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Atp_h_defs Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Sj_stage1_iface Sj_stage1_defs Sj_stage1 Od_hbaseA Atp_h_defsA Atp_activewA Atp_activeA Od_defsB Od_cpsB Od_hkit0A Od_hkit3A
  Od_setcapA Od_createwA Od_createA Od_lkitB Od_exitB Od_bodyB Od_beginB Od_top_defsB
  Od_setup_defsB Od_setup_defs2B Od_setupkB Od_setupk2B Od_setupw2B Od_setupbB Od_setupw4B Od_s1zB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma pres_fp_step2 : forall (L : list (Z * Z)) usp W (m0 m m' : mem),
  rt_pres_fp L [] usp W m0 m -> (forall a : word, aclient L [] usp (bv_unsigned a) -> outside W (bv_unsigned a) -> m' a = m a) -> rt_pres_fp L [] usp W m0 m'.
Proof. intros L usp W m0 m m' H HS a Ha Ho. rewrite (HS a Ha Ho). exact (H a Ha Ho). Qed.

Lemma sj_lib_agree : forall m m', sj_lib m -> agree_on (in_ranges LIB_FP) m m' -> sj_lib m'.
Proof. intros m m' H AG. apply (sj_lib_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

Lemma od_sbuf_range : forall L, 0 <= L <= 1048512 -> 64 <= OD_SBUF L <= 1747648 /\ OD_SBUF L mod 8 = 0 /\ L + 62 <= OD_SBUF L.
Proof. intros L H. unfold OD_SBUF, roundup64. Z.div_mod_to_equations. lia. Qed.

Lemma outside_lib : forall x, x < 0x11f420 \/ 0x656308 <= x -> outside LIB_FP x.
Proof. intros x H. unfold LIB_FP. cbn [outside]. repeat split; try lia; exact I. Qed.

Section PhaseC1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.
Hypothesis GETACT : getact_cps RT.
Hypothesis CREATE : create_cps RT.
Hypothesis HS1 : stage1_cps RT.
Hypothesis HS1Z : stage1z_cps RT.

Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold FUZZ_STACK, OD_NEED, CREATE_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem od_phaseC1 : od_phaseC1_stmt RT sj_lib PMc.
Proof using AF FDO MST RTF NEWA AFC AFV AFI GETACT CREATE HS1 HS1Z.
  intros K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 _ _ KC.
  unfold od_cutB_k.
  intros ΣB S1 F A cap size COPY BUF els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc mB FRM CB.
  destruct CB as [C0 DZ LV CPY CR (j0 & j144 & j176 & j264 & j288 & j336 & j376 & LOWF) (jp & PAR) SH].
  destruct C0 as [(U16 & UT) (S32 & S1R) (LOW & LOR) (F64 & FPOS) FRS0 LVPOS LVB CR0 ART0 MI0 ST0 FRS SP0 (j384 & j432 & HI) STp SAVED (h0 & h8 & HDR)
                  VR SZ1 WRS (jd & DOC) LIB0 CP0].
  set (s0 := od_s0 dz) in *. set (len0 := zlength s0) in *. set (doc := od_doc dz) in *. set (L := zlength doc) in *.
  pose proof (od_s0_ok dz (proj1 DZ)) as S0OK. fold s0 in S0OK.
  assert (LEN0 : 0 <= len0) by (subst len0; unfold zlength; lia).

  set (CN := if od_copied dz then len0 + 64 else 0).
  set (bb := if od_copied dz then padded_bytes doc else []).
  assert (DOCF : bytes_ok doc /\ 0 <= L <= 1048512 /\ 0 <= CN /\ COPY <= BUF /\ BUF + Z.of_nat (length bb) <= COPY + CN /\ bytes_at bsegs mB BUF bb
                 /\ 0 <= COPY /\ COPY mod 8 = 0
                 /\ rt_live RT ΣB = (if od_copied dz then [(COPY, CN)] else []) ++ vblockA A cap size ++ rt_live RT Σ0).
  { subst CN bb L doc. unfold od_doc in *. fold s0 in CPY |- *.
    assert (ECP : od_copied dz = (len0 <=? 1048512)) by reflexivity.
    revert CPY LV ECP. destruct (od_copied dz); intros CPY LV ECP.
    - symmetry in ECP. apply Z.leb_le in ECP. destruct CPY as (C0' & C16 & CR' & CL & CBY).
      assert (BK : bytes_ok (strip_bom s0)).
      { destruct (Z_lt_ge_dec len0 3) as [L3|L3]; [rewrite strip_bom_short by (subst len0; unfold zlength in L3; lia); exact S0OK|].
        destruct (strip_bom_cases s0 S0OK ltac:(subst len0; unfold zlength in L3; lia)) as [(_ & E & _)|(_ & E)]; rewrite E; [| exact S0OK].
        unfold bytes_ok in *. rewrite <- (firstn_skipn 3 s0) in S0OK. apply Forall_app in S0OK. exact (proj2 S0OK). }
      split; [exact BK|]. assert (0 <= zlength (strip_bom s0)) by (unfold zlength; lia).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold padded_bytes; rewrite length_app, zbytes_length, repeat_length; unfold zlength in *; lia|].
      split; [exact CBY|]. split; [lia|]. split; [clear - C16; Z.div_mod_to_equations; lia| exact LV].
    - destruct CPY as (-> & ->). split; [constructor|]. unfold zlength. cbn [length Z.of_nat]. repeat (split; try lia); try reflexivity; try exact LV; try (cbn [length Z.of_nat]; lia); try (intros i Hi; cbn in Hi; lia). }
  destruct DOCF as (DOCOK & LR & CNR & CB0 & CB1 & BUFB & CPOS0 & COPY8 & LVB').
  assert (CPYA : if od_copied dz then 0 < COPY /\ COPY mod 16 = 0 /\ COPY <= BUF <= COPY + 3 /\ BUF - COPY + L = len0 else COPY = 0 /\ BUF = 0).
  { revert CPY. destruct (od_copied dz); intros CPY; [destruct CPY as (X1 & X2 & X3 & X4 & _); repeat split; try assumption; lia| exact CPY]. }
  clear CPY LV. rename LVB' into LV.
  pose proof (od_sbuf_range L LR) as (SBR & SB8 & SBL).
  pose proof (sc_idx_bounds L ltac:(lia)) as IXB.
  pose proof (af_sp0_range RT AF ΣB mB ART0) as SP0R.
  assert (INF : In (F, 3%nat) (rt_frames RT ΣB)) by (rewrite FRS; left; reflexivity).
  pose proof (fframe_ranges RT AF ΣB mB F 3 ART0 INF) as (_ & FR1' & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF ΣB mB F 3 ART0 INF) as (FSL & FSF). pose proof (FSF F 3%nat INF) as FSELF.
  pose proof (af_frames_align RT AF ΣB mB F 3 ART0 INF) as (_ & FSEG).
  pose proof (af_frames_range RT AF ΣB mB F 3%nat ART0 INF) as (_ & _ & _ & FLV).
  change (fs_size 3) with 512 in *. rewrite SP0 in FR1', SHT.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL.
  assert (FD0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  set (S := F / 8 + 2147450880) in *.
  assert (GF : F + 512 <= lo /\ S + 64 <= lo /\ (F + 512 <= S \/ S + 64 <= F) /\ SEGTOP_A <= F) by (clear - FR1' SHT LOW FSELF FSEG; ul).
  destruct GF as (FLO & SLO & FSEP & FSG).
  assert (LOWB : rt_sp0 RT ΣB - STACK_WIN <= lo) by (rewrite SP0; exact LOW).
  assert (EU1 : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul).
  pose proof VR as (VSZ & VSC & VCAP & VA0 & VAT & _ & VB).
  destruct VB as [(B1 & B2)|(CAP1 & A16 & APOS & _)]; [lia|].
  assert (INV : In (A, 16 * size) (rt_live RT ΣB)).
  { rewrite LV. apply in_or_app. right. apply in_or_app. left. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  pose proof (af_live_range RT AF ΣB mB A (16 * size) ART0 INV) as (_ & AV1 & AIMG).
  assert (CIMG : In (COPY, CN) (rt_live RT ΣB) -> COPY + CN <= 0x10000 \/ SEGTOP_A <= COPY) by (intros X; exact (proj2 (proj2 (af_live_range RT AF ΣB mB _ _ ART0 X)))).
  pose proof (FLV A (16 * size) INV) as FAV. pose proof (FSL A (16 * size) INV) as SAV.
  assert (CPG : CN = 0 \/ (In (COPY, CN) (rt_live RT ΣB) /\ (F + 512 <= COPY \/ COPY + CN <= F) /\ (COPY + CN <= S \/ S + 64 <= COPY) /\ COPY + CN <= lo
                           /\ (COPY + CN <= A \/ A + 16 * size <= COPY))).
  { subst CN. revert LV. destruct (od_copied dz); intros LV; [right| left; reflexivity].
    assert (INC : In (COPY, len0 + 64) (rt_live RT ΣB)) by (rewrite LV; left; reflexivity).
    pose proof (af_live_range RT AF ΣB mB _ _ ART0 INC) as (_ & R1 & _).
    split; [exact INC|]. split; [exact (FLV _ _ INC)|]. split; [exact (FSL _ _ INC)|]. split; [clear - R1 LOWB; lia|].
    apply (af_live_disj RT AF ΣB mB COPY (len0 + 64) A (16 * size) [] (vblockA A cap size ++ rt_live RT Σ0) ART0 LV).
    cbn [app]. apply in_or_app. left. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  assert (ACLB : forall x, (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + CN) ->
                   aclient (rt_live RT ΣB) (rt_frames RT ΣB) S1 x).
  { intros x [H|[H|[H|[H|H]]]].
    - left. ul.
    - right; right; right; left. exists F, 3%nat. change (fs_size 3) with 512. split; [exact INF| lia].
    - right; right; right; right. exists F, 3%nat. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. split; [exact INF| lia].
    - right; right; left. exists A, (16 * size). split; [exact INV| lia].
    - destruct CPG as [E|(INC & _)]; [lia|]. right; right; left. exists COPY, CN. split; [exact INC| lia]. }
  assert (L0SUB : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT ΣB)).
  { intros e He. rewrite LV. apply in_or_app. right. apply in_or_app. right. exact He. }
  assert (CALLER : forall x, aclient (rt_live RT Σ0) [] usp x ->
            ~ (F <= x < F + 512) /\ ~ (S <= x < S + 64) /\ ~ (lo <= x < usp) /\ aclient (rt_live RT ΣB) (rt_frames RT ΣB) S1 x).
  { intros x [H|[H|[H|[H|H]]]].
    - split; [clear - H FLO LOR; ul|]. split; [clear - H SLO LOR; ul|]. split; [lia|]. left; clear - H S1R; lia.
    - pose proof (client_static_range x H) as CRr.
      split; [clear - CRr FSG; ul|]. split; [clear - CRr SHB0; ul|]. split; [clear - CRr SP0R LOWB; ul|]. right; left; exact H.
    - destruct H as (p & n & Hin & Hp). pose proof (L0SUB _ Hin) as HinL.
      pose proof (FLV p n HinL) as D1. pose proof (FSL p n HinL) as D2. pose proof (af_live_range RT AF ΣB mB p n ART0 HinL) as (_ & D3 & _).
      split; [clear - Hp D1; lia|]. split; [clear - Hp D2; lia|]. split; [clear - Hp D3 LOWB; lia|].
      right; right; left; exists p, n; split; [exact HinL| exact Hp].
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }

  unfold od_parserB, wz in PAR.
  lazymatch type of PAR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
    change (rw_cells bsegs mB (F + 96) ([c0; c1] ++ [c2; c3] ++ [c4; c5] ++ rest)) in PAR end.
  apply Sj_stage1_kit.rw_cells_app in PAR. destruct PAR as [PA0 X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [PA8 X].
  apply Sj_stage1_kit.rw_cells_app in X. destruct X as [PA24 PA40].
  cbn [cells_size csize Nat.add] in PA8, PA24, PA40.
  replace (F + 96 + Z.of_nat 8) with (F + 104) in * by lia.
  replace (F + 104 + Z.of_nat 16) with (F + 120) in * by lia.
  replace (F + 120 + Z.of_nat 16) with (F + 136) in * by lia.
  unfold od_shadow in SH. cbn [map] in SH. unfold od_lowB in LOWF. unfold fa_saved in SAVED.

  pose proof (rw_cells_pick 6 1 mB S1 (S1 + 168) _ LOWF ltac:(cbn [firstn cells_size csize Nat.add]; lia)) as P168.
  cbn [firstn skipn] in P168. unfold wz in P168, LOWF.

  change (Z_to_bv 64 OD_CUTB) with (Z_to_bv 64 0x96dac). unfold wz.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkC1 xra usp S1 F lo BUF L gp (Z_to_bv 64 0x656e70) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc mB
             ltac:(clear - FSG; ul) FLO ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) P168 PA8 (AFC ΣB mB ART0) MI0). }
  cbv beta. intros ms1 (m1 & a2' & -> & MU1 & WM1 & MI1 & PA81).
  apply evt_done.
  assert (FP1 : fp_ok RT ΣB lo [(F + 112, F + 120)]).
  { apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; right; right; left; exists F, 3%nat; (split; [exact INF|]); change (fs_size 3) with 512; lia. }
  pose proof (art_of_munch RT AF ΣB mB m1 lo _ ART0 LOWB FP1 MU1 WM1) as ART1.
  assert (AG01 : agree_on (fun x => ~ (F + 112 <= x < F + 120)) mB m1)
    by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  clear ART0 MI0 PA8 FP1.
  xfer_all sj_lib sj_lib_agree mB m1 AG01 WM1
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
          first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
                | destruct CPG as [E|(_ & P3 & P4 & P5 & _)]; [clear - Hx E CB0 CB1; lia| clear - Hx CB0 CB1 P3; lia] ])
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [clear - Hx; lia| clear - Hx FAV; lia])
    ltac:(intros a Ha; apply MU1; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R; split; [clear - R FSG; ul| exact I])
    ltac:(intros a Ha; apply MU1; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & _); split; [clear - C1; lia| exact I]).
  clear AG01 MU1.
  assert (LVLEN : Z.of_nat (length (rt_live RT ΣB)) + 5 <= LIVE_MAX).
  { rewrite LV, !length_app. assert ((length (if od_copied dz then [(COPY, CN)] else []) <= 1)%nat) by (destruct (od_copied dz); cbn; lia).
    assert ((length (vblockA A cap size) <= 3)%nat) by (unfold vblockA; destruct (cap =? 0); [cbn; lia| apply ann_block_length]).
    unfold FUZZ_LIVE, LIVE_MAX in *. lia. }
  pose proof (mcost_le (OD_SBUF L) ltac:(lia)) as MCS. pose proof (mcost_nonneg (OD_SBUF L) ltac:(lia)) as MCS0.
  pose proof (mcost_le (sc_idx L) ltac:(lia)) as MCI. pose proof (mcost_nonneg (sc_idx L) ltac:(lia)) as MCI0.
  assert (MC96 : mcost 96 = 2097152) by (vm_compute; reflexivity).
  assert (MC8K : mcost (8 * 1024) = 2097152) by (vm_compute; reflexivity).
  assert (MC1K : mcost 1024 = 2097152) by (vm_compute; reflexivity).
  assert (PADC : OD_PAD_COST = 4210688) by (vm_compute; reflexivity).
  assert (IXU : sc_idx L <= 4194340) by (clear - LR; unfold sc_idx, roundup64; Z.div_mod_to_equations; lia).
  unfold lh_regs.
  eapply (aevt_newarr RT PMc FDO MST NEWA ΣB K) with (n := OD_SBUF L) (lo := lo);
    rewrite ?EU1;
    [ clear - SBR; lia | reflexivity | reflexivity | clear - LVLEN; lia | clear - MCS SBR CR CR0 PADC; unfold OD_VEC_COST, FUZZ_COST in *; lia
    | exact ART1 | exact MI1 | exact ST0 | exact LOWB
    | clear - LOR S1R; ul | clear - S1R UT; ul | clear - S32; Z.div_mod_to_equations; lia | exact FRM | ].
  intros ΣS SB v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F2 fc2 m2 FRM2 (ART2 & MI2 & WM2 & ST2) PR2 WRSB ACCSB LVS FRSS SPS CRS SBPOS SB16 SBTOP.
  rewrite ?EU1 in ST2, PR2. rewrite (ret_pc_even 0x96de8) by lia.
  assert (AG12 : agree_on (fun x => (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + CN)) m1 m2)
    by (intros a Ha; exact (PR2 a (ACLB _ Ha))).
  clear ST0 ART1 MI1.
  xfer_all sj_lib sj_lib_agree m1 m2 AG12 WM2
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; subst S; clear - Hx S1R CB0 CB1; lia)
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [right; left; clear - Hx; lia| do 3 right; left; exact Hx])
    ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS' R]; apply PR2; right; left; exact CS')
    ltac:(intros a Ha; pose proof (CALLER _ Ha) as (_ & _ & _ & C4); apply PR2; exact C4).
  clear AG12 PR2.
  set (CAP := OD_SBUF L) in *.
  assert (INFS : In (F, 3%nat) (rt_frames RT ΣS)) by (rewrite FRSS; exact INF).
  assert (INSB : In (SB, CAP) (rt_live RT ΣS)) by (rewrite LVS; left; reflexivity).
  assert (LOWS : rt_sp0 RT ΣS - STACK_WIN <= lo) by (rewrite SPS; exact LOWB).
  pose proof (af_frames_range RT AF ΣS m2 F 3%nat ART2 INFS) as (_ & _ & _ & FLVS). change (fs_size 3) with 512 in FLVS.
  pose proof (af_fshadow_apart RT AF ΣS m2 F 3 ART2 INFS) as (FSLS & _). change (fs_size 3) with 512 in FSLS. rewrite SHF in FSLS. unfold shad, SHB in FSLS. fold S in FSLS.
  pose proof (FLVS SB CAP INSB) as SF. pose proof (FSLS SB CAP INSB) as SS.
  pose proof (af_live_range RT AF ΣS m2 SB CAP ART2 INSB) as (_ & SBL1 & SBIMG).
  assert (SBLO : SB + CAP <= lo) by (clear - SBL1 LOWS; lia).
  pose proof (af_live_disj RT AF ΣS m2 SB CAP A (16 * size) [] (rt_live RT ΣB) ART2 LVS INV) as SA.
  assert (SC : CN = 0 \/ (SB + CAP <= COPY \/ COPY + CN <= SB)).
  { destruct CPG as [E|(INC & _)]; [left; exact E| right]. exact (af_live_disj RT AF ΣS m2 SB CAP COPY CN [] (rt_live RT ΣB) ART2 LVS INC). }
  assert (ACLS : forall x, (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + CN) \/ (SB <= x < SB + CAP) ->
                   aclient (rt_live RT ΣS) (rt_frames RT ΣS) S1 x).
  { intros x [H|[H|[H|[H|[H|H]]]]].
    1-5: rewrite FRSS; apply (aclient_mono (rt_live RT ΣB) (rt_frames RT ΣB) S1 _ _ S1); [apply ACLB; clear - H; tauto| intros e He; rewrite LVS; right; exact He| auto| lia].
    right; right; left. exists SB, CAP. split; [exact INSB| lia]. }
  assert (CALLS : forall x, aclient (rt_live RT Σ0) [] usp x -> aclient (rt_live RT ΣS) (rt_frames RT ΣS) S1 x /\ ~ (SB <= x < SB + CAP)).
  { intros x Hx. pose proof (CALLER _ Hx) as (_ & _ & _ & C4). split.
    - rewrite FRSS. apply (aclient_mono _ _ _ _ _ _ _ C4); [intros e He; rewrite LVS; right; exact He| auto| lia].
    - apply (fresh_apart_l RT AF ΣS m2 [(SB, CAP)] (rt_live RT ΣB) SB CAP S1 x ART2 LVS ltac:(left; reflexivity) ltac:(clear - LOWS LOR S1R; ul)).
      rewrite FRSS. exact C4. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkC2 (Z_to_bv 64 0x96de8) usp S1 F lo SB gp (Z_to_bv 64 0x656e70) v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 L) (Z_to_bv 64 (F + 104)) (Z_to_bv 64 BUF) xs6 xs9 v3 v4 v5 v6
             (Z_to_bv 64 L) F2 fc2 m2 FPOS FLO ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) PA81 PA40 MI2). }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & PA403).
  apply evt_done.
  assert (FP3 : fp_ok RT ΣS lo [(F + 144, F + 152)]).
  { apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; right; right; left; exists F, 3%nat; (split; [exact INFS|]); change (fs_size 3) with 512; lia. }
  pose proof (art_of_munch RT AF ΣS m2 m3 lo _ ART2 LOWS FP3 MU3 WM3) as ART3.
  assert (AG23 : agree_on (fun x => ~ (F + 144 <= x < F + 152)) m2 m3)
    by (apply (agree_of_munch _ _ _ _ MU3); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  clear ART2 MI2 PA40 FP3 ACCSB.
  xfer_all sj_lib sj_lib_agree m2 m3 AG23 WM3
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
          first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul | clear - Hx SF; lia
                | destruct CPG as [E|(_ & P3 & P4 & P5 & _)]; [clear - Hx E CB0 CB1; lia| clear - Hx CB0 CB1 P3; lia] ])
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [clear - Hx; lia| clear - Hx FAV; lia])
    ltac:(intros a Ha; apply MU3; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R; split; [clear - R FSG; ul| exact I])
    ltac:(intros a Ha; apply MU3; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & _); split; [clear - C1; lia| exact I]).
  clear AG23 MU3.
  unfold lh_regs.
  eapply (aevt_rt RT PMc); [| exact FRM2 |].
  { exact (GETACT ΣS PMc (Z_to_bv 64 0x96f0c) (Z_to_bv 64 S1) gp (Z_to_bv 64 0x656e70) v0 v1 v2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m3 lo
             FDO MST LIB0 ART3 MI3 ltac:(rewrite EU1; exact ST2) LOWS ltac:(rewrite EU1; clear - LOR S1R; ul) ltac:(rewrite EU1; clear - S1R UT; ul) FRM2). }
  intros c4 HQ. eexists ΣS, _. split; [exact HQ|].
  intros ms4 (m4 & RS & (ART4 & MI4 & WM4 & ST4) & PR4 & LIB4) FRM4. revert FRM4.
  apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ms4 (fun ms => frm0 (ms_fcsr ms) -> aevt ΣS K ms) RS).
  intros y0 y1 y2 k1 k2 k3 k4 k5 k6 k7 y3 y4 y5 y6 F4 fc4 FRM4. cbn [ms_fcsr] in FRM4.
  rewrite ?EU1 in ST4, PR4. rewrite (ret_pc_even 0x96f0c) by lia.
  assert (AG34 : agree_on (fun x => (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + CN) \/ (SB <= x < SB + CAP)) m3 m4).
  { intros a Ha. apply (PR4 a (ACLS _ Ha)). apply outside_lib.
    destruct Ha as [H|[H|[H|[H|[H|H]]]]]; [clear - H S1R LOR LOWB SP0R SP0; ul| clear - H FSG; ul| subst S; clear - H SHB0; lia| | |].
    - clear - H AIMG. ul.
    - destruct CPG as [E|(INC & _)]; [clear - H E; lia|]. specialize (CIMG INC). clear - H CIMG. ul.
    - clear - H SBIMG. ul. }
  assert (CP4 : rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m4).
  { apply (pres_fp_step2 _ _ _ _ _ _ CP0). intros a Ha Ho. destruct (CALLS _ Ha) as (C1 & _). exact (PR4 a C1 Ho). }
  assert (LIBS : sj_lib m4) by (right; exact LIB4).
  clear CP0 LIB0 ST2 ART3 MI3.
  xfer_all sj_lib sj_lib_agree m3 m4 AG34 WM4
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; subst S; clear - Hx S1R CB0 CB1; lia)
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [right; left; clear - Hx; lia| do 3 right; left; exact Hx])
    ltac:(fail) ltac:(fail).
  clear AG34 PR4.

  assert (SZ0 : shz m4 0x656200 8 /\ shz m4 0x6562a0 8).
  { split; apply (shz_static RT AF ΣS m4 _ 8 ART4); try reflexivity; try (clear; lia); intros i Hi; (split; [apply client_static_intro| clear - Hi; lia]).
    - do 5 right; left. clear - Hi. lia.
    - do 10 right; left. clear - Hi. lia. }
  assert (SZV : shz m4 0x117900 64).
  { apply (od_shz_lit RT AF ΣS m4 0x117900 64 ART4); [unfold ACC_LITS; repeat (first [left; reflexivity | right])| reflexivity| lia| reflexivity]. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkC3 (Z_to_bv 64 0x96f0c) usp S1 F lo L gp (Z_to_bv 64 0x656e70) y0 y1 y2 k1 k2 k3 k4 k5 k6 k7 (Z_to_bv 64 (F + 96)) (Z_to_bv 64 BUF) xs6 xs9 y3 y4 y5 y6
             F4 fc4 m4 FPOS FLO ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) (proj1 SZ0) (proj2 SZ0) SZV LIB4 (AFI ΣS m4 ART4) MI4). }
  cbv beta. intros ms5 (a4' & ->). apply evt_done.

  lazymatch type of PA81 with rw_cells _ _ _ [?c0; ?c1] => change (rw_cells bsegs m4 (F + 104) ([c0] ++ [c1])) in PA81 end.
  apply Sj_stage1_kit.rw_cells_app in PA81. destruct PA81 as [PIM PC16]. cbn [cells_size csize Nat.add] in PC16. replace (F + 104 + Z.of_nat 8) with (F + 112) in PC16 by lia.
  assert (FOBJ : fobj RT ΣS m4 (F + 104) 8).
  { split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|]. change ((8 + 7) / 8) with 1.
    split; [exists F, 3%nat; change (fs_size 3) with 512; split; [exact INFS| lia]|].
    replace (shad (F + 104)) with (S + 13) by (subst S; unfold shad, SHB; clear - F64; Z.div_mod_to_equations; lia).
    pose proof SH as X.
    lazymatch type of X with rw_cells _ _ _ ?l => let l1 := eval cbv in (firstn 13 l) in let l2 := eval cbv in (firstn 1 (skipn 13 l)) in let l3 := eval cbv in (skipn 14 l) in
      change l with (l1 ++ l2 ++ l3) in X end.
    apply Sj_stage1_kit.rw_cells_app in X. destruct X as [_ X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. exact HB. }
  assert (LVLENS : Z.of_nat (length (rt_live RT ΣS)) + 4 <= LIVE_MAX) by (rewrite LVS; cbn [length]; clear - LVLEN; lia).
  unfold lh_regs.
  eapply (aevt_rt RT PMc); [| exact FRM4 |].
  { exact (CREATE ΣS PMc (Z_to_bv 64 0x96f7c) (Z_to_bv 64 S1) gp (Z_to_bv 64 0x656e70) y0 y1 y2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 (F + 104) L 1024 lo
             FDO MST eq_refl eq_refl eq_refl eq_refl ltac:(clear - LR; lia) ltac:(lia) FOBJ PIM LVLENS
             ltac:(rewrite CRS, MC96, MC8K, MC1K; fold CAP in MCS; clear - MCS MCI SBR IXU CR CR0 PADC; unfold OD_VEC_COST, FUZZ_COST in *; lia)
             ART4 MI4 ltac:(rewrite EU1; exact ST4) LOWS ltac:(rewrite EU1; clear - LOR S1R; ul) ltac:(rewrite EU1; clear - S1R UT; ul)
             ltac:(rewrite EU1; clear - S32; Z.div_mod_to_equations; lia) FRM4). }
  intros c6 (ΣI & IMPL & IDX & OC & IA & HQ6 & LVI & FRSI & SPI & CRI & (IMPOS & IM16) & (IXPOS & IX16) & (OCPOS & OC16) & (IAPOS & IA16)).
  eexists ΣI, _. split; [exact HQ6|].
  intros ms6 (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PR6 & PIM6 & FOBJ6 & (p12 & p28 & p50 & IMC)) FRM6. revert FRM6.
  apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ms6 (fun ms => frm0 (ms_fcsr ms) -> aevt ΣI K ms) RS6).
  intros z0 z1 z2 d1 d2 d3 d4 d5 d6 d7 z3 z4 z5 z6 F6 fc6 FRM6. cbn [ms_fcsr] in FRM6.
  rewrite ?EU1 in ST6, PR6. rewrite (ret_pc_even 0x96f7c) by lia.
  assert (AG46 : agree_on (fun x => ((S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + CN) \/ (SB <= x < SB + CAP))
                                     /\ ~ (F + 104 <= x < F + 112)) m4 m6).
  { intros a [H1 H2]. apply (PR6 a (ACLS _ H1)). cbn [outside]. split; [clear - H2; lia| exact I]. }
  clear ST4 ART4 MI4 PIM SZ0 SZV FOBJ LIB4.
  xfer_all sj_lib sj_lib_agree m4 m6 AG46 WM6
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
          split; [subst S; clear - Hx S1R CB0 CB1; lia| first [clear - Hx; lia | subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul | clear - Hx SF; lia
                                                               | destruct CPG as [E|(_ & P3 & _)]; [clear - Hx E CB0 CB1; lia| clear - Hx CB0 CB1 P3; lia] ]])
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [split; [right; left; clear - Hx; lia| clear - Hx; lia]| split; [do 3 right; left; exact Hx| clear - Hx FAV; lia]])
    ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS' R]; apply PR6; [right; left; exact CS'| cbn [outside]; split; [clear - R FSG; ul| exact I]])
    ltac:(intros a Ha; destruct (CALLS _ Ha) as (C1 & _); pose proof (CALLER _ Ha) as (C2 & _); apply PR6; [exact C1| cbn [outside]; split; [clear - C2; lia| exact I]]).
  clear AG46 PR6.

  assert (INFI : In (F, 3%nat) (rt_frames RT ΣI)) by (rewrite FRSI; exact INFS).
  assert (INIM : In (IMPL, 96) (rt_live RT ΣI)) by (rewrite LVI; do 3 right; left; reflexivity).
  assert (INIX : In (IDX, sc_idx L) (rt_live RT ΣI)) by (rewrite LVI; do 2 right; left; reflexivity).
  assert (LOWI : rt_sp0 RT ΣI - STACK_WIN <= lo) by (rewrite SPI; exact LOWS).
  pose proof (af_frames_range RT AF ΣI m6 F 3%nat ART6 INFI) as (_ & _ & _ & FLVI). change (fs_size 3) with 512 in FLVI.
  pose proof (af_fshadow_apart RT AF ΣI m6 F 3 ART6 INFI) as (FSLI & _). change (fs_size 3) with 512 in FSLI. rewrite SHF in FSLI. unfold shad, SHB in FSLI. fold S in FSLI.
  pose proof (FLVI IMPL 96 INIM) as IF'. pose proof (FSLI IMPL 96 INIM) as IS'. pose proof (FLVI IDX _ INIX) as XF. pose proof (FSLI IDX _ INIX) as XS.
  pose proof (af_live_range RT AF ΣI m6 IMPL 96 ART6 INIM) as (_ & IML1 & _).
  pose proof (af_live_range RT AF ΣI m6 IDX _ ART6 INIX) as (_ & IXL1 & _).
  assert (ILO : IMPL + 96 <= lo /\ IDX + sc_idx L <= lo) by (clear - IML1 IXL1 LOWI; lia).
  assert (LVI3 : rt_live RT ΣI = [(IA, 1024); (OC, 8 * 1024); (IDX, sc_idx L)] ++ (IMPL, 96) :: rt_live RT ΣS) by (rewrite LVI; reflexivity).
  assert (LVI2 : rt_live RT ΣI = [(IA, 1024); (OC, 8 * 1024)] ++ (IDX, sc_idx L) :: (IMPL, 96) :: rt_live RT ΣS) by (rewrite LVI; reflexivity).
  assert (IMX : IMPL + 96 <= IDX \/ IDX + sc_idx L <= IMPL).
  { apply (af_live_disj RT AF ΣI m6 IMPL 96 IDX (sc_idx L) _ _ ART6 LVI3). apply in_or_app. left. do 2 right. left. reflexivity. }
  assert (OLD : forall q k, In (q, k) (rt_live RT ΣS) -> (IMPL + 96 <= q \/ q + k <= IMPL) /\ (IDX + sc_idx L <= q \/ q + k <= IDX)).
  { intros q k Hq. split.
    - apply (af_live_disj RT AF ΣI m6 IMPL 96 q k _ _ ART6 LVI3). apply in_or_app. right. exact Hq.
    - apply (af_live_disj RT AF ΣI m6 IDX (sc_idx L) q k _ _ ART6 LVI2). apply in_or_app. right. right. exact Hq. }
  pose proof (OLD SB CAP INSB) as (ISB & XSB).
  pose proof (OLD A (16 * size) ltac:(rewrite LVS; right; exact INV)) as (IAV & XAV).
  assert (ICP : CN = 0 \/ ((IMPL + 96 <= COPY \/ COPY + CN <= IMPL) /\ (IDX + sc_idx L <= COPY \/ COPY + CN <= IDX))).
  { destruct CPG as [E|(INC & _)]; [left; exact E| right]. exact (OLD COPY CN ltac:(rewrite LVS; right; exact INC)). }
  assert (ACLI : forall x, (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + CN) \/ (SB <= x < SB + CAP)
                           \/ (IMPL <= x < IMPL + 96) \/ (IDX <= x < IDX + sc_idx L) ->
                   aclient (rt_live RT ΣI) (rt_frames RT ΣI) S1 x).
  { intros x [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
    1-6: rewrite FRSI; apply (aclient_mono (rt_live RT ΣS) (rt_frames RT ΣS) S1 _ _ S1); [apply ACLS; clear - H; tauto| intros e He; rewrite LVI; do 4 right; exact He| auto| lia].
    - right; right; left. exists IMPL, 96. split; [exact INIM| lia].
    - right; right; left. exists IDX, (sc_idx L). split; [exact INIX| lia]. }
  assert (CALLI : forall x, aclient (rt_live RT Σ0) [] usp x -> aclient (rt_live RT ΣI) (rt_frames RT ΣI) S1 x /\ ~ (IMPL <= x < IMPL + 96) /\ ~ (IDX <= x < IDX + sc_idx L)).
  { intros x Hx. destruct (CALLS _ Hx) as (C1 & _).
    assert (C1' : aclient (rt_live RT ΣS) (rt_frames RT ΣI) S1 x) by (rewrite FRSI; exact C1).
    split; [rewrite FRSI; apply (aclient_mono _ _ _ _ _ _ _ C1); [intros e He; rewrite LVI; do 4 right; exact He| auto| lia]|]. split.
    - apply (fresh_apart_l RT AF ΣI m6 [(IA, 1024); (OC, 8 * 1024); (IDX, sc_idx L); (IMPL, 96)] (rt_live RT ΣS) IMPL 96 S1 x ART6 LVI ltac:(do 3 right; left; reflexivity)
               ltac:(clear - LOWI LOR S1R; ul) C1').
    - apply (fresh_apart_l RT AF ΣI m6 [(IA, 1024); (OC, 8 * 1024); (IDX, sc_idx L); (IMPL, 96)] (rt_live RT ΣS) IDX (sc_idx L) S1 x ART6 LVI ltac:(do 2 right; left; reflexivity)
               ltac:(clear - LOWI LOR S1R; ul) C1'). }

  assert (PIMJ : rw_cells bsegs m6 (F + 104) ([C8 (Z_to_bv 64 IMPL)] ++ [C8 (Z_to_bv 64 0)])).
  { apply Sj_stage1_kit.rw_cells_app. split; [exact PIM6|]. cbn [cells_size csize Nat.add]. replace (F + 104 + Z.of_nat 8) with (F + 112) by lia. exact PC16. }
  cbn [app] in PIMJ. clear PIM6 PC16 FOBJ6.
  apply impl16_s1 in IMC.
  pose proof IMC as IMV.
  lazymatch type of IMV with rw_cells _ _ _ (?c0 :: ?rest) => change (rw_cells bsegs m6 IMPL ([c0] ++ rest)) in IMV end.
  apply Sj_stage1_kit.rw_cells_app in IMV. destruct IMV as [IMV _].
  assert (FP7 : fp_ok RT ΣI lo [(F + 112, F + 120); (F + 128, F + 136)]).
  { repeat apply Forall_cons; [| | apply Forall_nil]; cbn [fst snd]; right; right; left; exists F, 3%nat; (split; [exact INFI|]); change (fs_size 3) with 512; lia. }
  assert (IM8 : IMPL mod 8 = 0 /\ IDX mod 8 = 0 /\ SB mod 8 = 0) by (clear - IM16 IX16 SB16; Z.div_mod_to_equations; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { refine (od_walkC4 (Z_to_bv 64 0x96f7c) usp S1 F lo IMPL BUF L gp (Z_to_bv 64 0x656e70) z0 z1 z2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (F + 96)) xs6 xs9 z3 z4 z5 z6 _ _ _ F6 fc6 m6
             ltac:(clear - FSG; ul) FLO ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) IMPOS (proj1 ILO) (proj1 IM8) IF' _ _ (AFV ΣI m6 ART6) P168 PIMJ PA24 IMV MI6).
    - intros m' MU WM. pose proof (shz_live RT AF ΣI m' IMPL 96 (art_of_munch RT AF ΣI m6 m' lo _ ART6 LOWI FP7 MU WM) INIM (proj1 IM8)) as X. exact X.
    - intros m' MU WM. apply (od_shz_lit RT AF ΣI m' 0x1179c0 96 (art_of_munch RT AF ΣI m6 m' lo _ ART6 LOWI FP7 MU WM));
        [unfold ACC_LITS; repeat (first [left; reflexivity | right])| reflexivity| lia| reflexivity]. }
  cbv beta. intros ms7 (m7 & a4'' & -> & MU7 & WM7 & MI7 & PA87 & PA247).
  apply evt_done.
  pose proof (art_of_munch RT AF ΣI m6 m7 lo _ ART6 LOWI FP7 MU7 WM7) as ART7.
  assert (AG67 : agree_on (fun x => ~ (F + 112 <= x < F + 120) /\ ~ (F + 128 <= x < F + 136)) m6 m7).
  { apply (agree_of_munch _ _ _ _ MU7). intros x (H1 & H2). cbn [outside]. repeat split; assumption. }
  clear ART6 MI6 PIMJ PA24 IMV FP7.
  xfer_all sj_lib sj_lib_agree m6 m7 AG67 WM7
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta;
          first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul | clear - Hx SF; lia | clear - Hx IF'; lia
                | destruct CPG as [E|(_ & P3 & P4 & P5 & _)]; [clear - Hx E CB0 CB1; lia| clear - Hx CB0 CB1 P3; lia] ])
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [clear - Hx; lia| clear - Hx FAV; lia])
    ltac:(intros a Ha; apply MU7; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R; split; [clear - R FSG; ul|]; split; [clear - R FSG; ul| exact I])
    ltac:(intros a Ha; apply MU7; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & _); split; [clear - C1; lia|]; split; [clear - C1; lia| exact I]).
  clear AG67 MU7.

  set (icap := Z.to_nat (roundup64 L + 9)).
  assert (EIC : 4 * Z.of_nat icap = sc_idx L /\ L + 9 <= Z.of_nat icap).
  { subst icap. unfold sc_idx. assert (0 <= roundup64 L + 9 /\ L <= roundup64 L) by (clear - LR; unfold roundup64; Z.div_mod_to_equations; lia). rewrite Z2Nat.id by lia. lia. }
  destruct EIC as (EIC & ICL).
  destruct (af_acc_live RT AF ΣI m7 IDX _ ART7 INIX) as (WRX & _). rewrite <- EIC in WRX.
  destruct (u32arr_of_wr m7 IDX icap WRX) as (ws0 & U0 & LW0).
  set (ES := mkS1Env (Z_to_bv 64 0x97254) (Z_to_bv 64 S1) gp (Z_to_bv 64 0x656e70) (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 L) (Z_to_bv 64 (F + 96))
               (Z_to_bv 64 (F + 104)) (Z_to_bv 64 BUF) (Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 228)) xs9 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (F + 192))
               F6 fc6 lo IMPL BUF IDX doc icap (Z_to_bv 64 0x1179d0) p12
               (mid16 p28 (Z_to_bv 64 L) (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA)) (le8 (Z_to_bv 64 0)) m7).

  assert (FINC : forall (m8 : mem) (code : Z) (out : list Z) (nxt' : word) (ws' : list word) q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F8 fc8,
            frm0 fc8 -> rt_after RT ΣI S1 lo m7 m8 -> rt_pres_fp (rt_live RT ΣI) (rt_frames RT ΣI) S1 (a1_FP ES) m7 m8 ->
            rw_cells bsegs m8 IMPL (parser_cells ES (wz (Z.of_nat (length out))) nxt' (wz BUF) (wz L)) ->
            u32arr bsegs m8 IDX ws' -> length ws' = icap -> firstn (length out + 3) ws' = map wz (out ++ [L; L; 0]) ->
            ((od_copied dz = true /\ (code, out) = stage1 doc) \/ (od_copied dz = false /\ code = 13 /\ out = [])) ->
            aevt ΣI K (MS (mkR (Z_to_bv 64 0x97254) (Z_to_bv 64 S1) gp (Z_to_bv 64 0x656e70) q0 q1 q2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 code) r1 r2 r3 r4 r5 r6 r7
                              (Z_to_bv 64 L) (Z_to_bv 64 (F + 96)) (Z_to_bv 64 (F + 104)) (Z_to_bv 64 BUF) (Z_to_bv 64 0) (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 228))
                              xs9 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (F + 192)) q3 q4 q5 q6) F8 (Z_to_bv 64 0x97254) fc8 None m8 (seg_rom bsegs))).
  { intros m8 code out nxt' ws' q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F8 fc8 FRM8 (ART8 & MI8 & WM8 & ST8) PR8 IMC8 U8 LW8 FW8 CODE.
    assert (AG78 : agree_on (fun x => (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + CN) \/ (SB <= x < SB + CAP)) m7 m8).
    { intros a Ha. apply (PR8 a); [apply ACLI; clear - Ha; tauto|]. unfold a1_FP, ES. cbn [e_THIS e_IDX e_cap outside]. rewrite EIC.
      destruct Ha as [H|[H|[H|[H|[H|H]]]]].
      - clear - H ILO LOR S1R. split; [ul|]. split; [ul| exact I].
      - clear - H IF' XF. split; [lia|]. split; [lia| exact I].
      - clear - H IS' XS. split; [lia|]. split; [lia| exact I].
      - clear - H IAV XAV. split; [lia|]. split; [lia| exact I].
      - destruct ICP as [E|(P1 & P2)]; [clear - H E; lia|]. clear - H P1 P2. split; [lia|]. split; [lia| exact I].
      - clear - H ISB XSB. split; [lia|]. split; [lia| exact I]. }
    clear ST6 ART7 MI7 IMC U0 WRX.
    xfer_all sj_lib sj_lib_agree m7 m8 AG78 WM8
      ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; subst S; clear - Hx S1R CB0 CB1; lia)
      ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [right; left; clear - Hx; lia| do 3 right; left; exact Hx])
      ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS' R]; apply PR8; [right; left; exact CS'|]; unfold a1_FP, ES; cbn [e_THIS e_IDX e_cap outside]; rewrite EIC;
            pose proof (af_live_range RT AF ΣI m8 IMPL 96 ART8 INIM) as (_ & _ & [X|X]); pose proof (af_live_range RT AF ΣI m8 IDX _ ART8 INIX) as (_ & _ & [Y|Y]);
            (split; [clear - R X IMPOS; ul|]; split; [clear - R Y IXPOS IXB; ul| exact I]))
      ltac:(intros a Ha; destruct (CALLI _ Ha) as (C1 & C2 & C3); apply PR8; [exact C1|]; unfold a1_FP, ES; cbn [e_THIS e_IDX e_cap outside]; rewrite EIC;
            split; [exact C2|]; split; [exact C3| exact I]).
    apply (KC ΣI S1 F A cap size COPY BUF SB IMPL IDX OC IA code out els _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 m8 FRM8).
    constructor.
    - constructor; try assumption; try (split; assumption).
      + rewrite FRSI, FRSS. exact FRS.
      + rewrite SPI, SPS. exact SP0.
      + eexists _, _. exact HI.
      + eexists _, _. exact HDR.
      + eexists. exact DOC.
    - exact DZ.
    - fold doc L s0 len0. rewrite LVI, LVS, LV. fold CAP. subst CN. destruct (od_copied dz); reflexivity.
    - fold doc L s0 len0. revert CPYA BUFB. subst bb. destruct (od_copied dz); intros CPYA BUFB; [| exact CPYA].
      destruct CPYA as (X1 & X2 & X3 & X4). repeat (split; [assumption|]). exact BUFB.
    - repeat split; assumption.
    - fold doc L. fold CAP. rewrite CRI, CRS. change (8 * 1024) with 8192. clear - CR. lia.
    - eexists _, _, _, _, _, _, _. exact LOWF.
    - fold doc L. exists jp. unfold od_parserC, wz.
      change [C1 (Z_to_bv 8 0); CB 7 jp; C8 (Z_to_bv 64 IMPL); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 SB)]
        with ([C1 (Z_to_bv 8 0); CB 7 jp] ++ [C8 (Z_to_bv 64 IMPL); C8 (Z_to_bv 64 L)] ++ [C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 1024)] ++ [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 SB)]).
      apply Sj_stage1_kit.rw_cells_app. split; [exact PA0|]. cbn [cells_size csize Nat.add]. replace (F + 96 + Z.of_nat 8) with (F + 104) by lia.
      apply Sj_stage1_kit.rw_cells_app. split; [exact PA87|]. cbn [cells_size csize Nat.add]. replace (F + 104 + Z.of_nat 16) with (F + 120) by lia.
      apply Sj_stage1_kit.rw_cells_app. split; [exact PA247|]. cbn [cells_size csize Nat.add]. replace (F + 120 + Z.of_nat 16) with (F + 136) by lia.
      exact PA403.
    - exact SH.
    - fold doc L. exact WRSB.
    - fold doc. exact CODE.
    - fold doc L. exists p12, p28, p50, (le8 (Z_to_bv 64 0)), nxt'. exact IMC8.
    - fold doc L. exists ws'. split; [exact U8|]. split; [rewrite LW8; exact EIC| exact FW8]. }
  clear KC.
  assert (PCS : rw_cells bsegs m7 IMPL (parser_cells ES (wz 0) (wz 0) (wz 0) (wz 0))) by exact IMC.
  assert (ST7 : stk bsegs m7 lo (bv_unsigned (Z_to_bv 64 S1))) by (rewrite EU1; exact ST6).
  assert (BLD : blen doc = L) by reflexivity.
  unfold lh_regs.
  destruct (od_copied dz) eqn:ECP.
  -
    subst bb CN. cbv iota in *.
    assert (BBL : Z.of_nat (length (padded_bytes doc)) = L + 64) by (unfold padded_bytes; rewrite length_app, zbytes_length, repeat_length; unfold L, zlength; lia).
    rewrite BBL in CB1.
    destruct CPG as [E|(INC & _ & _ & CLO & _)]; [clear - E LEN0; lia|].
    destruct ICP as [E|(ICP1 & ICP2)]; [clear - E LEN0; lia|].
    assert (INC' : In (COPY, len0 + 64) (rt_live RT ΣI)) by (rewrite LVI, LVS; do 5 right; exact INC).
    eapply (aevt_rt RT PMc); [| exact FRM6 |].
    { refine (HS1 ΣI PMc ES z0 z1 z2 _ d5 d6 d7 z3 z4 z5 z6 (wz 0) (wz 0) (wz 0) (wz 0) ws0 FDO MST _ _ LOWI _ _ _ ART7 MI7 ST7 PCS U0 LW0 BUFB FRM6).
      - constructor; unfold ES; cbn [e_bs e_lo e_sp e_THIS e_IDX e_BUF e_cap]; rewrite ?EU1, ?EIC, ?BLD.
        + exact DOCOK. + unfold S1_LEN_MAX. clear - LR. lia. + clear - LOWB SP0R SP0. unfold A1_GTOP. ul. + clear - LOR S1R. unfold A1_STACK. ul.
        + clear - IMPOS ILO. lia. + clear - IXPOS ILO. lia. + clear - CB0 CB1 CLO CPOS0. lia. + clear - ICL. lia.
        + exact IMX. + clear - ICP1 CB0 CB1. lia. + clear - ICP2 CB0 CB1. lia.
      - unfold a1_live, ES. cbn [e_bs e_THIS e_IDX e_BUF e_cap]. rewrite ?EIC, ?BLD.
        split; [exact INIM|]. split; [exact INIX|]. split; [exists COPY, (len0 + 64); split; [exact INC'|]; split; [exact COPY8|]; clear - CB0 CB1; lia|].
        split; [exact (proj1 IM8)|]. split; [exact (proj1 (proj2 IM8))| clear - ICL; lia].
      - unfold ES. cbn [e_lo e_sp]. rewrite EU1. clear - LOR S1R. ul.
      - unfold ES. cbn [e_sp]. rewrite EU1. clear - S1R UT. ul.
      - unfold ES. cbn [e_sp]. rewrite EU1. clear - S32. Z.div_mod_to_equations. lia. }
    intros c8 HQ8. eexists ΣI, _. split; [exact HQ8|].
    intros ms8 (m8 & RS8 & FRM8 & RA8 & PR8 & (ws' & nxt' & IMC8 & _ & U8 & LW8 & FW8 & _)) _.
    revert FRM8.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 ms8 (fun ms => frm0 (ms_fcsr ms) -> aevt ΣI K ms) RS8).
    intros q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F8 fc8 FRM8. cbn [ms_fcsr] in FRM8.
    unfold ES in RA8, PR8. cbn [e_sp e_lo e_m0 e_ra] in RA8, PR8 |- *. rewrite ?EU1 in RA8, PR8. rewrite (ret_pc_even 0x97254) by lia.
    exact (FINC m8 (fst (stage1 doc)) (snd (stage1 doc)) nxt' ws' q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F8 fc8 FRM8 RA8 PR8 IMC8 U8 LW8 FW8
             (or_introl (conj eq_refl (surjective_pairing _)))).
  -
    assert (DNIL : doc = []) by (subst doc; unfold od_doc; rewrite ECP; reflexivity).
    eapply (aevt_rt RT PMc); [| exact FRM6 |].
    { refine (HS1Z ΣI PMc ES z0 z1 z2 _ d5 d6 d7 z3 z4 z5 z6 (wz 0) (wz 0) (wz 0) (wz 0) ws0 FDO MST _ _ LOWI _ _ _ ART7 MI7 ST7 PCS U0 LW0 FRM6).
      - constructor; unfold ES; cbn [e_bs e_lo e_sp e_THIS e_IDX e_BUF e_cap]; rewrite ?EU1, ?EIC.
        + exact DNIL. + clear - LOWB SP0R SP0. unfold B1_GTOP. ul. + clear - LOR S1R. unfold B1_STACK. ul.
        + clear - IMPOS ILO. lia. + clear - IXPOS ILO. lia. + clear - ICL LR. lia. + exact IMX.
      - unfold a1z_live, ES. cbn [e_bs e_THIS e_IDX e_BUF e_cap]. rewrite ?EIC, ?BLD.
        split; [exact INIM|]. split; [exact INIX|]. split; [exact (proj1 IM8)|]. split; [exact (proj1 (proj2 IM8))| clear - ICL; lia].
      - unfold ES. cbn [e_lo e_sp]. rewrite EU1. clear - LOR S1R. ul.
      - unfold ES. cbn [e_sp]. rewrite EU1. clear - S1R UT. ul.
      - unfold ES. cbn [e_sp]. rewrite EU1. clear - S32. Z.div_mod_to_equations. lia. }
    intros c8 HQ8. eexists ΣI, _. split; [exact HQ8|].
    intros ms8 (m8 & RS8 & FRM8 & RA8 & PR8 & (ws' & nxt' & IMC8 & U8 & LW8 & FW8)) _.
    revert FRM8.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 ms8 (fun ms => frm0 (ms_fcsr ms) -> aevt ΣI K ms) RS8).
    intros q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F8 fc8 FRM8. cbn [ms_fcsr] in FRM8.
    unfold ES in RA8, PR8. cbn [e_sp e_lo e_m0 e_ra] in RA8, PR8 |- *. rewrite ?EU1 in RA8, PR8. rewrite (ret_pc_even 0x97254) by lia.
    exact (FINC m8 13 [] nxt' ws' q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 F8 fc8 FRM8 RA8 PR8 IMC8 U8 LW8 FW8
             (or_intror (conj eq_refl (conj eq_refl eq_refl)))).
Qed.
End PhaseC1.
