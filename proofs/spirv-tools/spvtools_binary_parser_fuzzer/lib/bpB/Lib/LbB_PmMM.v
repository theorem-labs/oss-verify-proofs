(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_ContStmt LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DiagStmt LbB_WoDiagP LbB_WoKit2 LbB_PmMagW LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoDiagC LbB_WdMMS LbB_PmHTail LbB_WoKit3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoShK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WoDiagC2 LbB_WoDiagH LbB_PmCall LbB_PmGlue LbB_DRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep BZBridge.
Import ListNotations.
Open Scope Z_scope.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac mkin := solve [cbn [In]; repeat (first [left; reflexivity | right])].

Lemma mm_shvis_wm : forall m m' lo hi, shvis m lo hi -> wmono asegs m m' -> AIMG_TOP <= sh (hull_lo lo) -> shvis m' lo hi.
Proof.
  intros m m' lo hi SV WM HA. unfold shvis in *. pose proof SV as (T1 & T2 & T3).
  split; [exact T1|]. split; [exact T2|]. intros x Hx. destruct (T3 x Hx) as [HV _].
  pose proof (WM (wa x) HV) as HV'. split; [exact HV'|].
  assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (rewrite wa_unsigned by lia; lia).
  rewrite (BakeStackRep.wview_high m' (wa x) HX) in HV'.
  unfold mrd. destruct (m' (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
Qed.

Lemma mm_fld_of_cells4 : forall (m : mem) p v, rw_cells asegs m p [C4 (Z_to_bv 64 v)] -> fldA m p 4 v.
Proof.
  intros m p v Hc. unfold fldA, fld.
  pose proof (rw_cells_read asegs m p _ 0%nat _ Hc eq_refl) as RD. replace (p + Z.of_nat 0) with p in RD by lia.
  rewrite <- LbB_Conv.rdn_of_ov. exact RD.
Qed.

Section MM.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV_P5 ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV_P5 ds_repA.
  Hypothesis HTR : pm_tr_ok H.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Lemma mm_dtr : ds_tr_ok H.
  Proof. unfold pm_tr_ok, PM_DEL_RAS in HTR. unfold ds_tr_ok. exact (Forall_inv HTR). Qed.

  Section MMW.
    Variable e : went H.
    Variables ff fp : Z.
    Variable mo0 : Model.
    Variable w : piw H.
    Variable c0 : parserC.
    Variable LBs : list block.
    Variable s0 : as_St H.
    Variable LB0 : list block.
    Variable m0 : mem.
    Variable XSc0 : list (Z * Z).
    Hypothesis HP : wpre H e.
    Hypothesis HWL : bp_wl H e ff w.
    Hypothesis HPF : bp_pfresh H w s0 LB0 LBs m0 c0.
    Hypothesis HI0 : winv H e ff fp XSc0 s0 LB0 m0.
    Hypothesis HW0 : w_words e = 0.

    Lemma mm_pp : bp_pp H w LB0 LBs m0 c0.
    Proof. exact (proj1 HPF). Qed.

    Lemma mm_md : mdef m0 (pw_p H w) PARSER_SIZE.
    Proof. exact (bp_pp_mdef H w LB0 LBs m0 c0 mm_pp). Qed.

    Lemma mm_al : PM_RESERVE <= as_AL H s0.
    Proof. exact (bp_al_res H w s0 _ (proj1 (proj2 (proj2 HPF)))). Qed.

    Lemma mm_meas : pm_meas_ok (pw_n H w) LBs.
    Proof.
      pose proof HPF as (PP & (HD & _) & _).
      pose proof HWL as (_ & _ & _ & Wn & _).
      pose proof HP as (_ & _ & (Hn0 & _) & _).
      apply (LbB_WoDiagC2.bp_meas H w LB0 LBs m0 c0 PP (bp_phc_ste _ _ _ _ HD)). rewrite Wn. exact Hn0.
    Qed.

    Lemma mm_geo : exists q, ff = 64 * q /\ 0 <= ff /\ AIMG_TOP + AFS_HDR <= ff /\ ff + WO_FLAGP <= wS1 e - AINTRIN_STACK
      /\ (sh ff + 512 <= ff \/ ff + 4096 <= sh ff) /\ sh ff + 512 <= wS1 e - AINTRIN_STACK /\ 2 ^ 45 <= wS1 e
      /\ wS1 e + 192 <= 2 ^ 47 /\ ff + 4096 <= w_lo e.
    Proof.
      destruct (wframe_bounds H e ff fp XSc0 s0 LB0 m0 HP HI0) as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
      pose proof (LbB_WoDiagC.w_geo2 H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al) as (G1 & G2 & G3).
      exists (ff / 64). pose proof (Z.div_mod ff 64 ltac:(lia)) as D. rewrite B64, Z.add_0_r in D.
      unfold WO_FLAGP, AINTRIN_STACK in *. repeat split; lia.
    Qed.

    Lemma mm_sh_add : forall k, sh (ff + 8 * k) = sh ff + k.
    Proof. intros k. unfold sh. replace (ff + 8 * k) with (ff + k * 8) by ring. rewrite Z.div_add by lia. ring. Qed.

    Lemma mm_mod8 : forall k, (ff + 8 * k) mod 8 = 0.
    Proof.
      intros k. destruct mm_geo as (q & Hq & _). rewrite Hq.
      replace (64 * q + 8 * k) with ((8 * q + k) * 8) by ring. apply Z.mod_mul. lia.
    Qed.

    Lemma mm_ff8 : ff mod 8 = 0.
    Proof. pose proof (mm_mod8 0) as M. rewrite Z.mul_0_r, Z.add_0_r in M. exact M. Qed.

    Local Abbreviation wsr := (LbB_WoDiagC.wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0).
    Local Abbreviation wxkeep := (LbB_WoDiagC.wxkeep H e ff fp LB0).
    Let WST := LbB_WoDiagC.w_start H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al.
    Let WCH := LbB_WoDiagC.w_chunk H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al.
    Let WEX := LbB_WoDiagC.w_exit H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al.
    Let WGEO := LbB_WoDiagC.w_geo H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al.
    Let WOBJ := LbB_WoDiagC.w_obj H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al.
    Let WFK := LbB_WoDiagC.w_fld_keep H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al.
    Let WXA := LbB_WoDiagC.w_xagree H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al.
    Let WMS := LbB_WoDiagC2.w_memset H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al mm_meas.
    Let WCT := LbB_WoDiagC2.w_ctor H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al mm_meas HCTOR.
    Let WCS := LbB_WoDiagC2.w_cseq H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al mm_meas HCSEQ.
    Let WDT := LbB_WoDiagC2.w_dtor H HHbp ds_repA DSL mm_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL mm_pp HI0 mm_md mm_al mm_meas HDTOR.

    Definition mmP0 (m : mem) : Prop :=
      bp_shad ff [20; 21]%nat m /\ fldA m (ff + 3504) 8 0 /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3536) 8 0
      /\ fldA m (ff + 3376 + 32) 8 0.

    Definition mmR1 (R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 3456) /\ getr R 22 = wz (ff + 3504).

    Definition mmRms (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (0xea7c4 + 4356) /\ getr R 10 = wz (ff + 32) /\ getr R 11 = wz 0 /\ getr R 12 = wz 16
      /\ getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 32) /\ getr R 22 = wz (ff + 3504).

    Definition mmPms (m : mem) : Prop :=
      bp_shad ff [0; 2; 12; 20; 21]%nat m /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3536) 8 0
      /\ fldA m (ff + 3376 + 32) 8 0
      /\ (exists junk, rw_cells asegs m (ff + 32) [CB 16 junk]) /\ accessible m (ff + 32) 16 /\ shvis m (ff + 32) (ff + 32 + 16).

    Definition mmR2 (R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 32) /\ getr R 22 = wz (ff + 3504).

    Definition mmP2 (m : mem) : Prop :=
      bp_shad ff [0; 2; 12; 20; 21]%nat m /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3536) 8 0
      /\ fldA m (ff + 3376 + 32) 8 0 /\ rw_cells asegs m (ff + 32) [CB 16 (poison_bytes 16 0)].

    Definition mmRct (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (0xea7c4 + 4440) /\ getr R 10 = wz (ff + 800) /\ getr R 11 = wz (ff + 32) /\ getr R 12 = wz (ff + 3376)
      /\ getr R 13 = wz (ff + 96) /\ getr R 14 = wz 18446744073709551612 /\ getr R 15 = wz (ff + 160)
      /\ getr R 18 = wz (ff + 800) /\ getr R 25 = wz (ff + 96) /\ getr R 26 = wz (ff + 160) /\ getr R 22 = wz (ff + 3504).

    Definition mmPct (m : mem) : Prop :=
      bp_shad ff [0; 1; 2; 12; 20; 21]%nat m /\ wr_at asegs m ff 4096 /\ fldA m (ff + 3376 + 32) 8 0
      /\ fldA m (ff + 96) 2 0 /\ fldA m (ff + 160) 2 0 /\ fldA m (ff + 32) 8 0 /\ fldA m (ff + 32 + 8) 8 0
      /\ fldA m (ff + 32 + 16) 8 0
      /\ (exists j, rw_cells asegs m (ff + 96 + 2) [CB 22 j]) /\ (exists j, rw_cells asegs m (ff + 160 + 2) [CB 22 j]).

    Definition mmR3 (R : bvmap 5 word) : Prop :=
      getr R 18 = wz (ff + 800) /\ getr R 25 = wz (ff + 96) /\ getr R 26 = wz (ff + 160) /\ getr R 22 = wz (ff + 3504).

    Definition mmP3 (m : mem) : Prop :=
      bp_shad ff [0; 1; 2; 12; 20; 21]%nat m /\ fldA m (ff + 96) 1 0 /\ fldA m (ff + 160) 1 0.

    Ltac shf := match goal with |- fldA ?M (sh ?f + ?k) 1 ?v =>
      let a := eval vm_compute in (ASHADOW_BASE + k) in
      replace (sh f + k) with (f / 8 + a) by (unfold sh, ASHADOW_BASE; lia); assumption end.
    Ltac shfs := repeat (apply Forall_cons; [cbv beta; cbn [fst snd]; shf |]); apply Forall_nil.
    Ltac flw := unfold bp_flw; cbn [fst snd]; unfold sh, ASHADOW_BASE, WO_FLAGP in *; lia.
    Ltac dj := cbn [disjoint_from]; unfold sh, ASHADOW_BASE, WO_FLAGP, AINTRIN_STACK in *; lia.
    Ltac mkin2 := solve [cbn [In WD_KEEP WD_MKEEP]; repeat (first [left; reflexivity | right])].

    Lemma mm_wsr_ex : forall pc REGS S (P : mem -> Prop) (Pj : list byte -> mem -> Prop) spent c,
      wsr pc REGS S P spent c -> (forall m, P m -> exists j, Pj j m) ->
      exists j, wsr pc REGS S (fun m => P m /\ Pj j m) spent c.
    Proof.
      intros pc REGS S P Pj spent c (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL) EX.
      destruct (EX m HPm) as (j & Hj). exists j.
      exists s, R, F, fc, m, XSc, LB.
      split; [exact KR|]. split; [exact MP|]. split; [exact VIS|]. split; [exact RF|]. split; [exact FZ|].
      split; [exact HI|]. split; [exact SL|]. split; [exact RC|]. split; [exact RG|]. split; [exact AG|].
      split; [exact OWN|]. split; [exact SES|]. split; [exact (conj HPm Hj)|]. exact AL.
    Qed.

    Lemma mm_len : forall L, length (wo_sh L) = 476%nat.
    Proof.
      intros L. unfold wo_sh. rewrite length_app, repeat_length.
      assert (G : forall L L' k os, length (wo_sh_go L k os) = length (wo_sh_go L' k os)).
      { intros L1 L2 k os. revert k. induction os as [|[n r] os IH]; intros k; [reflexivity|].
        cbn [wo_sh_go]. rewrite !length_app, !repeat_length, IH. reflexivity. }
      rewrite (G L [] 0%nat WO_OBJS). vm_compute. reflexivity.
    Qed.

    Lemma mm_sh_hi : forall k, 0 <= k -> AIMG_TOP <= sh (hull_lo (ff + k)).
    Proof.
      intros k Hk. destruct mm_geo as (q & Hq & B0 & _). unfold sh, hull_lo.
      pose proof (Z.mod_le (ff + k) 64 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_pos (ff + k - (ff + k) mod 64) 8 ltac:(lia) ltac:(lia)).
      unfold ASHADOW_BASE, AIMG_TOP. lia.
    Qed.

    Definition mmR4 (R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 800) /\ getr R 21 = wz 18446744073709551608 /\ getr R 22 = wz (ff + 3504).

    Definition mmP4 (m : mem) : Prop := bp_shad ff [12; 20; 21]%nat m.

    Lemma mm_addr : forall m L k n, bp_shad ff L m -> 0 <= k -> k mod 8 = 0 -> 0 <= n -> n mod 8 = 0 ->
      k / 8 + n / 8 <= 476 -> firstn (Z.to_nat (n / 8)) (skipn (Z.to_nat (k / 8)) (wo_sh L)) = repeat 0 (Z.to_nat (n / 8)) ->
      addressable m (ff + k) n.
    Proof.
      intros m L k n SH K0 K8 N0 N8 LN FZ. destruct mm_geo as (q & Hq & B0 & _).
      apply (bp_shad_addr ff L m k n SH B0 mm_ff8 K0 K8 N0 N8); [rewrite mm_len; exact LN | exact FZ].
    Qed.

    Lemma mm_dsobj : forall m L, bp_shad ff L m -> firstn 49 (skipn 100 (wo_sh L)) = repeat 0 49 ->
      ds_obj H ((6, ff, fp) :: w_LF e) m (wS1 e) (ff + 800) DS_SIZE /\ obj_inframe ((6, ff, fp) :: w_LF e) (ff + 800) DS_SIZE.
    Proof.
      intros m L SH FZ. assert (M800 := mm_mod8 100). replace (ff + 8 * 100) with (ff + 800) in M800 by ring.
      exact (WOBJ m 800 392 ltac:(lia) ltac:(lia) ltac:(unfold WO_FLAGP; lia) M800
        (mm_addr m L 800 392 SH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(reflexivity) ltac:(apply Z.leb_le; reflexivity) FZ)).
    Qed.

    Lemma mm_shkeep : forall L m m', bp_shad ff L m -> wxkeep [(ff + 800, ff + 800 + DS_SIZE)] m m' -> bp_shad ff L m'.
    Proof.
      intros L m m' SH XK. destruct mm_geo as (q & Hq & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      assert (LW := mm_len L). unfold bp_shad in *. apply (LbB_DRep.u8arr_pteq m m' _ _ SH). intros x Hx.
      rewrite length_map, LW in Hx. change (Z.of_nat 476) with 476 in Hx.
      pose proof (Z.div_pos ff 8 B0 ltac:(lia)).
      apply (WXA _ m m' XK x); [|unfold sh, ASHADOW_BASE, AINTRIN_STACK in *; lia].
      split; [right; lia|]. constructor; [unfold DS_SIZE, sh, ASHADOW_BASE in *; cbn [fst snd]; lia | constructor].
    Qed.

    Definition mmR5 (R : bvmap 5 word) : Prop := getr R 21 = wz 18446744073709551608 /\ getr R 24 = wz 18446744073709551612 /\ getr R 22 = wz (ff + 3504).

    Definition mmRdt (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (0xea7c4 + 4568) /\ getr R 10 = wz (ff + 800) /\ getr R 21 = wz 18446744073709551608
      /\ getr R 24 = wz 18446744073709551612 /\ getr R 22 = wz (ff + 3504).

    Lemma mm_s5 : forall Q c spent, spent <= 624 ->
      wsr (0xea7c4 + 4568) mmR5 None (bp_shad ff [12; 20; 21]%nat) spent c -> bp_kwcf H e ff fp Q mo0 -> as_SR H Q c.
    Proof.
      intros Q c spent Hs HW K.
      destruct mm_geo as (q & Hq & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      apply (WCH Q (0xea7c4 + 4568) BP_WCF mmR5 (fun R => getr R 24 = wz 18446744073709551612 /\ getr R 22 = wz (ff + 3504)) None
        (bp_shad ff [12; 20; 21]%nat) (bp_shad ff [20; 21]%nat) spent c HW); [|intros c' HW'].
      - intros R F fc m XSc s LB RG RC HPm HI SL SES.
        destruct (WGEO XSc s LB m HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
        pose proof RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20).
        pose proof RG as (R21 & R24 & R22).
        destruct (LbB_WdMMS.wd_mm5_ea7c4 R F fc m ff ltac:(unfold LbB_WdMMS.wd_mm5_pre; repeat (first [assumption | lia | split])))
          as (R' & M' & ST & MU & WM & S149 & S148 & S143 & S142 & S141 & S140 & S147 & S146 & S145 & S144 & S135 & S134 & S133 & S132 & S139 & S138 & S137 & S136 & S127 & S126 & S125 & S124 & S131 & S130 & S129 & S128 & S119 & S118 & S117 & S116 & S123 & S122 & S121 & S120 & S111 & S110 & S109 & S108 & S115 & S114 & S113 & S112 & S103 & S102 & S101 & S100 & S107 & S106 & S105 & S104 & Q19 & Q21 & KP).
        exists R', M'. eexists. split; [exact ST|]. split; [exact MU|]. split; [exact WM|].
        split; [repeat (apply Forall_cons; [flw|]); apply Forall_nil|].
        split; [apply Forall_forall; intros iv _; exact I|].
        split; [unfold bp_rc; repeat split; first [assumption | rewrite KP by mkin; assumption]|].
        split; [split; rewrite KP by mkin; assumption|].
        apply (bp_shad_set ff [12; 20; 21]%nat [20; 21]%nat m M' _ [(100, 150)] [(100, 18446744073709551608); (101, 18446744073709551608); (102, 18446744073709551608); (103, 18446744073709551608); (104, 18446744073709551608); (105, 18446744073709551608); (106, 18446744073709551608); (107, 18446744073709551608); (108, 18446744073709551608); (109, 18446744073709551608); (110, 18446744073709551608); (111, 18446744073709551608); (112, 18446744073709551608); (113, 18446744073709551608); (114, 18446744073709551608); (115, 18446744073709551608); (116, 18446744073709551608); (117, 18446744073709551608); (118, 18446744073709551608); (119, 18446744073709551608); (120, 18446744073709551608); (121, 18446744073709551608); (122, 18446744073709551608); (123, 18446744073709551608); (124, 18446744073709551608); (125, 18446744073709551608); (126, 18446744073709551608); (127, 18446744073709551608); (128, 18446744073709551608); (129, 18446744073709551608); (130, 18446744073709551608); (131, 18446744073709551608); (132, 18446744073709551608); (133, 18446744073709551608); (134, 18446744073709551608); (135, 18446744073709551608); (136, 18446744073709551608); (137, 18446744073709551608); (138, 18446744073709551608); (139, 18446744073709551608); (140, 18446744073709551608); (141, 18446744073709551608); (142, 18446744073709551608); (143, 18446744073709551608); (144, 18446744073709551608); (145, 18446744073709551608); (146, 18446744073709551608); (147, 18446744073709551608); (148, 18446744073709551608); (149, 18446744073709551608)] HPm MU WM).
        + vm_compute. reflexivity.
        + intros i Hi Hr. cbn [in_rngs] in Hr. cbn [outside]. unfold sh, ASHADOW_BASE in *. lia.
        + shfs.
      - apply (WEX Q BP_WCF (fun R => getr R 24 = wz 18446744073709551612 /\ getr R 22 = wz (ff + 3504)) (fun R => getr R 22 = wz (ff + 3504)) (bp_shad ff [20; 21]%nat)
          spent c' [20; 21]%nat (bp_slots H) (-4) HW').
        + unfold PM_RESERVE. lia.
        + exact HPF.
        + intros m Hm. exact Hm.
        + intros m Sm _. exact Sm.
        + intros R (R24 & R22). split; [exact R22|]. rewrite R24. unfold wz. rewrite <- (BZBridge.Z_to_bv_mod64 (-4)). reflexivity.
        + lia.
        + exact K.
    Qed.

    Lemma mm_s4 : forall Q c len spent, spent <= 624 ->
      wsr (0xea7c4 + 4556) mmR4 (Some (ff + 800, -4, len)) mmP4 spent c -> bp_kwcf H e ff fp Q mo0 -> as_SR H Q c.
    Proof.
      intros Q c len spent Hs HW K.
      destruct mm_geo as (q & Hq & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      apply (WCH Q (0xea7c4 + 4556) ADS_DTOR mmR4 mmRdt (Some (ff + 800, -4, len)) mmP4 mmP4 spent c HW); [|intros c' HW'].
      - intros R F fc m XSc s LB RG RC HPm HI SL SES.
        destruct (WGEO XSc s LB m HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
        pose proof RG as (R18 & R21 & R22).
        assert (FE : fldA m (ff + 1160) 4 4294967292).
        { cbn [LbB_WoDiagC.wses] in SES. destruct SES as (DB & REP & _).
          pose proof DSL as DSL'. destruct DSL' as [_ DE _ _ _ _].
          pose proof (mm_fld_of_cells4 _ _ _ (DE _ _ _ _ _ _ REP)) as X.
          replace (ff + 1160) with (ff + 800 + DS_ERR_OFF) by (unfold DS_ERR_OFF; lia). exact X. }
        destruct (LbB_WdMMS.wd_mm4_ea7c4 R F fc m ff ltac:(unfold LbB_WdMMS.wd_mm4_pre; repeat (first [assumption | lia | split])))
          as (R' & M' & ST & EM & Q1 & Q10 & Q18 & Q24 & KP).
        subst M'.
        exists R', m, []. split; [exact ST|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
        split; [constructor|]. split; [constructor|].
        split; [unfold bp_rc in *; rewrite !KP by mkin; exact RC|].
        split; [unfold mmRdt; repeat split; first [assumption | rewrite KP by mkin; assumption]|]. exact HPm.
      - apply (WDT Q mmRdt mmR5 mmP4 (bp_shad ff [12; 20; 21]%nat) spent c' (0xea7c4 + 4568) (ff + 800) (-4) len HW').
        + intros R (R1 & R10 & _). split; assumption.
        + reflexivity.
        + lia.
        + unfold PM_RESERVE. lia.
        + unfold PO_PF. mkin.
        + lia.
        + unfold DS_SIZE. lia.
        + intros m SH. exact (mm_dsobj m _ SH ltac:(vm_compute; reflexivity)).
        + intros R R' (_ & _ & R21 & R24 & R22) KP. unfold mmR5. rewrite !KP by mkin2. repeat split; assumption.
        + intros m m' SH XK. exact (mm_shkeep _ m m' SH XK).
        + intros c'' HW''. exact (mm_s5 Q c'' spent Hs HW'' K).
    Qed.

    Definition mmRcs (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (0xea7c4 + 4556) /\ getr R 10 = wz (ff + 800) /\ getr R 11 = wz 147744 /\ getr R 12 = wz 15
      /\ getr R 18 = wz (ff + 800) /\ getr R 21 = wz 18446744073709551608 /\ getr R 22 = wz (ff + 3504).

    Lemma mm_lit : (forall m', ACONST m' -> accessible m' 147744 15) /\
      (exists bs, length bs = Z.to_nat 15 /\ forall m', mem_inv asegs m' -> bytes_at asegs m' 147744 bs).
    Proof.
      assert (HG : In (147744, 16, 32) aglobals) by (unfold aglobals; mkin).
      split.
      - intros m' AC. apply (addressable_accessible m' 147744 16 147744 15);
          [eapply ACONST_global_addressable; [exact AC | exact HG | lia] | lia | lia | unfold AAPP_HI; lia].
      - assert (RD : exists bs, PropExec.rdn asegs (fun _ => None) (Z_to_bv 64 147744) (Z.to_nat 15) = Some bs)
          by (eexists; vm_compute; reflexivity).
        destruct RD as (bs & RD). exists bs. split; [exact (LbB_PmGlue.rdn_length _ _ _ _ _ RD)|].
        intros m' MI. exact (proj1 (LbB_PmGlue.img_lit m' 147744 (Z.to_nat 15) bs MI ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) RD)).
    Qed.

    Lemma mm_s3 : forall Q c, wsr (0xea7c4 + 4440) mmR3 (Some (ff + 800, -4, 0)) mmP3 0 c ->
      bp_kwcf H e ff fp Q mo0 -> as_SR H Q c.
    Proof.
      intros Q c HW K.
      destruct mm_geo as (q & Hq & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      apply (WCH Q (0xea7c4 + 4440) APUT_CSEQ mmR3 mmRcs (Some (ff + 800, -4, 0)) mmP3 mmP4 0 c HW); [|intros c' HW'].
      - intros R F fc m XSc s LB RG RC HPm HI SL SES.
        destruct (WGEO XSc s LB m HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
        pose proof RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20).
        pose proof RG as (R18 & R25 & R26 & R22).
        pose proof HPm as (SH & F96 & F160).
        destruct (LbB_WdMMS.wd_mm3_ea7c4 R F fc m ff ltac:(unfold LbB_WdMMS.wd_mm3_pre; repeat (first [assumption | lia | split])))
          as (R' & M' & ST & MU & WM & S22 & S21 & S20 & S14 & S13 & S12 & S6 & S5 & S4 & Q1 & Q10 & Q11 & Q12 & Q18 & Q19 & Q21 & Q25 & Q26 & KP).
        assert (SD : sh (ff + 800) = sh ff + 100) by (rewrite <- mm_sh_add; f_equal; lia).
        exists R', M'. eexists. split; [exact ST|]. split; [exact MU|]. split; [exact WM|].
        split; [repeat (apply Forall_cons; [flw|]); apply Forall_nil|].
        split.
        { repeat (apply Forall_cons; [cbn [wfree fst snd]; rewrite SD; change (nsh DS_SIZE) with 49; unfold DS_SIZE;
            unfold sh, ASHADOW_BASE in *; lia|]); apply Forall_nil. }
        split; [unfold bp_rc; repeat split; first [assumption | rewrite KP by mkin; assumption]|].
        split; [unfold mmRcs; repeat split; first [assumption | rewrite KP by mkin; assumption]|].
        unfold mmP4. apply (bp_shad_set ff [0; 1; 2; 12; 20; 21]%nat [12; 20; 21]%nat m M' _ [(4, 7); (12, 15); (20, 23)] [(4, 18446744073709551608); (5, 18446744073709551608); (6, 18446744073709551608); (12, 18446744073709551608); (13, 18446744073709551608); (14, 18446744073709551608); (20, 18446744073709551608); (21, 18446744073709551608); (22, 18446744073709551608)] SH MU WM).
        + vm_compute. reflexivity.
        + intros i Hi Hr. cbn [in_rngs] in Hr. cbn [outside]. unfold sh, ASHADOW_BASE in *. lia.
        + shfs.
      - destruct mm_lit as (LACC & LBY).
        apply (WCS Q mmRcs mmR4 mmP4 mmP4 0 c' (0xea7c4 + 4556) (ff + 800) (-4) 0 147744 15 HW').
        + intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
        + reflexivity.
        + lia.
        + unfold ds_cost, PM_RESERVE. lia.
        + lia.
        + unfold DS_SIZE. lia.
        + intros m SH. exact (mm_dsobj m _ SH ltac:(vm_compute; reflexivity)).
        + lia.
        + unfold AIMG_LO. lia.
        + unfold AIMG_TOP. lia.
        + exact LACC.
        + exact LBY.
        + lia.
        + intros R R' (_ & _ & _ & _ & R18 & R21 & R22) KP _. unfold mmR4. rewrite !KP by mkin2. repeat split; assumption.
        + intros m m' SH XK. exact (mm_shkeep _ m m' SH XK).
        + intros c'' HW''. apply (mm_s4 Q c'' (0 + 15) (0 + ds_cost (0 + 15))); [unfold ds_cost; lia | exact HW'' | exact K].
    Qed.

    Lemma mm_s2 : forall Q c, wsr (0xea7c4 + 4356) mmR2 None mmP2 0 c -> bp_kwcf H e ff fp Q mo0 -> as_SR H Q c.
    Proof.
      intros Q c HW K.
      destruct mm_geo as (q & Hq & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      apply (WCH Q (0xea7c4 + 4356) ADS_CTOR mmR2 mmRct None mmP2 mmPct 0 c HW); [|intros c' HW'].
      - intros R F fc m XSc s LB RG RC HPm HI SL SES.
        destruct (WGEO XSc s LB m HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
        pose proof RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20).
        pose proof RG as (R18 & R24 & R22).
        pose proof HPm as (SH & FC & FK & F32 & PZ).
        assert (MB : fldA m (wS1 e + 40) 8 ASHADOW_BASE).
        { pose proof SL as (_ & X & _).
          replace [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE); C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]
            with ([C8 (wz (w_words e)); C8 (wz (w_n e))] ++ [C8 (wz ASHADOW_BASE)] ++ [C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]) in X
            by reflexivity.
          apply rw_cells_app in X as [_ X]. apply rw_cells_app in X as [X _].
          replace (wS1 e + 24 + Z.of_nat (cells_size [C8 (wz (w_words e)); C8 (wz (w_n e))])) with (wS1 e + 40) in X by (cbn; lia).
          eapply LbB_WoDiagH.w_fld_of_cells8; [exact X | unfold ASHADOW_BASE; lia]. }
        assert (C16 : (ff + 3376) mod 16 = 0).
        { rewrite Hq. replace (64 * q + 3376) with ((4 * q + 211) * 16) by ring. apply Z.mod_mul. lia. }
        destruct (LbB_WdMMS.wd_mm2_ea7c4 R F fc m ff (wS1 e) (ff + 3376) 0 ASHADOW_BASE
          ltac:(unfold LbB_WdMMS.wd_mm2_pre; repeat (first [assumption | lia | split]))) as (R' & M' & ST & MU & WM & F160 & F96 & S14 & S13 & S12 & F48 & Q1 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q18 & Q19 & Q20 & Q24 & Q25 & Q26 & Q27 & KP).
        assert (LW := mm_len [0; 2; 12; 20; 21]%nat).
        assert (SH' : bp_shad ff [0; 1; 2; 12; 20; 21]%nat M').
        { apply (bp_shad_set ff [0; 2; 12; 20; 21]%nat [0; 1; 2; 12; 20; 21]%nat m M' _ [(12, 15)] [(12, 0); (13, 0); (14, 0)] SH MU WM).
          - vm_compute. reflexivity.
          - intros i Hi Hr. rewrite LW in Hi. cbn [in_rngs] in Hr. cbn [outside]. unfold sh, ASHADOW_BASE in *. lia.
          - shfs. }
        exists R', M'. eexists. split; [exact ST|]. split; [exact MU|]. split; [exact WM|].
        split; [repeat (apply Forall_cons; [flw|]); apply Forall_nil|].
        split; [apply Forall_forall; intros iv _; exact I|].
        split; [unfold bp_rc; repeat split; first [assumption | rewrite KP by mkin; assumption]|].
        split; [unfold mmRct; repeat split; first [assumption | rewrite KP by mkin; assumption]|].
        unfold mmPct. split; [exact SH'|].
        split; [eapply wr_at_transport; [exact G1 | exact WM]|].
        split; [eapply LbB_PmCall.fld_munch; [exact F32 | exact MU | dj | lia | lia]|].
        split; [exact F96|]. split; [exact F160|].
        split.
        { pose proof (LbB_WoDiagH.w_zero_fld m (ff + 32) 16 0 PZ ltac:(lia) ltac:(cbn; lia)) as Z0.
          rewrite Z.add_0_r in Z0. eapply LbB_PmCall.fld_munch; [exact Z0 | exact MU | dj | lia | lia]. }
        split.
        { pose proof (LbB_WoDiagH.w_zero_fld m (ff + 32) 16 8 PZ ltac:(lia) ltac:(cbn; lia)) as Z8.
          eapply LbB_PmCall.fld_munch; [exact Z8 | exact MU | dj | lia | lia]. }
        split; [replace (ff + 32 + 16) with (ff + 48) by ring; exact F48|].
        split.
        { destruct (LbB_WoDiagH.w_junk H e ff fp XSc s LB m (ff + 96 + 2) 22 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (j & JK).
          exists j. eapply rw_cells_transport; [exact JK | exact MU | exact WM | cbn; dj]. }
        { destruct (LbB_WoDiagH.w_junk H e ff fp XSc s LB m (ff + 160 + 2) 22 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (j & JK).
          exists j. eapply rw_cells_transport; [exact JK | exact MU | exact WM | cbn; dj]. }
      - assert (AD : forall m L k n, bp_shad ff L m -> 0 <= k -> k mod 8 = 0 -> 0 <= n -> n mod 8 = 0 ->
            k / 8 + n / 8 <= 476 -> firstn (Z.to_nat (n / 8)) (skipn (Z.to_nat (k / 8)) (wo_sh L)) = repeat 0 (Z.to_nat (n / 8)) ->
            addressable m (ff + k) n).
        { intros m L k n SH K0 K8 N0 N8 LN FZ. apply (bp_shad_addr ff L m k n SH B0 mm_ff8 K0 K8 N0 N8); [rewrite mm_len; exact LN | exact FZ]. }
        apply (WCT Q mmRct mmR3 mmPct mmP3 0 c' (0xea7c4 + 4440) (ff + 800) (ff + 32) (ff + 3376) (ff + 96) (ff + 160) (-4) HW').
        + intros R (R1 & R10 & R11 & R12 & R13 & R14 & R15 & _). repeat split; assumption.
        + reflexivity.
        + lia.
        + unfold PM_RESERVE. lia.
        + lia.
        + lia.
        + unfold DS_SIZE. lia.
        + intros m (SH & WR & F32 & F96 & F160 & F32a & F40 & F48 & (j1 & J1) & (j2 & J2)).
          exists [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0], j1, j2.
          assert (M800 := mm_mod8 100). assert (M32 := mm_mod8 4). assert (M96 := mm_mod8 12).
          assert (M160 := mm_mod8 20). assert (M3376 := mm_mod8 422).
          replace (ff + 8 * 100) with (ff + 800) in M800 by ring. replace (ff + 8 * 4) with (ff + 32) in M32 by ring.
          replace (ff + 8 * 12) with (ff + 96) in M96 by ring. replace (ff + 8 * 20) with (ff + 160) in M160 by ring.
          replace (ff + 8 * 422) with (ff + 3376) in M3376 by ring.
          destruct (WOBJ m 800 392 ltac:(lia) ltac:(lia) ltac:(unfold WO_FLAGP; lia) M800
            (AD m _ 800 392 SH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(vm_compute; reflexivity))) as (DO1 & DI1).
          destruct (WOBJ m 32 24 ltac:(lia) ltac:(lia) ltac:(unfold WO_FLAGP; lia) M32
            (AD m _ 32 24 SH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(vm_compute; reflexivity))) as (DO2 & DI2).
          destruct (WOBJ m 96 24 ltac:(lia) ltac:(lia) ltac:(unfold WO_FLAGP; lia) M96
            (AD m _ 96 24 SH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(vm_compute; reflexivity))) as (DO3 & DI3).
          destruct (WOBJ m 160 24 ltac:(lia) ltac:(lia) ltac:(unfold WO_FLAGP; lia) M160
            (AD m _ 160 24 SH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(vm_compute; reflexivity))) as (DO4 & DI4).
          destruct (WOBJ m 3376 48 ltac:(lia) ltac:(lia) ltac:(unfold WO_FLAGP; lia) M3376
            (AD m _ 3376 48 SH ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(vm_compute; reflexivity))) as (DO5 & DI5).
          split; [exact DO1|]. split; [eapply LbB_PmCall.wr_at_sub; [exact WR | lia | unfold DS_SIZE; lia | unfold DS_SIZE; lia]|].
          split; [exact DI1|]. split; [exact DO2|].
          split; [apply LbB_WoDiagH.w_u64arr3; [exact F32a | exact F40 | exact F48 | eapply LbB_PmCall.wr_at_sub; [exact WR | lia | lia | lia] | lia | lia | lia]|].
          split; [reflexivity|]. split; [exact DI2|]. split; [exact DO3|].
          split; [apply LbB_WoDiagH.w_str; [exact F96 | eapply LbB_PmCall.wr_at_sub; [exact WR | lia | lia | lia] | exact J1]|].
          split; [exact DI3|]. split; [exact DO4|].
          split; [apply LbB_WoDiagH.w_str; [exact F160 | eapply LbB_PmCall.wr_at_sub; [exact WR | lia | lia | lia] | exact J2]|].
          split; [exact DI4|]. split; [exact DO5|].
          split; [apply LbB_WoDiagH.w_cells8_of_fld; [exact F32 | eapply LbB_PmCall.wr_at_sub; [exact WR | lia | lia | lia]]|].
          intros a Ha. unfold DS_SIZE in Ha. lia.
        + intros R R' (_ & _ & _ & _ & _ & _ & _ & R18 & R25 & R26 & R22) KP. unfold mmR3. rewrite !KP by mkin2. repeat split; assumption.
        + intros m m' (SH & WR & _ & F96 & F160 & _) XK.
          assert (LW := mm_len [0; 1; 2; 12; 20; 21]%nat).
          unfold mmP3. split.
          { unfold bp_shad in *. apply (LbB_DRep.u8arr_pteq m m' _ _ SH). intros x Hx. rewrite length_map, LW in Hx. change (Z.of_nat 476) with 476 in Hx.
            pose proof (Z.div_pos ff 8 B0 ltac:(lia)).
            apply (WXA _ m m' XK x); [|unfold sh, ASHADOW_BASE, AINTRIN_STACK in *; lia].
            split; [right; lia|]. constructor; [unfold DS_SIZE, sh, ASHADOW_BASE in *; cbn [fst snd]; lia | constructor]. }
          split.
          { pose proof (WFK _ m m' (ff + 96) 2 0 XK ltac:(left; cbn; unfold WO_FLAGP; lia)
              ltac:(constructor; [cbn; unfold DS_SIZE; lia | constructor]) F96) as X.
            exact (proj1 (fld2_split01 m' (ff + 96) 0 ltac:(lia) ltac:(unfold WO_FLAGP, AINTRIN_STACK in *; lia) ltac:(left; reflexivity) X)). }
          { pose proof (WFK _ m m' (ff + 160) 2 0 XK ltac:(left; cbn; unfold WO_FLAGP; lia)
              ltac:(constructor; [cbn; unfold DS_SIZE; lia | constructor]) F160) as X.
            exact (proj1 (fld2_split01 m' (ff + 160) 0 ltac:(lia) ltac:(unfold WO_FLAGP, AINTRIN_STACK in *; lia) ltac:(left; reflexivity) X)). }
        + intros c'' HW''. exact (mm_s3 Q c'' HW'' K).
    Qed.

    Lemma mm_s1 : forall Q c, wsr (0xea7c4 + 4112) mmR1 None mmP0 0 c -> bp_kwcf H e ff fp Q mo0 -> as_SR H Q c.
    Proof.
      intros Q c HW K.
      destruct mm_geo as (q & Hq & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
      apply (WCH Q (0xea7c4 + 4112) AASAN_MEMSET mmR1 mmRms None mmP0 mmPms 0 c HW); [|intros c' HW'].
      - intros R F fc m XSc s LB RG RC HPm HI SL SES.
        destruct (WGEO XSc s LB m HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
        pose proof RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20).
        pose proof HPm as (SH & FW & FC & FK & F32).
        destruct (LbB_WdMMS.wd_mm1_ea7c4 R F fc m ff ltac:(unfold LbB_WdMMS.wd_mm1_pre; repeat (first [assumption | lia | split])))
          as (R' & M' & ST & MU & WM & S22 & S21 & S20 & S6 & S5 & S4 & S149 & S148 & S143 & S142 & S141 & S140 & S147 & S146 & S145 & S144 & S135 & S134 & S133 & S132 & S139 & S138 & S137 & S136 & S127 & S126 & S125 & S124 & S131 & S130 & S129 & S128 & S119 & S118 & S117 & S116 & S123 & S122 & S121 & S120 & S111 & S110 & S109 & S108 & S115 & S114 & S113 & S112 & S103 & S102 & S101 & S100 & S107 & S106 & S105 & S104 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q24 & KP).
        assert (SH' : bp_shad ff [0; 2; 12; 20; 21]%nat M').
        { apply (bp_shad_set ff [20; 21]%nat [0; 2; 12; 20; 21]%nat m M' _ [(4, 7); (20, 23); (100, 150)] [(4, 0); (5, 0); (6, 0); (20, 0); (21, 0); (22, 0); (100, 0); (101, 0); (102, 0); (103, 0); (104, 0); (105, 0); (106, 0); (107, 0); (108, 0); (109, 0); (110, 0); (111, 0); (112, 0); (113, 0); (114, 0); (115, 0); (116, 0); (117, 0); (118, 0); (119, 0); (120, 0); (121, 0); (122, 0); (123, 0); (124, 0); (125, 0); (126, 0); (127, 0); (128, 0); (129, 0); (130, 0); (131, 0); (132, 0); (133, 0); (134, 0); (135, 0); (136, 0); (137, 0); (138, 0); (139, 0); (140, 0); (141, 0); (142, 0); (143, 0); (144, 0); (145, 0); (146, 0); (147, 0); (148, 0); (149, 0)] SH MU WM).
          - vm_compute. reflexivity.
          - intros i Hi Hr. cbn [in_rngs] in Hr. cbn [outside]. unfold sh, ASHADOW_BASE in *. lia.
          - shfs. }
        exists R', M'. eexists. split; [exact ST|]. split; [exact MU|]. split; [exact WM|].
        split; [repeat (apply Forall_cons; [flw|]); apply Forall_nil|].
        split; [apply Forall_forall; intros iv _; exact I|].
        split; [unfold bp_rc; repeat split; first [assumption | rewrite KP by mkin; assumption]|].
        split; [destruct RG as (RG18 & RG22); unfold mmRms; repeat split; first [assumption | rewrite KP by mkin; assumption]|].
        unfold mmPms. split; [exact SH'|].
        split; [eapply LbB_PmCall.fld_munch; [exact FC | exact MU | dj | lia | lia]|].
        split; [eapply LbB_PmCall.fld_munch; [exact FK | exact MU | dj | lia | lia]|].
        split; [eapply LbB_PmCall.fld_munch; [exact F32 | exact MU | dj | lia | lia]|].
        split.
        { destruct (LbB_WoDiagH.w_junk H e ff fp XSc s LB m (ff + 32) 16 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (junk & JK).
          exists junk. eapply rw_cells_transport; [exact JK | exact MU | exact WM | cbn; dj]. }
        split.
        { apply (addressable_accessible M' (ff + 32) 24 (ff + 32) 16); [| lia | lia | unfold AAPP_HI; lia].
          apply (bp_shad_addr ff [0; 2; 12; 20; 21]%nat M' 32 24 SH' B0 mm_ff8); try lia; try reflexivity.
          rewrite mm_len. apply Z.leb_le. reflexivity. }
        eapply mm_shvis_wm; [exact (LbB_WoDiagH.w_shvis H HH e ff fp XSc s LB m (ff + 32) 16 HP HI ltac:(lia) ltac:(lia) ltac:(lia)) | exact WM | apply mm_sh_hi; lia].
      - destruct (mm_wsr_ex _ _ _ _ (fun j m => rw_cells asegs m (ff + 32) [CB 16 j]) _ _ HW'
          ltac:(intros m (_ & _ & _ & _ & JK & _); exact JK)) as (junk & HW2).
        apply (WMS Q mmRms mmR2 None (fun m => mmPms m /\ rw_cells asegs m (ff + 32) [CB 16 junk]) mmP2 0 c'
          (0xea7c4 + 4356) (ff + 32) 0 16 junk HW2).
        + intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
        + reflexivity.
        + lia.
        + lia.
        + lia.
        + flw.
        + exact I.
        + lia.
        + lia.
        + unfold WO_FLAGP. lia.
        + exact I.
        + intros m ((_ & _ & _ & _ & _ & AC & SV) & JK). split; [exact JK|]. split; [exact AC | exact SV].
        + intros R R' (_ & _ & _ & _ & R18 & R24 & R22) KP. unfold mmR2. rewrite !KP by mkin2. repeat split; assumption.
        + intros m m' ((SH & FC & FK & F32 & _) & _) MU WM PZ.
          assert (LW := mm_len [0; 2; 12; 20; 21]%nat).
          unfold WO_FLAGP, AINTRIN_STACK in *.
          unfold mmP2. split.
          { unfold bp_shad in *. eapply u8arr_transport; [exact SH | exact MU | exact WM |]. rewrite length_map, LW. dj. }
          split; [eapply LbB_PmCall.fld_munch; [exact FC | exact MU | dj | lia | lia]|].
          split; [eapply LbB_PmCall.fld_munch; [exact FK | exact MU | dj | lia | lia]|].
          split; [eapply LbB_PmCall.fld_munch; [exact F32 | exact MU | dj | lia | lia]|].
          exact PZ.
        + intros c'' HW''. exact (mm_s2 Q c'' HW'' K).
    Qed.

    Lemma mm_s0 : forall Q c, wsr BP_HDR (bp_r480 ff) None mmP0 0 c -> bp_kwcf H e ff fp Q mo0 -> as_SR H Q c.
    Proof.
      intros Q c HW K.
      apply (WCH Q BP_HDR (0xea7c4 + 4112) (bp_r480 ff) mmR1 None mmP0 mmP0 0 c HW); [|intros c' HW'; exact (mm_s1 Q c' HW' K)].
      intros R F fc m XSc s LB RG RC HPm HI SL SES.
      destruct (WGEO XSc s LB m HI) as (G1 & G2 & G3 & G4 & _).
      pose proof RG as (R18 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
      pose proof HPm as (SH & FW & FC & FK & F32).
      destruct (LbB_WdMMS.wd_mm0_ea7c4 R F fc m ff ltac:(unfold LbB_WdMMS.wd_mm0_pre; repeat (first [assumption | lia | split])))
        as (R' & M' & ST & EM & Q10 & Q18 & Q22 & KP).
      subst M'.
      exists R', m, []. split; [exact ST|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [constructor|]. split; [constructor|].
      split; [unfold bp_rc in *; rewrite !KP by mkin; exact RC|].
      split; [unfold mmR1; split; assumption|]. exact HPm.
    Qed.

    Lemma mm_p0 : bp_shad ff [20; 21]%nat m0 -> mmP0 m0.
    Proof.
      intros SH.
      pose proof HPF as ((PR & PSH & HC & HU & HD & SO & OWN & CW) & (HDR & _) & _ & C32).
      pose proof HWL as (Wp & Wc & Ww & _).
      unfold parser_repA in PR.
      destruct PR as [PRc PRu PRh PRi PRk PRs PRd PRa PRr PRcf PRcm PRcd].
      destruct PRs as [S0 S1 S2 S3 S4 S5 S6 SM1 SM2 SM3 SV1 SV2 SV3 SD SA SN].
      destruct HDR as (HW & HN & HWI & HIC & _).
      cbn [bp_ste st_words st_nwords st_widx st_icount] in HW, HN, HWI, HIC.
      rewrite Wp in PRc, S0, S4. rewrite HW, Ww, HW0 in S0. rewrite HIC in S4. rewrite HC, Wc in PRc.
      rewrite Wc in C32.
      split; [exact SH|]. split; [|split; [|split]].
      - replace (ff + 3504) with (ff + 3456 + ST_OFF) by (unfold ST_OFF; lia). exact (proj2 S0).
      - replace (ff + 3464) with (ff + 3456 + 8) by lia. exact PRc.
      - replace (ff + 3536) with (ff + 3456 + ST_OFF + 32) by (unfold ST_OFF; lia). exact (proj2 S4).
      - eapply LbB_WoDiagH.w_fld_of_cells8; [exact C32 | lia].
    Qed.

    Lemma mm_run : forall Q msF mo R F fc,
      as_VIS H s0 msF = MS R F (Z_to_bv 64 BP_HDR) fc None m0 (seg_rom asegs) -> rfull R -> frm_zero fc ->
      as_AKREL H s0 (mkCfg msF mo) -> as_MPRES H mo0 mo -> bp_slots H e ff m0 -> bp_shad ff [20; 21]%nat m0 ->
      bp_rc H e ff R -> bp_r480 ff R -> bp_kwcf H e ff fp Q mo0 -> as_SR H Q (mkCfg msF mo).
    Proof.
      intros Q msF mo R F fc VIS RF FZ KR MP SL SH RC RG K.
      apply (WST Q msF mo R F fc BP_HDR (bp_r480 ff) mmP0 VIS RF FZ KR MP SL RC RG (mm_p0 SH)).
      intros c Hc. exact (mm_s0 Q c Hc K).
    Qed.
  End MMW.

  Lemma pm_mm : forall e ff fp Q mo0, w_words e = 0 -> bp_kwcf H e ff fp Q mo0 -> bp_khdr H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 W0 K. unfold bp_khdr, bp_hdr0.
    intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RG WL PF.
    exact (mm_run e ff fp mo0 w c LBs s LB m XSc HP WL PF HI W0 Q msF mo R F fc VIS RF FZ KR MP SL SH RC RG K).
  Qed.
End MM.
