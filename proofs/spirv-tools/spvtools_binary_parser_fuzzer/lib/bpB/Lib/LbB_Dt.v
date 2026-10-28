(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_PqK LbB_DtK LbB_DtR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK LbB_PcOvf LbB_PcXsp LbB_PcLem LbB_Pq.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition RTD0 : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 47); (4%bv, EVar 48); (8%bv, EVar 35); (9%bv, EVar 36);
   (18%bv, EVar 37); (19%bv, EVar 38); (20%bv, EVar 39); (21%bv, EVar 40); (22%bv, EVar 41); (23%bv, EVar 42);
   (24%bv, EVar 43); (25%bv, EVar 44); (26%bv, EVar 45); (27%bv, EVar 46); (10%bv, EVar 32)].

Definition RTD1 : list (reg * expr) :=
  [(1%bv, ELit 0xfca20); (3%bv, EVar 47); (4%bv, EVar 48); (8%bv, EVar 33); (10%bv, ELit 256);
   (18%bv, EVar 37); (19%bv, EVar 32); (20%bv, EVar 39); (21%bv, ELit SHBASE); (22%bv, EVar 41); (23%bv, EVar 42);
   (24%bv, EVar 43); (25%bv, EVar 44); (26%bv, EVar 45); (27%bv, EVar 46)].

Lemma C8_of_ftbl : forall W B m tbl k e, ftbl W B m tbl -> In (k, 8%nat, e) tbl -> rw_cells asegs m (B + k) [C8 (edenot (wenv W) e)].
Proof.
  intros W B m tbl k e HT Hi. pose proof (ftbl_In W B m tbl k 8%nat e HT Hi) as [[WF BA] WA].
  split; [split; [cbn; tauto | exact BA] | exact WA].
Qed.

Section DT.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (ds len err lo : Z) (LF : list fframe) (LB DB : list block)
            (ms : sbuf) (pp hm fl fill : Z) (sA : as_St H).

  Record dt_ctx : Prop := DT_CTX {
    c_a0 : a0 = Z_to_bv 64 ds;
    c_rep : ds_rep_w LB m0 ds err len DB ms pp hm fl fill;
    c_dsv : shvis m0 ds (ds + DS_SIZE);
    c_dsin : obj_inframe LF ds DS_SIZE;
    c_stk : stk asegs m0 lo (bv_unsigned sp);
    c_ceil : aceil <= lo;
    c_lo : lo <= bv_unsigned sp - ADS_STACK;
    c_sp16 : bv_unsigned sp mod 16 = 0;
    c_sphi : bv_unsigned sp <= AAPP_HI;
    c_mi : mem_inv asegs m0;
    c_ac : ACONST m0;
    c_lv : LINV_P5 m0;
    c_tp : tp = Z_to_bv 64 ATP;
    c_rfs : as_RFS H LF m0;
    c_lfn : (length LF + 1 <= AFS_MAXLIVE_BP)%nat;
    c_rh : as_RHEAP H sA LB m0;
    c_own : lb_own DB m0
  }.
  Hypothesis CTX : dt_ctx.

  Notation spz := (bv_unsigned sp) (only parsing).

  Definition hw : Z := match ms with SShort => 1 | SLong _ asz => asz + 1 end.
  Definition dptr : Z := match ms with SShort => 0x6e8000 | SLong d _ => d end.
  Definition hsel : nat := match ms with SShort => 1%nat | SLong _ _ => 2%nat end.

  Definition W0 : list word :=
    [Z_to_bv 64 ds; sp; ra; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp].
  Notation WDx ff fp spa := (LbB_DtK.WD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err ff fp spa hw dptr) (only parsing).

  Lemma HHb : asan_rt_hyps H. Proof. exact (rt_bp_base H HHbp). Qed.
  Lemma SM2 : stack_malloc_stmt_bp H 2 AFS_MALLOC_2. Proof. exact (proj1 (proj2 (rt_bp_ext H HHbp))). Qed.

  Lemma ds_facts : addressable m0 ds DS_SIZE /\ wr_at asegs m0 ds DS_SIZE /\ app_obj ds DS_SIZE /\ ds mod 8 = 0 /\ 0 < ds
    /\ ds + DS_SIZE + 64 <= AAPP_HI /\ as_FSB H + AFS_HDR <= ds /\ ds + DS_SIZE <= as_FSB H + AFS_SIZE /\ ds + DS_SIZE <= aceil
    /\ - 2 ^ 31 <= err < 0 /\ (hw mod 2 = 1 /\ 0 <= hw < 2 ^ 64 /\ AIMG_TOP <= dptr < 2 ^ 47)
    /\ dsr ds err m0 /\ hdrf ds hw dptr hsel m0.
  Proof.
    pose proof (c_rep CTX) as (DI & BLK & DSA & DSW & DSO & SBA). pose proof DSO as (O1 & O2 & O3).
    pose proof (c_rfs CTX) as RFS0. pose proof (c_dsin CTX) as DSin. pose proof (c_rh CTX) as RH0.
    destruct (LbB_DCtor.inframe_facts H HHb LF m0 ds DS_SIZE RFS0 DSin ltac:(unfold DS_SIZE; clear; lia) O1) as (DSH & _ & F3 & F4).
    destruct (ah_RFS_range H HHb LF m0 RFS0) as [(B1 & B2 & B3 & B4) FR].
    assert (F3' : as_FSB H + AFS_HDR <= ds).
    { destruct DSin as (f & Hf & X1 & X2). pose proof (FR f Hf) as (_ & L2 & _). clear - X1 L2. lia. }
    clear F3.
    pose proof DI as DI'. destruct DI'. pose proof di_ios as II. destruct II. pose proof di_sb as SB. destruct SB.
    assert (W8 : forall a, ds <= a -> a + 8 <= ds + DS_SIZE -> wr_at asegs m0 a 8) by (intros a X Y; eapply wr_at_sub; [exact DSW | lia | lia | lia]).
    assert (W4 : forall a, ds <= a -> a + 4 <= ds + DS_SIZE -> wr_at asegs m0 a 4) by (intros a X Y; eapply wr_at_sub; [exact DSW | lia | lia | lia]).
    assert (W1 : forall a, ds <= a -> a + 1 <= ds + DS_SIZE -> wr_at asegs m0 a 1) by (intros a X Y; eapply wr_at_sub; [exact DSW | lia | lia | lia]).
    assert (HW : hw mod 2 = 1 /\ 0 <= hw < 2 ^ 64 /\ AIMG_TOP <= dptr < 2 ^ 47).
    { unfold hw, dptr. destruct ms as [|d asz].
      - unfold AIMG_TOP. clear. split; [reflexivity | lia].
      - cbn [ds_blk] in BLK. destruct BLK as (pid & EDB & INb).
        pose proof (ah_blocks H HHb _ _ _ (pid, d, asz) RH0 INb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
        destruct si_str as (cs & STR & HL). destruct STR as (_ & _ & _ & _ & (_ & _ & _ & A8 & _) & _).
        pose proof aceil_facts as ((A1 & A2) & _).
        split; [| split; [clear - Rn RC A2 R0; lia | clear - RI RC A2 Rn; lia]].
        clear - A8 Rn. Z.div_mod_to_equations. lia. }
    unfold DS_SIZE in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try apply HW.
    - constructor.
      + replace (ds + 16) with (ds + 8 + 8) by lia. apply rw_cells_of_fld8; [exact si_loc | apply W8; lia].
      + replace (ds + 160) with (ds + 112 + 48) by lia. apply rw_cells_of_fld8; [exact ii_loc | apply W8; lia].
      + replace (ds + 168) with (ds + 112 + 56 + 8 * 0) by lia. apply rw_cells_of_fld8; [apply ii_zero; lia | apply W8; lia].
      + replace (ds + 176) with (ds + 112 + 56 + 8 * 1) by lia. apply rw_cells_of_fld8; [apply ii_zero; lia | apply W8; lia].
      + replace (ds + 184) with (ds + 112 + 56 + 8 * 2) by lia. apply rw_cells_of_fld8; [apply ii_zero; lia | apply W8; lia].
      + replace (ds + 200) with (ds + 112 + 56 + 8 * 4) by lia. apply rw_cells_of_fld8; [apply ii_zero; lia | apply W8; lia].
      + replace (ds + 224) with (ds + 112 + 56 + 8 * 7) by lia. apply rw_cells_of_fld8; [apply ii_zero; lia | apply W8; lia].
      + apply rw_cells_of_fld8; [exact di_f320 | apply W8; lia].
      + apply rw_cells_of_fld1; [exact di_f336 | apply W1; lia].
      + apply rw_cells_of_fld4; [exact di_f360 | apply W4; lia].
      + apply rw_cells_of_fld1; [exact di_f368 | apply W1; lia].
    - unfold hsel, hdrf, hw, dptr. destruct si_str as (cs & STR & HL). destruct ms as [|d asz].
      + destruct STR as (_ & _ & _ & _ & SH & _). cbn [str_cap] in HL. unfold SSO_CAP in HL.
        replace (ds + 72) with (ds + 8 + 64) by lia. replace 44 with (2 * Zlen cs) by (rewrite HL; reflexivity).
        apply rw_cells_of_fld1; [exact SH | apply W1; lia].
      + destruct STR as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & A0 & _ & A16) & _).
        split.
        * replace (ds + 72) with (ds + 8 + 64) by lia. apply rw_cells_of_fld8; [exact A0 | apply W8; lia].
        * replace (ds + 88) with (ds + 8 + 64 + 16) by lia. apply rw_cells_of_fld8; [exact A16 | apply W8; lia].
  Qed.

  Lemma p_ranges : 0 <= spz < 2 ^ 64 /\ aceil + ADS_STACK <= spz /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). pose proof (c_ceil CTX). pose proof (c_lo CTX). split; [lia|]. split; [lia|]. lia.
  Qed.

  Definition P0w (m : mem) : Prop := munch [(spz - 8192, spz)] m0 m /\ wmono asegs m0 m.

  Lemma p0_keep : forall m, P0w m -> mem_inv asegs m -> ACONST m /\ LINV_P5 m /\ stk asegs m lo spz.
  Proof.
    intros m [MU WM] MI. pose proof p_ranges as (R1 & R2 & R3). pose proof (c_ceil CTX) as CEIL. pose proof (c_lo CTX) as LO.
    split.
    { eapply ACONST_frame; [exact (c_ac CTX) | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil].
      apply LbB_DPdK.aconst_ok_hi. unfold ADS_STACK in *. lia. }
    split.
    { eapply LINV_P5_cl; [exact (c_lv CTX)|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by lia.
      cbn [outside]. unfold aimg_client, ADS_STACK in *. split; [lia | exact I]. }
    eapply LbB_PqK.stk_keep; [exact (c_stk CTX) | exact MU | exact WM | unfold AIMG_TOP, ADS_STACK in *; lia].
  Qed.

  Ltac evWW := cbn [edenot]; unfold wenv, HLib.Eseed, reg_ev, LbB_DtK.WD, W0;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app length N.of_nat Pos.of_succ_nat Pos.succ N.add Pos.add].
  Ltac evw0 := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, W0;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_q0_ok : forall R X m, P0w m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (W0 ++ X)) m LbB_Pq.kst_q0.
  Proof.
    intros R X m PW MI. destruct (p0_keep m PW MI) as (AC & (RL & _) & ST).
    pose proof p_ranges as (R1 & R2 & R3). pose proof (c_lo CTX) as LO. pose proof (c_sphi CTX) as SPHI.
    pose proof (ACONST_shbase m AC) as [_ CS]. pose proof (ACONST_uar m AC) as [_ CU].
    unfold ADS_STACK in *.
    unfold know_ok, LbB_Pq.kst_q0. repeat apply Forall_cons; try apply Forall_nil.
    - apply kimg_relro. exact RL.
    - eapply (kword_of_rw_cells asegs _ m ASHBASE_CELL _ 0%nat (C8 (wz 0x7fff8000))); [exact CS | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold ASHBASE_CELL; cbn; lia | unfold ASHBASE_CELL; cbn; lia | reflexivity].
    - eapply (kword_of_rw_cells asegs _ m AUAR_CELL _ 0%nat (C4 (wz 1))); [exact CU | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold AUAR_CELL; cbn; lia | unfold AUAR_CELL; cbn; lia | reflexivity].
    - eapply kwr_of_stk; [exact ST | | |]; evw0; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evw0. unfold AAPP_HI in *. lia.
  Qed.

  Definition tS0 (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -8192, 0, T, ks).

  Lemma tabs_wf0 : forall T ks, fwcl (wbound W0) T = true -> fin (-8192) 0 (fkeys T ++ ks) = true -> tabs_wf W0 [tS0 T ks].
  Proof.
    intros T ks C F1. pose proof p_ranges as (R1 & R2 & R3). split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tS0]; try reflexivity; try assumption; unfold ADS_STACK in *; lia.
    - intros u1 u2 H1 H2 Hb. destruct H1 as [<-|[]]; destruct H2 as [<-|[]]. vm_compute in Hb. discriminate Hb.
  Qed.

  Lemma P0w_step : forall T ks m m', P0w m -> munch (winsT [tS0 T ks]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> P0w m'.
  Proof.
    intros T ks m m' [MU0 WM0] MU WM _. split; [| eapply wmono_trans; eassumption].
    eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU].
    apply sub_fp_of. apply Forall_cons; [| apply Forall_nil]. exists (spz - 8192, spz). split; [left; reflexivity | cbn; lia].
  Qed.

  Lemma tabs_ok0 : forall m T ks, P0w m -> mem_inv asegs m -> ftbl W0 spz m T -> fin (-8192) 0 ks = true ->
    tabs_ok W0 m [tS0 T ks].
  Proof.
    intros m T ks PW MI HT F1. destruct (p0_keep m PW MI) as (_ & _ & ST).
    apply Forall_cons; [| apply Forall_nil]. split; [exact HT|].
    intros k w Hi. cbn [tB tks tS0] in *. destruct (fin_In _ _ _ k w F1 Hi) as (H1 & H2 & H3).
    pose proof (c_lo CTX) as LO'. unfold ADS_STACK in LO'.
    pose proof (wr_at_of_stk asegs m lo spz ST) as W. eapply wr_at_sub; [exact W | lia | lia | lia].
  Qed.

  Ltac dkrun0 HRT HSF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS0 SF []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (LbB_Pq.kst_q0 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound W0) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          eapply (dk_runN W0 [tS0 SF ks1] (tabs_wf0 SF ks1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    P0w (P0w_step SF ks1) Q R F pc fc m ro RT [] LbB_Pq.kst_q0 fuel stops (SCR [] [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok0; [exact HP | exact HMI | exact HSF | vm_compute; reflexivity]
          | exact HP | exact HMI | apply kst_q0_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end
    end.

  Lemma dt_p1 :
    evt asegs (fun msx => exists R1 m1, msx = MS R1 F (Z_to_bv 64 AFS_MALLOC_2) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl W0 R1 RTD1 /\ PropExec.getr R1 2 = Z_to_bv 64 ((spz - 192) - (spz - 192) mod 32)
                  /\ PropExec.getr R1 9 = PropExec.getr R1 2
                  /\ ftbl W0 spz m1 TSD /\ P0w m1 /\ mem_inv asegs m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ADS_DTOR) fc None m0 (seg_rom asegs)).
  Proof.
    pose proof p_ranges as (R1' & R2' & R3'). pose proof (c_mi CTX) as MI0.
    assert (RF0 : rfull (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) by apply rfull_mkR.
    assert (HRT : rtbl W0 (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) RTD0).
    { unfold rtbl, RTD0. repeat constructor; cbn [fst snd]. exact (c_a0 CTX). }
    assert (HSF : ftbl W0 spz m0 []) by constructor.
    assert (HP : P0w m0) by (split; [apply munch_refl | apply wmono_refl]).
    unfold ADS_DTOR.
    dkrun0 HRT HSF HP MI0 600%nat [AFS_MALLOC_2].
    { constructor. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    lazymatch type of HTS1 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS1; clear E end.
    apply Forall_cons_iff in HTS1 as [HSF1 _]. cbn [fst snd] in HSF1. cbn [s_pc].
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split.
    { rewrite (rtbl_In W0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-192))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). cbn [edenot].
      change (ev (wenv W0) 33) with sp.
      assert (EA : alu64 ALU_ADD sp (Z_to_bv 64 (-192)) = Z_to_bv 64 (spz - 192)).
      { rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite w_addm by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia).
        f_equal; clear; lia. }
      rewrite EA. rewrite LbB_Pq.pq_mul32 by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). reflexivity. }
    split.
    { rewrite (rtbl_In W0 R1 _ 9%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-192))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)).
      rewrite (rtbl_In W0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-192))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). reflexivity. }
    split; [apply (ftbl_sub _ _ _ _ _ HSF1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.

  Lemma new_frame2 : forall LFx m ff fp, as_RFS H ((2, ff, fp) :: LFx) m -> obj_inframe LFx ds DS_SIZE ->
    fresh_frame H LFx 2 ff fp
    /\ (ff + 256 <= ds \/ ds + DS_SIZE <= ff) /\ (fp + 1 <= ds \/ ds + DS_SIZE <= fp)
    /\ (hull_hi (ds + DS_SIZE) <= ff \/ ff + 256 <= hull_lo ds).
  Proof.
    intros LFx m ff fp RF DSx.
    destruct (ah_RFS_range H HHb _ _ RF) as [FO FR].
    pose proof (FR (2, ff, fp) (or_introl eq_refl)) as (K1 & K2 & K3 & (K4 & K5) & K6).
    cbn [ff_class ff_addr ff_flag fst snd] in K1, K2, K3, K4, K5, K6. unfold fsz in K3. change (64 * 2 ^ 2) with 256 in K3.
    pose proof (ah_RFS_nodup H HHb _ _ RF) as ND. cbn [map ff_addr fst snd] in ND. apply NoDup_cons_iff in ND as [NI _].
    assert (DJ : forall f, In f LFx -> (ff + 256 <= ff_addr f \/ ff_addr f + fsz (ff_class f) <= ff) /\ fp <> ff_flag f).
    { intros f Hf. assert (Hne : ff <> ff_addr f) by (intros E; apply NI; rewrite E; apply in_map; exact Hf).
      destruct (ah_RFS_disj H HHb _ _ (2, ff, fp) f RF (or_introl eq_refl) (or_intror Hf) Hne) as [D1 D2].
      cbn [ff_addr ff_class ff_flag fst snd] in D1, D2. unfold fsz in D1 at 1. change (64 * 2 ^ 2) with 256 in D1. split; [exact D1 | exact D2]. }
    destruct DSx as (f & Hf & F1 & F2).
    pose proof (FR f (or_intror Hf)) as (L1 & L2 & L3 & (L4 & L5) & L6).
    assert (FM : fsz (ff_class f) mod 64 = 0) by (unfold fsz; rewrite Z.mul_comm; apply Z_mod_mult).
    destruct (DJ f Hf) as [D1 D2]. pose proof ds_facts as (_ & _ & _ & DS8 & _).
    unfold AFS_HDR, AFS_FLAGS, DS_SIZE in *.
    split.
    { split; [exact (FR (2, ff, fp) (or_introl eq_refl)) | split; [exact FO|]]. intros g Hg. destruct (DJ g Hg) as [E1 E2].
      split; [unfold fsz at 1; change (64 * 2 ^ 2) with 256; exact E1 | exact E2]. }
    split; [clear - D1 F1 F2; lia|]. split; [clear - K6 L2 F1 F2; lia|].
    unfold hull_lo, hull_hi. clear - D1 F1 F2 L4 FM K4 DS8. Z.div_mod_to_equations. lia.
  Qed.

  Lemma mk_dg : forall ff fp spa, fresh_frame H LF 2 ff fp ->
    (ff + 256 <= ds \/ ds + DS_SIZE <= ff) -> (fp + 1 <= ds \/ ds + DS_SIZE <= fp) ->
    (hull_hi (ds + DS_SIZE) <= ff \/ ff + 256 <= hull_lo ds) ->
    spa mod 32 = 0 -> spz - 208 <= spa <= spz - 192 ->
    dg H sp ds err lo ff fp spa hw dptr.
  Proof.
    intros ff fp spa (FR & FO & _) D1 D2 D3 A1 A2.
    pose proof ds_facts as (_ & _ & DSO & DS8 & _ & DSH & F3 & F4 & DSM & ERR & HW & _).
    constructor.
    - split; [exact (c_ceil CTX) | exact (c_lo CTX)].
    - split; [exact (c_sp16 CTX) | exact (c_sphi CTX)].
    - split; [exact A1 | exact A2].
    - split; [exact DSO | split; [exact DS8 | split; [exact DSH | exact DSM]]].
    - split; [clear - F3; unfold AFS_HDR in F3; lia | exact F4].
    - exact ERR.
    - exact HW.
    - split; [exact FR | exact FO].
    - split; [exact D1 | split; [exact D2 | exact D3]].
  Qed.

  Definition WA2 (ff fp : Z) : list (Z * Z) :=
    [(spz - 16384, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32);
     (ds + 0, ds + 16); (ds + 112, ds + 120)].

  Lemma fr_place2 : forall LFx ff fp, fresh_frame H LFx 2 ff fp ->
    as_FSB H + 0x9000 <= ff /\ ff + 256 <= as_FSB H + 0xb09000 /\ ff mod 64 = 0
    /\ as_FSB H + 0x1000 <= fp /\ fp + 1 <= as_FSB H + 0x9000
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + 0xb09000 <= aceil /\ aceil + 16384 <= spz /\ spz <= 2 ^ 47
    /\ (as_FSB H + 0xb09000 <= 0x7fff7000 \/ 0x10007fff8000 <= as_FSB H) /\ aapp (as_FSB H) AFS_SIZE
    /\ 0x800d5000 <= sh (as_FSB H) /\ sh (as_FSB H) + 0x1200 <= sh ff /\ sh ff + 32 <= sh (as_FSB H + 0xb09000)
    /\ sh (as_FSB H + 0xb09000) + 2048 <= sh spz /\ sh spz <= 0x10007fff8000 /\ sh spz + 2 ^ 44 <= spz
    /\ sh (as_FSB H + 0xb09000) <= sh aceil /\ 0x7fff7f800000 <= aceil.
  Proof.
    intros LFx ff fp (FFR & FSB_OK & _).
    pose proof FFR as (K1 & K2 & K3 & (K4 & K5) & K6). unfold fsz in K3. change (64 * 2 ^ 2) with 256 in K3.
    pose proof FSB_OK as (B1 & B2 & B3 & B4). pose proof aceil_facts as ((A1 & A2) & A3 & A4). pose proof p_ranges as (R1 & R2 & R3).
    pose proof (c_sphi CTX) as SPHI.
    assert (B4' : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H).
    { clear - B4. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in *. destruct B4; [left | right]; lia. }
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO, ADS_STACK, AAPP_HI in *.
    assert (SH : 0x800d5000 <= sh (as_FSB H) /\ sh (as_FSB H) + 0x1200 <= sh ff /\ sh ff + 32 <= sh (as_FSB H + 0xb09000)
                 /\ sh (as_FSB H + 0xb09000) + 2048 <= sh spz /\ sh spz <= 0x10007fff8000 /\ sh spz + 2 ^ 44 <= spz
                 /\ sh (as_FSB H + 0xb09000) <= sh aceil).
    { clear - K2 K3 B1 B2 R2 R3 SPHI. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    repeat match goal with |- _ /\ _ => split end; try assumption; clear B4 B4'; lia.
  Qed.

  Lemma wa2_keep : forall ff fp m, fresh_frame H LF 2 ff fp ->
    (ff + 256 <= ds \/ ds + DS_SIZE <= ff) -> (fp + 1 <= ds \/ ds + DS_SIZE <= fp) ->
    (hull_hi (ds + DS_SIZE) <= ff \/ ff + 256 <= hull_lo ds) ->
    munch (WA2 ff fp) m0 m -> wmono asegs m0 m ->
    addressable m ds DS_SIZE /\ wr_at asegs m ds DS_SIZE /\ shvis m ds (ds + DS_SIZE) /\ dsr ds err m /\ hdrf ds hw dptr hsel m
    /\ LINV_P5 m /\ ACONST m /\ stk asegs m lo spz.
  Proof.
    intros ff fp m FRX D1 D2 D3 MU WM.
    pose proof (fr_place2 LF ff fp FRX) as (K2 & K3 & K4 & K6 & K6' & B1 & B2 & R2 & R3 & B4 & AP & S1 & S2 & S3 & S4 & S5 & S6 & S7 & A1).
    pose proof ds_facts as (DSA & DSW & DSO & DS8 & DS0 & DSH & F3 & F4 & DSM & _ & _ & DF & HF).
    pose proof (c_ceil CTX) as CEIL. pose proof (c_lo CTX) as LO.
    assert (SH : sh (as_FSB H) <= sh ds /\ sh ds + 49 <= sh (as_FSB H + 0xb09000)
                 /\ (sh ff + 32 <= sh ds \/ sh ds + 49 <= sh ff)
                 /\ sh ds - 8 <= sh (hull_lo ds) /\ sh (hull_hi (ds + DS_SIZE)) <= sh ds + 57
                 /\ (sh ff + 32 <= sh (hull_lo ds) \/ sh (hull_hi (ds + DS_SIZE)) <= sh ff)).
    { unfold DS_SIZE, AFS_HDR, AFS_SIZE in *. clear - F3 F4 K4 DS8 D1 D3.
      unfold sh, hull_lo, hull_hi, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
    destruct SH as (T1 & T2 & T3 & T4 & T5 & T6).
    unfold DS_SIZE, ADS_STACK, AFS_HDR, AFS_FLAGS, AFS_SIZE in *.
    assert (DSH49 : disjoint_from (WA2 ff fp) (sh ds) 49).
    { unfold WA2, AFS_FLAGS. cbn [disjoint_from]. clear - S1 T1 T2 T3 S4 S5 S6 R2 B2 B4 F3 F4 K2 K3 K6 K6' CEIL LO. lia. }
    assert (DSHU : disjoint_from (WA2 ff fp) (sh (hull_lo ds)) (sh (hull_hi (ds + 392)) - sh (hull_lo ds))).
    { unfold WA2, AFS_FLAGS. cbn [disjoint_from]. clear - S1 T1 T2 T4 T5 T6 S4 S5 S6 R2 B2 B4 F3 F4 K2 K3 K6 K6' CEIL LO. lia. }
    split; [eapply addressable_transport; [exact DSA | exact MU | exact WM | exact DSH49]|].
    split; [eapply wr_at_transport; [exact DSW | exact WM]|].
    split; [eapply shvis_transport; [exact (c_dsv CTX) | exact MU | exact WM | exact DSHU]|].
    split.
    { eapply dsr_keep; [exact DF | exact MU | exact WM |]. unfold DSR_FIELDS, WA2, AFS_FLAGS.
      clear - R2 CEIL LO D1 D2 K6 K6' F3 F4 B2 B4 S1 S2 S3 S4 S5 DSM K2 K3. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from]; lia. }
    split.
    { eapply (hdrf_keep ds hw dptr hsel); [exact HF | exact MU | exact WM | |]; unfold WA2, AFS_FLAGS; cbn [disjoint_from];
        clear - R2 CEIL LO D1 D2 K6 K6' F3 F4 B2 B4 S1 S2 S3 S4 S5 DSM K2 K3; lia. }
    split.
    { eapply LINV_P5_cl; [exact (c_lv CTX)|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by (clear - Ha; lia).
      unfold aimg_client, AIMG_LO, AIMG_TOP in Hc. unfold WA2, AFS_FLAGS. apply LbB_PqK.outside_of.
      clear - Hc R2 A1 CEIL LO B1 K2 K6 F3 S1 S2. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    split.
    { eapply ACONST_frame; [exact (c_ac CTX) | exact MU | exact WM |]. unfold WA2, AFS_FLAGS.
      repeat apply Forall_cons; try apply Forall_nil.
      - apply LbB_DPdK.aconst_ok_hi. clear - R2 A1 CEIL LO. lia.
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact AP | clear; lia | clear; lia].
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact AP | clear - K6; lia | clear - K6'; lia].
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact AP | clear - K2; lia | exact K3].
      - apply LbB_DPdK.aconst_ok_hi. clear - S1 S2. lia.
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact AP | clear - F3; lia | clear - F4; lia].
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact AP | clear - F3; lia | clear - F4; lia]. }
    eapply LbB_PqK.stk_keep; [exact (c_stk CTX) | exact MU | exact WM | clear - CEIL A1; unfold AIMG_TOP; lia].
  Qed.

  Lemma wa2_laws : forall LBx LFx ff fp, fresh_frame H LF 2 ff fp -> In (2, ff, fp) LFx -> obj_inframe LFx ds DS_SIZE ->
    Forall (aclient_write_ok H LBx) (WA2 ff fp) /\ Forall stack0_ok (WA2 ff fp) /\ Forall aconst_ok (WA2 ff fp)
    /\ (forall a, aimg_client a -> outside (WA2 ff fp) a) /\ Forall (fun iv => AIMG_TOP <= fst iv) (WA2 ff fp).
  Proof.
    intros LBx LFx ff fp FR I1 OD.
    pose proof (fr_place2 LF ff fp FR) as (K2 & K3 & K4 & K6 & K6' & B1 & B2 & R2 & R3 & B4 & AP & S1 & S2 & S3 & S4 & S5 & S6 & S7 & A1).
    pose proof ds_facts as (_ & _ & DSO & _ & _ & DSH & F3 & F4 & DSM & _). unfold AFS_HDR, AFS_SIZE, DS_SIZE in F3, F4, DSM.
    pose proof (c_ceil CTX) as CEIL. pose proof (c_lo CTX) as LO. unfold ADS_STACK in LO.
    assert (SA : ALOWSH_LO <= sh aceil) by (clear - A1; unfold sh, ASHADOW_BASE, ALOWSH_LO in *; Z.div_mod_to_equations; lia).
    unfold WA2, AFS_FLAGS. split; [|split; [|split; [|split]]].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      + left. clear - R2 B2. lia.
      + right; right; right; right; left. clear. unfold AFS_SIZE. lia.
      + right; right; right; right; left. clear - K6 K6'. unfold AFS_SIZE in *. lia.
      + right; right; right; right; left. clear - K2 K3. unfold AFS_SIZE in *. lia.
      + right; right; right; right; right; left. clear - S2 S3 S1. unfold AFS_SIZE. unfold sh in *. lia.
      + right; right; right; right; left. clear - F3 F4. unfold AFS_SIZE. lia.
      + right; right; right; right; left. clear - F3 F4. unfold AFS_SIZE. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok; cbn [fst snd].
      + left. clear - R2 B2 A1. unfold AHI_LO in *. lia.
      + clear - B4 SA. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + clear - B4 SA K6 K6'. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + clear - B4 SA K2 K3. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + right. clear - S3 S7. lia.
      + clear - B4 SA F3 F4. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + clear - B4 SA F3 F4. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - R2 R3 B2 A1. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear; lia | clear; unfold AFS_SIZE; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - K6; lia | clear - K6'; unfold AFS_SIZE in *; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - K2; lia | clear - K3; unfold AFS_SIZE; lia].
      + apply LbB_DPdK.aconst_ok_hi. clear - S1 S2. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - F3; lia | clear - F4; unfold AFS_SIZE; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - F3; lia | clear - F4; unfold AFS_SIZE; lia].
    - intros a Ha. unfold aimg_client in Ha. apply LbB_PqK.outside_of.
      clear - Ha R2 B1 B2 K2 K6 F3 S1 S2 A1. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - R2 B1 B2 K2 K6 F3 S1 S2 A1; unfold AIMG_TOP; lia.
  Qed.

  Record dt_st1 (ff fp spa : Z) (R : bvmap 5 word) (m : mem) : Prop := DT_ST1 {
    t1_g : dg H sp ds err lo ff fp spa hw dptr;
    t1_fr : fresh_frame H LF 2 ff fp;
    t1_rf : rfull R;
    t1_rt : rtbl (WDx ff fp spa) R RTD2;
    t1_ts : ftbl (WDx ff fp spa) spz m TSD;
    t1_tf : ftbl (WDx ff fp spa) ff m FTD0;
    t1_q : df sp ds err lo ff fp hw dptr hsel m;
    t1_mi : mem_inv asegs m;
    t1_rfs : as_RFS H ((2, ff, fp) :: LF) m;
    t1_mu : munch (WA2 ff fp) m0 m;
    t1_wm : wmono asegs m0 m
  }.

  Lemma dt_s1 :
    evt asegs (fun msx => exists ff fp spa R m, msx = MS R F (Z_to_bv 64 ADT_D2) fc None m (seg_rom asegs) /\ dt_st1 ff fp spa R m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ADS_DTOR) fc None m0 (seg_rom asegs)).
  Proof.
    pose proof p_ranges as (R1' & R2' & R3').
    pose proof (c_ceil CTX) as CEIL. pose proof (c_lo CTX) as LO. pose proof (c_sp16 CTX) as SP16. pose proof (c_tp CTX) as TP.
    pose proof (c_rfs CTX) as RFS0. pose proof (c_rh CTX) as RH0. pose proof (c_lfn CTX) as LFn. pose proof (c_dsin CTX) as DSin.
    eapply evt_cut; [apply dt_p1|].
    intros ms1 (R1 & m1 & -> & RF1 & HRT1 & K2e & K9e & HTS1 & HP1 & HMI1).
    destruct (p0_keep m1 HP1 HMI1) as (AC1 & LV1 & ST1). destruct HP1 as [MU1 WM1].

    assert (K1 : PropExec.getr R1 1 = Z_to_bv 64 0xfca20).
    { apply (rtbl_In W0 R1 _ 1%bv (ELit 0xfca20) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K4 : PropExec.getr R1 4 = tp).
    { apply (rtbl_In W0 R1 _ 4%bv (EVar 48) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (SPA0 : exists spa, spa = (spz - 192) - (spz - 192) mod 32) by (eexists; reflexivity).
    destruct SPA0 as [spa Espa]. rewrite <- Espa in K2e.
    assert (SPA : spz - 208 <= spa <= spz - 192 /\ spa mod 32 = 0).
    { subst spa. clear - SP16 R1' R2'. unfold ADS_STACK in *. Z.div_mod_to_equations. lia. }
    clear Espa. destruct SPA as [SPA SPA32].
    assert (Us : bv_unsigned (PropExec.getr R1 2) = spa)
      by (rewrite K2e; apply unsigned_lit; clear - SPA R1' R2' R3'; unfold ADS_STACK in *; lia).

    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HHb); [exact RFS0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd].
      destruct (ah_RFS_range H HHb LF m0 RFS0) as [(B1 & B2 & B3 & B4) _].
      clear - R1' R2' R3' B2. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ADS_STACK, AFS_SIZE in *. lia. }
    assert (RH1 : as_RHEAP H sA LB m1).
    { eapply (ah_RHEAP_frame H HHb); [exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. clear - R2'. unfold ADS_STACK in *. lia. }
    pose proof (ah_thr H HHb sA LB m1 RH1) as THR1.
    assert (LFn1 : (length LF < AFS_MAXLIVE_BP)%nat) by (clear - LFn; lia).
    rewrite (MS_full_eq R1 F _ fc m1 _ RF1).
    eapply evt_cut.
    { apply (SM2 (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5)
               (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10)
               (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15)
               (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20)
               (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
               (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30)
               (PropExec.getr R1 31) F fc m1 LF lo RFS1 LFn1).
      - rewrite Us. destruct (stk_split asegs m1 lo spa spz ST1 ltac:(clear - LO SPA; unfold ADS_STACK in *; lia)) as [S _]. exact S.
      - exact CEIL.
      - rewrite Us. clear - LO SPA. unfold AFS_STACK, ADS_STACK in *. lia.
      - exact HMI1.
      - rewrite K4. exact TP.
      - exact AC1.
      - exact THR1. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff & fp & junk1 & junk2
                & E2 & MU2 & WM2 & MI2 & ST2 & RF2 & FRC & SHF & FLG & AC2).
    subst ms2. rewrite K1, ret_pc_even; [| clear; lia | reflexivity].
    replace (fsz 2) with 256 in MU2 by reflexivity. replace (fshn 2) with 32 in MU2 by reflexivity.
    lazymatch goal with |- evt _ _ (MS ?RR _ _ _ _ _ _) => remember RR as R2 eqn:ER2 end.
    assert (RF2' : rfull R2) by (rewrite ER2; apply rfull_mkR).
    destruct (new_frame2 LF m2 ff fp RF2 DSin) as (FRESH & FD1 & FD2 & FD3).
    pose proof (mk_dg ff fp spa FRESH FD1 FD2 FD3 SPA32 SPA) as G.
    pose proof (fr_place2 LF ff fp FRESH) as (Q2 & Q3 & Q4 & Q6 & Q6' & B1 & B2 & _ & _ & B4 & AP & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & A1).

    rewrite Us in MU2, ST2.
    assert (MUA : munch (WA2 ff fp) m0 m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; apply sub_fp_of; unfold WA2.
      - apply Forall_cons; [| apply Forall_nil]. exists (spz - 16384, spz). split; [left; reflexivity | cbn; clear; lia].
      - apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - SPA; unfold AFS_STACK; lia]|].
        apply Forall_cons; [exists (as_FSB H, as_FSB H + AFS_FLAGS); split; [right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp, fp + 1); split; [right; right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (ff, ff + 256); split; [right; right; right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff, sh ff + 32); split; [right; right; right; right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_nil. }
    assert (WMA : wmono asegs m0 m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    destruct (wa2_keep ff fp m2 FRESH FD1 FD2 FD3 MUA WMA) as (DSA2 & DSW2 & DSV2 & DF2 & HF2 & LV2 & _ & ST2').
    assert (FRW2 : wr_at asegs m2 ff 256) by (destruct FRC as [_ W]; exact W).
    assert (FSW2 : wr_at asegs m2 (sh ff) 32) by (destruct SHF as (_ & _ & _ & W); exact W).
    assert (FLW2 : wr_at asegs m2 fp 1) by (destruct FLG as [_ W]; exact W).
    assert (Q1 : df sp ds err lo ff fp hw dptr hsel m2).
    { constructor; [exact AC2 | exact LV2 | exact ST2' | exact DSA2 | exact DSW2 | exact DSV2 | exact DF2 | exact HF2 | exact FRW2 | exact FSW2 | exact FLW2]. }
    apply evt_done. exists ff, fp, spa, R2, m2. split; [reflexivity|].

    set (WW := WDx ff fp spa).
    assert (EWW : WW = W0 ++ [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 spa; Z_to_bv 64 (err mod 2 ^ 32); Z_to_bv 64 hw; Z_to_bv 64 dptr]) by reflexivity.
    assert (KP : forall r, In r KEPT -> PropExec.getr R2 r = PropExec.getr R1 r).
    { intros r Hr. rewrite ER2. apply (getr_mkR_keptR R1); [exact (eq_sym K1) | exact Hr]. }
    assert (HRT2 : rtbl WW R2 RTD2).
    { assert (HK : rtbl WW R2 (keptk RTD1)).
      { rewrite EWW. apply rtbl_wext; [vm_compute; reflexivity|].
        apply (rtbl_keep W0 R1 R2 _ KEPT); [apply rtbl_keptk; exact HRT1 | apply rsub_keptk | exact KP]. }
      assert (HX : rtbl WW R2 [(2%bv, EVar 51); (9%bv, EVar 51); (10%bv, EVar 49)]).
      { unfold rtbl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        - rewrite (KP 2%bv ltac:(apply LbB_Pq.inr_In; vm_compute; reflexivity)), K2e. subst WW. evWW. reflexivity.
        - rewrite (KP 9%bv ltac:(apply LbB_Pq.inr_In; vm_compute; reflexivity)), K9e, K2e. subst WW. evWW. reflexivity.
        - rewrite ER2. subst WW. cbn [PropExec.getr mkR]. evWW. reflexivity. }
      apply (rtbl_sub _ _ _ _ (rtbl_app _ _ _ _ HK HX)). vm_compute. reflexivity. }

    assert (HTS2 : ftbl WW spz m2 TSD).
    { rewrite EWW. apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch W0 spz m1 m2 _ _ (-104) 0); [exact HTS1 | exact MU2 | exact WM2 | vm_compute; reflexivity |].
      cbn [disjoint_from]. clear - SPA Q2 Q3 Q6 Q6' B2 R2' R3' Z1 Z2 Z3 Z4 Z5 Z6 A1. unfold AFS_STACK, AFS_FLAGS, ADS_STACK in *. lia. }
    assert (HTF2 : ftbl WW ff m2 FTD0).
    { apply (proj1 (rw_cells_app asegs m2 ff [CB 24 junk1] _)) in FRC as [_ FRC1].
      apply (proj1 (rw_cells_app asegs m2 _ [C8 (PropExec.getr R1 2)] _)) in FRC1 as [C24 FRC2].
      apply (proj1 (rw_cells_app asegs m2 _ [CB (Z.to_nat (fsz 2 - 40)) junk2] _)) in FRC2 as [_ C248].
      cbn [cells_size csize Nat.add] in C24, C248.
      replace (ff + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat (Z.to_nat (fsz 2 - 40) + 0)) with (ff + 248) in C248 by (unfold fsz; clear; lia).
      replace (ff + Z.of_nat 24) with (ff + 24) in C24 by (clear; lia).
      unfold FTD0. apply (ftbl_app WW ff m2 [(24, 8%nat, EVar 51)] [(248, 8%nat, EVar 50)]).
      - apply ftbl_of_C8. subst WW. evWW. rewrite <- K2e. exact C24.
      - apply ftbl_of_C8. subst WW. evWW. exact C248. }
    constructor; [exact G | exact FRESH | exact RF2' | exact HRT2 | exact HTS2 | exact HTF2 | exact Q1 | exact MI2 | exact RF2 | exact MUA | exact WMA].
  Qed.

  Definition RT2x : list (reg * expr) := match ms with SShort => RTD3 | SLong _ _ => RTD2L end.
  Definition PC2x : Z := match ms with SShort => ADT_D3 | SLong _ _ => AOPDEL2 end.

  Record dt_st2 (ff fp spa : Z) (R : bvmap 5 word) (m : mem) : Prop := DT_ST2 {
    t2_g : dg H sp ds err lo ff fp spa hw dptr;
    t2_fr : fresh_frame H LF 2 ff fp;
    t2_rf : rfull R;
    t2_rt : rtbl (WDx ff fp spa) R RT2x;
    t2_ts : ftbl (WDx ff fp spa) spz m TSD;
    t2_ta : ftbl (WDx ff fp spa) spa m ATD2;
    t2_td0 : ftbl (WDx ff fp spa) ds m D0T2;
    t2_td1 : ftbl (WDx ff fp spa) ds m D1T2;
    t2_tf : ftbl (WDx ff fp spa) ff m FTD2;
    t2_th : ftbl (WDx ff fp spa) (ff / 8) m HTD2;
    t2_q : df sp ds err lo ff fp hw dptr hsel m;
    t2_mi : mem_inv asegs m;
    t2_rfs : as_RFS H ((2, ff, fp) :: LF) m;
    t2_mu : munch (WA2 ff fp) m0 m;
    t2_wm : wmono asegs m0 m
  }.

  Lemma dsin2 : forall ff fp, obj_inframe ((2, ff, fp) :: LF) ds DS_SIZE.
  Proof. intros ff fp. destruct (c_dsin CTX) as (f & Hf & A1 & A2). exists f. split; [right; exact Hf | split; [exact A1 | exact A2]]. Qed.

  Lemma wa2_grow : forall ff fp spa m m', dg H sp ds err lo ff fp spa hw dptr ->
    munch (WA2 ff fp) m0 m -> munch (removelast (LbB_DtK.QWD sp ds ff fp spa)) m m' -> munch (WA2 ff fp) m0 m'.
  Proof.
    intros ff fp spa m m' G MU MU'. pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU.
    eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. apply sub_fp_of. unfold LbB_DtK.QWD, WA2. cbn [removelast].
    rewrite !Z.add_assoc, (LbB_DtK.shbd_eq ff), Z.add_0_r.
    apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
    apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
    apply Forall_cons; [exists (ds, ds + 16); split; [do 5 right; left; reflexivity | cbn; clear; lia]|].
    apply Forall_cons; [exists (ds + 112, ds + 120); split; [do 6 right; left; reflexivity | cbn; clear; lia]|].
    apply Forall_cons; [exists (ff, ff + 256); split; [do 3 right; left; reflexivity | cbn; clear; lia]|].
    apply Forall_cons; [exists (sh ff, sh ff + 32); split; [do 4 right; left; reflexivity | cbn; clear; lia]|].
    apply Forall_nil.
  Qed.

  Lemma dt_s2 : forall ff fp spa R m, dt_st1 ff fp spa R m ->
    evt asegs (fun msx => exists R' m', msx = MS R' F (Z_to_bv 64 PC2x) fc None m' (seg_rom asegs) /\ dt_st2 ff fp spa R' m')
      (MS R F (Z_to_bv 64 ADT_D2) fc None m (seg_rom asegs)).
  Proof.
    intros ff fp spa R m [G FR RF HRT HTS HTF Q MI RFS MU WM].
    assert (HTA : ftbl (WDx ff fp spa) spa m []) by constructor.
    assert (HTD : ftbl (WDx ff fp spa) ds m []) by constructor.
    assert (HTH : ftbl (WDx ff fp spa) (ff / 8) m []) by constructor.
    pose proof (conj Q (LbB_DtK.Dx_refl sp ds ff fp spa m)) as HQP.
    unfold PC2x. unfold hsel in HQP. destruct ms as [|d asz] eqn:Ems.
    - eapply evt_cut; [eapply (q_d2s H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds err lo ff fp spa hw dptr G m R m RF HRT HTS HTA HTD HTF HTH HQP MI)|].
      intros ms1 (R1 & m1 & -> & RF1 & HRT1 & HX1 & HA1 & HD01 & HD11 & HF1 & HH1 & HQP1 & MI1 & MU1 & WM1).
      apply evt_done. exists R1, m1. split; [reflexivity|].
      constructor; try assumption.
      + unfold RT2x. rewrite Ems. exact HRT1.
      + unfold hsel. rewrite Ems. exact (LbB_DtK.Dx_ok H sp ds err lo ff fp spa hw dptr G 1%nat m m1 HQP1 MI1).
      + eapply (LbB_DtK.RFS_stepd H HHbp sp ds err lo ff fp spa hw dptr G);
          [exact RFS | left; reflexivity | apply dsin2 | exact MU1 | exact WM1].
      + exact (wa2_grow ff fp spa m m1 G MU MU1).
      + eapply wmono_trans; [exact WM | exact WM1].
    - eapply evt_cut; [eapply (q_d2l H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds err lo ff fp spa hw dptr G m R m RF HRT HTS HTA HTD HTF HTH HQP MI)|].
      intros ms1 (R1 & m1 & -> & RF1 & HRT1 & HX1 & HA1 & HD01 & HD11 & HF1 & HH1 & HQP1 & MI1 & MU1 & WM1).
      apply evt_done. exists R1, m1. split; [reflexivity|].
      constructor; try assumption.
      + unfold RT2x. rewrite Ems. exact HRT1.
      + unfold hsel. rewrite Ems. exact (LbB_DtK.Dx_ok H sp ds err lo ff fp spa hw dptr G 2%nat m m1 HQP1 MI1).
      + eapply (LbB_DtK.RFS_stepd H HHbp sp ds err lo ff fp spa hw dptr G);
          [exact RFS | left; reflexivity | apply dsin2 | exact MU1 | exact WM1].
      + exact (wa2_grow ff fp spa m m1 G MU MU1).
      + eapply wmono_trans; [exact WM | exact WM1].
  Qed.

End DT.
