(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmStep2U1.PmUpdU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PmStep2U1 PmLoopU1 PmInstU1 PmStep3U1 PmZw.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_calleesU1 SEGS Ly.L MI ST G tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBaseU1.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Notation DL := (cu_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  #[local] Notation pm_exit := (PmCoreU1.pm_exit MI ST).
  #[local] Notation pmx_ds_room := (PmStepU1.pmx_ds_room CL).
  #[local] Notation pm_tail_6733c := (PmStepU1.pm_tail_6733c CL).
  #[local] Notation cregs_kept := (PmStepU1.cregs_kept CL).
  #[local] Notation pm_put_cstr := (PmStepU1.pm_put_cstr CL).
  #[local] Notation pm_put_chars := (PmStepU1.pm_put_chars CL).
  #[local] Notation pm_put_num := (PmStepU1.pm_put_num CL).
  #[local] Notation pm_put_u16 := (PmStepU1.pm_put_u16 CL).
  #[local] Notation pm_put_u32 := (PmStepU1.pm_put_u32 CL).
  #[local] Notation pm_put_u64 := (PmStepU1.pm_put_u64 CL).
  #[local] Notation pm_put_int := (PmStepU1.pm_put_int CL).
  #[local] Notation pm_pdiagQ := (PmStepU1.pm_pdiagQ CL).
  #[local] Notation pm_dtor := (PmStepU1.pm_dtor CL).
  #[local] Notation pm_exhausted := (PmStepU1.pm_exhausted CL).
  #[local] Notation pm_fixword := (PmStepU1.pm_fixword CL).
  #[local] Notation pm_is_host_endian := (PmStepU1.pm_is_host_endian CL).
  #[local] Notation pm_binend := (PmStepU1.pm_binend CL).
  #[local] Notation pm_ecw_pbs := (PmStep2U1.pm_ecw_pbs CL).
  #[local] Notation pm_ecw_pbs1 := (PmStep2U1.pm_ecw_pbs1 CL).
  #[local] Notation pm_ecw_pbs2 := (PmStep2U1.pm_ecw_pbs2 CL).
  #[local] Notation pmx_upd_foot := (PmStep2U1.pmx_upd_foot).
  #[local] Notation pm_v2_push_fast := (PmStep2U1.pm_v2_push_fast).
  #[local] Notation pm_opcode_split := (PmStep2U1.pm_opcode_split CL).
  #[local] Notation pm_lookup_opcode := (PmStep2U1.pm_lookup_opcode CL).
  #[local] Notation pm_lookup_operand := (PmStep2U1.pm_lookup_operand CL).
  #[local] Notation pm_lookup_ext := (PmStep2U1.pm_lookup_ext CL).
  #[local] Notation pm_idesc_operands := (PmStep3U1.pm_idesc_operands CL).
  #[local] Notation pm_odesc_operands := (PmStep3U1.pm_odesc_operands CL).
  #[local] Notation pm_edesc_operands := (PmStep3U1.pm_edesc_operands CL).
  #[local] Notation pm_push_types := (PmStep3U1.pm_push_types CL).
  #[local] Notation pm_take_first := (PmStep3U1.pm_take_first CL).

  #[local] Notation izero := (PmInstU1.izero).
  #[local] Notation ictx := (PmInstU1.ictx).
  #[local] Notation nodes := (PmLoopU1.nodes).
  #[local] Notation macct := (PmLoopU1.macct).

  Definition oregs (w : pmw MI ST) (R : bvmap 5 word) : Prop := loop_regs w R.
  Definition OSREGS : list reg := [9; 18; 19; 20; 21; 25]%bv.

  Lemma loop_regs_oregs : forall (w : pmw MI ST) R, loop_regs w R -> oregs w R.
  Proof using AC MI ST. intros w R H. exact H. Qed.
  Lemma oregs_kept : forall (w : pmw MI ST) R R', oregs w R -> kept R R' -> oregs w R'.
  Proof using AC MI ST.
    intros w R R' OR KP. destruct OR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q25). unfold oregs, loop_regs.
    rewrite !KP by (first [solve [clear; cbv; tauto] | cbv; tauto]). repeat split; assumption.
  Qed.
  Lemma oregs_glue : forall (w : pmw MI ST) R R1,
    oregs w R -> (forall r, In r OSREGS -> getr R1 r = getr R r) ->
    getr R1 2%bv = Z_to_bv 64 (w_sp w) -> getr R1 3%bv = getr R 3%bv -> getr R1 4%bv = getr R 4%bv -> getr R1 8%bv = Z_to_bv 64 (w_p w) ->
    oregs w R1.
  Proof using AC MI ST.
    intros w R R1 OR GS G2 G3 G4 G8. destruct OR as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q25).
    unfold oregs, loop_regs. rewrite G2, G3, G4, G8, Q3, Q4. rewrite !GS by (unfold OSREGS; (first [solve [clear; cbn; tauto] | cbn; tauto])).
    rewrite Q9, Q18, Q19, Q20, Q21, Q25. repeat split; reflexivity.
  Qed.

  Definition ifr (w : pmw MI ST) (M : mem) : Prop :=
    exists ext tid rid,
      cellw SEGS M (w_sp w + 240) 8 0 /\ cellw SEGS M (w_sp w + 248) 2 0 /\ cellw SEGS M (w_sp w + 252) 4 ext /\
      cellw SEGS M (w_sp w + 256) 4 tid /\ cellw SEGS M (w_sp w + 260) 4 rid /\ cellw SEGS M (w_sp w + 264) 8 0 /\ cellw SEGS M (w_sp w + 272) 8 0
      /\ 0 <= ext < 2 ^ 31.
  Lemma izero_ifr : forall (w : pmw MI ST) M, izero w M -> ifr w M.
  Proof using AC MI ST. intros w M IZ. destruct IZ as (C1 & C2 & C3 & C4 & C5 & C6 & C7). exists 0, 0, 0. repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. Qed.
  Lemma ifr_ext : forall (w : pmw MI ST) M, ifr w M -> exists ext, cellw SEGS M (w_sp w + 252) 4 ext /\ 0 <= ext < 2 ^ 31.
  Proof using AC MI ST. intros w M (ext & tid & rid & _ & _ & C & _ & _ & _ & _ & H). exists ext. split; [exact C | exact H]. Qed.
  Lemma ifr_agree : forall (w : pmw MI ST) M M', ifr w M -> 0 <= w_sp w -> w_sp w + 280 < 2 ^ 64 ->
    CRep.agree_on (fun a => zwin (w_sp w + 240) (w_sp w + 280) a /\ ~ zwin (w_sp w + 250) (w_sp w + 252) a) M M' -> ifr w M'.
  Proof using AC MI ST.
    intros w M M' (ext & tid & rid & C1 & C2 & C3 & C4 & C5 & C6 & C7 & Hext) Hlo Hhi AG. exists ext, tid, rid.
    repeat match goal with |- _ /\ _ => split end; [ .. | lia | lia];
      (eapply (cellw_frame M M'); [eassumption | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Lemma ifr_store4 : forall (w : pmw MI ST) M (o v : Z),
    ifr w M -> ((o = 252 /\ v < 2 ^ 31) \/ o = 256 \/ o = 260) -> 0 <= v < 2 ^ 32 -> 0 <= w_sp w -> w_sp w + 280 < 2 ^ 64 ->
    ifr w (wbytes M (Z_to_bv 64 (w_sp w + o)) (word_to_le_bytes 4 (Z_to_bv 64 v))).
  Proof using AC MI ST.
    intros w M o v (ext & tid & rid & C1 & C2 & C3 & C4 & C5 & C6 & C7 & Hext) Ho Hv Hlo Hhi.
    assert (STo : stores_in (zwin (w_sp w + o) (w_sp w + o + 4)) M (wbytes M (Z_to_bv 64 (w_sp w + o)) (word_to_le_bytes 4 (Z_to_bv 64 v)))) by stin.
    assert (KEEP : forall a wd x, cellw SEGS M a wd x -> 0 <= a -> a + Z.of_N wd < 2 ^ 64 -> (a + Z.of_N wd <= w_sp w + o \/ w_sp w + o + 4 <= a) ->
                   cellw SEGS (wbytes M (Z_to_bv 64 (w_sp w + o)) (word_to_le_bytes 4 (Z_to_bv 64 v))) a wd x).
    { intros a wd x C Ha Hw Hd. eapply (cellw_frame M); [exact C | lia | lia | eapply stores_in_agree; [exact STo | unfold zwin; intros; lia]]. }
    assert (NEW : cellw SEGS (wbytes M (Z_to_bv 64 (w_sp w + o)) (word_to_le_bytes 4 (Z_to_bv 64 v))) (w_sp w + o) 4 v).
    { split; [cbn; lia | rdback]. }
    destruct Ho as [[-> Hv31] |[-> | ->]].
    - exists v, tid, rid. repeat match goal with |- _ /\ _ => split end; first [exact NEW | apply KEEP; [assumption | lia | cbn; lia | cbn; lia] | lia].
    - exists ext, v, rid. repeat match goal with |- _ /\ _ => split end; first [exact NEW | apply KEEP; [assumption | lia | cbn; lia | cbn; lia] | lia].
    - exists ext, tid, v. repeat match goal with |- _ /\ _ => split end; first [exact NEW | apply KEEP; [assumption | lia | cbn; lia | cbn; lia] | lia].
  Qed.

  Record ictxR : Type := ICTX { i_io : Z; i_fw : Z; i_iwc : Z; i_op : Z; i_d : Z; i_l : list Z }.
  Definition ipure (I : ictxR) : Prop :=
    i_iwc I = i_fw I / 2 ^ 16 /\ i_op I = i_fw I mod 2 ^ 16 /\ i_iwc I <> 0 /\ 0 <= i_fw I < 2 ^ 32 /\
    g_op G (i_op I) = Some (i_l I) /\ idesc (i_d I) (i_op I) /\ 0 <= i_io I.
  Lemma ipure_ranges : forall I, ipure I -> 0 < i_iwc I < 2 ^ 16 /\ 0 <= i_op I < 2 ^ 16.
  Proof using G idesc.
    intros I (E1 & E2 & Hnz & Hfw & _ & _ & _). rewrite E1, E2.
    pose proof (hi16_range (i_fw I) Hfw). pose proof (lo16_range (i_fw I)). rewrite <- E1 in *. lia.
  Qed.

  Definition popnd (w : pmw MI ST) (M : mem) (off t : Z) : Prop :=
    cellw SEGS M (w_sp w + 716) 2 off /\ cellw SEGS M (w_sp w + 718) 2 1 /\ cellw SEGS M (w_sp w + 720) 4 t /\
    cellw SEGS M (w_sp w + 724) 4 0 /\ cellw SEGS M (w_sp w + 728) 4 0 /\ cellw SEGS M (w_sp w + 732) 4 0.
  Lemma popnd_agree : forall (w : pmw MI ST) M M' off t, popnd w M off t -> 0 <= w_sp w -> w_sp w + 736 < 2 ^ 64 ->
    CRep.agree_on (zwin (w_sp w + 716) (w_sp w + 736)) M M' -> popnd w M' off t.
  Proof using AC MI ST.
    intros w M M' off t (C1 & C2 & C3 & C4 & C5 & C6) Hlo Hhi AG. unfold popnd.
    repeat match goal with |- _ /\ _ => split end;
      (eapply (cellw_frame M M'); [eassumption | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Definition OBASE (w : pmw MI ST) (I : ictxR) A M model c R : Prop :=
    PMX w A M model c /\ c_tr c = [] /\ pm_bud (w_n w) c /\ oregs w R /\ loop_mem w M /\
    ictx w M (i_io I) (i_fw I) (i_iwc I) (i_op I) (i_d I) /\ ifr w M /\
    c_icount c + 4 <= i_io I /\ c_endian c < 2 /\ w_words w <> 0 /\ macct c /\
    Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c)).

  Definition omeas (I : ictxR) (c : pmc) : Z :=
    3 * Z.max 0 (i_io I + i_iwc I - c_widx c) + zw_next (t3b (c_v3 c)).

  Definition iacc (I : ictxR) (c : pmc) : Prop :=
    (exists r, 0 <= r <= 1 /\ 2 * Zlen (t3c (c_m1 c)) <= i_io I + 2 * r /\ (r = 1 -> 2 <= c_widx c - i_io I) /\ ridc (t3b (c_v3 c)) + r <= 1) /\
    2 * Zlen (t3c (c_m2 c)) <= i_io I /\
    (exists p, 0 <= p <= 1 /\ 3 * Zlen (t3c (c_m3 c)) <= i_io I + 3 * p /\
       (i_op I <> OP_EXT_INST_IMPORT -> p = 0) /\
       (i_op I = OP_EXT_INST_IMPORT ->
          (p = 0 /\ t3b (c_v3 c) = [OT_LITERAL_STRING; OT_RESULT_ID]) \/
          (p = 0 /\ t3b (c_v3 c) = [OT_LITERAL_STRING] /\ 2 <= c_widx c - i_io I) \/
          (t3b (c_v3 c) = [] /\ (p = 1 -> 3 <= c_widx c - i_io I)))) /\
    (generates_type (i_op I) = true -> 2 <= c_widx c - i_io I \/ exists ys, t3b (c_v3 c) = ys ++ [OT_RESULT_ID]).

  Lemma notrid_push : forall (l xs l' : list Z), ~ In OT_RESULT_ID l -> push_types l xs = xs ++ l' -> ~ In OT_RESULT_ID l'.
  Proof using.
    intros l xs l' Hl E Hin. destruct (push_types_split l xs) as (l2 & E2 & _ & Hsub). rewrite E in E2. apply app_inv_head in E2. subst l2.
    exact (Hl (Hsub _ Hin)).
  Qed.
  Lemma notrid_operand : forall t v (l xs l' : list Z), g_operand G t v = Some l -> push_types l xs = xs ++ l' -> ~ In OT_RESULT_ID l'.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL. intros t v l xs l' Hg E. eapply notrid_push; [| exact E]. exact ((proj1 (proj2 (cu_rid1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL))) t v l Hg). Qed.
  Lemma notrid_ext : forall e v (l xs l' : list Z), g_ext G e v = Some l -> push_types l xs = xs ++ l' -> ~ In OT_RESULT_ID l'.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL. intros e v l xs l' Hg E. eapply notrid_push; [| exact E]. exact ((proj2 (proj2 (cu_rid1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL))) e v l Hg). Qed.
  Lemma notrid_spec : forall op (l xs l' : list Z), g_specop G op = true -> g_op G op = Some l -> push_types (skipn 2 l) xs = xs ++ l' -> ~ In OT_RESULT_ID l'.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL. intros op l xs l' Hs Hg E. eapply notrid_push; [| exact E]. exact ((cu_spec_rid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) op l Hs Hg). Qed.
  Lemma notrid_varid : ~ In OT_RESULT_ID [OT_VARIABLE_ID].
  Proof using. intros [H|[]]. cbv in H. discriminate. Qed.

  Lemma iacc_step : forall (I : ictxR) (c c' : pmc) (t : Z) (xs1 l' : list Z) (nw : Z),
    iacc I c -> t3b (c_v3 c) <> [] -> i_io I + 1 <= c_widx c ->
    take_first (t3b (c_v3 c)) = (t, xs1) ->
    t3b (c_v3 c') = xs1 ++ l' -> c_widx c' = c_widx c + nw ->
    (1 <= nw \/ (nw = 0 /\ zw_type t = true /\ l' = [])) ->
    (l' = [] \/ (t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING)) ->
    c_m2 c' = c_m2 c ->
    (c_m1 c' = c_m1 c \/ (t = OT_RESULT_ID /\ Zlen (t3c (c_m1 c')) <= Zlen (t3c (c_m1 c)) + 1)) ->
    (c_m3 c' = c_m3 c \/ (t = OT_LITERAL_STRING /\ i_op I = OP_EXT_INST_IMPORT /\ Zlen (t3c (c_m3 c')) <= Zlen (t3c (c_m3 c)) + 1)) ->
    ~ In OT_RESULT_ID l' ->
    iacc I c'.
  Proof using generates_type.
    intros I c c' t xs1 l' nw IACC Hne Hw1 Htf Exs' Ew' Hnw Hlits Em2 Hm1 Hm3 Hnrid.
    destruct IACC as ((r & Hr & Hm1le & Hr2 & Hrid) & Hm2 & (p & Hp & Hm3le & HpN & HpI) & G5).
    pose proof (ridc_take_first (t3b (c_v3 c)) Hne) as RT. rewrite Htf in RT. cbn [fst snd] in RT.
    pose proof (ridc_nonneg xs1) as R0. pose proof (ridc_nonneg (t3b (c_v3 c))) as R1.
    assert (Exs2 : ridc (t3b (c_v3 c')) = ridc xs1) by (rewrite Exs', ridc_app, (ridc_notin l' Hnrid); lia).
    assert (Hnw0 : 0 <= nw) by (destruct Hnw as [?|(? & _)]; lia).
    assert (Ht3 : t = OT_RESULT_ID -> 1 <= nw).
    { intros ->. destruct Hnw as [?|(_ & Hz & _)]; [lia | cbv in Hz; discriminate]. }
    unfold iacc. rewrite Ew', Em2, Exs2. split; [| split; [exact Hm2 | split]].
    -
      destruct Hm1 as [E1 | [Et Hins]].
      + exists r. rewrite E1. split; [lia|]. split; [lia|]. split; [intros H1; specialize (Hr2 H1); lia|].
        destruct (Z.eq_dec t OT_RESULT_ID); lia.
      + exists 1. rewrite Et in RT. destruct (Z.eq_dec OT_RESULT_ID OT_RESULT_ID) as [_|N]; [| exfalso; exact (N eq_refl)].
        specialize (Ht3 Et). split; [lia|]. split; [lia|]. split; [intros _; lia | lia].
    -
      destruct (Z.eq_dec (i_op I) OP_EXT_INST_IMPORT) as [EI | NI].
      + destruct (HpI EI) as [[Hp0 Exs] | [(Hp0 & Exs & Hd2) | [Exs Hd3]]].
        *
          rewrite Exs in Htf. change (take_first [OT_LITERAL_STRING; OT_RESULT_ID]) with (OT_RESULT_ID, [OT_LITERAL_STRING]) in Htf.
          injection Htf. intros Exs1 Et. subst t xs1.
          assert (El' : l' = []) by (destruct Hlits as [?|(N & _)]; [assumption | exfalso; exact (N eq_refl)]). subst l'.
          destruct Hm3 as [E3 | [Et _]]; [| exfalso; unfold OT_RESULT_ID, OT_LITERAL_STRING in Et; lia].
          exists p. rewrite E3. specialize (Ht3 eq_refl). split; [lia|]. split; [lia|]. split; [intros N; exfalso; exact (N EI)|].
          intros _. right; left. rewrite Exs'. split; [lia|]. split; [reflexivity | lia].
        *
          rewrite Exs in Htf. change (take_first [OT_LITERAL_STRING]) with (OT_LITERAL_STRING, @nil Z) in Htf.
          injection Htf. intros Exs1 Et. subst t xs1.
          assert (El' : l' = []) by (destruct Hlits as [?|(_ & _ & N)]; [assumption | exfalso; exact (N eq_refl)]). subst l'.
          assert (Hnw1 : 1 <= nw) by (destruct Hnw as [?|(_ & Hz & _)]; [lia | cbv in Hz; discriminate]).
          destruct Hm3 as [E3 | (_ & _ & Hins)].
          -- exists p. rewrite E3. split; [lia|]. split; [lia|]. split; [intros N; exfalso; exact (N EI)|].
             intros _. right; right. rewrite Exs'. split; [reflexivity | intros ->; lia].
          -- exists 1. split; [lia|]. split; [lia|]. split; [intros N; exfalso; exact (N EI)|].
             intros _. right; right. rewrite Exs'. split; [reflexivity | intros _; lia].
        * exfalso. exact (Hne Exs).
      + pose proof (HpN NI) as Hp0. destruct Hm3 as [E3 | (_ & EI & _)]; [| exfalso; exact (NI EI)].
        exists 0. rewrite E3. split; [lia|]. split; [lia|]. split; [intros _; reflexivity | intros EI; exfalso; exact (NI EI)].
    -
      intros Hgt. destruct (G5 Hgt) as [Hd | (ys & Eys)]; [left; lia|].
      rewrite Eys, take_first_snoc_rid in Htf. injection Htf. intros Exs1 Et. subst t. specialize (Ht3 eq_refl). left. lia.
  Qed.

  Definition OLI (w : pmw MI ST) (I : ictxR) A M model c R : Prop :=
    OBASE w I A M model c R /\
    i_io I + 1 <= c_widx c /\
    nodes c + 2 <= c_widx c + 3 /\
    t3b (c_v1 c) + omeas I c <= 3 * 2 ^ 16 + 1 /\
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I /\
    Zlen (t3b (c_v3 c)) + zw_next (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 1 /\
    zw_stack_ok (t3b (c_v3 c)) /\
    nty (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) /\
    iacc I c.

  Definition AE (w : pmw MI ST) (I : ictxR) A M model c R (t word : Z) : Prop :=
    OBASE w I A M model c R /\
    i_io I + 1 <= c_widx c < w_n w /\ c_widx c < i_io I + i_iwc I /\
    nodes c + 2 <= c_widx c + 3 /\ t3b (c_v1 c) + 1 <= 3 * 2 ^ 16 + 1 /\ Zlen (t3b (c_v2 c)) <= c_widx c - i_io I /\
    Zlen (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 2 /\
    0 <= t < 2 ^ 31 /\ 0 <= word < 2 ^ 32 /\
    getr R 22%bv = Z_to_bv 64 (PrsNeeds.sx32 word) /\ getr R 27%bv = Z_to_bv 64 t /\
    getr R 24%bv = Z_to_bv 64 (c_widx c - i_io I) /\ getr R 23%bv = Z_to_bv 64 (i_io I) /\ getr R 26%bv = Z_to_bv 64 (i_op I) /\
    popnd w M (c_widx c - i_io I) t /\ cellw SEGS M (w_sp w + 712) 4 word.

  Definition PUSHK (w : pmw MI ST) (I : ictxR) (K : TSet) (fx : FPState) (c : pmc) (t : Z) : Prop :=
    forall A' M' model' c' R' (nw : Z) (l' : list Z),
      OBASE w I A' M' model' c' R' ->
      getr R' 27%bv = Z_to_bv 64 t -> getr R' 23%bv = Z_to_bv 64 (i_io I) -> getr R' 26%bv = Z_to_bv 64 (i_op I) ->
      cellw SEGS M' (w_sp w + 718) 2 nw -> (1 <= nw \/ (nw = 0 /\ zw_type t = true /\ l' = [])) ->
      c_widx c' = c_widx c -> c_v1 c' = c_v1 c -> c_v2 c' = c_v2 c -> nodes c' <= nodes c + Z.min nw 1 ->
      t3b (c_v3 c') = t3b (c_v3 c) ++ l' -> seed_free l' -> Zlen l' <= 125 ->
      l' = [] \/ (t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING) ->
      c_m2 c' = c_m2 c ->
      (c_m1 c' = c_m1 c \/ (t = OT_RESULT_ID /\ Zlen (t3c (c_m1 c')) <= Zlen (t3c (c_m1 c)) + 1)) ->
      (c_m3 c' = c_m3 c \/ (t = OT_LITERAL_STRING /\ i_op I = OP_EXT_INST_IMPORT /\ Zlen (t3c (c_m3 c')) <= Zlen (t3c (c_m3 c)) + 1)) ->
      ~ In OT_RESULT_ID l' ->
      srealizes SEGS (cfg fx R' 0x67f60 M' model') K.

  Definition CHECKK (w : pmw MI ST) (K : TSet) (fx : FPState) : Prop :=
    forall A' M' model' c' R' (e : Z),
      PMX w A' M' model' c' -> c_tr c' = [] -> pm_bud (w_n w) c' ->
      getr R' 2%bv = Z_to_bv 64 (w_sp w) -> getr R' 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R' 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
      getr R' 8%bv = Z_to_bv 64 (w_p w) -> getr R' 22%bv = sxw e -> 0 < e < 2 ^ 32 ->
      srealizes SEGS (cfg fx R' 0x677c4 M' model') K.

  Definition aacc (I : ictxR) (c : pmc) (t : Z) : Prop :=
    (t = OT_RESULT_ID -> 2 * Zlen (t3c (c_m1 c)) <= i_io I) /\
    (t = OT_LITERAL_STRING -> i_op I = OP_EXT_INST_IMPORT -> 3 * Zlen (t3c (c_m3 c)) <= i_io I /\ 2 <= c_widx c - i_io I) /\
    (i_op I = OP_EXT_INST_IMPORT -> t = OT_RESULT_ID \/ t = OT_LITERAL_STRING).

  Lemma iacc_aacc : forall (I : ictxR) (c c' : pmc) (t : Z) (xs1 : list Z),
    iacc I c -> t3b (c_v3 c) <> [] -> take_first (t3b (c_v3 c)) = (t, xs1) ->
    c_m1 c' = c_m1 c -> c_m3 c' = c_m3 c -> c_widx c' = c_widx c -> aacc I c' t.
  Proof using generates_type.
    intros I c c' t xs1 ((r & Hr & Hm1 & Hr2 & Hrid) & _ & (p & Hp & Hm3 & HpN & HpI) & _) Hne Htf E1 E3 Ew.
    pose proof (ridc_take_first (t3b (c_v3 c)) Hne) as RT. rewrite Htf in RT. cbn [fst snd] in RT. pose proof (ridc_nonneg xs1) as R0.
    split; [| split].
    - intros ->. rewrite E1. destruct (Z.eq_dec OT_RESULT_ID OT_RESULT_ID) as [_|N]; [| exfalso; exact (N eq_refl)]. lia.
    - intros -> EI. rewrite E3, Ew. destruct (HpI EI) as [[Hp0 Exs] | [(Hp0 & Exs & Hd2) | [Exs Hd3]]].
      + exfalso. rewrite Exs in Htf. change (take_first [OT_LITERAL_STRING; OT_RESULT_ID]) with (OT_RESULT_ID, [OT_LITERAL_STRING]) in Htf.
        injection Htf. intros _ E. unfold OT_RESULT_ID, OT_LITERAL_STRING in E. lia.
      + split; lia.
      + exfalso. exact (Hne Exs).
    - intros EI. destruct (HpI EI) as [[Hp0 Exs] | [(Hp0 & Exs & Hd2) | [Exs Hd3]]].
      + left. rewrite Exs in Htf. change (take_first [OT_LITERAL_STRING; OT_RESULT_ID]) with (OT_RESULT_ID, [OT_LITERAL_STRING]) in Htf. injection Htf. intros _ E. exact (eq_sym E).
      + right. rewrite Exs in Htf. change (take_first [OT_LITERAL_STRING]) with (OT_LITERAL_STRING, @nil Z) in Htf. injection Htf. intros _ E. exact (eq_sym E).
      + exfalso. exact (Hne Exs).
  Qed.

  Definition arm_stmt (t pc : Z) : Prop :=
    forall (w : pmw MI ST) c0 K (fx : FPState) (I : ictxR) A M model c R (word : Z),
      PMS w c0 K -> frm_zero (@fp_csr fx) -> fconsts fx -> ipure I ->
      AE w I A M model c R t word ->
      (forall fx' : FPState, frm_zero (@fp_csr fx') -> fconsts fx' -> PUSHK w I K fx' c t) ->
      (forall fx' : FPState, frm_zero (@fp_csr fx') -> fconsts fx' -> CHECKK w K fx') ->
      aacc I c t ->
      srealizes SEGS (cfg fx R pc M model) K.

  Lemma AE_facts : forall (w : pmw MI ST) I A M model c R t word,
    ipure I -> AE w I A M model c R t word ->
    0 < i_iwc I < 2 ^ 16 /\ 0 <= i_op I < 2 ^ 16 /\ 0 <= c_widx c - i_io I < 2 ^ 16 /\
    Zlen (t3b (c_v3 c)) + 126 <= V3MAX /\ 0 <= c_icount c /\ c_icount c + 5 <= c_widx c.
  Proof using AC MI ST G idesc.
    intros w I A M model c R t word IP HAE. pose proof (ipure_ranges I IP) as (R1 & R2).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & _). destruct OB as (X & _ & _ & _ & _ & _ & _ & Hic & _).
    pose proof (x_scal X) as (S1 & S2 & _). unfold V3MAX. lia.
  Qed.
End PM.
