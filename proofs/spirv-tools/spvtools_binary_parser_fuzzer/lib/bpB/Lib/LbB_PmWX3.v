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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmHex LbB_PmDS LbB_PmExit2 LbB_PmLH LbB_PmOL LbB_TablStmt LbB_PmLeaf LbB_PmLeafW LbB_PmWords LbB_PmU2K LbB_PmWC1 LbB_PmWX1 LbB_PmWX2 LbB_PmWX5.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord.
Definition X3_FFX : list (Z * Z) := [(32, 8)].

Definition RT_X3F : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (10%bv, ELit 22); (19%bv, WADD WV_FF 9040); (20%bv, SH_FF);
   (22%bv, WADD WV_P 88); (23%bv, EVar WV_P); (24%bv, WADD WV_FF 7984); (25%bv, WADD WV_P 48); (26%bv, WADD WV_P 216);
   (27%bv, EVar WV_FF)].

Definition RT_X3K : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF); (21%bv, WADD WV_FF 9060); (23%bv, EVar WV_P);
   (25%bv, WADD WV_P 48); (27%bv, EVar WV_FF)].

Definition RT_X3I1 : list (reg * expr) :=
  [(1%bv, ELit 0xf502c); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (19%bv, WADD WV_P 88); (20%bv, SH_FF);
   (22%bv, WADD WV_FF 10112); (23%bv, EVar WV_P); (24%bv, WADD WV_FF 7984); (25%bv, WADD WV_P 48); (26%bv, WADD WV_P 216);
   (27%bv, EVar WV_FF)].

Definition RT_X3I2 : list (reg * expr) :=
  [(1%bv, ELit 0xf50cc); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (19%bv, WADD WV_P 88); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 9060); (22%bv, WADD WV_FF 10112); (23%bv, EVar WV_P); (24%bv, WADD WV_FF 7984); (25%bv, WADD WV_P 48);
   (27%bv, EVar WV_FF)].

Lemma ev_sltu0 : forall E (n : N) (x : Z), edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  edenot E (EAlu ALU_SLTU (ELit 0) (EVar n)) = Z_to_bv 64 (if x =? 0 then 0 else 1).
Proof.
  intros E n x He Hx.
  change (edenot E (EAlu ALU_SLTU (ELit 0) (EVar n))) with (alu64 ALU_SLTU (edenot E (ELit 0)) (edenot E (EVar n))).
  rewrite He. change (edenot E (ELit 0)) with (Z_to_bv 64 0). rewrite w_sltu by lia.
  destruct (Z.eqb_spec x 0) as [-> | Hn]; [reflexivity|].
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Definition EW12 : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12).
Definition EW8b : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 8).

Lemma x3_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

Lemma x3_ereg : forall R vals (n : N) v, (n < 32)%N -> PropExec.getr R (Z_to_bv 5 (Z.of_N n)) = v ->
  edenot (Eseed R vals) (EVar n) = v.
Proof. intros R vals n v Hn Hv. cbn [edenot]. rewrite Eseed_reg by exact Hn. exact Hv. Qed.

Lemma x3_sxr : forall x, 0 <= x < 2 ^ 32 -> 0 <= sx32A x < 2 ^ 64.
Proof. intros x Hx. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec x (2 ^ 31)); lia. Qed.

Lemma x3_ew : forall E (io wd k : Z), edenot E (EVar 21) = Z_to_bv 64 io -> edenot E (EVar 36) = Z_to_bv 64 wd ->
  0 <= io -> 0 <= wd -> 0 <= k -> wd + 4 * io + k < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) = Z_to_bv 64 (wd + 4 * io)
  /\ edenot E (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit k)) = Z_to_bv 64 (wd + 4 * io + k).
Proof.
  intros E io wd k H21 H36 Hio Hwd Hk Hs.
  assert (B : edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) = Z_to_bv 64 (wd + 4 * io))
    by (apply ev_idx4; [exact H21 | exact H36 | lia | lia | lia]).
  split; [exact B|]. apply ev_add2; [exact B | apply x3_lit | lia | lia | lia].
Qed.

Lemma x3_and3 : forall E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 4 = 0 ->
  edenot E (EAlu ALU_AND e (ELit 3)) = Z_to_bv 64 0.
Proof.
  intros E e a He Ha Hm. change (edenot E (EAlu ALU_AND e (ELit 3))) with (alu64 ALU_AND (edenot E e) (edenot E (ELit 3))).
  rewrite He, x3_lit. rewrite w_and by lia. f_equal. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact Hm.
Qed.

Lemma x3_and7 : forall E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 8 = 0 ->
  edenot E (EAlu ALU_ADD (EAlu ALU_AND e (ELit 7)) (ELit 3)) = Z_to_bv 64 3.
Proof.
  intros E e a He Ha Hm.
  change (edenot E (EAlu ALU_ADD (EAlu ALU_AND e (ELit 7)) (ELit 3)))
    with (alu64 ALU_ADD (alu64 ALU_AND (edenot E e) (edenot E (ELit 7))) (edenot E (ELit 3))).
  rewrite He, !x3_lit. rewrite w_and by lia.
  assert (L7 : Z.land a 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact Hm).
  rewrite L7. rewrite w_add by lia. reflexivity.
Qed.

Lemma x3_srl : forall E (n : N) x K, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x -> 0 <= K -> x + K < 2 ^ 62 ->
  edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar n) (ELit K)) (ELit 62)) = Z_to_bv 64 0.
Proof.
  intros E n x K He Hx HK Hs.
  change (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar n) (ELit K)) (ELit 62)))
    with (alu64 ALU_SRL (edenot E (EAlu ALU_ADD (EVar n) (ELit K))) (edenot E (ELit 62))).
  rewrite (ev_add E n x K He ltac:(lia) ltac:(lia)), x3_lit. rewrite w_srl by lia. f_equal. apply Z.div_small. lia.
Qed.

Lemma x3_sltu : forall E e a wd, edenot E (EVar 36) = Z_to_bv 64 wd -> edenot E e = Z_to_bv 64 a ->
  0 < wd < 2 ^ 64 -> 1 <= a < 2 ^ 64 ->
  branch_taken BC_NE (edenot E (EAlu ALU_SLTU (ELit 0) (EVar 36))) (edenot E (EAlu ALU_SLTU e (ELit 1))) = true.
Proof.
  intros E e a wd H36 He Hwd Ha.
  change (edenot E (EAlu ALU_SLTU (ELit 0) (EVar 36))) with (alu64 ALU_SLTU (edenot E (ELit 0)) (edenot E (EVar 36))).
  change (edenot E (EAlu ALU_SLTU e (ELit 1))) with (alu64 ALU_SLTU (edenot E e) (edenot E (ELit 1))).
  rewrite H36, He, !x3_lit. rewrite !w_sltu by lia.
  replace (0 <? wd) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (a <? 1) with false by (symmetry; apply Z.ltb_ge; lia). rewrite br_ne by lia. reflexivity.
Qed.

Lemma x3_endv : forall E (n : N) e, edenot E (EVar n) = Z_to_bv 64 e -> (e = 0 \/ e = 1) ->
  edenot E (EExt true 0 4 (EVar n)) = Z_to_bv 64 e.
Proof. intros E n e He He01. rewrite (edenot_sext32 E n e He) by lia. f_equal. destruct He01 as [-> | ->]; reflexivity. Qed.

Section TX3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHx3 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Ltac tlx3_sc1 a bs RD YB YA :=
    first
      [ eapply (sc_rd_w4s _ _ _ a bs _);
          [ apply (adenot_of_estart _ _ a); [unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | lia]
          | exact RD | ev_xs; reflexivity ]
      | eapply (sc_flat_lit asegs _ _ _ _ a 4);
          [unfold estart; cbn [a_base a_off]; rewrite YB, u64_of_Z by lia; lia | apply elit_u; lia | lia | lia | lia]
      | eapply (sc_flat_lit asegs _ _ _ _ (a / 8 + SHBASE) 1);
          [apply (estart_sh _ _ a YA); lia | apply elit_u; lia
          | unfold SHBASE; Z.div_mod_to_equations; lia | lia | unfold SHBASE; Z.div_mod_to_equations; lia] ].

  Ltac x3_br :=
    cbn [sc_denot];
    first
      [ eapply x3_sltu; [eassumption | eassumption | lia | lia]
      | repeat match goal with
               | Y : edenot ?E ?e = _ |- context [edenot ?E ?e] => rewrite Y
               end;
        rewrite ?x3_lit; rewrite ?br_eq, ?br_ne, ?br_geu, ?br_ge_small, ?br_lts_small by lia; bool_lia ].

  Lemma x3_fk : forall (w : pmwA H) m m1 m2 W, ffkeepX w X3_FFX m m1 -> munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => wa_ff w + 16384 <= fst iv \/ snd iv <= wa_ff w
             \/ Exists (fun on : Z * Z => wa_ff w + fst on <= fst iv /\ snd iv <= wa_ff w + fst on + snd on) X3_FFX) W ->
    ffkeepX w X3_FFX m m2.
  Proof.
    intros w m m1 m2 W K MU WM FW.
    exact (ffkeepX_trans w X3_FFX X3_FFX X3_FFX m m1 m2 K (ffkeepX_munch w X3_FFX W m1 m2 MU WM FW) (incl_refl _) (incl_refl _)).
  Qed.

  Lemma x3_fkleaf : forall (w : pmwA H) m m1 m2 STK, pmw_okA H w -> 0 <= STK <= 4096 -> ffkeepX w X3_FFX m m1 ->
    munch ((wa_s1 w - STK, wa_s1 w) :: offs_wins (wa_ff w) []) m1 m2 -> wmono asegs m1 m2 -> ffkeepX w X3_FFX m m2.
  Proof.
    intros w m m1 m2 STK OK HS K MU WM. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    apply (x3_fk w m m1 m2 _ K MU WM). apply Forall_cons; [left; cbn [fst]; lia | apply Forall_nil].
  Qed.

  Definition K3234 (w : pmwA H) (s : as_St H) LB LBs (m : mem) (c : pmc) F fc (Q : config -> Prop) : Prop :=
    forall msF1 mo1 m1 R1 (ty wd enc : Z),
      as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf5128) fc None m1 (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m1 mo1 c S_INSTR TBL_EEF44 [] ->
      regs_tbl w R1 RT_X3K -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 26%bv = Z_to_bv 64 ty -> 0 <= ty <= 3 ->
      PropExec.getr R1 24%bv = Z_to_bv 64 wd -> 0 <= wd < 2 ^ 64 ->
      PropExec.getr R1 15%bv = Z_to_bv 64 enc -> 0 <= enc < 16 ->
      ffkeepX w X3_FFX m m1 ->
      as_SR H Q (mkCfg msF1 mo1).

  Definition KB9C (w : pmwA H) (s : as_St H) LB LBs (m : mem) (c : pmc) F fc (Q : config -> Prop) : Prop :=
    forall msF1 mo1 R1,
      as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf5d28) fc None m (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m mo1 c S_INSTR TBL_EEF44 [] ->
      regs_tbl w R1 RT_X5 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      as_SR H Q (mkCfg msF1 mo1).

  Definition KFLT (w : pmwA H) (s : as_St H) LB LBs (m : mem) (c : pmc) F fc (io : Z) (Q : config -> Prop) : Prop :=
    forall msF1 mo1 R1,
      as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf4e1c) fc None m (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m mo1 c S_INSTR TBL_EEF44 [] ->
      regs_tbl w R1 RT_X3F -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 21%bv = Z_to_bv 64 io ->
      as_SR H Q (mkCfg msF1 mo1).

  Lemma tl_x3 : forall (w : pmwA H) s LB LBs m mo (c : pmc) msF R F fc (io iwc op : Z) (bg : bool) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf4e04) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_3054 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 io -> PropExec.getr R 18%bv = Z_to_bv 64 op ->
    PropExec.getr R 10%bv = Z_to_bv 64 (if bg then 1 else 0) ->
    0 <= io -> 0 <= iwc < 2 ^ 16 -> 0 <= op < 2 ^ 16 -> io + iwc <= wa_n w -> wa_words w <> 0 ->
    (bg = true -> op = OP_TYPE_INT -> 4 <= iwc) -> (bg = true -> tg_generates_type op = true) ->
    c_endian c = 0 \/ c_endian c = 1 ->
    KB9C w s LB LBs m c F fc Q ->
    (bg = true -> op = OP_TYPE_FLOAT -> KFLT w s LB LBs m c F fc io Q) ->
    (tg_generates_type op = true -> K3234 w s LB LBs m c F fc Q) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc io iwc op bg Q OK X0 KR0 VIS0 RF0 HT0 G3_0 G4_0 G21 G18 G10
           Hio Hiwc Hop Hn Hw Hint Hgt Hend KB KF KK.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    assert (WP : 0 < wa_words w /\ wa_words w mod 16 = 0).
    { destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction | exact (conj W0 W16)]. }
    assert (Y21 : forall Xs, edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 21) = Z_to_bv 64 io)
      by (intros Xs; apply x3_ereg; [lia | exact G21]).
    assert (Y18 : forall Xs, edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 18) = Z_to_bv 64 op)
      by (intros Xs; apply x3_ereg; [lia | exact G18]).
    destruct bg.
    2: {
      set (Xs := @nil word).
      assert (Y10x : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 10) = Z_to_bv 64 0) by (apply x3_ereg; [lia | exact G10]).
      assert (HKN : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m []) by apply Forall_nil.
      pm_goX HHx3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs (@nil kentry) HKN
            40%nat [0xf5d28; 0xf5128; AT_FIXWORD; 0xf4e1c] [true] 41%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X5.
      { split_scs. all: first [x3_br | match goal with |- ?g => idtac "SCLEFT" g end]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      eapply (KB msF1 mo1 R1 KR1 VIS1 RF1 X1);
        [exact (regs_tbl_restrict w [] _ R1 RT_X5 HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0]. }
    assert (Y10 : forall Xs, edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 10) = Z_to_bv 64 1)
      by (intros Xs; apply x3_ereg; [lia | exact G10]).
    destruct (Z.eq_dec op 21) as [I21 | N21].
    2: {
      set (Xs := @nil word).
      pose proof (Y10 Xs) as Y10x. pose proof (Y18 Xs) as Y18x. pose proof (Y21 Xs) as Y21x.
      assert (HKN : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m []) by apply Forall_nil.
      destruct (Z.eq_dec op 22) as [I22 | N22].
      - pm_goX HHx3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs (@nil kentry) HKN
              40%nat [0xf5d28; 0xf5128; AT_FIXWORD; 0xf4e1c] [false; false; false] 41%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X3F.
        { split_scs. all: first [x3_br | match goal with |- ?g => idtac "SCLEFT" g end]. }
        intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
        lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
        change (mem_denot _ m _) with m in VIS1.
        eapply (KF eq_refl I22 msF1 mo1 R1 KR1 VIS1 RF1 X1);
          [exact (regs_tbl_restrict w [] _ R1 RT_X3F HTx1 ltac:(vm_compute; reflexivity))
          | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rewrite (HR1 21%bv); exact Y21x].
      - pm_goX HHx3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs (@nil kentry) HKN
              40%nat [0xf5d28; 0xf5128; AT_FIXWORD; 0xf4e1c] [false; false; true] 41%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X3K.
        { split_scs. all: first [x3_br | match goal with |- ?g => idtac "SCLEFT" g end]. }
        intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
        lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
        change (mem_denot _ m _) with m in VIS1.
        eapply (KK (Hgt eq_refl) msF1 mo1 m R1 0 0 0 KR1 VIS1 RF1 X1);
          [ exact (regs_tbl_restrict w [] _ R1 RT_X3K HTx1 ltac:(vm_compute; reflexivity))
          | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0
          | rewrite (HR1 26%bv); reflexivity | lia | rewrite (HR1 24%bv); reflexivity | lia
          | rewrite (HR1 15%bv); reflexivity | lia | apply ffkeepX_refl ]. }

    assert (Hi4 : 4 <= iwc) by (apply Hint; [reflexivity | exact I21]).
    destruct (words_rd4 H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] [] 0 (io + 3) OK X0 Hw ltac:(lia)) as (bs3 & RD3 & L3).
    pose proof (bytes_le_to_Z_range4 bs3 L3) as Rg3.
    replace (wa_words w + 4 * (io + 3)) with (wa_words w + 4 * io + 12) in RD3 by lia.

    assert (CONTI : forall msF1 mo1 R1,
              as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs) -> rfull R1 ->
              PMXA H LINV w s LB LBs m mo1 c S_INSTR TBL_EEF44 [] ->
              regs_tbl w R1 RT_X3I1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
              PropExec.getr R1 21%bv = Z_to_bv 64 io -> PropExec.getr R1 18%bv = Z_to_bv 64 (io + 2 ^ 61) ->
              PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A (bytes_le_to_Z bs3)) -> PropExec.getr R1 11%bv = Z_to_bv 64 (c_endian c) ->
              as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G21_1 G18_1 G10_1 G11_1.
      eapply (pm_leafW H HHx3 LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) (bytes_le_to_Z bs3, c_endian c) []
                w s LB LBs m mo1 c S_INSTR TBL_EEF44 [] [] 0 msF1 R1 F fc 0xf502c Q []);
        [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | rtf HT1 | rtf HT1 | reflexivity | lia | lia | reflexivity | reflexivity
        | cbn beta iota; split; [lia|]; split; [exact G10_1|]; split; [lia | exact G11_1]
        | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
        | intros r0 r1 m9 k9 n9 a9 _ Hin9; destruct Hin9
        | ].
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (r1 & Hr1 & Er1).
      pose proof (regs_keep w [] R1 R2 RT_X3I1 HT1 KEEP2) as HT2. change (rt_keep RT_X3I1) with RT_X3I1 in HT2.
      assert (FK2 : ffkeepX w X3_FFX m m2) by exact (x3_fkleaf w m m m2 0 OK ltac:(lia) (ffkeepX_refl w X3_FFX m) MU2 WM2).
      assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inb)); exact G3_1).
      assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inb)); exact G4_1).
      destruct (words_rd4 H LINV w s LB LBs m2 mo2 c S_INSTR TBL_EEF44 [] [] 0 (io + 2) OK X2 Hw ltac:(lia)) as (bs2 & RD2 & L2).
      pose proof (bytes_le_to_Z_range4 bs2 L2) as R2r.
      replace (wa_words w + 4 * (io + 2)) with (wa_words w + 4 * io + 8) in RD2 by lia.
      set (Xs := [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs2))]).
      pose proof (env_world_seed H w R2 Xs) as HE.
      pose proof (ev_world_all H w _ HE) as (_ & _ & _ & _ & E36 & _).
      assert (Y41 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (sx32A (bytes_le_to_Z bs2)))
        by (ev_xs; apply swrap32_sx32A; lia).
      assert (Y21x : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 21) = Z_to_bv 64 io)
        by (apply x3_ereg; [lia | transitivity (PropExec.getr R1 21%bv); [exact (KEEP2 21%bv ltac:(inb)) | exact G21_1]]).
      assert (Y18x : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 18) = Z_to_bv 64 (io + 2 ^ 61))
        by (apply x3_ereg; [lia | transitivity (PropExec.getr R1 18%bv); [exact (KEEP2 18%bv ltac:(inb)) | exact G18_1]]).
      assert (Y10x : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EVar 10) = Z_to_bv 64 (sx32A r1)) by (apply x3_ereg; [lia | exact Er1]).
      destruct (x3_ew (Eseed R2 (wenv_vals w ++ Xs)) io (wa_words w) 8 Y21x E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (YB & YA).
      assert (YEN : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EExt true 0 4 (EVar 41)) = Z_to_bv 64 (c_endian c))
        by (apply x3_endv; [exact Y41 | exact Hend]).
      assert (YAND : edenot (Eseed R2 (wenv_vals w ++ Xs))
                       (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 8)) (ELit 3)) = Z_to_bv 64 0)
        by (apply (x3_and3 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
      assert (YSRL : edenot (Eseed R2 (wenv_vals w ++ Xs)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 18) (ELit 2)) (ELit 62)) = Z_to_bv 64 0)
        by (apply (x3_srl _ _ (io + 2 ^ 61)); [exact Y18x | lia | lia | lia]).
      assert (HKX : know_ok asegs (Eseed R2 (wenv_vals w ++ Xs)) m2
                      [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW8b (ELit 3)) SHBASE) 1 (ELit 0)]).
      { apply Forall_cons; [eapply pmk_scal_endian with (1 := OK) (2 := X2) (3 := HE); exact Y41|].
        apply Forall_cons; [| apply Forall_nil].
        apply (pmk_sh_wordsE H HHx3 LINV w s LB LBs m2 mo2 c S_INSTR TBL_EEF44 [] [] 0 _ EW8b (io + 2) OK X2 Hw);
          [unfold EW8b; rewrite YA; f_equal; lia | lia | Z.div_mod_to_equations; lia]. }
      pm_goX HHx3 LINV_frame OK X2 KR2 VIS2 RF2 HT2 Xs
            [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW8b (ELit 3)) SHBASE) 1 (ELit 0)] HKX
            200%nat [0xf5d28; 0xf5128; AT_FIXWORD; 0xf4e1c] [true; true; true; true; true; true] 42%N S_INSTR (@nil Z) (@nil Z)
            TBL_EEF44 (@nil (Z * expr)) RT_X3I2.
      { split_scs. all: first [ tlx3_sc1 (wa_words w + 4 * io + 8) bs2 RD2 YB YA | x3_br
                              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
      lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m2 in X3 end.
      change (mem_denot _ m2 _) with m2 in VIS3.
      pose proof (regs_tbl_restrict w [] _ R3 RT_X3I2 HTx3 ltac:(vm_compute; reflexivity)) as HT3.
      assert (G3_3 : PropExec.getr R3 3%bv = wa_gp w) by (rewrite (HR3 3%bv); exact G3_2).
      assert (G4_3 : PropExec.getr R3 4%bv = wa_tp w) by (rewrite (HR3 4%bv); exact G4_2).
      assert (Hty : 0 <= (if sx32A r1 =? 0 then 0 else 1) + 1 <= 3) by (destruct (sx32A r1 =? 0); lia).
      assert (G26_3 : PropExec.getr R3 26%bv = Z_to_bv 64 ((if sx32A r1 =? 0 then 0 else 1) + 1)).
      { rewrite (HR3 26%bv).
        lazymatch goal with |- context [sr_get ?sr 26%bv] =>
          change (sr_get sr 26%bv) with (EAlu ALU_ADD (EAlu ALU_SLTU (ELit 0) (EVar 10)) (ELit 1)) end.
        apply ev_add2; [apply ev_sltu0; [exact Y10x | apply x3_sxr; lia] | apply x3_lit | destruct (sx32A r1 =? 0); lia | lia
                       | destruct (sx32A r1 =? 0); lia]. }
      eapply (pm_leafW H HHx3 LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) (bytes_le_to_Z bs2, c_endian c) []
                w s LB LBs m2 mo3 c S_INSTR TBL_EEF44 [] [] 0 msF3 R3 F fc 0xf50cc Q []);
        [ exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | rtf HT3 | rtf HT3 | reflexivity | lia | lia | reflexivity | reflexivity
        | cbn beta iota; split; [lia|]; split; [rewrite (HR3 10%bv); exact Y42|]; split; [lia | rewrite (HR3 11%bv); exact YEN]
        | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
        | intros r0 r1' m9 k9 n9 a9 _ Hin9; destruct Hin9
        | ].
      intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 (r2 & Hr2 & Er2).
      pose proof (regs_keep w [] R3 R4 RT_X3I2 HT3 KEEP4) as HT4. change (rt_keep RT_X3I2) with RT_X3I2 in HT4.
      assert (FK4 : ffkeepX w X3_FFX m m4) by exact (x3_fkleaf w m m2 m4 0 OK ltac:(lia) FK2 MU4 WM4).
      assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv ltac:(inb)); exact G3_3).
      assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv ltac:(inb)); exact G4_3).
      assert (G26_4 : PropExec.getr R4 26%bv = Z_to_bv 64 ((if sx32A r1 =? 0 then 0 else 1) + 1))
        by (rewrite (KEEP4 26%bv ltac:(inb)); exact G26_3).
      set (Xs3 := @nil word).
      assert (HKN : know_ok asegs (Eseed R4 (wenv_vals w ++ Xs3)) m4 []) by apply Forall_nil.
      pm_goX HHx3 LINV_frame OK X4 KR4 VIS4 RF4 HT4 Xs3 (@nil kentry) HKN
            40%nat [0xf5d28; 0xf5128; AT_FIXWORD; 0xf4e1c] (@nil bool) 41%N S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X3K.
      { split_scs. }
      intros msF5 mo5 R5 KR5 VIS5 RF5 X5 HTx5 HR5 Hlf5.
      lazymatch type of X5 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m4 in X5 end.
      change (mem_denot _ m4 _) with m4 in VIS5.
      eapply (KK (Hgt eq_refl) msF5 mo5 m4 R5 ((if sx32A r1 =? 0 then 0 else 1) + 1) (sx32A r2) 0 KR5 VIS5 RF5 X5);
        [ exact (regs_tbl_restrict w [] _ R5 RT_X3K HTx5 ltac:(vm_compute; reflexivity))
        | rewrite (HR5 3%bv); exact G3_4 | rewrite (HR5 4%bv); exact G4_4
        | rewrite (HR5 26%bv); exact (x3_ereg R4 _ 26 _ ltac:(lia) G26_4) | exact Hty
        | rewrite (HR5 24%bv); exact (x3_ereg R4 _ 10 _ ltac:(lia) Er2) | apply x3_sxr; lia
        | rewrite (HR5 15%bv); reflexivity | lia | exact FK4 ]. }

    destruct (Z_le_gt_dec (4 * (io + 3) + 4) (8 * ((4 * wa_n w) / 8))) as [FULL | PART].
    - set (Xs := [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs3))]).
      pose proof (env_world_seed H w R Xs) as HE.
      pose proof (ev_world_all H w _ HE) as (_ & _ & _ & _ & E36 & _).
      pose proof (Y10 Xs) as Y10x. pose proof (Y18 Xs) as Y18x. pose proof (Y21 Xs) as Y21x.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (sx32A (bytes_le_to_Z bs3)))
        by (ev_xs; apply swrap32_sx32A; lia).
      destruct (x3_ew (Eseed R (wenv_vals w ++ Xs)) io (wa_words w) 12 Y21x E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (YB & YA).
      assert (YEN : edenot (Eseed R (wenv_vals w ++ Xs)) (EExt true 0 4 (EVar 41)) = Z_to_bv 64 (c_endian c))
        by (apply x3_endv; [exact Y41 | exact Hend]).
      assert (YAND : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12)) (ELit 3)) = Z_to_bv 64 0)
        by (apply (x3_and3 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
      assert (YSRL : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_SRL (EAlu ALU_ADD (EVar 21) (ELit 2305843009213693955)) (ELit 62)) = Z_to_bv 64 0)
        by (apply (x3_srl _ _ io); [exact Y21x | lia | lia | lia]).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m
                      [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW12 (ELit 3)) SHBASE) 1 (ELit 0)]).
      { apply Forall_cons; [eapply pmk_scal_endian with (1 := OK) (2 := X0) (3 := HE); exact Y41|].
        apply Forall_cons; [| apply Forall_nil].
        apply (pmk_sh_wordsE H HHx3 LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] [] 0 _ EW12 (io + 3) OK X0 Hw);
          [unfold EW12; rewrite YA; f_equal; lia | lia | exact FULL]. }
      pm_goX HHx3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW12 (ELit 3)) SHBASE) 1 (ELit 0)] HKX
            200%nat [0xf5d28; 0xf5128; AT_FIXWORD; 0xf4e1c] [false; true; true; true; true; true; true; true] 42%N S_INSTR
            (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X3I1.
      { split_scs. all: first [ tlx3_sc1 (wa_words w + 4 * io + 12) bs3 RD3 YB YA | x3_br
                              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      eapply (CONTI msF1 mo1 R1 KR1 VIS1 RF1 X1);
        [ exact (regs_tbl_restrict w [] _ R1 RT_X3I1 HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rewrite (HR1 21%bv); exact Y21x
        | rewrite (HR1 18%bv); exact (ev_add _ 21 io (2 ^ 61) Y21x ltac:(lia) ltac:(lia))
        | rewrite (HR1 10%bv); exact Y42 | rewrite (HR1 11%bv); exact YEN ].
    - assert (Hp : 4 * (io + 3) = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4) by (Z.div_mod_to_equations; lia).
      set (Xs := [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z bs3))]).
      pose proof (env_world_seed H w R Xs) as HE.
      pose proof (ev_world_all H w _ HE) as (_ & _ & _ & _ & E36 & _).
      pose proof (Y10 Xs) as Y10x. pose proof (Y18 Xs) as Y18x. pose proof (Y21 Xs) as Y21x.
      assert (Y41 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 41) = Z_to_bv 64 (c_endian c)) by (ev_xs; reflexivity).
      assert (Y42 : edenot (Eseed R (wenv_vals w ++ Xs)) (EVar 42) = Z_to_bv 64 (sx32A (bytes_le_to_Z bs3)))
        by (ev_xs; apply swrap32_sx32A; lia).
      destruct (x3_ew (Eseed R (wenv_vals w ++ Xs)) io (wa_words w) 12 Y21x E36 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (YB & YA).
      assert (YEN : edenot (Eseed R (wenv_vals w ++ Xs)) (EExt true 0 4 (EVar 41)) = Z_to_bv 64 (c_endian c))
        by (apply x3_endv; [exact Y41 | exact Hend]).
      assert (YAND : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12)) (ELit 3)) = Z_to_bv 64 0)
        by (apply (x3_and3 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
      assert (Y7 : edenot (Eseed R (wenv_vals w ++ Xs))
                     (EAlu ALU_ADD (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 21)) (EVar 36)) (ELit 12)) (ELit 7)) (ELit 3))
                   = Z_to_bv 64 3)
        by (apply (x3_and7 _ _ _ YA); [lia | Z.div_mod_to_equations; lia]).
      assert (YSRL : edenot (Eseed R (wenv_vals w ++ Xs))
                       (EAlu ALU_SRL (EAlu ALU_ADD (EVar 21) (ELit 2305843009213693955)) (ELit 62)) = Z_to_bv 64 0)
        by (apply (x3_srl _ _ io); [exact Y21x | lia | lia | lia]).
      assert (HKX : know_ok asegs (Eseed R (wenv_vals w ++ Xs)) m
                      [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW12 (ELit 3)) SHBASE) 1 (ELit 4)]).
      { apply Forall_cons; [eapply pmk_scal_endian with (1 := OK) (2 := X0) (3 := HE); exact Y41|].
        apply Forall_cons; [| apply Forall_nil].
        apply (pmk_sh_wordsE_part H HHx3 LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] [] 0 _ EW12 (io + 3) OK X0 Hw);
          [unfold EW12; rewrite YA; f_equal; lia | exact (proj1 Hp) | exact (proj2 Hp)]. }
      pm_goX HHx3 LINV_frame OK X0 KR0 VIS0 RF0 HT0 Xs
            [KWord (SA (EVar 32) 88) 4 (EVar 41); KWord (SA (EAlu ALU_SRL EW12 (ELit 3)) SHBASE) 1 (ELit 4)] HKX
            200%nat [0xf5d28; 0xf5128; AT_FIXWORD; 0xf4e1c] [false; true; true; true; true; true; true; true; true] 42%N S_INSTR
            (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_X3I1.
      { split_scs. all: first [ tlx3_sc1 (wa_words w + 4 * io + 12) bs3 RD3 YB YA | x3_br
                              | match goal with |- ?g => idtac "SCLEFT" g end ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in X1 end.
      change (mem_denot _ m _) with m in VIS1.
      eapply (CONTI msF1 mo1 R1 KR1 VIS1 RF1 X1);
        [ exact (regs_tbl_restrict w [] _ R1 RT_X3I1 HTx1 ltac:(vm_compute; reflexivity))
        | rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rewrite (HR1 21%bv); exact Y21x
        | rewrite (HR1 18%bv); exact (ev_add _ 21 io (2 ^ 61) Y21x ltac:(lia) ltac:(lia))
        | rewrite (HR1 10%bv); exact Y42 | rewrite (HR1 11%bv); exact YEN ].
  Qed.
End TX3.
