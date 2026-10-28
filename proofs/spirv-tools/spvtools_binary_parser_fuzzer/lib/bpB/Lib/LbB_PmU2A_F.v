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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmFin LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHex LbB_TablStmt LbB_PmLeaf LbB_PmWords LbB_PmVops LbB_PmU2K LbB_PmOL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HUbsan HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.

Definition RT_F06E4 : list (reg * expr) :=
  [(1%bv, ELit 0xf06e8); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (10%bv, WADD WV_FF 9040); (11%bv, ELit 0);
   (12%bv, ELit 40); (16%bv, EVar WV_FF); (18%bv, EVar WV_FF); (19%bv, WADD WV_FF 9040); (20%bv, SH_FF); (23%bv, EVar WV_P);
   (25%bv, ELit SHBASE)].
Definition RT_F06E8 : list (reg * expr) :=
  [(1%bv, ELit 0xf06e8); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, EVar WV_FF); (19%bv, WADD WV_FF 9040);
   (20%bv, SH_FF); (23%bv, EVar WV_P); (25%bv, ELit SHBASE)].
Definition RT_F07C8 : list (reg * expr) :=
  [(1%bv, ELit 0xf07c4); (2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, WADD WV_FF 9120);
   (19%bv, WADD WV_FF 9040); (20%bv, SH_FF); (23%bv, EVar WV_P); (25%bv, ELit SHBASE); (27%bv, WADD WV_P 48)].
Definition SH_P (k : Z) : expr := EAlu ALU_ADD (EAlu ALU_SRL (WADD WV_P k) (ELit 3)) (ELit SHBASE).
Definition TBL_F07C8 : list (Z * expr) :=
  TBL_PI0 ++ [(664, WADD WV_P 72); (656, SH_P 72); (536, SH_P 48); (544, ELit (2 ^ 61)); (520, SH_P 88); (512, WADD WV_P 88);
              (568, EVar WV_FF); (624, WADD WV_FF 9040)].
Definition FTBL_F07C8 : list (Z * expr) := zwords 9040 5.
Definition c_F06BC (c : pmc) : pmc := set_scalA c (c_widx c) (c_icount c + 1) (c_endian c) (c_reqconv c).
Definition WADDR : expr := EAlu ALU_ADD (EVar WV_WORDS) (EMd M_MUL (ELit 4) (EVar 41)).
Definition KX_F06E8 (v : Z) : list kentry :=
  [KWord (SA (EAlu ALU_SRL WADDR (ELit 3)) SHBASE) 1 (ELit v);
   KDisj (SA (EAlu ALU_SRL WADDR (ELit 3)) SHBASE) (ELit 1) (SA (EVar WV_S1) PM_RF_LO) (ELit (832 - PM_RF_LO));
   KDisj (SA (EAlu ALU_SRL WADDR (ELit 3)) SHBASE) (ELit 1) (SA FSHB SHBASE) (ELit PM_NSH)].

Lemma ev_waddr : forall E (y x : Z), edenot E (EVar WV_WORDS) = Z_to_bv 64 y -> edenot E (EVar 41) = Z_to_bv 64 x ->
  0 <= x -> 0 <= y -> y + 4 * x < 2 ^ 64 -> edenot E WADDR = Z_to_bv 64 (y + 4 * x).
Proof.
  intros E y x Hy Hx H0 H1 H2. unfold WADDR. cbn [edenot]. change (ev E 41) with (edenot E (EVar 41)).
  change (ev E WV_WORDS) with (edenot E (EVar WV_WORDS)). rewrite Hx, Hy. rewrite w_mul_litA. cbn [alu64 alu]. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (4 * x) (2 ^ 64)) by lia. rewrite (Z.mod_small y (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma estart_of_ev : forall E e off v, edenot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> estart E (SA e off) = v + off.
Proof. intros E e off v He Hv. unfold estart. cbn [a_base a_off]. rewrite He, u64_of_Z by lia. reflexivity. Qed.

Lemma estart_srl3 : forall E e off v, edenot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  estart E (SA (EAlu ALU_SRL e (ELit 3)) off) = v / 8 + off.
Proof. intros E e off v He Hv. unfold estart. cbn [a_base a_off]. rewrite (srl3_val E e v He Hv). reflexivity. Qed.

Lemma elenZ_litA : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. rewrite elenZ_lit. apply Z.mod_small. exact Hz. Qed.

Lemma sc_align4 : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 4 = 0 ->
  sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND e (ELit 3)) (ELit 0)).
Proof.
  intros SEGS M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
  rewrite w_and by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Hal. reflexivity.
Qed.

Lemma sc_sltu_ne : forall (SEGS : list Segment) M E e1 e2 a b, edenot E e1 = Z_to_bv 64 a -> edenot E e2 = Z_to_bv 64 b ->
  0 < a < 2 ^ 64 -> 0 < b < 2 ^ 64 ->
  sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_SLTU (ELit 0) e1) (EAlu ALU_SLTU e2 (ELit 1))).
Proof.
  intros SEGS M E e1 e2 a b H1 H2 Ha Hb. cbn [sc_denot]. cbn [edenot]. rewrite H1, H2.
  rewrite !w_sltu by lia. replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). rewrite br_eq by lia. reflexivity.
Qed.

Lemma sc_lt0_false : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 63 ->
  sc_denot SEGS M E (SCBr false BC_LT e (ELit 0)).
Proof.
  intros SEGS M E e a He Ha. cbn [sc_denot]. cbn [edenot]. rewrite He. rewrite br_lt by lia. apply Z.ltb_ge. lia.
Qed.

Lemma estart_of_ev0 : forall E e v, edenot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> estart E (SA e 0) = v.
Proof. intros E e v He Hv. unfold estart. cbn [a_base a_off]. rewrite He, u64_of_Z by lia. lia. Qed.

Lemma sc_ge_and7 : forall (SEGS : list Segment) M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 8 = 0 ->
  sc_denot SEGS M E (SCBr false BC_GE (EAlu ALU_ADD (EAlu ALU_AND e (ELit 7)) (ELit 3)) (ELit 4)).
Proof.
  intros SEGS M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He. rewrite (and7_add3_w a Ha Hal).
  rewrite br_ge by lia. reflexivity.
Qed.

Ltac u2a_sc X :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCDisj (SA _ 0) _ (SA (EVar _) _) _) =>
      eapply sc_disj_lit;
      [ eapply estart_of_ev; [eassumption | lia] | apply elenZ_litA; lia
      | eapply estart_of_ev; [eassumption | lia] | apply elenZ_litA; lia | lia | lia | lia | lia | lia | lia | lia ]
  | |- sc_denot _ _ _ (SCDisj (SA _ 0) _ (SA (EAlu ALU_SRL _ (ELit 3)) _) _) =>
      eapply sc_disj_lit;
      [ eapply estart_of_ev; [eassumption | lia] | apply elenZ_litA; lia
      | eapply estart_srl3; [eassumption | lia] | apply elenZ_litA; lia | lia | lia | lia | zlia | lia | zlia | zlia ]
  | |- sc_denot _ _ _ (SCReadBase (SA _ 0) 4 true _) =>
      eapply sc_rd_w4s; [ apply adenot_of_estart; [apply estart_of_ev0; [eassumption | lia] | lia] | eassumption | eassumption ]
  | |- sc_denot _ _ _ (SCReadBase (SA (EVar 32) 88) 4 true _) =>
      eapply sc_rd_fld4s;
      [ exact (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | cbn [c_endian c_F06BC set_scalA]; lia
      | apply adenot_of_estart; [apply estart_of_ev; [eassumption | lia] | unfold O_ENDIAN; lia] | eassumption ]
  | |- sc_denot _ _ _ (SCReadBase (SA (EVar 32) 72) 8 false _) =>
      eapply sc_rd_fld8;
      [ exact (xa_widx _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
      | apply adenot_of_estart; [apply estart_of_ev; [eassumption | lia] | unfold O_WIDX; lia] | eassumption ]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL _ (ELit 3)) _) _) =>
      eapply sc_flat_lit; [ eapply estart_srl3; [eassumption | lia] | apply elenZ_litA; lia | zlia | lia | zlia ]
  | |- sc_denot _ _ _ (SCFlat (SA _ 0) _) =>
      eapply sc_flat_lit; [ eapply estart_of_ev; [eassumption | lia] | apply elenZ_litA; lia | lia | lia | lia ]
  | |- sc_denot _ _ _ (SCBr false BC_LT _ (ELit 0)) => eapply sc_lt0_false; [eassumption | lia]
  | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_AND _ (ELit 3)) (ELit 0)) => eapply sc_align4; [eassumption | lia | zlia]
  | |- sc_denot _ _ _ (SCBr false BC_EQ (EVar _) (ELit 0)) => eapply sc_trap_null; [eassumption | lia]
  | |- sc_denot _ _ _ (SCBr false BC_LTU _ (EVar _)) => eapply sc_trap_wrap; [eassumption | eassumption | lia | lia | lia]
  | |- sc_denot _ _ _ (SCBr false BC_NE (EAlu ALU_SRL (EAlu ALU_ADD (EVar _) (ELit _)) (ELit _)) (ELit 0)) =>
      eapply sc_trap_srl; [eapply ev_add; [eassumption | lia | lia] | lia | lia]
  | |- sc_denot _ _ _ (SCBr false BC_EQ (EAlu ALU_SLTU (ELit 0) _) (EAlu ALU_SLTU _ (ELit 1))) =>
      eapply sc_sltu_ne; [eassumption | eassumption | lia | lia]
  | |- sc_denot _ _ _ (SCBr false BC_GE (EAlu ALU_ADD (EAlu ALU_AND _ (ELit 7)) (ELit 3)) (ELit 4)) =>
      eapply sc_ge_and7; [eassumption | lia | zlia]
  end.

Section U2A.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Record HS_F06E8 (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
              (msF : machine_state) (R F : bvmap 5 word) (fc : bv 32) : Prop := MKHS_F06E8 {
    h6_x   : PMXA H LINV w s LB LBs m mo (c_F06BC c) [OB_INST] TBL_PI0 FTBL_F07C8;
    h6_kr  : as_AKREL H s (mkCfg msF mo);
    h6_vis : as_VIS H s msF = MS R F (Z_to_bv 64 0xf06e8) fc None m (seg_rom asegs);
    h6_rf  : rfull R;
    h6_rt  : regs_tbl w R RT_F06E8;
    h6_gp  : PropExec.getr R 3%bv = wa_gp w;
    h6_tp  : PropExec.getr R 4%bv = wa_tp w
  }.

  Record HS_F07C8 (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
              (msF : machine_state) (R F : bvmap 5 word) (fc : bv 32) (r : Z) : Prop := MKHS_F07C8 {
    h8_x   : PMXA H LINV w s LB LBs m mo (c_F06BC c) [OB_INST; OB_FIRST_WORD] TBL_F07C8 FTBL_F07C8;
    h8_kr  : as_AKREL H s (mkCfg msF mo);
    h8_vis : as_VIS H s msF = MS R F (Z_to_bv 64 0xf07c8) fc None m (seg_rom asegs);
    h8_rf  : rfull R;
    h8_fz  : frm_zero fc;
    h8_rt  : regs_tbl w R RT_F07C8;
    h8_gp  : PropExec.getr R 3%bv = wa_gp w;
    h8_tp  : PropExec.getr R 4%bv = wa_tp w;
    h8_r   : 0 <= r < 2 ^ 32;
    h8_a0  : PropExec.getr R 10%bv = Z_to_bv 64 (sx32A r);
    h8_fw  : rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 (sx32A r))]
  }.

  Lemma u2a_words : forall w s LB LBs m mo c ins tbl ftbl TB spal,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> wa_words w <> 0 ->
    0 < wa_words w /\ wa_words w mod 16 = 0 /\ wa_words w + 4 * wa_n w <= 2 ^ 47
    /\ (wa_words w + 4 * wa_n w <= wa_s1 w + PM_RF_LO \/ wa_s1 w + 832 <= wa_words w)
    /\ (wa_words w + 4 * wa_n w <= sh (wa_ff w) \/ sh (wa_ff w) + 2048 <= wa_words w).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal OK X Hw.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    assert (HinLB : In (pw, wa_words w, k) LB).
    { apply (Permutation_in _ (Permutation_sym (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)))). apply in_app_iff. left. exact Hin. }
    pose proof (ah_blocks H HHm _ _ _ _ RH HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (aapp_disjoint_sh (wa_words w) k (wa_ff w) 16384 RAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS.
    unfold nsh in DS. change ((16384 + 7) / 8) with 2048 in DS. unfold PM_RF_LO.
    split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
  Qed.

  Lemma pm_u2a_head : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PI0A H LINV w s LB LBs m mo c msF R F fc ->
    (forall msF1 mo1 m1 R1, HS_F06E8 w s LB LBs m1 mo1 c msF1 R1 F fc -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK P0 K.
    destruct P0 as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz Hic Hend Hw Hbud Hacc Hlt Ha0].
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    pm_goS HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) (@nil kentry) 100%nat [AASAN_MEMSET] (@nil bool) 41%N
          [OB_INST] (@nil Z) (@nil Z) TBL_PI0 (@nil (Z * expr)) RT_F06E4 (c_F06BC c).
    - split_scs.
    - unfold scal_after, sval. lfield_rw. cbn beta iota.
      rewrite (ev_add _ 10%N (c_icount c) 1) by first [exact Ha0 | lia].
      rewrite u64_of_Z by lia. reflexivity.
    - unfold c_F06BC, set_scalA; cbn [c_widx]; lia.
    - unfold c_F06BC, set_scalA; cbn [c_widx c_icount]; lia.
    - unfold c_F06BC, set_scalA; cbn [c_endian]; lia.
    - unfold c_F06BC, set_scalA; cbn [c_reqconv]; lia.
    - intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
      eapply (pm_memset H HHm LINV LINV_frame w s LB LBs M1 mo1 _ [OB_INST] TBL_PI0 [] [] 0 msF1 R1 F fc 9040 40 0 0xf06e8 Q TBL_PI0 []);
        [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | rtf HTx1 | rtf HTx1
        | reflexivity | lia | lia | lia | lia | lia | vm_compute; reflexivity | apply incl_refl | vm_compute; reflexivity
        | apply incl_refl | vm_compute; reflexivity | vm_compute; reflexivity | ].
      intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 CZ2 FK2.
      pose proof (pmxa_ftbl_zeros H LINV w s LB LBs m2 mo2 _ _ _ _ _ _ 9040 40 5 X2 CZ2 ltac:(lia) ltac:(lia)) as X2z.
      pose proof (regs_keep w [] R1 R2 RT_F06E4 HTx1 (fun r Hr => KEEP2 r (or_intror Hr))) as HT2.
      change (rt_keep RT_F06E4) with RT_F06E8 in HT2.
      apply (K msF2 mo2 m2 R2). constructor.
      + exact X2z.
      + exact KR2.
      + exact VIS2.
      + exact RF2.
      + exact HT2.
      + rewrite (KEEP2 3%bv ltac:(right; inb)), (HR1 3%bv). exact G3_0.
      + rewrite (KEEP2 4%bv ltac:(right; inb)), (HR1 4%bv). exact G4_0.
  Qed.
  Lemma pm_u2a_tail : forall (w : pmwA H) s LB LBs m mo c msF R F fc (x : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo (c_F06BC c) [OB_INST; OB_FIRST_WORD] TBL_F07C8 FTBL_F07C8 ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_F07C8 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    0 <= x < 2 ^ 32 -> PropExec.getr R 10%bv = Z_to_bv 64 (sx32A x) ->
    PropExec.getr R 11%bv = Z_to_bv 64 (c_endian c) -> 0 <= c_endian c < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1 (r : Z), HS_F07C8 w s LB LBs m1 mo1 c msF1 R1 F fc r -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc x Q OK X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Hx G10 G11 Hen K.
    pose proof (pmw_bounds H w OK) as BND.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) (x, c_endian c) w _ _ _ _ _ (c_F06BC c) _ _ _ _ _
              msF R F fc 0xf07c4 Q);
      [ exact OK | exact X0 | exact KR0 | exact VIS0 | exact RF0 | rtf HT0 | rtf HT0 | reflexivity | lia | lia | reflexivity
      | cbn beta iota; split; [exact Hx|]; split; [exact G10|]; split; [exact Hen | exact G11]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 KEEP1 MU1 WM1 (r & Hr & Er).
    pose proof (regs_keep w [] R R1 RT_F07C8 HT0 KEEP1) as HT1. change (rt_keep RT_F07C8) with RT_F07C8 in HT1.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (KEEP1 3%bv ltac:(inb)); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (KEEP1 4%bv ltac:(inb)); exact G4_0).
    pm_go HHm LINV_frame OK X1 KR1 VIS1 RF1 HT1 (@nil word) (@nil kentry) 10%nat [0xf07c8] (@nil bool) 41%N
          [OB_INST; OB_FIRST_WORD] (@nil Z) (@nil Z) TBL_F07C8 FTBL_F07C8 RT_F07C8.
    { split_scs. }
    intros msF2 mo2 R2 KR2 VIS2 RF2 X2 HTx2 HR2 Hlf2.
    assert (LOGE : s_log SSr = [SE (SA (EVar WV_FF) 9120) 4 (EVar 10)]) by (vm_compute; reflexivity).
    pose proof (ev_world_all H w _ (env_world_seed H w R1 [])) as (_ & EV33 & _).
    assert (CW : rw_cells asegs (mem_denot (Eseed R1 (wenv_vals w ++ [])) m1 (s_log SSr)) (wa_ff w + 9120) [C4 (Z_to_bv 64 (sx32A r))]).
    { rewrite LOGE. rewrite LOGE in Hlf2.
      apply (rw_cells_mem_denot_w (Eseed R1 (wenv_vals w ++ [])) m1 [] (SA (EVar WV_FF) 9120) 4 (EVar 10) [] (wa_ff w + 9120)
               (C4 (Z_to_bv 64 (sx32A r)))).
      - exact Hlf2.
      - apply Forall_nil.
      - apply estart_of_ev; [exact EV33 | lia].
      - eapply wr_at_sub; [exact (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) | lia | change (fsz PM_FCLASS) with 16384; lia | lia].
      - reflexivity.
      - cbn. exact I.
      - change (edenot (Eseed R1 (wenv_vals w ++ [])) (EVar 10)) with (PropExec.getr R1 10%bv). rewrite Er. reflexivity. }
    eapply (K msF2 mo2 _ R2 r). constructor.
    - exact X2.
    - exact KR2.
    - exact VIS2.
    - exact RF2.
    - exact FZ0.
    - exact HTx2.
    - rewrite (HR2 3%bv). exact G3_1.
    - rewrite (HR2 4%bv). exact G4_1.
    - exact Hr.
    - rewrite (HR2 10%bv). exact Er.
    - exact CW.
  Qed.
  Lemma pm_u2a_F : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PI0A H LINV w s LB LBs m mo c msF R F fc ->
    4 * c_widx c + 4 <= 8 * ((4 * wa_n w) / 8) ->
    (forall msF1 mo1 m1 R1 (r : Z), HS_F07C8 w s LB LBs m1 mo1 c msF1 R1 F fc r -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK P0 HG K.
    pose proof P0 as P0c.
    destruct P0 as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz Hic Hend Hw Hbud Hacc Hlt Ha0].
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    apply (pm_u2a_head w s LB LBs m mo c msF R F fc Q OK P0c).
    intros msF1 mo1 m1 R1 [X1 KR1 VIS1 RF1 HT1 G3_1 G4_1].
    pose proof (u2a_words w s LB LBs m1 mo1 _ _ _ _ _ _ OK X1 (proj1 Hw)) as (WP & W16 & WN & WS1 & WSH).
    pose proof (pmw_apart_ff H HHm _ w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (_ & _ & WFF).
    specialize (WFF (proj1 Hw)).
    unfold sh, ASHADOW_BASE, SHBASE, PM_RF_LO in *.
    destruct (words_rd4 H LINV w s LB LBs m1 mo1 _ _ _ _ _ _ (c_widx c) OK X1 (proj1 Hw) ltac:(lia)) as (bs0 & RD0 & LN0).
    pose proof (bytes_le_to_Z_range4 bs0 LN0) as XR0.
    set (x0 := bytes_le_to_Z bs0) in *.
    set (E1 := Eseed R1 (wenv_vals w ++ [Z_to_bv 64 (c_widx c); Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)])).
    assert (HE1 : env_world H w E1) by exact (env_world_seed H w R1 _).
    pose proof (ev_world_all H w E1 HE1) as (EV32 & EV33 & EV34 & EV35 & EV36 & _).
    assert (EV41 : edenot E1 (EVar 41) = Z_to_bv 64 (c_widx c)) by reflexivity.
    assert (EV42 : edenot E1 (EVar 42) = Z_to_bv 64 (c_endian c)) by reflexivity.
    assert (EV43 : edenot E1 (EVar 43) = Z_to_bv 64 (bv_swrap 32 x0)) by reflexivity.
    assert (EWA : edenot E1 WADDR = Z_to_bv 64 (wa_words w + 4 * c_widx c)) by (apply ev_waddr; [exact EV36 | exact EV41 | lia | lia | lia]).
    assert (HKX : know_ok asegs E1 m1 (KX_F06E8 0)).
    { unfold KX_F06E8. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      - exact (pmk_sh_wordsE H HHm LINV w s LB LBs m1 mo1 _ _ _ _ _ _ E1 WADDR (c_widx c) OK X1 (proj1 Hw) EWA ltac:(lia) HG).
      - eapply pmk_sh_s1disj with (1 := OK) (2 := X1) (3 := HE1) (4 := EWA); lia.
      - eapply pmk_sh_fshdisj with (1 := OK) (2 := X1) (3 := HE1) (4 := EWA); lia. }
    pm_goX HHm LINV_frame OK X1 KR1 VIS1 RF1 HT1 [Z_to_bv 64 (c_widx c); Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)]
          (KX_F06E8 0) HKX 100%nat [AT_FIXWORD] [false; false; false; false; false; false] 41%N
          [OB_INST; OB_FIRST_WORD] [664; 656; 536; 544; 520; 512; 568; 624] (@nil Z) TBL_F07C8 FTBL_F07C8 RT_F07C8.
    { split_scs; u2a_sc X1. }
    intros msF2 mo2 R2 KR2 VIS2 RF2 X2 HTx2 HR2 Hlf2.
    pose proof (regs_tbl_restrict w [] _ R2 RT_F07C8 HTx2 ltac:(vm_compute; reflexivity)) as HT2.
    eapply (pm_u2a_tail w s LB LBs _ mo2 c msF2 R2 F fc x0 Q OK X2 KR2 VIS2 RF2 FZ0 HT2); [ | | exact XR0 | | | | exact K].
    - rewrite (HR2 3%bv). exact G3_1.
    - rewrite (HR2 4%bv). exact G4_1.
    - rewrite (HR2 10%bv). exact (swrap32_sx32A x0 XR0).
    - rewrite (HR2 11%bv). exact EV42.
    - lia.
  Qed.
End U2A.
