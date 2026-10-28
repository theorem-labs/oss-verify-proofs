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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.


From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmLeaf LbB_PmLH LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_TablImg LbB_PmEntry2 LbB_PmOL.

Definition RT_F1090 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (19%bv, EVar WV_P); (20%bv, SH_FF);
   (22%bv, WADD WV_FF 10112); (25%bv, WADD WV_P 264)].

Definition TBL_F1090 : list (Z * expr) :=
  [(400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216));
  (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (432, EAlu ALU_ADD (EVar 32) (ELit 232));
  (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224));
  (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880));
  (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880));
  (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88));
  (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48));
  (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952);
  (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240));
  (568, EVar 33); (576, EVar 33); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880);
  (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32);
  (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72));
  (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32);
  (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].

Definition KS_F1090 : list Z := [32; 40; 48; 56; 64; 72; 80; 88; 96; 112; 120; 128; 136; 144; 152; 160; 168; 200; 208; 216; 224; 232; 240; 248; 256; 264; 288; 296; 312; 328; 336; 344; 352; 384; 392; 424; 456; 472; 488].

Definition INS_F121C : list nat := S_INSTR ++ [46%nat].

Definition RT_F121C : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, WADD WV_FF 10144); (19%bv, EVar WV_P); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 9040); (22%bv, WADD WV_FF 10112); (23%bv, WADD WV_FF 7984); (24%bv, WADD WV_FF 5936);
   (25%bv, WADD WV_P 264); (26%bv, WADD WV_FF 112)].

Definition RT_IDESC : list (reg * expr) := RT_F121C ++ [(1%bv, ELit 0xf121c); (10%bv, EVar 41)].

Definition RT_PT : list (reg * expr) := RT_F121C ++ [(1%bv, ELit 0xf1230); (10%bv, WADD WV_FF 10144); (11%bv, WADD WV_P 264)].

Definition TBL_F121C : list (Z * expr) :=
  [(400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216));
  (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (432, EAlu ALU_ADD (EVar 32) (ELit 232));
  (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224));
  (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880));
  (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880));
  (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88));
  (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48));
  (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952);
  (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240));
  (568, EVar 33); (576, EVar 33); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880);
  (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32);
  (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72));
  (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32);
  (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040)); (32, EAlu ALU_ADD (EVar 33) (ELit 5472));
  (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032));
  (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008));
  (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (112, EAlu ALU_ADD (EVar 33) (ELit 6000));
  (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024));
  (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120));
  (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512));
  (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576));
  (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488));
  (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544));
  (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512));
  (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928));
  (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (456, EAlu ALU_ADD (EVar 33) (ELit 64));
  (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480))].

Lemma u2f_fld8 : forall m a z, rw_cells asegs m a [C8 (Z_to_bv 64 z)] -> 0 <= a -> fld ASEGS m a 8 z.
Proof.
  intros m a z Hc Ha. unfold fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma u2f_and3 : forall x, 0 <= x < 2 ^ 64 -> x mod 4 = 0 -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 0.
Proof.
  intros x Hx Hal. cbn [alu64 alu]. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small x) by lia. change (3 mod 2 ^ 64) with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  rewrite Hal. reflexivity.
Qed.

Lemma u2f_rt_in {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) X R RT r e,
  regs_tblX w X R RT -> In (r, e) RT -> PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ X)) e.
Proof. intros w X R RT r e HT Hin. exact (proj1 (Forall_forall _ _) HT (r, e) Hin). Qed.

Ltac u2_inl := unfold RT_IDESC, RT_PT, RT_F121C, KEPT_REGS; cbn [app]; repeat (first [left; reflexivity | right]).

Section U2F.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma u2f_ff_val : forall (w : pmwA H) X, pmw_okA H w ->
    edenot (Eseed bvmap_empty (wenv_vals w ++ X)) (EVar WV_FF) = Z_to_bv 64 (wa_ff w).
  Proof. intros w X OK. destruct (ev_world_all H w _ (env_world_seed H w bvmap_empty X)) as (_ & E33 & _). exact E33. Qed.

  Lemma u2f_rt_wv : forall (w : pmwA H) X R RT r (n : N) (z k : Z), pmw_okA H w ->
    regs_tblX w X R RT -> In (r, WADD n k) RT -> edenot (Eseed bvmap_empty (wenv_vals w ++ X)) (EVar n) = Z_to_bv 64 z ->
    0 <= z -> 0 <= k -> z + k < 2 ^ 64 -> PropExec.getr R r = Z_to_bv 64 (z + k).
  Proof.
    intros w X R RT r n z k OK HT Hin Hn Hz Hk Hzk. rewrite (u2f_rt_in w X R RT r _ HT Hin). unfold WADD.
    transitivity (alu64 ALU_ADD (edenot (Eseed bvmap_empty (wenv_vals w ++ X)) (EVar n)) (Z_to_bv 64 k)); [reflexivity|].
    rewrite Hn. apply w_add; lia.
  Qed.

  Lemma pm_u2f : forall (w : pmwA H) s LB LBs m mo c msF R F fc tbl (d op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR tbl [] -> incl TBL_F1090 tbl ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1090) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_F1090 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 9616) [C8 (Z_to_bv 64 d)] -> idescA d op ->
    (forall msF1 mo1 m1 R1 (sp_p : Z) (l : list Z),
       as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_PUSH_TYPES) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c INS_F121C TBL_F121C [] -> regs_tbl w R1 RT_F121C ->
       PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 1%bv = Z_to_bv 64 0xf1230 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) ->
       PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + 10144) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_p w + O_V3) ->
       rw_cells asegs m1 (wa_ff w + 10144) [C8 (Z_to_bv 64 sp_p); C8 (Z_to_bv 64 (Zlen l))] ->
       g_op TG op = Some l -> spanA sp_p l -> ffkeepX w [(10144, 16)] m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc tbl d op Q OK X0 IT KR0 VIS0 RF0 HT0 G3_0 G4_0 CD HID K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    destruct (idescA_facts d op HID) as (ir & _ & _ & _ & Hd1 & Hd2 & Hd4 & _).
    pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_F1090 [] OK X0 IT (incl_refl _)) as X0r.
    pm_go HHm LINV_frame OK X0r KR0 VIS0 RF0 HT0 [Z_to_bv 64 d]
          (@nil kentry) 300%nat [AT_IDESC_OPERANDS] [false; false] 41%N
          INS_F121C KS_F1090 (@nil Z) TBL_F121C (@nil (Z * expr)) RT_IDESC.
    { pose proof (env_world_seed H w R [Z_to_bv 64 d]) as HE.
      pose proof (ev_ff H w _ OK HE) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc.
      split_scs.
      - cbn [sc_denot]. cbn [edenot]. change (ev ?E 41) with (edenot E (EVar 41)). ev_xs.
        rewrite u2f_and3 by lia. rewrite br_ne by lia. reflexivity.
      - cbn [sc_denot]. ev_xs. cbn [edenot]. rewrite br_eq by lia. apply Z.eqb_neq. lia.
      - eapply sc_rd_fld8; [exact (u2f_fld8 _ _ _ CD ltac:(lia)) | | ev_xs; reflexivity].
        apply adenot_of_estart; [| lia]. unfold estart. cbn [a_base a_off]. rewrite EFc. reflexivity. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    lazymatch type of VIS1 with context [Z_to_bv 64 (s_pc ?ss)] => replace (s_pc ss) with AT_IDESC_OPERANDS in VIS1 by reflexivity end.
    pose proof (env_world_seed H w R [Z_to_bv 64 d]) as HE1.
    destruct (ev_world_all H w _ HE1) as (_ & E33 & _ & E35 & _).
    destruct (ev_world_all H w _ (env_world_seed H w bvmap_empty [])) as (P32 & F33 & _ & S35 & _).
    destruct (ev_world_all H w _ (env_world_seed H w bvmap_empty [Z_to_bv 64 d])) as (_ & _ & _ & S35d & _).
    assert (FK1 : ffkeepX w [] m M1).
    { pose proof (munch_sym _ m _ [(EVar WV_S1, 0, 832); (EAlu ALU_SRL (EVar WV_FF) (ELit 3), SHBASE, SHBASE + 2048)] Hlf1
                    ltac:(vm_compute; reflexivity)) as MUc.
      cbn [num_wins map] in MUc. rewrite (srl3_val _ (EVar WV_FF) (wa_ff w) E33 ltac:(lia)), (ev_s1 H w _ OK HE1) in MUc.
      apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)).
      apply Forall_cons; [left; cbn [fst]; lia|].
      apply Forall_cons; [destruct Q6; [left | right; left]; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (G1_1 : PropExec.getr R1 1%bv = Z_to_bv 64 0xf121c).
    { rewrite (u2f_rt_in w _ R1 RT_IDESC 1%bv (ELit 0xf121c) HTx1 ltac:(u2_inl)). reflexivity. }
    assert (G10_1 : PropExec.getr R1 10%bv = Z_to_bv 64 d).
    { rewrite (u2f_rt_in w _ R1 RT_IDESC 10%bv (EVar 41) HTx1 ltac:(u2_inl)). ev_xs. reflexivity. }
    assert (G2_1 : PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w)).
    { rewrite (u2f_rt_in w _ R1 RT_IDESC 2%bv (EVar WV_S1) HTx1 ltac:(u2_inl)). exact S35d. }
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    pose proof (regs_tbl_sub w _ R1 _ RT_F121C HTx1 ltac:(vm_compute; reflexivity)) as HTk1.
    pose proof (regs_tbl_restrict w [] _ R1 RT_F121C HTk1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_IDESC_OPERANDS TL_STACK _ _ _ (tla_idesc_operands HTL) (d, op)
              w s LB LBs M1 mo1 c INS_F121C TBL_F121C [] [] 0 msF1 R1 F fc 0xf121c Q OK X1 KR1 VIS1 RF1 G2_1 G1_1 eq_refl ltac:(lia)
              ltac:(unfold TL_STACK; lia) eq_refl (conj HID G10_1) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 QF2.
    destruct QF2 as (sp_p & l & Hg & HSP & E10 & E11).
    assert (FK2 : ffkeepX w [] M1 m2).
    { apply (ffkeepX_munch w _ _ _ _ MU2 WM2). apply Forall_cons; [left; cbn [fst]; unfold TL_STACK; lia | apply Forall_nil]. }
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(u2_inl)); exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(u2_inl)); exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_F121C HT1 KEEP2) as HT2.
    replace (rt_keep RT_F121C) with RT_F121C in HT2 by (vm_compute; reflexivity).
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word)
          (@nil kentry) 100%nat [AT_PUSH_TYPES] (@nil bool) 41%N
          INS_F121C (@nil Z) (@nil Z) TBL_F121C (@nil (Z * expr)) RT_PT.
    { split_scs. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    lazymatch type of VIS3 with context [Z_to_bv 64 (s_pc ?ss)] => replace (s_pc ss) with AT_PUSH_TYPES in VIS3 by reflexivity end.
    pose proof (env_world_seed H w R2 (@nil word)) as HE3.
    pose proof (ev_ff H w _ OK HE3) as EF3. change (EVar WV_FF) with (EVar 33%N) in EF3.
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2) as FW. change (fsz PM_FCLASS) with 16384 in FW.
    assert (WRk : forall k n, 0 <= k -> k + n <= 16384 -> wr_at asegs m2 (wa_ff w + k) n).
    { intros k n Hk Hkn. destruct FW as (F1 & F2 & F3). split; [lia|]. split; [lia|]. intros i Hi.
      replace (wa_ff w + k + i) with (wa_ff w + (k + i)) by lia. apply F3. lia. }
    assert (C0 : rw_cells asegs M3 (wa_ff w + 10144) [C8 (Z_to_bv 64 sp_p)]).
    { subst M3. eapply (rw_cells_log_nth_sb _ m2 _ 1%nat (EVar 33%N) 10144 8 (EVar 10));
        [exact Hlf3 | reflexivity | vm_compute; reflexivity | rewrite EF3; reflexivity | apply WRk; lia | reflexivity | exact Logic.I |].
      cbn [edenot]. rewrite Eseed_reg by lia. rewrite <- E10. reflexivity. }
    assert (C1 : rw_cells asegs M3 (wa_ff w + 10152) [C8 (Z_to_bv 64 (Zlen l))]).
    { subst M3. eapply (rw_cells_log_nth_sb _ m2 _ 0%nat (EVar 33%N) 10152 8 (EVar 11));
        [exact Hlf3 | reflexivity | vm_compute; reflexivity | rewrite EF3; reflexivity | apply WRk; lia | reflexivity | exact Logic.I |].
      cbn [edenot]. rewrite Eseed_reg by lia. rewrite <- E11. reflexivity. }
    assert (CC : rw_cells asegs M3 (wa_ff w + 10144) [C8 (Z_to_bv 64 sp_p); C8 (Z_to_bv 64 (Zlen l))]).
    { apply (proj2 (rw_cells_appA M3 (wa_ff w + 10144) [C8 (Z_to_bv 64 sp_p)] [C8 (Z_to_bv 64 (Zlen l))])). split; [exact C0|].
      replace (wa_ff w + 10144 + Z.of_nat (cells_size [C8 (Z_to_bv 64 sp_p)])) with (wa_ff w + 10152) by (cbn; lia). exact C1. }
    assert (FK3 : ffkeepX w [(10144, 16)] m2 M3).
    { pose proof (munch_sym _ m2 _ [(EVar 33%N, 10144, 10160)] Hlf3 ltac:(vm_compute; reflexivity)) as MUc.
      cbn [num_wins map] in MUc. rewrite EF3 in MUc.
      apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)).
      apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (FKall : ffkeepX w [(10144, 16)] m M3).
    { apply (ffkeepX_trans w [] [(10144, 16)] _ m m2 M3); [| exact FK3 | apply incl_nil_l | apply incl_refl].
      exact (ffkeepX_trans w [] [] [] m M1 m2 FK1 FK2 (incl_refl _) (incl_refl _)). }
    pose proof (regs_tbl_sub w [] R3 _ RT_F121C HTx3 ltac:(vm_compute; reflexivity)) as HT3.
    refine (K msF3 mo3 M3 R3 sp_p l KR3 VIS3 RF3 X3 HT3 _ _ _ _ _ _ CC Hg HSP FKall).
    - rewrite (HR3 3%bv). exact G3_2.
    - rewrite (HR3 4%bv). exact G4_2.
    - rewrite (u2f_rt_in w [] R3 RT_PT 1%bv (ELit 0xf1230) HTx3 ltac:(u2_inl)). reflexivity.
    - rewrite (u2f_rt_in w [] R3 RT_PT 2%bv (EVar WV_S1) HTx3 ltac:(u2_inl)). exact S35.
    - exact (u2f_rt_wv w [] R3 RT_PT 10%bv WV_FF (wa_ff w) 10144 OK HTx3 ltac:(u2_inl) F33 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (u2f_rt_wv w [] R3 RT_PT 11%bv WV_P (wa_p w) O_V3 OK HTx3 ltac:(u2_inl) P32 ltac:(lia) ltac:(unfold O_V3; lia) ltac:(unfold O_V3; lia)).
  Qed.
End U2F.
