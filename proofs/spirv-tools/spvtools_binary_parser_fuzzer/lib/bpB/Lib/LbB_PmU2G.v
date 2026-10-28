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


From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PmHyps PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RtOwn LbB_DStat LbB_ContStmt LbB_TablStmt LbB_PmLeaf LbB_PmLH LbB_PmVup LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_TablImg
  LbB_PmEntry2 LbB_PiStmt LbB_PmOL LbB_PmWG LbB_PmWPT LbB_PmU2F.

Definition KS_F1230 : list Z := [104; 176; 184; 192; 272; 280; 304; 320; 360; 368; 376; 496; 584; 592; 632].

Definition TBL_F12FC : list (Z * expr) :=
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
  (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (104, ELit 65535); (176, ELit 262140);
  (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (272, EAlu ALU_ADD (EVar 32) (ELit 96));
  (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936));
  (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40));
  (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880));
  (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (632, EAlu ALU_ADD (EVar 32) (ELit 264))].

Lemma u2g_bfilter_app : forall (P : Z -> Prop) (H : forall x, base.Decision (P x)) (a b : list Z),
  base.filter P (a ++ b) = base.filter P a ++ base.filter P b.
Proof.
  intros P H a b. induction a as [|x a IH]; [rewrite bfilter_nil; reflexivity|]. cbn [app]. rewrite !bfilter_cons, IH.
  destruct (base.decide (P x)); reflexivity.
Qed.
Lemma u2g_push_types_nil_cons : forall z r, push_types (z :: r) [] = push_types r [] ++ (if negb (z =? OT_NONE) then [z] else []).
Proof.
  intros z r. unfold push_types. cbn [app rev]. rewrite u2g_bfilter_app, bfilter_cons, bfilter_nil.
  destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
    exfalso; [exact Hd | apply Hd; exact Logic.I].
Qed.
Lemma u2g_push_types_nil_snoc : forall r z, push_types (r ++ [z]) [] = (if negb (z =? OT_NONE) then [z] else []) ++ push_types r [].
Proof.
  intros r z. unfold push_types. cbn [app]. rewrite rev_app_distr. cbn [rev app]. rewrite bfilter_cons.
  destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
    exfalso; [exact Hd | apply Hd; exact Logic.I].
Qed.

Lemma u2g_zw_init : forall l, op_list_ok l -> zw_stack_ok (push_types l []).
Proof.
  intros l [SF H47]. destruct l as [|z r _] using rev_ind.
  - change (push_types [] []) with (@nil Z ++ @nil Z). apply zw_stack_ok_intro; [exact seed_free_nil | left; reflexivity].
  - rewrite removelast_last in SF. rewrite u2g_push_types_nil_snoc.
    destruct (push_types_split r []) as (top & Etop & _ & Hin). cbn [app] in Etop. rewrite Etop.
    assert (SFt : seed_free top) by (intros t Ht; exact (SF t (Hin t Ht))).
    destruct (negb (z =? OT_NONE)) eqn:Ez.
    + destruct (zw_seed z) eqn:Es.
      * change ([z] ++ top) with ([z] ++ top). apply zw_stack_ok_intro; [exact SFt|].
        unfold zw_seed, zw_type in Es. unfold_OT.
        pose proof (H47 z ltac:(apply in_app_iff; right; left; reflexivity)) as Hz47. unfold_OT.
        destruct (Z.eqb_spec z 9); [subst; right; left; reflexivity|].
        destruct (Z.eqb_spec z 47); [exfalso; exact (Hz47 ltac:(assumption))|].
        destruct (Z.eqb_spec z 54); [subst; right; right; right; left; reflexivity|].
        destruct (Z.eqb_spec z 8); [subst; right; right; left; reflexivity|].
        cbn in Es. discriminate.
      * change ([z] ++ top) with ([] ++ ([z] ++ top)). apply zw_stack_ok_intro; [| left; reflexivity].
        intros t [<-|Ht]; [exact Es | exact (SFt t Ht)].
    + cbn [app]. change top with ([] ++ top). apply zw_stack_ok_intro; [exact SFt | left; reflexivity].
Qed.

Definition U2_ICTX_CELLS : list (Z * Z) := [(10112, 8); (9120, 4); (9136, 2); (9050, 2); (9616, 8)].
Definition U2_IFR_CELLS : list (Z * Z) := [(9040, 8); (9048, 2); (9052, 4); (9056, 4); (9060, 4); (9064, 8); (9072, 8)].
Definition u2_apart (X : list (Z * Z)) (cells : list (Z * Z)) : bool :=
  forallb (fun kn : Z * Z => forallb (fun on : Z * Z => (fst kn + snd kn <=? fst on) || (fst on + snd on <=? fst kn))%bool X) cells.
Lemma u2_apart_in : forall X cells k n, u2_apart X cells = true -> In (k, n) cells ->
  forallb (fun on : Z * Z => (k + n <=? fst on) || (fst on + snd on <=? k))%bool X = true.
Proof. intros X cells k n Hc Hin. exact (proj1 (forallb_forall _ _) Hc (k, n) Hin). Qed.

Section U2G.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis HPT : push_types_stmtA H.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma u2g_ictx_keep : forall (w : pmwA H) m m' X (I : ictxR),
    ictxA H w m I -> ffkeepX w X m m' -> u2_apart X U2_ICTX_CELLS = true -> ictxA H w m' I.
  Proof.
    intros w m m' X I (D1 & D2 & D3 & D4 & D5) K B.
    split; [| split; [| split; [| split]]];
      (eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (u2_apart_in X U2_ICTX_CELLS); [exact B | cbn; tauto]]).
  Qed.

  Lemma u2g_ifr_keep : forall (w : pmwA H) m m' X,
    ifrA H w m -> ffkeepX w X m m' -> u2_apart X U2_IFR_CELLS = true -> ifrA H w m'.
  Proof.
    intros w m m' X (ext & tid & rid & D1 & D2 & D3 & D4 & D5 & D6 & D7 & R1 & R2 & R3) K B.
    exists ext, tid, rid.
    do 7 (split; [eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (u2_apart_in X U2_IFR_CELLS); [exact B | cbn; tauto]]|]).
    split; [exact R1|]. split; [exact R2 | exact R3].
  Qed.

  Lemma pm_u2g : forall (w : pmwA H) s LB LBs m mo c msF R F fc (lw fw d sp_p : Z) (l : list Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c INS_F121C TBL_F121C [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_PUSH_TYPES) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_F121C -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 1%bv = Z_to_bv 64 0xf1230 -> PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R 10%bv = Z_to_bv 64 (wa_ff w + 10144) -> PropExec.getr R 11%bv = Z_to_bv 64 (wa_p w + O_V3) ->
    rw_cells asegs m (wa_ff w + 10144) [C8 (Z_to_bv 64 sp_p); C8 (Z_to_bv 64 (Zlen l))] ->
    g_op TG (fw mod 2 ^ 16) = Some l -> spanA sp_p l ->
    c_tr c = [] -> (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud (wa_n w) c ->
    c_widx c = lw + 1 -> c_icount c + 4 <= lw ->
    c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1) -> wa_words w <> 0 /\ 5 <= wa_n w ->
    pi_macct c -> pi_nodes c + 1 <= lw + 3 ->
    2 * Zlen (t3c (c_m1 c)) <= lw -> 2 * Zlen (t3c (c_m2 c)) <= lw -> 3 * Zlen (t3c (c_m3 c)) <= lw ->
    t3b (c_v1 c) = 0 -> Zlen (t3b (c_v2 c)) <= 1 -> t3b (c_v3 c) = [] ->
    0 <= fw < 2 ^ 32 -> fw / 2 ^ 16 <> 0 -> idescA d (fw mod 2 ^ 16) ->
    ictxA H w m (ICTX lw fw (fw / 2 ^ 16) (fw mod 2 ^ 16) d l) -> ifrA H w m ->
    (forall (I : ictxR) s' LB' LBs' m' mo' c' msF' R',
       OLIA H LINV w s' LB' LBs' m' mo' c' msF' R' F fc I -> i_io I = lw ->
       i_fw I = fw -> i_d I = d -> i_l I = l -> (exists b cap, c' = set_v3A c (b, push_types l [], cap)) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc lw fw d sp_p l Q OK X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 G1_0 G2_0 G10_0 G11_0 CS Hg SPN
           Htr Hbsz BUD Hwidx Hic Hend Hw MAC NOD L1 L2 L3 V1 V2 V3 Hfw Hnz HID IC FR K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pm_bud_v3bound _ _ BUD) as CAPB.
    pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR.
    assert (TRR : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF])
      by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_RREF) ltac:(cbn; repeat (first [left; reflexivity | right]))).
    assert (TRC : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF])
      by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_CREF) ltac:(cbn; repeat (first [left; reflexivity | right]))).
    pose proof TG_ok as GOK. pose proof tg_maxlen as TML.
    pose proof (go_len_op _ GOK _ l Hg) as LL. unfold Zlength in LL. change (Zlen l <= g_maxlen TG) in LL.
    assert (LR : Forall (fun t => 0 <= t < 2 ^ 31) l).
    { apply Forall_forall. intros x Hx. eapply (go_range _ GOK l x); [left; exists (fw mod 2 ^ 16); exact Hg | exact Hx]. }
    assert (BUDm : forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c))) (t3c (c_v3 c)) (Zlen l) ->
                   pm_bud (wa_n w) (set_v3A c (b'', xs'', cap''))).
    { intros b'' xs'' cap'' Hc. apply pm_bud_v3cap; [exact BUD|]. rewrite V3 in Hc. unfold capmax in Hc. replace (Zlen (@nil Z)) with 0 in Hc by reflexivity. pose proof (Zlen_nonneg l). lia. }
    eapply (pm_push_types H HHbp LINV LINV_cl LINV_relro HOWN HPT w s LB LBs m mo c _ TBL_F121C [] [] 0 msF R F fc 0xf1230 10144 sp_p l Q
              OK X0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KR0 VIS0 RF0 G1_0 eq_refl ltac:(lia) G2_0 G4_0 G10_0 G11_0
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) eq_refl CS SPN ltac:(lia) LR BUDm TRC TRR).
    intros msF8 mo8 m8 R8 s8 LB8 LBs8 b8 cap8 KR8 VIS8 RF8 X8 KEEP8 BUD8 CAPR8 GROW8 CELLS8.
    rewrite V3 in X8, BUD8. cbn [app] in X8, BUD8.
    set (c8 := set_v3A c (b8, push_types l [], cap8)) in *.
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); exact G3_0).
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(cbn; repeat (first [left; reflexivity | right]))); exact G4_0).
    pose proof (regs_keepK w [] R R8 RT_F121C V4_KEPT HT0 KEEP8) as HT8.
    replace (rt_keepK V4_KEPT RT_F121C) with RT_F121C in HT8 by (vm_compute; reflexivity).
    assert (FK8 : ffkeepX w [] m m8) by (intros k cs Hk Hkn _ C; exact (CELLS8 k cs Hk Hkn C)).
    pm_go HHm LINV_frame OK X8 KR8 VIS8 RF8 HT8 (@nil word)
          (@nil kentry) 100%nat [OL_HEAD] (@nil bool) 41%N
          S_INSTR KS_F1230 (@nil Z) TBL_F12FC (@nil (Z * expr)) RT_EEF44.
    { split_scs. }
    intros msF9 mo9 R9 KR9 VIS9 RF9 X9 HTx9 HR9 Hlf9.
    lazymatch type of X9 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M9 := mm) in * end.
    lazymatch type of VIS9 with context [Z_to_bv 64 (s_pc ?ss)] => replace (s_pc ss) with OL_HEAD in VIS9 by reflexivity end.
    pose proof (env_world_seed H w R8 (@nil word)) as HE9.
    destruct (ev_world_all H w _ HE9) as (_ & E33 & _ & _ & _).
    assert (FK9 : ffkeepX w [] m8 M9).
    { pose proof (munch_sym _ m8 _ [(EVar WV_S1, 0, 832); (EAlu ALU_SRL (EVar WV_FF) (ELit 3), SHBASE, SHBASE + 2048)] Hlf9
                    ltac:(vm_compute; reflexivity)) as MUc.
      cbn [num_wins map] in MUc. rewrite (srl3_val _ (EVar WV_FF) (wa_ff w) E33 ltac:(lia)), (ev_s1 H w _ OK HE9) in MUc.
      apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)).
      apply Forall_cons; [left; cbn [fst]; lia|].
      apply Forall_cons; [destruct Q6; [left | right; left]; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (FK : ffkeepX w [] m M9) by exact (ffkeepX_trans w [] [] [] m m8 M9 FK8 FK9 (incl_refl _) (incl_refl _)).
    pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X9
                  (tbl_incl TBL_EEF44 TBL_F12FC ltac:(vm_compute; reflexivity)) (incl_refl _)) as X9r.
    set (I := ICTX lw fw (fw / 2 ^ 16) (fw mod 2 ^ 16) d l).
    assert (IP : ipureA I).
    { unfold ipureA, PmODefsS1.ipure. cbn [I PmODefsS1.i_io PmODefsS1.i_fw PmODefsS1.i_iwc PmODefsS1.i_op PmODefsS1.i_d PmODefsS1.i_l].
      pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hnz|]. split; [exact Hfw|]. split; [exact Hg|]. split; [exact HID | lia]. }
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop].
    cbn [I PmODefsS1.i_iwc PmODefsS1.i_op] in Riwc, Rop.
    destruct (push_types_split l []) as (xs & Exs & Hxl & Hin). cbn [app] in Exs.
    pose proof (zw_next_range (push_types l [])) as Hzn.
    assert (Hbsz8 : forall q k, In (q, k) (c_blocks c8) -> k <= 2 ^ 40).
    { pose proof (pm_bud_v3bound _ _ BUD8) as CAP8.
      intros q k Hin'. subst c8. destruct (c_blocks_v3_in c _ _ _ _ _ Hin') as [Hin''| ->]; [exact (Hbsz _ _ Hin'') |].
      cbn [set_v3A c_v3 t3c snd] in CAP8. clear - CAP8. lia. }
    refine (K I s8 LB8 LBs8 M9 mo9 c8 msF9 R9 _ eq_refl eq_refl eq_refl eq_refl (ex_intro _ b8 (ex_intro _ cap8 eq_refl))).
    unfold OLIA, omeas, iaccA, PmODefsS1.iacc.
    cbn [I PmODefsS1.i_io PmODefsS1.i_fw PmODefsS1.i_iwc PmODefsS1.i_op PmODefsS1.i_d PmODefsS1.i_l].
    subst c8. cbn [set_v3A c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
    rewrite V1, Hwidx.
    split.
    { constructor.
      - exact X9r.
      - exact KR9.
      - exact VIS9.
      - exact RF9.
      - exact FZ0.
      - exact HTx9.
      - rewrite (HR9 3%bv). exact G3_8.
      - rewrite (HR9 4%bv). exact G4_8.
      - exact Htr.
      - exact Hbsz8.
      - exact BUD8.
      - exact IP.
      - exact (u2g_ictx_keep w m M9 [] I IC FK eq_refl).
      - exact (u2g_ifr_keep w m M9 [] FR FK eq_refl).
      - exact Hic.
      - exact Hend.
      - exact Hw.
      - exact MAC.
      - rewrite Exs. apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) LR x (Hin x Hx)). }
    split; [lia|].
    split; [unfold pi_nodes in *; cbn [set_v3A c_m1 c_m2 c_m3] in *; lia|].
    split; [rewrite Z.max_r by lia; lia|].
    split; [lia|].
    split; [rewrite Exs in *; lia|].
    split; [exact (u2g_zw_init l (go_op_zw _ GOK _ l Hg))|].
    split.
    { destruct (Z.eq_dec (fw mod 2 ^ 16) OP_TYPE_INT) as [EI|NI];
        [| destruct (Z.eq_dec (fw mod 2 ^ 16) OP_TYPE_FLOAT) as [EF|NF]; [| exact (nty_other _ _ _ NI NF)]].
      - rewrite EI in Hg |- *. rewrite (go_typeint _ GOK l Hg). apply nty_init_int. lia.
      - rewrite EF in Hg |- *. rewrite (go_typefloat _ GOK l Hg). apply nty_init_float. lia. }
    split.
    { exists 0. split; [lia|]. split; [lia|]. split; [intros; lia|].
      pose proof (ridc_push_types_nil l) as RP1.
      pose proof (ridc_le1_of_count l ((proj1 tg_rid1) _ l Hg)). lia. }
    split; [lia|].
    split.
    { exists 0. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|].
      intros EI. left. split; [reflexivity|]. rewrite EI in Hg. unfold PmHyps.OP_EXT_INST_IMPORT in Hg. rewrite tg_import in Hg.
      injection Hg. intros <-. reflexivity. }
    intros Hgt. right. destruct (tg_gt_rid _ l Hgt Hg) as (r & ->).
    exists (push_types r []). rewrite u2g_push_types_nil_cons. reflexivity.
  Qed.
End U2G.
