(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase PmHyps PrsGrammar PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar TablFacts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmXp LbA_PmExit LbA_PmInit LbA_PmFin LbA_PmExit2 LbA_DiagStmt LbA_PmDS LbA_PmGlue.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_RtOwn LbA_DStat LbA_TablStmt LbA_ContStmt LbA_PmLeaf LbA_PmLeafW LbA_PmLH LbA_PmVops LbA_PmVup LbA_PmU2K LbA_PmU2D LbA_PmOL LbA_PmWG LbA_PmWPT.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PmOLX LbA_PmOHD LbA_PmU2 LbA_PmOH.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma pb_bfilter_app : forall (P : Z -> Prop) (H : forall x, base.Decision (P x)) (a b : list Z),
  base.filter P (a ++ b) = base.filter P a ++ base.filter P b.
Proof.
  intros P H a b. induction a as [|x a IH]; [rewrite bfilter_nil; reflexivity|]. cbn [app]. rewrite !bfilter_cons, IH.
  destruct (base.decide (P x)); reflexivity.
Qed.
Lemma pb_push_types_nil_cons : forall z r, push_types (z :: r) [] = push_types r [] ++ (if negb (z =? OT_NONE) then [z] else []).
Proof.
  intros z r. unfold push_types. cbn [app rev]. rewrite pb_bfilter_app, bfilter_cons, bfilter_nil.
  destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
    exfalso; [exact Hd | apply Hd; exact Logic.I].
Qed.
Lemma pb_push_types_nil_snoc : forall r z, push_types (r ++ [z]) [] = (if negb (z =? OT_NONE) then [z] else []) ++ push_types r [].
Proof.
  intros r z. unfold push_types. cbn [app]. rewrite rev_app_distr. cbn [rev app]. rewrite bfilter_cons.
  destruct (base.decide (Is_true (negb (z =? OT_NONE)))) as [Hd|Hd]; destruct (negb (z =? OT_NONE)) eqn:E; try reflexivity;
    exfalso; [exact Hd | apply Hd; exact Logic.I].
Qed.

Lemma pb_zw_init : forall l, op_list_ok l -> zw_stack_ok (push_types l []).
Proof.
  intros l [SF H47]. destruct l as [|z r _] using rev_ind.
  - change (push_types [] []) with (@nil Z ++ @nil Z). apply zw_stack_ok_intro; [exact seed_free_nil | left; reflexivity].
  - rewrite removelast_last in SF. rewrite pb_push_types_nil_snoc.
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

Section BODY.
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
  Hypothesis TFS : take_first_stmtA H.

  Hypothesis ARMS : forall t, arm_stmtAX H LINV t (arm_pcA t).

  Hypothesis TAIL : push_tail_stmtAX H LINV.
  Hypothesis CHK : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      (F0 : bvmap 5 word) (fc0 : bv 32),
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w -> CHECKKA H LINV w (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 st0 LB0 LF p c0 lo B shi m0 mo0).

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Section W.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
            (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
            (F0 : bvmap 5 word) (fc0 : bv 32).
  Let w : pmwA H := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi.
  Let QP : config -> Prop := pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 st0 LB0 LF p c0 lo B shi m0 mo0.

  Hypothesis IHEAD : forall s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> LIA H LINV w s LB LBs m mo c msF R F fc -> c_widx c < wa_n w ->
    U2DZK H LINV w F fc Q -> U2LZK H LINV w F fc Q -> U2HK H LINV w c F fc Q -> as_SR H Q (mkCfg msF mo).
  Hypothesis XDZ : forall s LB LBs m mo c msF R F fc,
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [61; 62; 63; 86]%nat TBL_EE8CC FTBL_EE8E8 -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xeea78) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EE8CC -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    rw_cells asegs m (wa_ff w + 10512) [C2 (Z_to_bv 64 0)] ->
    as_SR H QP (mkCfg msF mo).
  Hypothesis XLZ : forall s LB LBs m mo c msF R F fc (rr op : Z),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [61; 62; 63; 65; 86]%nat TBL_EE8CC FTBL_EE8E8 -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xeea94) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EE8CC -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    PropExec.getr R 10%bv = Z_to_bv 64 rr -> - 2 ^ 31 <= rr < 2 ^ 31 -> rr <> 0 -> 0 <= op < 2 ^ 16 ->
    rw_cells asegs m (wa_ff w + 10426) [C2 (Z_to_bv 64 op)] -> rw_cells asegs m (wa_ff w + 10992) [C8 (Z_to_bv 64 0)] ->
    as_SR H QP (mkCfg msF mo).

  Hypothesis EXIT : forall (I : ictxR) s LB LBs m mo c msF R F fc,
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> i_io I + i_iwc I <= c_widx c ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc',
       LIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' -> i_io I + 1 <= c_widx c' -> as_SR H QP (mkCfg msF' mo')) ->
    as_SR H QP (mkCfg msF mo).

  Hypothesis OHX : forall s LB LBs m mo c msF R F fc (io iwc op t : Z),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef140) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EEFB0 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    PropExec.getr R 10%bv = Z_to_bv 64 t -> 0 <= t < 2 ^ 31 -> 0 <= io <= c_widx c -> 0 <= iwc < 2 ^ 16 -> c_widx c < io + iwc -> 0 <= op < 2 ^ 16 ->
    wa_n w <= c_widx c ->
    rw_cells asegs m (wa_ff w + 11488) [C8 (Z_to_bv 64 io)] -> rw_cells asegs m (wa_ff w + 10426) [C2 (Z_to_bv 64 op)] ->
    as_SR H QP (mkCfg msF mo).

  Hypothesis OHZ : forall (I : ictxR) s LB LBs m mo c msF R F fc,
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) = [] ->
    as_SR H QP (mkCfg msF mo).

  Lemma pm_oloopA : forall (I : ictxR), pmw_okA H w -> ipureA I ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc',
       LIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' -> i_io I + 1 <= c_widx c' -> as_SR H QP (mkCfg msF' mo')) ->
    forall s LB LBs m mo c msF R F fc, OLIA H LINV w s LB LBs m mo c msF R F fc I -> as_SR H QP (mkCfg msF mo).
  Proof.
    intros I OK IP BK.
    assert (IND : forall k s LB LBs m mo c msF R F fc, Z.to_nat (omeas I c) = k ->
                    OLIA H LINV w s LB LBs m mo c msF R F fc I -> as_SR H QP (mkCfg msF mo)).
    { intros k. induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
      intros s LB LBs m mo c msF R F fc Hk HOLI.
      assert (Hm0 : 0 <= omeas I c) by (unfold omeas; pose proof (zw_next_range (t3b (c_v3 c))); lia).
      destruct (Z.lt_ge_cases (c_widx c) (i_io I + i_iwc I)) as [Hlt|Hge].
      - eapply (pm_oheadA H HHbp LINV LINV_frame LINV_cl LINV_relro HOWN HTL TFS ARMS TAIL CHK
                  ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi F0 fc0
                  I s LB LBs m mo c msF R F fc OK IP HOLI Hlt).
        +
          intros s' LB' LBs' m' mo' c' msF' R' io iwc op t X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' HT10 Ht Hio Hiwc HLT2 Hop HGE BUD' CIO COP.
          exact (OHX s' LB' LBs' m' mo' c' msF' R' F fc io iwc op t OK X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' HT10 Ht Hio Hiwc HLT2 Hop HGE CIO COP).
        +
          intros s' LB' LBs' m' mo' c' msF' R' F' fc' HOLI' Hlt' Hnil. exact (OHZ I s' LB' LBs' m' mo' c' msF' R' F' fc' OK HOLI' Hlt' Hnil).
        +
          intros s' LB' LBs' m' mo' c' msF' R' F' fc' HOLI' HM.
          assert (Hm0' : 0 <= omeas I c') by (unfold omeas; pose proof (zw_next_range (t3b (c_v3 c'))); lia).
          eapply (IH (Z.to_nat (omeas I c'))); [lia | reflexivity | exact HOLI'].
      - exact (EXIT I s LB LBs m mo c msF R F fc OK HOLI Hge BK). }
    intros s LB LBs m mo c msF R F fc HOLI. exact (IND _ s LB LBs m mo c msF R F fc eq_refl HOLI).
  Qed.

  Lemma pm_bodyA : pmw_okA H w -> body_stmtA H LINV w QP.
  Proof.
    intros OK s LB LBs m mo c msF R F fc HL HLT BK.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (wk_n H w OK) as WN. pose proof (pmw_bounds H w OK) as BND.
    pose proof HL as HL'. destruct HL' as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz Hic Hend Hw Hbud (ACC & MACC & LACC)].
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    eapply (IHEAD s LB LBs m mo c msF R F fc QP OK HL HLT).
    -
      intros s' LB' LBs' m' mo' c' msF' R' fw X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' Rfw IWZ CWC COP.
      rewrite IWZ in CWC. exact (XDZ s' LB' LBs' m' mo' c' msF' R' F fc OK X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' CWC).
    -
      intros s' LB' LBs' m' mo' c' msF' R' fw r X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' G10 Rr Hr Rfw COP CD.
      exact (XLZ s' LB' LBs' m' mo' c' msF' R' F fc r (fw mod 2 ^ 16) OK X' Htr' Hbsz' KR' VIS' RF' FZ' HT' G3' G4' G10 Rr Hr
               ltac:(pose proof (Z.mod_pos_bound fw (2 ^ 16) ltac:(lia)); lia) COP CD).
    -
      intros s' LB' LBs' m' mo' c' msF' R' fw d l X' KR' VIS' RF' HT' G3' G4' Htr' Hbsz' Hbud' Ew Eic Een Erc Em1 Em2 Em3 Ev1 [b2 [cap2 Ev2]] [b3 [cap3 Ev3]]
             Rfw Hnz Hdesc Hg Cio Cfw Ciwc Cop Cd Cz24 Cz28.
      set (I := PmODefsS1.ICTX (c_widx c) fw (fw / 2 ^ 16) (fw mod 2 ^ 16) d l).
      assert (IP : ipureA I).
      { unfold ipureA, PmODefsS1.ipure. cbn [I PmODefsS1.i_io PmODefsS1.i_fw PmODefsS1.i_iwc PmODefsS1.i_op PmODefsS1.i_d PmODefsS1.i_l].
        split; [reflexivity|]. split; [reflexivity|]. split; [exact Hnz|]. split; [exact Rfw|]. split; [exact Hg|]. split; [exact Hdesc | lia]. }
      pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop].
      cbn [I PmODefsS1.i_iwc PmODefsS1.i_op] in Riwc, Rop.
      pose proof (go_op_zw TG TG_ok _ l Hg) as OLOK.
      pose proof (go_len_op TG TG_ok _ l Hg) as Hll. unfold HRep.Zlength in Hll. change (Zlen l <= g_maxlen TG) in Hll.
      pose proof tg_maxlen as Hml.
      assert (Hrange : Forall (fun x => 0 <= x < 2 ^ 31) l).
      { apply Forall_forall. intros x Hx. eapply (go_range TG TG_ok l x); [left; exists (fw mod 2 ^ 16); exact Hg | exact Hx]. }
      destruct (push_types_split l []) as (xs & Exs & Hxl & Hin). cbn [app] in Exs.
      assert (FRxs : Forall (fun x => 0 <= x < 2 ^ 31) xs).
      { apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) Hrange x (Hin x Hx)). }
      pose proof (Zlen_nonneg xs) as Hxs0. pose proof (zw_next_range xs) as Hzn.

      pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X'
                    (tbl_incl TBL_EEF44 TBL_EEE9C ltac:(vm_compute; reflexivity)) (fun x (Hx : In x []) => False_ind _ Hx)) as XH.
      assert (HTH : regs_tbl w R' RT_EEF44) by (apply (regs_tbl_sub w [] R' RT_EEED4 RT_EEF44 HT'); vm_compute; reflexivity).

      pose proof (xa_fslots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X') as FS. unfold fslots_ok, FTBL_EE8E8 in FS.
      pose proof (Forall_inv FS) as Z16. pose proof (Forall_inv (Forall_inv_tail FS)) as Z32.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail FS))) as Z40. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FS)))) as Z48.
      cbn [fst snd edenot] in Z16, Z32, Z40, Z48. clear FS.
      destruct (proj1 (rw_cells_appA m' (wa_ff w + 10432) [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)]) (rw_cells_zero_split44 m' _ Z32)) as [Z32a Z36].
      match type of Z36 with rw_cells _ _ ?a _ => replace a with (wa_ff w + 10436) in Z36 by (cbn; lia) end.
      apply (pm_oloopA I OK IP
               (fun s'' LB'' LBs'' m'' mo'' c'' msF'' R'' F'' fc'' HL'' Hp => BK s'' LB'' LBs'' m'' mo'' c'' msF'' R'' F'' fc'' HL'' ltac:(cbn [I PmODefsS1.i_io] in Hp; lia))
               s' LB' LBs' m' mo' c' msF' R' F fc).

      unfold I in *. clear I.
      unfold OLIA, omeas, iaccA, PmODefsS1.iacc, nodesA, macctA, laccA in *.
      cbn [PmODefsS1.i_io PmODefsS1.i_fw PmODefsS1.i_iwc PmODefsS1.i_op PmODefsS1.i_d PmODefsS1.i_l] in *.
      rewrite ?Ew, ?Eic, ?Een, ?Erc, ?Ev1, ?Ev2, ?Ev3, ?Em1, ?Em2, ?Em3 in *. cbn [t3a t3b t3c fst snd] in *. rewrite ?Exs in *.
      split.
      { split; [exact XH | exact KR' | exact VIS' | exact RF' | exact FZ0 | exact HTH | exact G3' | exact G4' | exact Htr' | exact Hbsz' | exact Hbud' | exact IP
               | | | cbn [PmODefsS1.i_io]; rewrite Eic; lia | rewrite Een, Erc; exact Hend | exact Hw | unfold macctA; rewrite Em1, Em2, Em3; exact MACC | rewrite Ev3; cbn [t3b fst snd]; rewrite ?Exs; exact FRxs].
        -   unfold ictxA. cbn [PmODefsS1.i_io PmODefsS1.i_fw PmODefsS1.i_iwc PmODefsS1.i_op PmODefsS1.i_d].
          split; [exact Cio|]. split; [exact Cfw|]. split; [exact Ciwc|]. split; [exact Cop | exact Cd].
        -   exists 0, 0, 0. split; [exact Z16|]. split; [exact Cz24|]. split; [exact Cz28|]. split; [exact Z32a|]. split; [exact Z36|].
          split; [exact Z40|]. split; [exact Z48|]. lia. }
      rewrite ?Ew, ?Ev1, ?Ev2, ?Ev3, ?Em1, ?Em2, ?Em3. cbn [t3a t3b t3c fst snd].
      split; [lia|]. split; [lia|].
      split. { change (Zlen [fw]) with 1 in *. replace (c_widx c + fw / 2 ^ 16 - (c_widx c + 1)) with (fw / 2 ^ 16 - 1) by lia. rewrite Z.max_r by lia. lia. }
      split. { change (Zlen [fw]) with 1. lia. }
      split; [lia|].
      split; [rewrite <- Exs; exact (pb_zw_init l OLOK)|].
      split.
      {   destruct (Z.eq_dec (fw mod 2 ^ 16) OP_TYPE_INT) as [EI|NI]; [| destruct (Z.eq_dec (fw mod 2 ^ 16) OP_TYPE_FLOAT) as [EF|NF]; [| exact (nty_other _ xs _ NI NF)]].
        - rewrite EI in Hg |- *. rewrite (go_typeint TG TG_ok l Hg) in Exs. rewrite <- Exs. apply nty_init_int. lia.
        - rewrite EF in Hg |- *. rewrite (go_typefloat TG TG_ok l Hg) in Exs. rewrite <- Exs. apply nty_init_float. lia. }

      destruct LACC as (L1 & L2 & L3).
      split.
      { exists 0. split; [lia|]. split; [lia|]. split; [intros; lia|].
        pose proof (ridc_push_types_nil l) as RP1. rewrite Exs in RP1.
        pose proof (ridc_le1_of_count l ((proj1 tg_rid1) _ l Hg)). lia. }
      split; [lia|].
      split.
      { exists 0. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|].
        intros EI. left. split; [reflexivity|]. rewrite EI in Hg. unfold PmHyps.OP_EXT_INST_IMPORT in Hg. rewrite tg_import in Hg.
        injection Hg. intros <-. rewrite <- Exs. reflexivity. }
      intros Hgt. right. destruct (tg_gt_rid _ l Hgt Hg) as (r & ->).
      exists (push_types r []). rewrite <- Exs, pb_push_types_nil_cons. reflexivity.
  Qed.
  End W.
End BODY.
