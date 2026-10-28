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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmLeaf LbB_PmLeafW LbB_PmVops LbB_PmU2K LbB_PmOL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmU2C.

Definition RT_F0FB0 : list (reg * expr) :=
  [(2%bv, EVar WV_S1);
   (8%bv, EVar WV_SP0);
   (9%bv, EVar WV_S1);
   (10%bv, ELit 0);
   (11%bv, EAlu ALU_ADD (EVar WV_S1) (ELit 720));
   (12%bv, ELit 0);
   (13%bv, ELit SHBASE);
   (18%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (19%bv, EVar WV_P);
   (20%bv, SH_FF);
   (21%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9050));
   (22%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 10112));
   (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 224)) (ELit 3)) (ELit SHBASE));
   (24%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (25%bv, ELit SHBASE);
   (26%bv, EAlu ALU_ADD (EVar WV_P) (ELit 216));
   (27%bv, EVar WV_FF)].
Definition TBL_F0FB0 : list (Z * expr) :=
  [(400, EAlu ALU_ADD (EVar WV_FF) (ELit 9616));
   (408, EAlu ALU_ADD (EVar WV_P) (ELit 216));
   (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 216)) (ELit 3)) (ELit SHBASE));
   (432, EAlu ALU_ADD (EVar WV_P) (ELit 232));
   (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 232)) (ELit 3)) (ELit SHBASE));
   (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 240)) (ELit 3)) (ELit SHBASE));
   (512, EAlu ALU_ADD (EVar WV_P) (ELit 88));
   (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 88)) (ELit 3)) (ELit SHBASE));
   (528, EAlu ALU_ADD (EVar WV_P) (ELit 48));
   (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 48)) (ELit 3)) (ELit SHBASE));
   (544, ELit (2 ^ 61));
   (560, EAlu ALU_ADD (EVar WV_P) (ELit 240));
   (568, EVar WV_FF);
   (576, EVar WV_FF);
   (608, EAlu ALU_ADD (EVar WV_FF) (ELit 9050));
   (624, EAlu ALU_ADD (EVar WV_FF) (ELit 9040));
   (640, EAlu ALU_ADD (EVar WV_FF) (ELit 9136));
   (648, EVar WV_P);
   (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 72)) (ELit 3)) (ELit SHBASE));
   (664, EAlu ALU_ADD (EVar WV_P) (ELit 72));
   (680, EVar WV_FF);
   (448, EAlu ALU_ADD (EVar WV_P) (ELit 224));
   (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar WV_P) (ELit 224)) (ELit 3)) (ELit SHBASE));
   (688, EAlu ALU_ADD (EVar WV_FF) (ELit 10112));
   (696, EAlu ALU_ADD (EVar WV_FF) (ELit 9136));
   (704, EVar WV_P);
   (712, EAlu ALU_ADD (EVar WV_FF) (ELit 9120));
   (720, EAlu ALU_ADD (EVar WV_FF) (ELit 9040))].

Definition c_F0FB0 (c : pmc) : pmc := set_scalA c (c_widx c + 1) (c_icount c) (c_endian c) (c_reqconv c).

Fixpoint nb_out_u2e (bs : list (expr * Z * Z)) (se : sentry) : bool :=
  match bs with
  | [] => false
  | (b, lo, hi) :: bs' => (expr_eqb (a_base (e_addr se)) b && (lo <=? a_off (e_addr se))
                           && (a_off (e_addr se) + Z.of_nat (e_width se) <=? hi)) || nb_out_u2e bs' se
  end.

Lemma rw_cells_log_nth_u2e : forall E M lg (k : nat) (a : saddr) (w : nat) (v : expr) (A : Z) (c : cell) bs,
  log_flat E lg -> nth_error lg k = Some (SE a w v) ->
  forallb (nb_out_u2e bs) (firstn k lg) = true ->
  Forall (fun t : expr * Z * Z => A + Z.of_nat w <= bv_unsigned (edenot E (fst (fst t))) + snd (fst t)
                                  \/ bv_unsigned (edenot E (fst (fst t))) + snd t <= A) bs ->
  estart E a = A -> wr_at asegs M A (Z.of_nat w) ->
  csize c = w -> cell_wf c -> cbytes c = word_to_le_bytes w (edenot E v) ->
  rw_cells asegs (mem_denot E M lg) A [c].
Proof.
  intros E M lg k a w v A c bs Hf Hn Hd HD Hs HW Hc Hwf Hb.
  eapply (rw_cells_log_nth E M lg k a w v A c Hf Hn); [| exact Hs | exact HW | exact Hc | exact Hwf | exact Hb].
  apply Forall_forall. intros e' He'. cbv beta. rewrite forallb_forall in Hd. specialize (Hd e' He'). rewrite Hs.
  revert HD Hd. induction bs as [|[[b lo] hi] bs IH]; intros HD Hd; cbn [nb_out_u2e] in Hd; [discriminate|].
  apply Forall_cons_iff in HD as [HD1 HD2]. cbn [fst snd] in HD1.
  apply orb_true_iff in Hd. destruct Hd as [Hd|Hd].
  - apply andb_true_iff in Hd as [Hd H2]. apply andb_true_iff in Hd as [Hbe H1]. apply expr_eqb_true in Hbe.
    apply Z.leb_le in H1, H2. unfold estart. rewrite Hbe. lia.
  - exact (IH HD2 Hd).
Qed.

Section U2E.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Record HS_F0FB0 (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
              (msF : machine_state) (R F : bvmap 5 word) (fc : bv 32) (fw d : Z) (l : list Z) : Prop := MKHS_F0FB0 {
    hb0_x   : PMXA H LINV w s LB LBs m mo (c_F0FB0 c) S_INSTR TBL_F0FB0 [];
    hb0_tr  : c_tr (c_F0FB0 c) = [];
    hb0_bsz : forall q k, In (q, k) (c_blocks (c_F0FB0 c)) -> k <= 2 ^ 40;
    hb0_bud : pm_bud (wa_n w) (c_F0FB0 c);
    hb0_v1  : t3b (c_v1 (c_F0FB0 c)) = 0;
    hb0_kr  : as_AKREL H s (mkCfg msF mo);
    hb0_vis : as_VIS H s msF = MS R F (Z_to_bv 64 0xf0fb0) fc None m (seg_rom asegs);
    hb0_rf  : rfull R;
    hb0_fz  : frm_zero fc;
    hb0_rt  : regs_tbl w R RT_F0FB0;
    hb0_gp  : PropExec.getr R 3%bv = wa_gp w;
    hb0_tp  : PropExec.getr R 4%bv = wa_tp w;
    hb0_wlt : c_widx c < wa_n w;
    hb0_io  : rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 (c_widx c))];
    hb0_fwr : 0 <= fw < 2 ^ 32;
    hb0_wc0 : fw / 2 ^ 16 <> 0;
    hb0_fw  : rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 fw)];
    hb0_wc  : rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 (fw / 2 ^ 16))];
    hb0_op  : rw_cells asegs m (wa_ff w + 9050) [C2 (Z_to_bv 64 (fw mod 2 ^ 16))];
    hb0_d   : rw_cells asegs m (wa_ff w + 9616) [C8 (Z_to_bv 64 d)];
    hb0_id  : idescA d (fw mod 2 ^ 16);
    hb0_g   : g_op TG (fw mod 2 ^ 16) = Some l
  }.

  Lemma pm_u2e : forall (w : pmwA H) s LB LBs m mo c msF R F fc (fw r : Z) (Q : config -> Prop),
    pmw_okA H w -> HS_F0A6C H LINV w s LB LBs m mo c msF R F fc fw r -> r = 0 -> c_widx c < wa_n w ->
    (forall msF1 mo1 m1 R1 (d : Z) (l : list Z), HS_F0FB0 w s LB LBs m1 mo1 c msF1 R1 F fc fw d l ->
       ffkeepX w [(10112, 8)] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc fw r Q OK HS Hr0 Hlt K.
    destruct HS as [X0 Htr Hbsz Hbud Hv1 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Hfw Hwc CF CW CO Ga0 Hr Hfnd Hd Hd0].
    subst r.
    destruct (proj1 Hfnd eq_refl) as [l Hl].
    destruct (Hd eq_refl) as (d & CD & Hid).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    pose proof (pmw_apart_ff H HHm LINV w _ _ _ _ _ _ _ _ _ _ _ OK X0) as (PA & _ & _).
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (FW0 & FW1 & FW2). change (fsz PM_FCLASS) with 16384 in FW2.
    assert (HTa : regs_tbl w R (RT_F0A6C ++ [(10%bv, ELit 0)])).
    { apply regs_tbl_app; [exact HT0|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. rewrite Ga0. reflexivity. }
    pm_goS HHm LINV_frame OK X0 KR0 VIS0 RF0 HTa [Z_to_bv 64 (c_widx c)]
           [KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 41)] 300%nat [0xf0fb0] (@nil bool) 42%N
           S_INSTR [448; 464; 688; 696; 704; 712; 720] (@nil Z) TBL_F0FB0 (@nil (Z * expr)) RT_F0FB0 (c_F0FB0 c).
    - first [split_scs | exact I | apply Forall_nil | constructor].
    - unfold scal_after, sval. lfield_rw. cbn beta iota.
      rewrite (ev_add _ 41%N (c_widx c) 1) by first [ev_xs; reflexivity | lia].
      rewrite u64_of_Z by lia. reflexivity.
    - unfold c_F0FB0, set_scalA; cbn [c_widx]; lia.
    - unfold c_F0FB0, set_scalA; cbn [c_widx c_icount]; lia.
    - unfold c_F0FB0, set_scalA; cbn [c_endian]; lia.
    - unfold c_F0FB0, set_scalA; cbn [c_reqconv]; lia.
    - intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      set (E1 := Eseed R (wenv_vals w ++ [Z_to_bv 64 (c_widx c)])) in *.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
      lazymatch type of VIS1 with context [Z_to_bv 64 (s_pc ?ss)] => replace (s_pc ss) with 0xf0fb0 in VIS1 by reflexivity end.
      pose proof (regs_tbl_restrict w [] _ R1 RT_F0FB0 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
      pose proof (env_world_seed H w R [Z_to_bv 64 (c_widx c)]) as HE1.
      pose proof (ev_world_all H w E1 HE1) as (_ & EV33 & _).
      pose proof (ev_ff H w E1 OK HE1) as U33.
      pose proof (ev_s1 H w E1 OK HE1) as US1.
      pose proof (ev_p H w E1 OK HE1) as UP.
      assert (UFS : bv_unsigned (edenot E1 FSHB) = wa_ff w / 8) by (unfold FSHB; apply srl3_val; [exact EV33 | lia]).
      assert (FK : ffkeepX w [(10112, 8)] m M1).
      { pose proof (munch_sym E1 m (s_log SSr)
                      [(EVar WV_S1, 0, 832); (EVar WV_P, 72, 80); (EVar WV_FF, 10112, 10120); (FSHB, SHBASE, SHBASE + PM_NSH)]
                      Hlf1 ltac:(vm_compute; reflexivity)) as MU.
        cbn [num_wins map] in MU. rewrite US1, UP, U33, UFS in MU.
        apply (ffkeepX_munch w _ _ _ _ MU (wmono_mem_denot _ _ _)).
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]; cbn [fst snd].
        - left. lia.
        - unfold PARSER_SIZE in PA. destruct PA as [D|D]; [right; left | left]; lia.
        - right; right. apply Exists_cons_hd. cbn [fst snd]. lia.
        - unfold PM_NSH. destruct Q6 as [D|D]; [left | right; left]; lia. }
      assert (CIO : rw_cells asegs M1 (wa_ff w + 10112) [C8 (Z_to_bv 64 (c_widx c))]).
      { subst M1. eapply (rw_cells_log_nth_u2e E1 m _ 5%nat (SA (EVar 33%N) 10112) 8 (EVar 41) _ _
                            [(EVar WV_S1, 0, 832); (EVar WV_P, 72, 80)]).
        - exact Hlf1.
        - reflexivity.
        - vm_compute; reflexivity.
        - apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
          + rewrite US1. left. lia.
          + rewrite UP. unfold PARSER_SIZE in PA. destruct PA as [D|D]; [right | left]; lia.
        - unfold estart. cbn [a_base a_off]. change (EVar 33%N) with (EVar WV_FF). rewrite U33. reflexivity.
        - split; [lia|]. split; [lia|]. intros i Hi.
          replace (wa_ff w + 10112 + i) with (wa_ff w + (10112 + i)) by lia. apply FW2. lia.
        - reflexivity.
        - exact Logic.I.
        - cbn [cbytes]. ev_xs. reflexivity. }
      assert (CF1 : rw_cells asegs M1 (wa_ff w + 9120) [C4 (Z_to_bv 64 fw)]).
      { apply (FK 9120 _); [lia | cbn; lia | | exact CF].
        apply Forall_cons; [| apply Forall_nil]; cbn [fst snd cells_size csize]; lia. }
      assert (CW1 : rw_cells asegs M1 (wa_ff w + 9136) [C2 (Z_to_bv 64 (fw / 2 ^ 16))]).
      { apply (FK 9136 _); [lia | cbn; lia | | exact CW].
        apply Forall_cons; [| apply Forall_nil]; cbn [fst snd cells_size csize]; lia. }
      assert (CO1 : rw_cells asegs M1 (wa_ff w + 9050) [C2 (Z_to_bv 64 (fw mod 2 ^ 16))]).
      { apply (FK 9050 _); [lia | cbn; lia | | exact CO].
        apply Forall_cons; [| apply Forall_nil]; cbn [fst snd cells_size csize]; lia. }
      assert (CD1 : rw_cells asegs M1 (wa_ff w + 9616) [C8 (Z_to_bv 64 d)]).
      { apply (FK 9616 _); [lia | cbn; lia | | exact CD].
        apply Forall_cons; [| apply Forall_nil]; cbn [fst snd cells_size csize]; lia. }
      apply (K msF1 mo1 M1 R1 d l); [constructor | exact FK].
      + exact X1.
      + exact Htr.
      + unfold c_F0FB0. rewrite c_blocks_scal. exact Hbsz.
      + unfold c_F0FB0. apply pm_bud_scal. exact Hbud.
      + exact Hv1.
      + exact KR1.
      + exact VIS1.
      + exact RF1.
      + exact FZ0.
      + exact HT1.
      + rewrite (HR1 3%bv). exact G3_0.
      + rewrite (HR1 4%bv). exact G4_0.
      + exact Hlt.
      + exact CIO.
      + exact Hfw.
      + exact Hwc.
      + exact CF1.
      + exact CW1.
      + exact CO1.
      + exact CD1.
      + exact Hid.
      + exact Hl.
  Qed.
End U2E.
