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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmVup LbB_PmHdr LbB_TablStmt LbB_PiStmt LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section OLX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Record OBAS (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
              (msF : machine_state) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (I : ictxR)
              (pc : Z) (RT : list (reg * expr)) (ins : list nat) (tbl : list (Z * expr)) (spal : Z) : Prop := MKOBAS {
    obs_x    : PMXAT H LINV w s LB LBs m mo c ins tbl [] [] spal;
    obs_kr   : as_AKREL H s (mkCfg msF mo);
    obs_vis  : as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs);
    obs_rf   : rfull R;
    obs_fz   : frm_zero fc;
    obs_rt   : regs_tbl w R RT;
    obs_gp   : PropExec.getr R 3%bv = wa_gp w;
    obs_tp   : PropExec.getr R 4%bv = wa_tp w;
    obs_tr   : c_tr c = [];
    obs_bsz  : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    obs_bud  : pm_bud (wa_n w) c;
    obs_ip   : ipureA I;
    obs_ictx : ictxA H w m I;
    obs_ifr  : ifrA H w m;
    obs_ic   : c_icount c + 4 <= i_io I;
    obs_end  : c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1);
    obs_w    : wa_words w <> 0 /\ 5 <= wa_n w;
    obs_acc  : pi_macct c;
    obs_v3r  : Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c))
  }.

  Lemma oba_obas : forall w s LB LBs m mo c msF R F fc I pc RT ins tbl,
    OBA H LINV w s LB LBs m mo c msF R F fc I pc RT ins tbl -> OBAS w s LB LBs m mo c msF R F fc I pc RT ins tbl 0.
  Proof. intros w s LB LBs m mo c msF R F fc I pc RT ins tbl []. constructor; assumption. Qed.

  Definition PUSHKAX (w : pmwA H) (I : ictxR) (Q : config -> Prop) (c : pmc) (t : Z) : Prop :=
    forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (nw : Z) (l' : list Z) (spal : Z),
      OBAS w s' LB' LBs' m' mo' c' msF' R' F' fc' I OL_PUSHK RT_PUSHK S_OPER tbl' spal -> 0 <= spal <= PM_STRK * nw ->
      incl TBL_EEF44 tbl' ->
      PropExec.getr R' 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R' 25%bv = Z_to_bv 64 (i_io I) ->
      (exists ty, PropExec.getr R' 18%bv = Z_to_bv 64 ty /\ 0 <= ty < 2 ^ 32) ->
      rw_cells asegs m' (wa_ff w + 114) [C2 (Z_to_bv 64 nw)] -> (1 <= nw < 2 ^ 16 \/ (nw = 0 /\ zw_type t = true /\ l' = [])) ->
      (exists off ty, rw_cells asegs m' (wa_ff w + 112) [C2 (Z_to_bv 64 off)] /\ rw_cells asegs m' (wa_ff w + 116) [C4 (Z_to_bv 64 ty)]) ->
      mdef m' (wa_ff w + 112) 20 ->
      c_widx c' = c_widx c -> c_v1 c' = c_v1 c -> c_v2 c' = c_v2 c -> pi_nodes c' <= pi_nodes c + Z.min nw 1 ->
      t3b (c_v3 c') = t3b (c_v3 c) ++ l' -> seed_free l' -> Zlen l' <= 125 ->
      l' = [] \/ (t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING) ->
      c_m2 c' = c_m2 c ->
      (c_m1 c' = c_m1 c \/ (t = OT_RESULT_ID /\ Zlen (t3c (c_m1 c')) <= Zlen (t3c (c_m1 c)) + 1)) ->
      (c_m3 c' = c_m3 c \/ (t = OT_LITERAL_STRING /\ i_op I = OP_EXT_INST_IMPORT /\ Zlen (t3c (c_m3 c')) <= Zlen (t3c (c_m3 c)) + 1)) ->
      ~ In OT_RESULT_ID l' ->
      as_SR H Q (mkCfg msF' mo').

  Definition arm_stmtAX (t pc : Z) : Prop :=
    forall (w : pmwA H) s LB LBs m mo c msF R F fc (I : ictxR) (tbl : list (Z * expr)) (word : Z) (Q : config -> Prop),
      pmw_okA H w -> AEA H LINV w s LB LBs m mo c msF R F fc I pc tbl t word -> incl TBL_EEF44 tbl ->
      tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
      PUSHKAX w I Q c t -> CHECKKA H LINV w Q -> aacc I c t ->
      as_SR H Q (mkCfg msF mo).

  Definition push_tail_stmtAX : Prop :=
    forall (spal : Z) (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc tbl (t nw : Z) (Q : config -> Prop),
    pmw_okA H w -> OBAS w s LB LBs m mo c msF R F fc I OL_PUSHK RT_PUSHK S_OPER tbl spal -> 0 <= spal <= PM_STRK * nw -> incl TBL_EEF44 tbl ->
    PropExec.getr R 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R 25%bv = Z_to_bv 64 (i_io I) ->
    (exists ty, PropExec.getr R 18%bv = Z_to_bv 64 ty /\ 0 <= ty < 2 ^ 32) ->
    0 <= t < 2 ^ 32 ->
    rw_cells asegs m (wa_ff w + 114) [C2 (Z_to_bv 64 nw)] -> 0 <= nw < 2 ^ 16 -> mdef m (wa_ff w + 112) 20 ->
    i_io I + 1 <= c_widx c -> c_widx c < i_io I + i_iwc I -> Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    (t3b (c_v1 c) = t3c (c_v1 c) -> 40 * t3c (c_v1 c) + 20 <= 2 ^ 23) ->
    CHECKKA H LINV w Q ->
    (forall s' LB' LBs' m' mo' msF' R' F' fc' (b1 cap1 : Z) (v2 : Z * list Z * Z),
       OBA H LINV w s' LB' LBs' m' mo' (set_scalA (set_v2A (set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c))
           msF' R' F' fc' I OL_HEAD RT_EEF44 S_INSTR TBL_EEF44 ->
       Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw -> c_widx c + nw <= wa_n w ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).

  Lemma pushka_of_x : forall w I Q c t, PUSHKAX w I Q c t -> PUSHKA H LINV w I Q c t.
  Proof.
    intros w I Q c t PX s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' nw l' OB IT G22 G25 G18 NW Hnw OT MD Ew E1 E2 EN E3 SF L125 LT Em2 Em1 Em3 NR.
    apply (PX s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' nw l' 0 (oba_obas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OB)); try assumption.
    unfold PM_STRK. destruct Hnw as [Hnw|(Hnw & _)]; lia.
  Qed.

  Lemma arm_AX_of_A : forall t pc, arm_stmtA H LINV t pc -> arm_stmtAX t pc.
  Proof.
    intros t pc ARM w s LB LBs m mo c msF R F fc I tbl word Q OK HAE IT TC TK TN PX CK AACC.
    exact (ARM w s LB LBs m mo c msF R F fc I tbl word Q OK HAE IT TC TK TN (pushka_of_x w I Q c t PX) CK AACC).
  Qed.
End OLX.
