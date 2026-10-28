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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmHdr LbB_TablStmt LbB_PiStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition ipureA (I : ictxR) : Prop := @PmODefsS1.ipure TG idescA I.
Definition iaccA (I : ictxR) (c : pmc) : Prop := @PmODefsS1.iacc tg_generates_type I c.

Definition RT_OL : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (19%bv, WADD WV_FF 7984); (20%bv, SH_FF);
   (26%bv, WADD WV_FF 112); (27%bv, ELit 18446744073709551608)].

Definition RT_EEF44 : list (reg * expr) := RT_OL ++ [(21%bv, WADD WV_FF 9136); (22%bv, WADD WV_FF 10112); (25%bv, WADD WV_P 264)].

Definition RT_ARM : list (reg * expr) := RT_OL ++ [(23%bv, EVar WV_P); (24%bv, WADD WV_FF 7984)].

Definition RT_OLJ : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF); (27%bv, ELit 18446744073709551608)].
Definition RT_PUSHK : list (reg * expr) := RT_OLJ ++ [(24%bv, WADD WV_FF 7984); (26%bv, WADD WV_FF 112)].
Definition RT_CHECK : list (reg * expr) := RT_OLJ ++ [(24%bv, WADD WV_FF 7984); (26%bv, WADD WV_FF 112)].

Definition TBL_EEF44 : list (Z * expr) :=
  [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].

Definition OL_PUSHK : Z := 0xf18c8.
Definition OL_CHECK : Z := 0xf12dc.
Definition OL_HEAD : Z := 0xf12fc.

Definition PI0_PC : Z := 0xf06bc.
Definition RT_PI0 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (16%bv, EVar WV_FF); (18%bv, EVar WV_FF);
   (19%bv, EAlu ALU_ADD (EVar WV_FF) (ELit 9040)); (20%bv, SH_FF); (23%bv, EVar WV_P); (25%bv, ELit SHBASE)].
Definition TBL_PI0 : list (Z * expr) := [(576, EVar WV_FF); (680, EVar WV_FF)].
Definition EXIT_RET : Z := 0xf0b4c.
Definition EXIT_OPC : Z := 0xf0f10.
Definition EXIT_IWC : Z := 0xf0f1c.
Definition TBL_EXIT : list (Z * expr) := [(568, EVar WV_FF); (576, EVar WV_FF)].
Definition RT_EXIT : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF); (27%bv, EVar WV_FF)].

Section OL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Definition ictxA (w : pmwA H) (m : mem) (I : ictxR) : Prop :=
    rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 (i_io I))]
    /\ rw_cells asegs m (wa_ff w + 9120) [C4 (Z_to_bv 64 (i_fw I))]
    /\ rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 (i_iwc I))]
    /\ rw_cells asegs m (wa_ff w + 9050) [C2 (Z_to_bv 64 (i_op I))]
    /\ rw_cells asegs m (wa_ff w + 9616) [C8 (Z_to_bv 64 (i_d I))].

  Definition ifrA (w : pmwA H) (m : mem) : Prop :=
    exists ext tid rid,
      rw_cells asegs m (wa_ff w + 9040) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m (wa_ff w + 9048) [C2 (Z_to_bv 64 0)]
      /\ rw_cells asegs m (wa_ff w + 9052) [C4 (Z_to_bv 64 ext)] /\ rw_cells asegs m (wa_ff w + 9056) [C4 (Z_to_bv 64 tid)]
      /\ rw_cells asegs m (wa_ff w + 9060) [C4 (Z_to_bv 64 rid)]
      /\ rw_cells asegs m (wa_ff w + 9064) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m (wa_ff w + 9072) [C8 (Z_to_bv 64 0)]
      /\ 0 <= ext < 2 ^ 31 /\ 0 <= tid < 2 ^ 32 /\ 0 <= rid < 2 ^ 32.

  Definition popndA (w : pmwA H) (m : mem) (off t : Z) : Prop :=
    rw_cells asegs m (wa_ff w + 112) [C2 (Z_to_bv 64 off)] /\ rw_cells asegs m (wa_ff w + 114) [C2 (Z_to_bv 64 1)]
    /\ rw_cells asegs m (wa_ff w + 116) [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m (wa_ff w + 120) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m (wa_ff w + 124) [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m (wa_ff w + 128) [C4 (Z_to_bv 64 0)].

  Record OBA (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
             (msF : machine_state) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (I : ictxR)
             (pc : Z) (RT : list (reg * expr)) (ins : list nat) (tbl : list (Z * expr)) : Prop := MKOBA {
    ob_x    : PMXA H LINV w s LB LBs m mo c ins tbl [];
    ob_kr   : as_AKREL H s (mkCfg msF mo);
    ob_vis  : as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs);
    ob_rf   : rfull R;
    ob_fz   : frm_zero fc;
    ob_rt   : regs_tbl w R RT;
    ob_gp   : PropExec.getr R 3%bv = wa_gp w;
    ob_tp   : PropExec.getr R 4%bv = wa_tp w;
    ob_tr   : c_tr c = [];
    ob_bsz  : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    ob_bud  : pm_bud (wa_n w) c;
    ob_ip   : ipureA I;
    ob_ictx : ictxA w m I;
    ob_ifr  : ifrA w m;
    ob_ic   : c_icount c + 4 <= i_io I;
    ob_end  : c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1);
    ob_w    : wa_words w <> 0 /\ 5 <= wa_n w;
    ob_acc  : pi_macct c;
    ob_v3r  : Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c))
  }.

  Definition OLIA (w : pmwA H) s LB LBs m mo c msF R F fc (I : ictxR) : Prop :=
    OBA w s LB LBs m mo c msF R F fc I OL_HEAD RT_EEF44 S_INSTR TBL_EEF44
    /\ i_io I + 1 <= c_widx c
    /\ pi_nodes c + 2 <= c_widx c + 3
    /\ t3b (c_v1 c) + omeas I c <= 3 * 2 ^ 16 + 1
    /\ Zlen (t3b (c_v2 c)) <= c_widx c - i_io I
    /\ Zlen (t3b (c_v3 c)) + zw_next (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 1
    /\ zw_stack_ok (t3b (c_v3 c))
    /\ nty (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I)
    /\ iaccA I c.

  Definition AEA (w : pmwA H) s LB LBs m mo c msF R F fc (I : ictxR) (pc : Z) (tbl : list (Z * expr)) (t word : Z) : Prop :=
    OBA w s LB LBs m mo c msF R F fc I pc RT_ARM S_OPER tbl
    /\ i_io I + 1 <= c_widx c < wa_n w /\ c_widx c < i_io I + i_iwc I
    /\ pi_nodes c + 2 <= c_widx c + 3 /\ t3b (c_v1 c) + 1 <= 3 * 2 ^ 16 + 1 /\ Zlen (t3b (c_v2 c)) <= c_widx c - i_io I
    /\ Zlen (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 2
    /\ 0 <= t < 2 ^ 31 /\ 0 <= word < 2 ^ 32
    /\ PropExec.getr R 22%bv = Z_to_bv 64 (i_op I) /\ PropExec.getr R 25%bv = Z_to_bv 64 (i_io I)
    /\ PropExec.getr R 18%bv = Z_to_bv 64 t /\ PropExec.getr R 21%bv = Z_to_bv 64 (sx32A word)
    /\ popndA w m (c_widx c - i_io I) t
    /\ rw_cells asegs m (wa_ff w + 176) [C4 (Z_to_bv 64 word)].

  Definition PUSHKA (w : pmwA H) (I : ictxR) (Q : config -> Prop) (c : pmc) (t : Z) : Prop :=
    forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (nw : Z) (l' : list Z),
      OBA w s' LB' LBs' m' mo' c' msF' R' F' fc' I OL_PUSHK RT_PUSHK S_OPER tbl' -> incl TBL_EEF44 tbl' ->
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

  Definition CHECKKA (w : pmwA H) (Q : config -> Prop) : Prop :=
    forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal e : Z),
      PMXAT H LINV w s' LB' LBs' m' mo' c' (OB_PARSED_OPERAND :: S_INSTR) tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' ->
      (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) ->
      rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
      PropExec.getr R' 23%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 ->
      as_SR H Q (mkCfg msF' mo').

  Definition arm_stmtA (t pc : Z) : Prop :=
    forall (w : pmwA H) s LB LBs m mo c msF R F fc (I : ictxR) (tbl : list (Z * expr)) (word : Z) (Q : config -> Prop),
      pmw_okA H w -> AEA w s LB LBs m mo c msF R F fc I pc tbl t word -> incl TBL_EEF44 tbl ->
      tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
      PUSHKA w I Q c t -> CHECKKA w Q -> aacc I c t ->
      as_SR H Q (mkCfg msF mo).
  Record PI0A (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
             (msF : machine_state) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) : Prop := MKPI0A {
    p0_x   : PMXA H LINV w s LB LBs m mo c [] TBL_PI0 [];
    p0_kr  : as_AKREL H s (mkCfg msF mo);
    p0_vis : as_VIS H s msF = MS R F (Z_to_bv 64 PI0_PC) fc None m (seg_rom asegs);
    p0_rf  : rfull R;
    p0_fz  : frm_zero fc;
    p0_rt  : regs_tbl w R RT_PI0;
    p0_gp  : PropExec.getr R 3%bv = wa_gp w;
    p0_tp  : PropExec.getr R 4%bv = wa_tp w;
    p0_tr  : c_tr c = [];
    p0_bsz : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    p0_ic  : c_icount c + 5 <= c_widx c;
    p0_end : c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1);
    p0_w   : wa_words w <> 0 /\ 5 <= wa_n w;
    p0_bud : pm_bud (wa_n w) c;
    p0_acc : pi_nodes c + 1 <= c_widx c + 3 /\ pi_macct c /\ pi_lacc c;
    p0_lt  : c_widx c < wa_n w;
    p0_a0  : PropExec.getr R 10%bv = Z_to_bv 64 (c_icount c)
  }.

  Definition pi_moreA (w : pmwA H) (lw : Z) (c : pmc) : Prop :=
    lw < c_widx c /\ c_icount c + 5 <= c_widx c /\ c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1)
    /\ wa_words w <> 0 /\ 5 <= wa_n w /\ pm_bud (wa_n w) c /\ pi_nodes c + 1 <= c_widx c + 3 /\ pi_macct c /\ pi_lacc c.

  Record EXA (w : pmwA H) (s : as_St H) (LB LBs : list block) (m : mem) (mo : Model) (c : pmc)
             (msF : machine_state) (R F : bvmap 5 word) (fc : bv 32) (pc : Z) (ins : list nat) (r lw : Z) : Prop := MKEXA {
    ex_x   : exists tbl spal, PMXAT H LINV w s LB LBs m mo c ins tbl [] [] spal /\ incl TBL_EXIT tbl /\ (r = 0 -> spal = 0);
    ex_kr  : as_AKREL H s (mkCfg msF mo);
    ex_vis : as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs);
    ex_rf  : rfull R;
    ex_fz  : frm_zero fc;
    ex_rt  : regs_tbl w R RT_EXIT;
    ex_gp  : PropExec.getr R 3%bv = wa_gp w;
    ex_tp  : PropExec.getr R 4%bv = wa_tp w;
    ex_r   : PropExec.getr R 23%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31;
    ex_tr  : c_tr c = [];
    ex_bsz : forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40;
    ex_ok  : r = 0 -> pi_moreA w lw c
  }.

  Definition EXITKA (w : pmwA H) (lw : Z) (Q : config -> Prop) : Prop :=
    forall s LB LBs m mo c msF R F fc pc ins r, EXA w s LB LBs m mo c msF R F fc pc ins r lw ->
      (pc = EXIT_RET /\ ins = S_INSTR) \/ (pc = EXIT_OPC /\ ins = [OB_INST; OB_FIRST_WORD; OB_INST_WC; OB_OPCODE_DESC])
      \/ (pc = EXIT_IWC /\ ins = [OB_INST; OB_FIRST_WORD; OB_INST_WC] /\ PropExec.getr R 11%bv = Z_to_bv 64 (wa_ff w)) ->
      as_SR H Q (mkCfg msF mo).
  Definition U2HK (w : pmwA H) (c : pmc) (F : bvmap 5 word) (fc : bv 32) (Q : config -> Prop) : Prop :=
    forall (I : ictxR) s' LB' LBs' m' mo' c' msF' R',
      OLIA w s' LB' LBs' m' mo' c' msF' R' F fc I -> i_io I = c_widx c -> as_SR H Q (mkCfg msF' mo').

  Definition pm_body_allB : Prop :=
    forall (w : pmwA H) (Q : config -> Prop) s LB LBs m mo c msF R F fc,
      pmw_okA H w -> PI0A w s LB LBs m mo c msF R F fc -> EXITKA w (c_widx c) Q -> as_SR H Q (mkCfg msF mo).
End OL.
