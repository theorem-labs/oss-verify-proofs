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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmCall LbA_PmHdr LbA_PmLH LbA_TablStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition ipureA (I : ictxR) : Prop := @PmODefsS1.ipure TG idescA I.
Definition iaccA (I : ictxR) (c : pmc) : Prop := @PmODefsS1.iacc tg_generates_type I c.

Definition RT_OL : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, EVar WV_FF); (19%bv, EVar WV_P); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608)].

Definition RT_EEF44 : list (reg * expr) := RT_OL ++ [(26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition RT_ARM : list (reg * expr) := RT_OL ++ [(25%bv, WADD WV_FF 944)].

Definition RT_OLJ : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF); (22%bv, ELit 18446744073709551608)].
Definition RT_PUSHK : list (reg * expr) := RT_OLJ.
Definition RT_CHECK : list (reg * expr) := RT_OLJ.

Definition TBL_EEF44 : list (Z * expr) :=
  [(1056, EVar 33); (968, EVar 33); (1040, EVar 33); (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (1000, EAlu ALU_ADD (EVar 32) (ELit 48)); (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (936, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (944, EAlu ALU_ADD (EVar 32) (ELit 56)); (960, EAlu ALU_ADD (EVar 33) (ELit 11488)); (712, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 92)) (ELit 3)) (ELit 2147450880)); (632, EAlu ALU_ADD (EVar 32) (ELit 92)); (848, EAlu ALU_ADD (EVar 32) (ELit 88)); (800, EAlu ALU_ADD (EVar 33) (ELit 10512)); (976, ELit 2147450880); (720, EAlu ALU_ADD (EVar 33) (ELit 10496)); (784, EAlu ALU_ADD (EVar 33) (ELit 10416)); (808, EVar 32); (792, EAlu ALU_ADD (EVar 32) (ELit 80)); (344, EAlu ALU_ADD (EVar 33) (ELit 10432)); (440, EAlu ALU_ADD (EVar 33) (ELit 10436)); (216, EAlu ALU_ADD (EVar 33) (ELit 6737)); (488, EAlu ALU_ADD (EVar 33) (ELit 6736)); (888, EAlu ALU_ADD (EVar 33) (ELit 10426)); (648, EAlu ALU_ADD (EVar 33) (ELit 11024)); (520, EAlu ALU_ADD (EVar 33) (ELit 9312)); (728, EAlu ALU_ADD (EVar 33) (ELit 10992)); (704, EAlu ALU_ADD (EVar 33) (ELit 10528)); (688, EAlu ALU_ADD (EVar 33) (ELit 10352)); (736, EAlu ALU_ADD (EVar 33) (ELit 10288)); (640, EAlu ALU_ADD (EVar 33) (ELit 10224)); (608, EAlu ALU_ADD (EVar 33) (ELit 10160)); (680, EAlu ALU_ADD (EVar 33) (ELit 10096)); (592, EAlu ALU_ADD (EVar 33) (ELit 10032)); (528, EAlu ALU_ADD (EVar 33) (ELit 9968)); (496, EAlu ALU_ADD (EVar 33) (ELit 9904)); (504, EAlu ALU_ADD (EVar 33) (ELit 9840)); (296, EAlu ALU_ADD (EVar 33) (ELit 9376)); (392, EAlu ALU_ADD (EVar 33) (ELit 9344)); (776, EAlu ALU_ADD (EVar 33) (ELit 9280)); (128, EAlu ALU_ADD (EVar 33) (ELit 7264)); (536, EAlu ALU_ADD (EVar 33) (ELit 8816)); (584, EAlu ALU_ADD (EVar 33) (ELit 8784)); (144, EAlu ALU_ADD (EVar 33) (ELit 8752)); (232, EAlu ALU_ADD (EVar 33) (ELit 8288)); (304, EAlu ALU_ADD (EVar 33) (ELit 8256)); (576, EAlu ALU_ADD (EVar 33) (ELit 8224)); (696, EAlu ALU_ADD (EVar 33) (ELit 7760)); (672, EAlu ALU_ADD (EVar 33) (ELit 7728)); (112, EAlu ALU_ADD (EVar 33) (ELit 6800)); (136, EAlu ALU_ADD (EVar 33) (ELit 4816)); (24, EAlu ALU_ADD (EVar 33) (ELit 6272)); (72, EAlu ALU_ADD (EVar 33) (ELit 5808)); (224, EAlu ALU_ADD (EVar 33) (ELit 5344)); (32, EAlu ALU_ADD (EVar 33) (ELit 5312)); (48, EAlu ALU_ADD (EVar 33) (ELit 4848)); (256, EAlu ALU_ADD (EVar 33) (ELit 4352)); (248, EAlu ALU_ADD (EVar 33) (ELit 2400)); (184, EAlu ALU_ADD (EVar 33) (ELit 4336)); (56, EAlu ALU_ADD (EVar 33) (ELit 3872)); (152, EAlu ALU_ADD (EVar 33) (ELit 3840)); (64, EAlu ALU_ADD (EVar 33) (ELit 3824)); (320, EAlu ALU_ADD (EVar 33) (ELit 3792)); (240, EAlu ALU_ADD (EVar 33) (ELit 3328)); (40, EAlu ALU_ADD (EVar 33) (ELit 2864)); (360, EAlu ALU_ADD (EVar 32) (ELit 32)); (336, EAlu ALU_ADD (EVar 32) (ELit 152)); (312, EAlu ALU_ADD (EVar 32) (ELit 168)); (400, EAlu ALU_ADD (EVar 32) (ELit 160)); (384, EAlu ALU_ADD (EVar 32) (ELit 144)); (448, EAlu ALU_ADD (EVar 32) (ELit 136)); (352, EAlu ALU_ADD (EVar 32) (ELit 96)); (208, EAlu ALU_ADD (EVar 32) (ELit 176)); (600, EAlu ALU_ADD (EVar 32) (ELit 93)); (544, EAlu ALU_ADD (EVar 32) (ELit 280)); (864, EAlu ALU_ADD (EVar 32) (ELit 272)); (952, EAlu ALU_ADD (EVar 32) (ELit 264)); (872, EAlu ALU_ADD (EVar 32) (ELit 8)); (752, EAlu ALU_ADD (EVar 32) (ELit 40)); (856, EAlu ALU_ADD (EVar 32) (ELit 232)); (896, EAlu ALU_ADD (EVar 32) (ELit 224)); (768, EAlu ALU_ADD (EVar 32) (ELit 216)); (992, EAlu ALU_ADD (EVar 32) (ELit 256)); (928, EAlu ALU_ADD (EVar 32) (ELit 248)); (920, EAlu ALU_ADD (EVar 32) (ELit 240)); (432, EAlu ALU_ADD (EVar 33) (ELit 12480)); (424, EAlu ALU_ADD (EVar 33) (ELit 12016)); (552, EAlu ALU_ADD (EVar 33) (ELit 11552)); (568, EAlu ALU_ADD (EVar 33) (ELit 11520)); (176, EAlu ALU_ADD (EVar 33) (ELit 1936)); (160, EAlu ALU_ADD (EVar 33) (ELit 1472)); (168, EAlu ALU_ADD (EVar 33) (ELit 1008)); (912, EAlu ALU_ADD (EVar 33) (ELit 944)); (80, EAlu ALU_ADD (EVar 33) (ELit 928)); (96, EAlu ALU_ADD (EVar 33) (ELit 896)); (88, EAlu ALU_ADD (EVar 33) (ELit 880)); (264, ELit 16843009); (272, ELit 252645135); (280, ELit 858993459); (288, ELit 1431655765); (368, ELit 18446744072850558157); (120, ELit 65535); (200, ELit 262140); (104, EAlu ALU_ADD (EVar 33) (ELit 848)); (656, EAlu ALU_ADD (EVar 33) (ELit 784)); (616, EAlu ALU_ADD (EVar 33) (ELit 720)); (624, EAlu ALU_ADD (EVar 33) (ELit 656)); (512, EAlu ALU_ADD (EVar 33) (ELit 592)); (464, EAlu ALU_ADD (EVar 33) (ELit 528)); (472, EAlu ALU_ADD (EVar 33) (ELit 464)); (984, EAlu ALU_ADD (EVar 33) (ELit 448)); (408, EAlu ALU_ADD (EVar 33) (ELit 384)); (456, EAlu ALU_ADD (EVar 33) (ELit 320)); (328, EAlu ALU_ADD (EVar 33) (ELit 256)); (416, EAlu ALU_ADD (EVar 33) (ELit 192)); (480, EAlu ALU_ADD (EVar 33) (ELit 128)); (376, EAlu ALU_ADD (EVar 33) (ELit 64)); (192, EAlu ALU_ADD (EVar 33) (ELit 32)); (1016, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (1024, EAlu ALU_ADD (EVar 32) (ELit 72)); (560, EAlu ALU_ADD (EVar 32) (ELit 16)); (840, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 80)) (ELit 3)) (ELit 2147450880)); (880, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (1032, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 248)) (ELit 3)) (ELit 2147450880)); (904, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 256)) (ELit 3)) (ELit 2147450880)); (832, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)); (744, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (760, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (816, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 40)) (ELit 3)); (824, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (1096, EAlu ALU_ADD (EVar 33) (ELit 10416)); (1088, EAlu ALU_ADD (EVar 33) (ELit 10496)); (1080, EVar 32); (1072, EAlu ALU_ADD (EVar 33) (ELit 10512)); (1064, EAlu ALU_ADD (EVar 33) (ELit 11488))].

Definition OL_PUSHK : Z := 0xf22cc.
Definition OL_CHECK : Z := 0xf2560.
Definition OL_HEAD : Z := 0xef0d4.

Section OL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Definition ictxA (w : pmwA H) (m : mem) (I : ictxR) : Prop :=
    rw_cells asegs m (wa_ff w + 11488) [C8 (Z_to_bv 64 (i_io I))]
    /\ rw_cells asegs m (wa_ff w + 10496) [C4 (Z_to_bv 64 (i_fw I))]
    /\ rw_cells asegs m (wa_ff w + 10512) [C2 (Z_to_bv 64 (i_iwc I))]
    /\ rw_cells asegs m (wa_ff w + 10426) [C2 (Z_to_bv 64 (i_op I))]
    /\ rw_cells asegs m (wa_ff w + 10992) [C8 (Z_to_bv 64 (i_d I))].

  Definition ifrA (w : pmwA H) (m : mem) : Prop :=
    exists ext tid rid,
      rw_cells asegs m (wa_ff w + 10416) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m (wa_ff w + 10424) [C2 (Z_to_bv 64 0)]
      /\ rw_cells asegs m (wa_ff w + 10428) [C4 (Z_to_bv 64 ext)] /\ rw_cells asegs m (wa_ff w + 10432) [C4 (Z_to_bv 64 tid)]
      /\ rw_cells asegs m (wa_ff w + 10436) [C4 (Z_to_bv 64 rid)]
      /\ rw_cells asegs m (wa_ff w + 10440) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m (wa_ff w + 10448) [C8 (Z_to_bv 64 0)]
      /\ 0 <= ext < 2 ^ 31 /\ 0 <= tid < 2 ^ 32 /\ 0 <= rid < 2 ^ 32.

  Definition popndA (w : pmwA H) (m : mem) (off t : Z) : Prop :=
    rw_cells asegs m (wa_ff w + 944) [C2 (Z_to_bv 64 off)] /\ rw_cells asegs m (wa_ff w + 946) [C2 (Z_to_bv 64 1)]
    /\ rw_cells asegs m (wa_ff w + 948) [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m (wa_ff w + 952) [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m (wa_ff w + 956) [C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m (wa_ff w + 960) [C4 (Z_to_bv 64 0)].

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
    ob_acc  : macctA c;
    ob_v3r  : Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c))
  }.

  Definition OLIA (w : pmwA H) s LB LBs m mo c msF R F fc (I : ictxR) : Prop :=
    OBA w s LB LBs m mo c msF R F fc I OL_HEAD RT_EEF44 S_INSTR TBL_EEF44
    /\ i_io I + 1 <= c_widx c
    /\ nodesA c + 2 <= c_widx c + 3
    /\ t3b (c_v1 c) + omeas I c <= 3 * 2 ^ 16 + 1
    /\ Zlen (t3b (c_v2 c)) <= c_widx c - i_io I
    /\ Zlen (t3b (c_v3 c)) + zw_next (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 1
    /\ zw_stack_ok (t3b (c_v3 c))
    /\ nty (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I)
    /\ iaccA I c.

  Definition AEA (w : pmwA H) s LB LBs m mo c msF R F fc (I : ictxR) (pc : Z) (tbl : list (Z * expr)) (t word : Z) : Prop :=
    OBA w s LB LBs m mo c msF R F fc I pc RT_ARM S_OPER tbl
    /\ i_io I + 1 <= c_widx c < wa_n w /\ c_widx c < i_io I + i_iwc I
    /\ nodesA c + 2 <= c_widx c + 3 /\ t3b (c_v1 c) + 1 <= 3 * 2 ^ 16 + 1 /\ Zlen (t3b (c_v2 c)) <= c_widx c - i_io I
    /\ Zlen (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 2
    /\ 0 <= t < 2 ^ 31 /\ 0 <= word < 2 ^ 32
    /\ PropExec.getr R 23%bv = Z_to_bv 64 (i_op I) /\ PropExec.getr R 24%bv = Z_to_bv 64 (i_io I)
    /\ PropExec.getr R 26%bv = Z_to_bv 64 t /\ PropExec.getr R 27%bv = Z_to_bv 64 (sx32A word)
    /\ popndA w m (c_widx c - i_io I) t
    /\ rw_cells asegs m (wa_s1 w + 1108) [C4 (Z_to_bv 64 word)].

  Definition PUSHKA (w : pmwA H) (I : ictxR) (Q : config -> Prop) (c : pmc) (t : Z) : Prop :=
    forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (nw : Z) (l' : list Z),
      OBA w s' LB' LBs' m' mo' c' msF' R' F' fc' I OL_PUSHK RT_PUSHK S_OPER tbl' -> incl TBL_EEF44 tbl' ->
      PropExec.getr R' 23%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R' 24%bv = Z_to_bv 64 (i_io I) ->
      PropExec.getr R' 26%bv = Z_to_bv 64 t ->
      rw_cells asegs m' (wa_ff w + 946) [C2 (Z_to_bv 64 nw)] -> (1 <= nw < 2 ^ 16 \/ (nw = 0 /\ zw_type t = true /\ l' = [])) ->
      (exists off ty, rw_cells asegs m' (wa_ff w + 944) [C2 (Z_to_bv 64 off)] /\ rw_cells asegs m' (wa_ff w + 948) [C4 (Z_to_bv 64 ty)]) ->
      mdef m' (wa_ff w + 944) 20 ->
      c_widx c' = c_widx c -> c_v1 c' = c_v1 c -> c_v2 c' = c_v2 c -> nodesA c' <= nodesA c + Z.min nw 1 ->
      t3b (c_v3 c') = t3b (c_v3 c) ++ l' -> seed_free l' -> Zlen l' <= 125 ->
      l' = [] \/ (t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING) ->
      c_m2 c' = c_m2 c ->
      (c_m1 c' = c_m1 c \/ (t = OT_RESULT_ID /\ Zlen (t3c (c_m1 c')) <= Zlen (t3c (c_m1 c)) + 1)) ->
      (c_m3 c' = c_m3 c \/ (t = OT_LITERAL_STRING /\ i_op I = OP_EXT_INST_IMPORT /\ Zlen (t3c (c_m3 c')) <= Zlen (t3c (c_m3 c)) + 1)) ->
      ~ In OT_RESULT_ID l' ->
      as_SR H Q (mkCfg msF' mo').

  Definition CHECKKA (w : pmwA H) (Q : config -> Prop) : Prop :=
    forall s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (spal e : Z),
      PMXAT H LINV w s' LB' LBs' m' mo' c' S_OPER tbl' [] [] spal -> incl TBL_EEF44 tbl' -> c_tr c' = [] -> pm_bud (wa_n w) c' ->
      (forall q k, In (q, k) (c_blocks c') -> k <= 2 ^ 40) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_CHECK) fc' None m' (seg_rom asegs) ->
      rfull R' -> frm_zero fc' -> regs_tbl w R' RT_CHECK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
      PropExec.getr R' 25%bv = Z_to_bv 64 (sx32A e) -> 0 < e < 2 ^ 32 ->
      as_SR H Q (mkCfg msF' mo').

  Definition arm_stmtA (t pc : Z) : Prop :=
    forall (w : pmwA H) s LB LBs m mo c msF R F fc (I : ictxR) (tbl : list (Z * expr)) (word : Z) (Q : config -> Prop),
      pmw_okA H w -> AEA w s LB LBs m mo c msF R F fc I pc tbl t word -> incl TBL_EEF44 tbl ->
      tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true ->
      PUSHKA w I Q c t -> CHECKKA w Q -> aacc I c t ->
      as_SR H Q (mkCfg msF mo).
End OL.
