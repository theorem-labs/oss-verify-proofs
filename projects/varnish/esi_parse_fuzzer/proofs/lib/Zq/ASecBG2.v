(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Divembc SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMTac AMallocI AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g ABudget ACover ANodeA7 ANodeA6 ASecComb ASecr83 ASecSrz ASecA1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecFinB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp ASecImg ASecB1 ASecB2 ASecB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecB5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecB5 ASecB6 ASecZ ACor4x6 ANodd09 ASecG2S.

Module ASeczyk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Divembc SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMTac AMallocI AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g ABudget ACover ANodeA7 ANodeA6 ASecComb ASecr83 ASecSrz ASecA1 ASecs86 ASeclpb ASecO4A8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecFinB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp ASecImg ASecB1 ASecB2 ASecB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecB5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecB5 ASecB6 ASecZ ACor4x6 ANodd09 ASecG2S.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g.AMal5j7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecr83 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecSrz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecA1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecs86 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASeclpb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecO4A8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecFinB.ASecFin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB5.ASecB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecZ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodd09 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecG2S.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SplitAll.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize in *.
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
(* [comment removed for export] *)
Ltac lia2 X K := clear - X K; Zify.zify; xlia zchecker.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac pick_out i X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K :=
  lazymatch i with
  | 1 => lia2 X1 K | 2 => lia2 X2 K | 3 => lia2 X3 K | 4 => lia2 X4 K | 5 => lia2 X5 K | 6 => lia2 X6 K
  | 7 => lia2 X7 K | 8 => lia2 X8 K | 9 => lia2 X9 K | 10 => lia2 X10 K | 11 => lia2 X11 K
  end.
Ltac solve_outs idxs X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K :=
  lazymatch idxs with
  | @nil _ => first [exact I | idtac]
  | @cons _ ?i ?rest => split; [pick_out i X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K | solve_outs rest X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K]
  end.
(* [comment removed for export] *)
Ltac transport_keep segs m m' MU WM KEEP :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | clear - KEEP; cbn [disjoint_from]; simpl_sizes; slia ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | clear - KEEP; cbn [disjoint_from]; simpl_sizes; slia ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | clear - KEEP; cbn [disjoint_from]; simpl_sizes; slia ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | clear - KEEP; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
  | H : stk segs m ?loq ?hiq |- _ =>
      apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | clear - KEEP; cbn [disjoint_from]; slia ]
  end.

(* [comment removed for export] *)
Ltac transport_keep_t segs m m' MU WM cut :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cut; cbn [disjoint_from]; simpl_sizes; first [ solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.rlia_loc_tiers ] | slia ] ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cut; cbn [disjoint_from]; simpl_sizes; first [ solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.rlia_loc_tiers ] | slia ] ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cut; cbn [disjoint_from]; simpl_sizes; first [ solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.rlia_loc_tiers ] | slia ] ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cut; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; first [ solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.rlia_loc_tiers ] | slia ] ]
  | H : stk segs m ?loq ?hiq |- _ =>
      apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cut; cbn [disjoint_from]; first [ solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.rlia_loc_tiers ] | slia ] ]
  end.

(* [comment removed for export] *)
Definition grow_W (mb ms : Z) : list (Z * Z) := [(mb, mb + ms); (sh mb, sh mb + ms / 8)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Section GrantC2A8.
Context {Clg : Ceiling}.
  Variables (rac spa gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n lo hi stkobj canfill : Z) (key : list Z) (T1 : TSet).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Hypothesis SPA : bv_unsigned spa mod 16 = 0.
  Hypothesis CFL : 0 <= canfill <= 1.
  (* [comment removed for export] *)
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOSA : lo <= bv_unsigned spa - 4096.
  Hypothesis SAHI : bv_unsigned spa <= hi <= 2^47.
  Hypothesis SMW : mapped (aview_of (pa_hull A) m) lo (hi - lo).
  (* [comment removed for export] *)
  Hypothesis SOB : bv_unsigned spa <= stkobj /\ stkobj + 2064 <= hi.
  Hypothesis TRC : ro_cells rsegs (aview_of (pa_hull A) m) stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRB : bytes_at rsegs (aview_of (pa_hull A) m) (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  (* [comment removed for export] *)
  Hypothesis LIM : as_livebytes A + n <= LIVE_MAX.
  Hypothesis NLV : as_nlive A + 1 <= NLIVE_MAX.
  Hypothesis SCRED : 1 <= as_seccred A.
  (* [comment removed for export] *)
  Hypothesis LMID : lma_mid_stmt.
  Hypothesis LTAIL : lma_tail_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis P0 : poison0_stmt.
  Hypothesis DPS : depot_put_stmt depot_repL.
  Hypothesis LESP : lma_esp_stmt.
  Hypothesis MFP : mapfixed_pre_stmt.
  Hypothesis LESPOST : lma_espost_stmt.
  (* [comment removed for export] *)
  Hypothesis K1 : alloc_core_K1v rac spa gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1.

  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation H0 := (hidc (pa_hull A)).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).

  (* [comment removed for export] *)
  Variables (m1 : mem) (md1 : Model) (t0' t1' t2' a6' t3' t4' t5' t6' : word) (junk0 scrL scrM : list byte).
  Hypothesis MU1 : munch [(lo, sa)] v m1.
  Hypothesis WM1 : wmono rsegs v m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 lo (sa + -128 + -48 + -96 + -48).
  Hypothesis HI1 : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
  Hypothesis SB1 : same_but_materialized md md1.
  Hypothesis CL1 : forall a, H0 a = true -> m1 a = None.
  Hypothesis FRA : rw_cells rsegs m1 (sa + -128) (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0).
  Hypothesis FRC : rw_cells rsegs m1 (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3731c)).
  Hypothesis FRL : rw_cells rsegs m1 (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1558) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).
  Hypothesis FRM : rw_cells rsegs m1 (sa + -128 + -48 + -96 + -48) [CB 12 scrM; C4 (wz 34); C8 (wz ms); C8 (wz ASecComb.LMA); C8 (wz ASecComb.LSTAT); C8 (wz lma_mapret)].
  (* [comment removed for export] *)
  Variable mbw : word.
  Hypothesis GOK : grant_okf (wz 34) (wz 0) md1 mbw ms = true.
  Local Notation mb := (bv_unsigned mbw).
  (* [comment removed for export] *)
  Hypothesis NCH0 : Z.of_nat (length (sr_chunks (a_sec A))) = 0 /\ sr_reserved (a_sec A) = 0.

  Local Notation M1 := (munrestrict H0 m m1).
  Local Notation M2 := (apply_zeros M1 [(mbw, wz ms)]).
  Local Notation md2 := (grant_model (wz 34) mbw (wz ms) false md1).

  #[using="NCH0 GOK FRM FRL FRC FRA CL1 SB1 HI1 ST1 MI1 WM1 MU1 scrM scrL junk0 K1 LESPOST MFP LESP DPS P0 PS TSS LTAIL LMID SCRED NLV LIM KR KEYU TRB TRC SOB SMW SAHI LOSA CLO CFL SPA NR AI key canfill hi lo md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Theorem sec_grant2_a8 :
    srealizes (cl_segs LPA)
      (mkCfg (MS (mkR (wz mmapordie_resume) (wz (sa + -128 + -48 + -96 + -48)) gp (cl_tp LPA) t0' t1' t2'
                      (wz lma_name) (wz ms) mbw (wz ms) (wz 3) (wz 34) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz ANodeA7.PSC) (wz (needed_size2 n)) (wz (rz_size n)) (wz 8) (wz 0xb1558) (wz stkobj) (wz 7) (wz 7) (wz thr) (wz 1)
                      t3' t4' t5' t6')
                 F (wz ANodeA7.mmap_after_pc) fc None M2 (seg_rom (cl_segs LPA))) md2) T1.
  Proof.
    unfold alloc_core_K1v in K1. cbn [cl_segs cl_malloc_pc LPA] in K1 |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    assert (NR30 : kMaxPrimaryUser < n < 2^30 + 1) by exact NR. pose proof NR30 as NRu. unfold kMaxPrimaryUser in NRu.
    (first [ pose proof ((g_facts A m md md1 n mbw AI SB1 GOK)) as dR_1; dand4 dR_1 as MBA MB0 MBC RF | pose proof (g_facts A m md md1 n mbw AI SB1 GOK) as (MBA & MB0 & MBC & RF) ]).
    pose proof (MSP A n mbw NR30 MB0) as MSP. pose proof (MSA n) as MSA.
    assert (MSW : bv_unsigned (wz ms) = ms) by (apply unsigned_lit; lia).
    pose proof (gf_APART A m md mbw ms AI MB0 MSP RF) as APART.
    pose proof (gf_aobj A m md mbw ms AI MBA MB0 MBC MSP MSA RF) as AOBJ.
    (first [ pose proof ((sec_nch A m md AI)) as dR_2; dand4 dR_2 as NC1 NC2 NC3 NC4 | pose proof (sec_nch A m md AI) as (NC1 & NC2 & NC3 & NC4) ]).
    destruct NCH0 as [NCHZ NRES0].
    set (nch := Z.of_nat (length (sr_chunks (a_sec A)))) in *.
    set (A' := secA A mb n key kChunksBlockCount).
    assert (WF' : WF A').
    { subst A'. apply (sec_WF A v mb n key kChunksBlockCount AR NR30 MBA (proj2 (aobj_app_rangeA _ _) AOBJ) MBC APART eq_refl KEYU LIM NLV SCRED). }
    set (pahi := p_pa (a_pl A) + 8 * kChunksBlockCount).
    assert (PAHI : pahi = p_pa (a_pl A) + 8 * nch + 8 \/ (nch = 0 /\ pahi = p_pa (a_pl A) + 8 * kChunksBlockCount)) by (right; split; [exact NCHZ| reflexivity]).
    pose proof (GEO A m md n mbw lo pahi AI NR30 CLO MBA MB0 MBC RF PAHI) as G. fold nch in G.
    pose proof (SHG A m md n mbw lo pahi AI NR30 CLO MBA MB0 MBC RF PAHI) as SG.
    (first [ pose proof ((GEOP A m md n mbw AI NR30 MBA MB0 MBC RF)) as dR_3; dand5 dR_3 as Gt Gn Gf Gp Gm | pose proof (GEOP A m md n mbw AI NR30 MBA MB0 MBC RF) as (Gt & Gn & Gf & Gp & Gm) ]).
    aobj_lin1 Gt. aobj_lin1 Gn. aobj_lin1 Gf. aobj_lin1 Gp. aobj_lin1 Gm.
    (* [comment removed for export] *)
    set (H1 := pa_hull A') in *.
    set (m3 := mrestrict (hidc H1) M2).
    assert (ZSPEC : forall x : word, M2 x = if in_range mb ms x then Some (Z_to_bv 8 0) else M1 x).
    { intros x. rewrite <- (Z_to_bv_bv_unsigned mbw) at 1. change (Z_to_bv 64 mb) with (wa mb). apply apply_zeros_spec; lia. }
    assert (VISg : forall x, mb <= x < mb + ms -> hidc H1 (wz x) = false).
    { intros x Hx. unfold hidc. apply negb_false_iff. apply (in_hullb_intro _ _ mb (mb + ms)); [| rewrite unsigned_lit by lia; exact Hx].
      subst H1 A'. rewrite (sec_hull A mb n key kChunksBlockCount). rewrite !in_app_iff. right; left; right. cbn. left. reflexivity. }
    assert (VISs : forall z, sh mb <= z < sh mb + ms / 8 -> hidc H1 (wz z) = false).
    { intros z Hz. unfold hidc. apply negb_false_iff. apply (in_hullb_intro _ _ (sh mb) (sh mb + ms / 8)); [| rewrite unsigned_lit by (unfold sh in *; kung_all; lia); exact Hz].
      subst H1 A'. rewrite (sec_hull A mb n key kChunksBlockCount). rewrite !in_app_iff. right; left; right.
      rewrite (gf_sh mbw ms MBA MSP MSA). cbn. right. left. f_equal. }
    assert (Z3 : zrange m3 mb ms).
    { intros i Hi. subst m3. unfold mrestrict. rewrite (VISg (mb + i)) by lia. rewrite ZSPEC.
      unfold in_range. rewrite unsigned_lit by lia. replace ((mb <=? mb + i) && (mb + i <? mb + ms)) with true; [reflexivity|].
      symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
    assert (P3 : forall z, sh mb <= z < sh mb + ms / 8 -> m3 (wz z) <> None).
    { intros z Hz. subst m3. unfold mrestrict. rewrite (VISs z Hz). rewrite ZSPEC.
      (first [ dand9 SG as SG1 SG2 SG3 SG4 SG5 SG6 SG7 SG8 SG9 | destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9) ]).
      assert (Z64 : 0 <= z < 2^64) by (unfold sh in *; kung_all; lia).
      unfold in_range. rewrite unsigned_lit by exact Z64.
      replace ((mb <=? z) && (z <? mb + ms)) with false.
      2:{ symmetry. apply andb_false_iff. (first [ dand8 G as _ _ _ _ _ _ GX _ | destruct G as (_ & _ & _ & _ & _ & _ & GX & _) ]). kung_all. unfold sh in *.
          destruct (Z_lt_le_dec z mb); [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia]. }
      pose proof (gf_shadow A m md mbw ms AI MBA MB0 MBC MSP MSA RF z Hz) as [GH _].
      pose proof (proj1 (proj1 (ai_hidden _ _ _ _ _ _ _ AI) z GH)) as PM.
      unfold munrestrict. destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact PM|].
      apply (wmono_NN v m1 z WM1); [pose proof GH as [[X|X] _]; kung_all; lia| exact Z64|]. unfold aview_of, mrestrict. rewrite E. exact PM. }
    (* [comment removed for export] *)
    pose proof (sec_hull_sub A m md n mbw key lo pahi AI NR30 CLO MBA MB0 MBC RF PAHI) as SUB. fold A' H1 in SUB.
    assert (NEW : forall x, in_hullb H1 x = true -> in_hullb (pa_hull A) x = false -> ~ outside (grow_W mb ms) x).
    { intros x V1 V0 OUT. cbn [grow_W outside] in OUT. (first [ dand3 OUT as O1 O2 _ | destruct OUT as (O1 & O2 & _) ]).
      destruct (sec_hull_cases A m md n mbw key lo pahi AI NR30 CLO MBA MB0 MBC RF PAHI x V1) as [X|[X|X]]; [rewrite X in V0; discriminate| lia| lia]. }
    assert (MZ : forall a, outside (grow_W mb ms) (bv_unsigned a) -> M2 a = M1 a).
    { intros a OUT. rewrite ZSPEC. cbn [grow_W outside] in OUT. destruct OUT as (O1 & _).
      unfold in_range. replace ((mb <=? bv_unsigned a) && (bv_unsigned a <? mb + ms)) with false; [reflexivity|].
      symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (bv_unsigned a) mb); [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia]. }
    assert (PRESV : forall a, hidc (pa_hull A) a = false -> m1 a <> None -> M2 a <> None).
    { intros a V0 P1. rewrite ZSPEC. destruct (in_range mb ms a); [discriminate|]. unfold munrestrict. rewrite V0. exact P1. }
    pose proof (restrict_grow_munch (pa_hull A) H1 (grow_W mb ms) SUB NEW m m1 M2 CL1 MZ) as MU13g. fold m3 in MU13g.
    pose proof (restrict_grow_wmono (pa_hull A) H1 SUB m1 M2 CL1 PRESV rsegs) as WM13g. fold m3 in WM13g.
    (* [comment removed for export] *)
    set (Wc := (lo, sa) :: grow_W mb ms).
    assert (MU13 : munch Wc v m3).
    { apply (munch_trans Wc v m1 m3).
      - eapply (munch_weaken [(lo, sa)] Wc v m1); [unfold sub_fp, Wc; cbn [outside grow_W]; intros; slia| exact MU1].
      - eapply (munch_weaken (grow_W mb ms) Wc m1 m3); [unfold sub_fp, Wc; cbn [outside grow_W]; intros; slia| exact MU13g]. }
    pose proof (wmono_trans _ _ _ _ WM1 WM13g) as WM13. subst Wc. unfold grow_W in MU13.
    (first [ pose proof ((hit_place A m md AI)) as dR_7; dand7 dR_7 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]). pose proof CT1 as Gc. aobj_lin1 Gc.
    (first [ pose proof ((bm_nth_fixed A)) as dR_8; dand10 dR_8 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    pose proof (APART _ _ _ E1) as Dm1. pose proof (APART _ _ _ E4) as Dm4. pose proof (APART _ _ _ E5) as Dm5.
    unfold a_pa, a_thr, a_ctx in Dm1, Dm4, Dm5.
    assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e7bd8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    pose proof (hit_PCo A m md AI) as PCo. pose proof (hit_AF1 A m md AI) as AF1. pose proof (hit_AF2 A m md AI) as AF2.
    pose proof (hit_AF44 A m md AI) as AF44. pose proof (hit_AF52 A m md AI) as AF52. pose proof (hit_LS1 A m md AI) as LS1. pose proof (hit_LS2 A m md AI) as LS2.
    pose proof (hit_HK A m md AI) as HK. pose proof (hit_SBc A m md AI) as SBc.
    pose proof (hit_TC A m md AI) as TC. pose proof (hit_TH0 A m md AI) as TH0. pose proof (hit_CT8 A m md AI) as CT8.
    pose proof (sec_LMA0 A m md AI) as PGS. pose proof (sec_LPA8 A m md AI) as LPA8. pose proof (sec_LPA16 A m md AI) as LPA16.
    pose proof (sec_CF260 A m md AI) as CF260. pose proof (sec_CF144 A m md AI) as Lmlim.
    pose proof (sec_LREG A m md AI) as LREG. destruct (sec_LCS A m) as [cs LCS]. (first [ pose proof ((sec_LSTA A m)) as dR_9; dex5 dR_9 as na nf ca mx bsl; destruct dR_9 as [LSTA LBSL] | pose proof ((sec_LSTA A m)) as dR_9; dand7 dR_9 as na nf ca mx bsl LSTA LBSL | destruct (sec_LSTA A m) as (na & nf & ca & mx & bsl & LSTA & LBSL) ]).
    pose proof (sec_LMTX A m md AI) as LMTX. (first [ pose proof ((sec_GST A m)) as dR_10; dex2 dR_10 as sta stm; rename dR_10 into GST | pose proof ((sec_GST A m)) as dR_10; dand3 dR_10 as sta stm GST | destruct (sec_GST A m) as (sta & stm & GST) ]).
    (first [ pose proof ((sec_thr_stats A m md AI)) as dR_11; dex6 dR_11 as v0 v1 v2 mm72 mm80 vl; dand3 dR_11 as STS STM STL | pose proof ((sec_thr_stats A m md AI)) as dR_11; dand9 dR_11 as v0 v1 v2 mm72 mm80 vl STS STM STL | destruct (sec_thr_stats A m md AI) as (v0 & v1 & v2 & mm72 & mm80 & vl & STS & STM & STL) ]).
    pose proof (hit_DR A m md AI) as DR0.
    (first [ dand6 TC as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand13 PCo as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PCo as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    unfold ASecComb.LMA, ASecComb.LSTAT, ANodeA7.CF, off_th_stats in *.
    (* [comment removed for export] *)
    assert (GL : 64512 < n < 2^30 + 1 /\ 4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ 4096 <= mb /\ mb + ms <= alloc_ceiling /\ n + 4096 <= ms /\ ms < 2^31 /\
                 4096 <= p_pa (a_pl A) /\ p_pa (a_pl A) + kPtrArrayReserve <= alloc_ceiling /\ 0 <= nch < kChunksBlockCount /\
                 alloc_ceiling <= lo /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
                 0x7fff8000 + 512 <= sh mb /\ sh mb + ms / 8 <= kHighMemBeg /\ lo <= sa - 4096 /\ sa <= stkobj /\ stkobj + 2064 <= hi /\ hi <= 2^47)
      by (unfold sh in *; split_all; lia).
    clear G. unfold sh in *. kung_all.
    set (vv := aview_of (pa_hull A) m) in *.
    transport_after_call rsegs vv m3 MU13 WM13.
    (* [comment removed for export] *)
    clear MU1 WM1. unfold grow_W, sh, kShadowOffset in MU13g.
    transport_after_call rsegs m1 m3 MU13g WM13g.
    (* [comment removed for export] *)
    assert (MI3 : mem_inv rsegs m3).
    { intros a b Hab. subst m3. unfold mrestrict in Hab. destruct (hidc H1 a) eqn:V1; [discriminate|].
      pose proof (bv_unsigned_in_range _ a) as AR64. change (bv_modulus 64) with (2^64) in AR64.
      destruct (ro_addr rsegs a) eqn:RO; [| reflexivity]. exfalso. pose proof (proj1 (pa_ro_addr_iff _) RO) as ROr.
      rewrite ZSPEC in Hab. destruct (in_range mb ms a) eqn:IR.
      - unfold in_range in IR. apply andb_true_iff in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2. clear - ROr I1 I2 GL Gm. lia.
      - unfold munrestrict in Hab. destruct (hidc (pa_hull A) a) eqn:V0.
        + destruct (sec_hidc_new A m md n mbw key lo pahi AI NR30 CLO MBA MB0 MBC RF PAHI a V0 V1) as [X|X]; [| unfold sh, kShadowOffset in X; clear - ROr X GL; lia].
          unfold in_range in IR. apply andb_false_iff in IR. destruct IR as [IR|IR]; [apply Z.leb_gt in IR| apply Z.ltb_ge in IR]; clear - IR X; lia.
        + pose proof (MI1 a b Hab) as Y. rewrite RO in Y. discriminate. }
    (* [comment removed for export] *)
    pose proof (needed_size2_secondary n ltac:(lia)) as NS2. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT. pose proof (rounded_size_mod8 n) as RM8.
    assert (MSE : ms = round_up (needed_size2 n) 4096 + 4096) by reflexivity.
    pose proof (conj (conj (round_up_ge (needed_size2 n) 4096 ltac:(lia)) (round_up_lt (needed_size2 n) 4096 ltac:(lia))) (round_up_mod (needed_size2 n) 4096 ltac:(lia))) as RUF.
    (first [ dand9 SG as SG1 SG2 SG3 SG4 SG5 SG6 SG7 SG8 SG9 | destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9) ]).
    pose proof (Z_div_mod_eq_full n 8) as NDE0. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as ER.
    set (d := n / 8) in *. set (e := n mod 8) in *.
    set (dc := d + (if e =? 0 then 0 else 1)).
    assert (DCE : dc = d + Z.min e 1) by (subst dc; clear - ER; destruct (Z.eqb_spec e 0); lia).
    set (q := mb / 8 + 512). set (ru := (ms - 4096) / 8).
    assert (ABQ : mb + 4096 = 8 * q) by (subst q; clear - SG2; lia).
    assert (RU8 : round_up (needed_size2 n) 4096 = 8 * ru) by (subst ru; clear - MSE RUF; pose proof (Z_div_mod_eq_full (ms - 4096) 8); pose proof (Z_div_mod_eq_full (round_up (needed_size2 n) 4096) 4096); lia).
    assert (QSH : q + 2147450880 = mb / 8 + 2147450880 + 512) by (subst q; clear; lia).
    assert (RUB : 256 + dc <= ru /\ q + ru + 2147450880 = mb / 8 + 2147450880 + ms / 8).
    { subst q ru dc. clear - NS2 RGE RLT RM8 MSE RUF SG2 SG3 NDE0 ER GL. pose proof (Z_div_mod_eq_full (rounded_size n) 8). destruct (Z.eqb_spec e 0); lia. }
    assert (TC3 : thread_cells m3 (cl_tp LPA) pa_tsd (p_ctx (a_pl A)) thr) by exact (conj Cini (conj Ckey (conj Ctsd (conj Cctx (conj Cthr2 Bnds))))).
    assert (PCo3 : poison_consts m3)
      by exact (conj Ccan (conj Cgotcf (conj Cthr (conj Cgotsh (conj Cshoff (conj Cgotmid (conj Cgotmide (conj Cgothi (conj Chivars (conj Cgotms (conj Creal (conj Cgotps Cps)))))))))))).
    (* [comment removed for export] *)
    assert (MB64 : mb + ms <= 2^64) by (clear - GL; lia).
    assert (MBI : 0x60a000 <= mb) by (clear - GL Gm NRu; lia). assert (SHI : 0x60a000 <= mb / 8 + 2147450880) by (clear - GL; lia).
    assert (Zc1 : zrange m3 mb (8 * Z.of_nat 3)) by (apply (zrange_sub _ _ _ _ _ Z3); clear - GL; lia).
    assert (Zc2 : zrange m3 (mb + 24) (8 * Z.of_nat 1)) by (apply (zrange_sub _ _ _ _ _ Z3); clear - GL; lia).
    assert (Zc3 : zrange m3 (mb + 4096) (8 * Z.of_nat 2)) by (apply (zrange_sub _ _ _ _ _ Z3); clear - GL; lia).
    assert (Zc4 : zrange m3 (mb + 4096 + 2032) 16) by (apply (zrange_sub _ _ _ _ _ Z3); clear - GL NS2 RGE RUF MSE; lia).
    assert (Zc5 : zrange m3 (mb + 4096 + 2048) (Z.of_nat 4096)) by (apply (zrange_sub _ _ _ _ _ Z3); clear - GL NS2 RGE RUF MSE; lia).
    pose proof (zrange_C8s m3 mb MBI 3%nat ltac:(clear - GL; lia) Zc1) as J012. cbn [map repeat] in J012.
    pose proof (zrange_C8s m3 (mb + 24) ltac:(clear - MBI; lia) 1%nat ltac:(clear - GL; lia) Zc2) as CIDX. cbn [map repeat] in CIDX.
    pose proof (zrange_C8s m3 (mb + 4096) ltac:(clear - MBI; lia) 2%nat ltac:(clear - GL; lia) Zc3) as ABH. cbn [map repeat] in ABH.
    pose proof (zrange_HDR m3 (mb + 4096 + 2032) ltac:(clear - MBI; lia) ltac:(clear - GL; lia) Zc4) as HDR.
    pose proof (zrange_CB m3 (mb + 4096 + 2048) ltac:(clear - MBI; lia) (Z.to_nat 4096) ltac:(clear - GL; lia) Zc5) as USR. (* [comment removed for export] *)
    assert (P3m : forall a k, mb / 8 + 2147450880 <= a -> a + k <= mb / 8 + 2147450880 + ms / 8 -> mapped m3 a k).
    { intros a k H1k H2k i Hi. apply P3. clear - H1k H2k Hi. lia. }
    assert (Pm1 : mapped m3 (mb / 8 + 2147450880) (Z.of_nat 512)) by (apply P3m; clear - GL; lia).
    assert (Pm2 : mapped m3 (q + 2147450880) (Z.of_nat 256)) by (apply P3m; clear - GL QSH RUB; lia).
    assert (Pm3 : mapped m3 (q + 256 + 2147450880) (Z.of_nat (Z.to_nat d))) by (apply P3m; clear - GL QSH RUB NDE0 ER DCE; lia).
    assert (Pm5 : mapped m3 (q + 256 + dc + 2147450880) (ru - 256 - dc)) by (apply P3m; clear - GL QSH RUB NDE0 ER DCE; lia).
    (first [ pose proof ((mapped_CBj m3 (mb / 8 + 2147450880) SHI 512%nat ltac:(clear - GL; lia) Pm1)) as dR_15; dex1 dR_15 as old1; destruct dR_15 as [_ SH512] | pose proof ((mapped_CBj m3 (mb / 8 + 2147450880) SHI 512%nat ltac:(clear - GL; lia) Pm1)) as dR_15; dand3 dR_15 as old1 _ SH512 | destruct (mapped_CBj m3 (mb / 8 + 2147450880) SHI 512%nat ltac:(clear - GL; lia) Pm1) as (old1 & _ & SH512) ]).
    (first [ pose proof ((mapped_CBj m3 (q + 2147450880) ltac:(clear - SHI QSH; lia) 256%nat ltac:(clear - GL QSH; lia) Pm2)) as dR_16; dex1 dR_16 as oll; destruct dR_16 as [_ SHL] | pose proof ((mapped_CBj m3 (q + 2147450880) ltac:(clear - SHI QSH; lia) 256%nat ltac:(clear - GL QSH; lia) Pm2)) as dR_16; dand3 dR_16 as oll _ SHL | destruct (mapped_CBj m3 (q + 2147450880) ltac:(clear - SHI QSH; lia) 256%nat ltac:(clear - GL QSH; lia) Pm2) as (oll & _ & SHL) ]).
    (first [ pose proof ((mapped_u8arr m3 (q + 256 + 2147450880) ltac:(clear - SHI QSH; lia) (Z.to_nat d) ltac:(clear - GL QSH NDE0 ER; lia) Pm3)) as dR_17; dex1 dR_17 as olds; destruct dR_17 as [OL SHU] | pose proof ((mapped_u8arr m3 (q + 256 + 2147450880) ltac:(clear - SHI QSH; lia) (Z.to_nat d) ltac:(clear - GL QSH NDE0 ER; lia) Pm3)) as dR_17; dand3 dR_17 as olds OL SHU | destruct (mapped_u8arr m3 (q + 256 + 2147450880) ltac:(clear - SHI QSH; lia) (Z.to_nat d) ltac:(clear - GL QSH NDE0 ER; lia) Pm3) as (olds & OL & SHU) ]).
    assert (SHP : exists oldp, e <> 0 -> rw_cells rsegs m3 (q + 256 + d + 2147450880) [C1 oldp]).
    { destruct (Z.eq_dec e 0) as [Ee0|NE0]; [exists (Z_to_bv 8 0); intros X; exfalso; exact (X Ee0)|].
      assert (Pm4 : mapped m3 (q + 256 + d + 2147450880) 1) by (apply P3m; clear - GL QSH RUB NDE0 ER DCE NE0; lia).
      destruct (mapped_C1j m3 (q + 256 + d + 2147450880) ltac:(clear - SHI QSH NDE0 ER GL; lia) ltac:(clear - GL QSH NDE0 ER; lia) Pm4) as [oldp X].
      exists oldp. intros _. exact X. }
    destruct SHP as [oldp SHP].
    pose proof (mapped_stk m3 (q + 256 + dc + 2147450880) ltac:(clear - SHI QSH NDE0 ER DCE GL; lia) (ru - 256 - dc) ltac:(clear - GL QSH RUB; lia) Pm5) as SHT.
    replace (q + 256 + dc + 2147450880 + (ru - 256 - dc)) with (q + ru + 2147450880) in SHT by lia.
    (* [comment removed for export] *)
    (first [ pose proof ((hit_sep A m md AI)) as dR_18; dand13 dR_18 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
    pose proof DN01 as Gn0. aobj_lin1 Gn0. pose proof DF01 as Gf0. aobj_lin1 Gf0.
    pose proof (APART _ _ _ E7) as Dm7. pose proof (APART _ _ _ E8) as Dm8. unfold a_nodes0, a_frames0 in Dm7, Dm8.
    unfold kDepotNodesBlock, kStackStoreBlockBytes in Gn0, Gf0, DN02, DF02.
    assert (DRF : forall D' (ma mb' : mem), depot_repL AL_pboth rsegs D' (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) ma ->
              (forall a, ACells.depot_foot AL_pboth (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a -> mb' (Z_to_bv 64 a) = ma (Z_to_bv 64 a)) ->
              depot_repL AL_pboth rsegs D' (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) mb').
    { intros D' ma mb' X1 X2. exact (depot_repL_agree AL_pboth rsegs D' _ _ ma mb' X1 X2). }
    assert (DR3 : depot_repL AL_pboth rsegs (a_depot A) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) m3).
    { apply (DRF _ vv m3 DR0). intros a Ha. apply MU13.
      unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes, kDepotTabBytes in Ha.
      rewrite unsigned_lit by (clear - Ha GL Gn0 Gf0; lia). cbn [outside].
      destruct Ha as [Ha|[Ha|Ha]]; (split; [clear - Ha GL Gn0 Gf0; lia| split; [clear - Ha GL Gm Dm7 Dm8; lia| split; [clear - Ha GL Gn0 Gf0; lia| exact I]]]). }
    clear Dm7 Dm8.
    (* [comment removed for export] *)
    assert (HOFF1 : H_off_segments rsegs (hidc H1)).
    { intros a Ha. apply (asI_hull_segs A m md AI a). exact (hidc_grow (pa_hull A) H1 SUB a Ha). }
    assert (NRES' : sr_reserved (a_sec A) <= kChunksBlockCount <= kChunksBlockCount) by (rewrite NRES0; unfold kChunksBlockCount; lia).
    pose proof (sec_minv_grant1 A m md md1 n mbw key kChunksBlockCount AI SB1 HI1 NR30 GOK WF' NRES') as HI2. fold A' H1 in HI2.
    pose proof (g_halted A m md md1 n mbw AI SB1) as HH2.
    (first [ pose proof ((hit_depot_wf A m md AI)) as dR_19; dand7 dR_19 as DND DLEN DTOT3 DKEY DINC DNDk DNN | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & DTOT3 & DKEY & DINC & DNDk & DNN) ]).
    (first [ pose proof ((sec_dkeys A WF0)) as dR_20; dand3 dR_20 as DK1 _ DK3 | pose proof (sec_dkeys A WF0) as (DK1 & _ & DK3) ]).
    assert (KL : (1 <= length key <= 255)%nat) by exact (proj1 (Forall_forall _ _) DK1 key KEYU).
    assert (DTOT : depot_total (a_depot A) + 1 + Z.of_nat (length key) < kStackStoreBlockFrames).
    { (first [ pose proof ((wfD A WF0)) as dR_21; dand3 dR_21 as INC NDd _ | destruct (wfD A WF0) as (INC & NDd & _) ]).
      assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk)).
      (first [ pose proof ((depot_universe_bounds _ _ DK1 DK3 NDd INC')) as dR_22; dand3 dR_22 as L1 _ L3 | pose proof (depot_universe_bounds _ _ DK1 DK3 NDd INC') as (L1 & _ & L3) ]). unfold kStackStoreBlockFrames. clear - L1 L3 KL. lia. }
    (first [ pose proof ((sb_facts A WF0)) as dR_23; dand5 dR_23 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]). unfold a_b6 in HB6, RSB.
    (first [ pose proof ((sec_pa A m md AI)) as dR_24; dand3 dR_24 as PA1 PA2 PA3 | pose proof (sec_pa A m md AI) as (PA1 & PA2 & PA3) ]).
    pose proof (APART _ _ _ E0) as Dm0. pose proof (APART _ _ _ E7) as Dm7. pose proof (APART _ _ _ E8) as Dm8.
    pose proof (bm_sep A 1 4 _ _ _ _ WF0 E1 E4 ltac:(lia)) as D14. pose proof (bm_sep A 1 5 _ _ _ _ WF0 E1 E5 ltac:(lia)) as D15.
    pose proof (bm_sep A 1 7 _ _ _ _ WF0 E1 E7 ltac:(lia)) as D17. pose proof (bm_sep A 1 8 _ _ _ _ WF0 E1 E8 ltac:(lia)) as D18.
    unfold a_b6, a_sb, a_pa, a_thr, a_ctx, a_nodes0, a_frames0 in Dm0, Dm7, Dm8, D14, D15, D17, D18.
    Ltac o_sides GL CLO LOSA SAHI TH1 TH2 CT1 CT2 STM AOBJ MBC HB6 RSB SCE Dm0 Dm4 Dm5 Dm7 Dm8 Dm1 NC1 NC2 NC3 D14 D15 D17 D18 PA1 PA2 PA3 SOB DN01 DN02 DF01 DF02 NCHZ NRES0 :=
      lazymatch goal with
      | |- 64513 <= n < 2^31 => clear - NR; unfold kMaxPrimaryUser in NR; lia
      | |- kMaxPrimaryUser < n < 2^31 => clear - NR; unfold kMaxPrimaryUser in *; lia
      | |- alloc_ceiling <= _ <= _ => clear - CLO LOSA; lia
      | |- _ + 65536 < 2^64 => clear - SAHI; lia
      | |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by (clear - GL; kung_all; lia); reflexivity
      | |- @eq Z _ _ => first [reflexivity | clear - NCHZ NRES0; lia]
      | |- aobj (p_thr _) 4096 /\ _ => exact (conj TH1 TH2)
      | |- aobj (p_ctx _) _ /\ _ => exact (conj CT1 CT2)
      | |- rw_cells _ _ (_ + 2872) _ => replace (p_thr (a_pl A) + 2872) with (p_thr (a_pl A) + 2800 + 72) by lia; exact STM
      | |- aobj (bv_unsigned _) _ /\ _ => exact (conj AOBJ MBC)
      | |- kHighMemBeg <= a_sb A /\ _ => clear - HB6 RSB SCE; kung_all; lia
      | |- apart (bv_unsigned _) _ (a_sb A) _ => unfold apart; clear - Dm0 HB6 RSB; kung_all; lia
      | |- apart (bv_unsigned _) _ (p_thr _) _ => unfold apart; clear - Dm4; lia
      | |- apart (bv_unsigned _) _ (p_ctx _) _ => unfold apart; clear - Dm5; lia
      | |- apart (bv_unsigned _) _ (p_nodes0 _) _ => unfold apart; clear - Dm7; kung_all; lia
      | |- apart (bv_unsigned _) _ (p_frames0 _) _ => unfold apart; clear - Dm8; kung_all; lia
      | |- apart (bv_unsigned _) _ (p_pa _) _ => unfold apart; clear - Dm1 NC1 NC2 NRES0; kung_all; lia
      | |- apart (p_pa _) _ (p_thr _) _ => unfold apart; clear - D14 NC1 NC2 NRES0; kung_all; lia
      | |- apart (p_pa _) _ (p_ctx _) _ => unfold apart; clear - D15 NC1 NC2 NRES0; kung_all; lia
      | |- apart (p_pa _) _ (p_nodes0 _) _ => unfold apart; clear - D17 NC1 NC2 NRES0; kung_all; lia
      | |- apart (p_pa _) _ (p_frames0 _) _ => unfold apart; clear - D18 NC1 NC2 NRES0; kung_all; lia
      | |- 0 <= _ <= sr_reserved _ /\ _ => clear - NC1 NC2; kung_all; lia
      | |- aobj (p_pa _) _ /\ _ => split; [apply (aobj_sub _ _ _ _ PA1); clear - NC1 NC2 NC3 PA2 NRES0; kung_all; lia
                                   | split; [clear - PA2 NC1 NC2 NRES0; kung_all; lia| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact PA3]]]
      | |- _ mod 4096 = 0 /\ _ + 131072 <= alloc_ceiling => split; [exact PA3| clear - PA2; kung_all; lia]
      | |- 0 <= 0 < 256 /\ _ => lia
      | |- bv_unsigned _ <= _ /\ _ + 2064 <= 2^47 => clear - SOB SAHI; lia
      | |- aobj (p_nodes0 _) _ /\ _ => exact (conj DN01 DN02)
      | |- aobj (p_frames0 _) _ /\ _ => exact (conj DF01 DF02)
      | |- Z.of_nat _ = 0 /\ sr_reserved _ = 0 => exact (conj NCHZ NRES0)
      end.
    eapply (srz_evt_restrict rsegs H1 HOFF1 pa_wx _ (pa_eager A + ms) _ _ md2 T1 HI2 HH2).
    { rewrite restrict_MS. fold m3.
      eapply (sec_o3b_a8 rac spa gp (cl_tp LPA) t0' t1' t2' s0 s1 (wz ms) (wz 3) (wz 34) (wz (-1)) (wz 0) a6' (wz 222)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' (wz ms) mbw F fc m3 lo n stkobj canfill pa_tsd (p_ctx (a_pl A)) thr (a_sb A) mb
                q d e dc ru (p_pa (a_pl A)) nch (sr_reserved (a_sec A)) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) junk0 scrL scrM old1 key 0 0 cs
                na nf ca mx (wz 0) sta stm v0 v1 v2 vl mm72 mm80 (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0)
                (Z_to_bv 8 0) (Z_to_bv 8 0) bsl (a_depot A) olds oll (repeat (Z_to_bv 8 0) (Z.to_nat 4096)) oldp depot_repL).
      all: try eassumption.
      all: o_sides GL CLO LOSA SAHI TH1 TH2 CT1 CT2 STM AOBJ MBC HB6 RSB SCE Dm0 Dm4 Dm5 Dm7 Dm8 Dm1 NC1 NC2 NC3 D14 D15 D17 D18 PA1 PA2 PA3 SOB DN01 DN02 DF01 DF02 NCHZ NRES0. }
    (* [comment removed for export] *)
    intros msr4 md4 Q4 HI4 SB4 CL4.
    (first [ dex11 Q4 as t0e t1e t2e a6e t3e t4e t5e t6e scrX olt m4; dand36 Q4 as -> MU34 WM34 MI4 ST4 LZR FRX PCo4 TC4 AF1' AF2' AF44' AF52' LS1' LS2' HK' SBc' PGS' LPA8' LPA16' Lgotcf' Lmlim' CF260' TH0' CT8' STS4 STM4 STL4 HW4 CIDX4 ABH4 HDR4 USR4 SHH4 SHL4 dR_Q4_t0; dand13 dR_Q4_t0 as SHU4 SHP4 SHT4 LREG4 LSTA4 LMTX4 GST4 DR4 TRC4 TRB4 FRA4 FRC4 FRL4 | dand36 Q4 as t0e t1e t2e a6e t3e t4e t5e t6e scrX olt m4 -> MU34 WM34 MI4 ST4 LZR FRX PCo4 TC4 AF1' AF2' AF44' AF52' LS1' LS2' HK' SBc' PGS' LPA8' LPA16' Lgotcf' Lmlim' CF260' TH0' dR_Q4_t0; dand24 dR_Q4_t0 as CT8' STS4 STM4 STL4 HW4 CIDX4 ABH4 HDR4 USR4 SHH4 SHL4 SHU4 SHP4 SHT4 LREG4 LSTA4 LMTX4 GST4 DR4 TRC4 TRB4 FRA4 FRC4 FRL4 | destruct Q4 as (t0e & t1e & t2e & a6e & t3e & t4e & t5e & t6e & scrX & olt & m4 & -> & MU34 & WM34 & MI4 & ST4 & LZR & FRX & PCo4 & TC4
                    & AF1' & AF2' & AF44' & AF52' & LS1' & LS2' & HK' & SBc' & PGS' & LPA8' & LPA16' & Lgotcf' & Lmlim' & CF260' & TH0' & CT8'
                    & STS4 & STM4 & STL4 & HW4 & CIDX4 & ABH4 & HDR4 & USR4 & SHH4 & SHL4 & SHU4 & SHP4 & SHT4 & LREG4 & LSTA4 & LMTX4 & GST4 & DR4
                    & TRC4 & TRB4 & FRA4 & FRC4 & FRL4) ]).
    rewrite unrestrict_MSsvc. cbn [ms_mem] in CL4.
    assert (CL4' : forall a, hidc H1 a = true -> m4 a = None) by exact CL4.
    assert (HH4 : m_halted md4 = None) by (rewrite (same_but_materialized_halted _ _ SB4); exact HH2).
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms4 := ms) end.
    pose proof (c_gate A m md md1 n mbw AI SB1 NR30 GOK md4 SB4) as GATE.
    pose proof (c_contained A m md md1 n mbw kChunksBlockCount AI SB1 NR30 GOK NRES' md4 SB4) as CONT.
    assert (A0E : ms_gpr ms4 0 = wz (p_pa (a_pl A))) by (subst ms4; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A1E : ms_gpr ms4 1 = wz 0x20000) by (subst ms4; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (PRU4 : page_round_up_Z (bv_unsigned (ms_gpr ms4 1)) = 8 * kChunksBlockCount).
    { rewrite A1E, unsigned_lit by lia. unfold page_round_up_Z, page_size, kChunksBlockCount. reflexivity. }
    assert (BR : pa_eager A + ms + 0x20000 + hull_bytes (pa_lhull A') <= vm_limit (m_vmmaps md4)).   (* [comment removed for export] *)
    { fold H1 in HI4. exact (c_budget_room A m md md1 n mbw key kChunksBlockCount AI SB1 WF' md4 (pa_eager A + ms) SB4 HI4 eq_refl eq_refl NRES0). }
    eapply (srz_mmap_fixed_rw_contained_nf rsegs ms4 md4 (wz 222) (wz 50) T1 HH4 eq_refl eq_refl).
    - unfold mmap_fixed_args. subst ms4. rewrite !ms_gpr_MSsvc. simp_regs. split; [| rsplit; reflexivity].
      intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
    - exact fixed_rw_shape_plain.
    - rewrite PRU4, A0E. exact GATE.
    - unfold fixed_contained. rewrite PRU4, A0E. exact CONT.
    - rewrite PRU4, A0E. exact (c_budget A m md md1 n mbw key kChunksBlockCount AI SB1 NR30 GOK NRES' md4 (pa_eager A + ms) SB4 HI4 BR).
    - (* [comment removed for export] *)
      rewrite !PRU4, !A0E. subst ms4.
      rewrite advance_apply_MSsvc, mkR_set_a0, lit_add_lit. change (ANodeA7.mmap_ecall_pc + 4) with ANodd09.mmap_after_pc.
      change (apply_unmaps ?mm []) with mm. cbn [apply_writes].
      set (M5 := apply_zeros (munrestrict (hidc H1) M2 m4) [(wz (p_pa (a_pl A)), wz (8 * kChunksBlockCount))]).
      set (md5 := commit_model (wz 50) (wz (p_pa (a_pl A))) (wz (8 * kChunksBlockCount)) false md4).
      set (m5 := mrestrict (hidc H1) M5).
      assert (ZSPEC5 : forall x : word, M5 x = if in_range (p_pa (a_pl A)) 131072 x then Some (Z_to_bv 8 0) else munrestrict (hidc H1) M2 m4 x).
      { intros x. subst M5. change (Z_to_bv 64 (p_pa (a_pl A))) with (wa (p_pa (a_pl A))). unfold kChunksBlockCount.
        change (8 * 2 ^ 14) with 131072. apply apply_zeros_spec; clear - GL; lia. }
      assert (VISp : forall x, p_pa (a_pl A) <= x < p_pa (a_pl A) + 131072 -> hidc H1 (wz x) = false).
      { intros x Hx. unfold hidc. apply negb_false_iff. apply (in_hullb_intro _ _ (p_pa (a_pl A)) (p_pa (a_pl A) + 8 * kChunksBlockCount)); [| rewrite unsigned_lit by (clear - GL Hx; lia); unfold kChunksBlockCount; clear - Hx; lia].
        apply SUB. apply pa_hull_region. apply fixed_in_aregions. unfold fixed_regions_. cbn [In]. do 10 right. left. reflexivity. }
      assert (Z5 : zrange m5 (p_pa (a_pl A)) 131072).
      { intros i Hi. subst m5. unfold mrestrict. rewrite (VISp (p_pa (a_pl A) + i)) by lia. rewrite ZSPEC5.
        unfold in_range. rewrite unsigned_lit by (clear - GL Hi; lia).
        replace ((p_pa (a_pl A) <=? p_pa (a_pl A) + i) && (p_pa (a_pl A) + i <? p_pa (a_pl A) + 131072)) with true; [reflexivity|].
        symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      assert (MU45 : munch [(p_pa (a_pl A), p_pa (a_pl A) + 131072)] m4 m5).
      { intros x OUT. cbn [outside] in OUT. destruct OUT as [O1 _]. subst m5. unfold mrestrict. destruct (hidc H1 x) eqn:V1.
        - symmetry. exact (CL4 x V1).
        - rewrite ZSPEC5. unfold in_range. replace ((p_pa (a_pl A) <=? bv_unsigned x) && (bv_unsigned x <? p_pa (a_pl A) + 131072)) with false.
          + unfold munrestrict. rewrite V1. reflexivity.
          + symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (bv_unsigned x) (p_pa (a_pl A))) as [l|g]; [left; apply Z.leb_gt; clear - l; lia| right; apply Z.ltb_ge; clear - O1 g; lia]. }
      assert (WM45 : wmono rsegs m4 m5).
      { intros x Hx. unfold wview in *. subst m5. unfold mrestrict. destruct (hidc H1 x) eqn:V1.
        - rewrite (CL4' x V1) in Hx. exact Hx.
        - rewrite ZSPEC5. destruct (in_range (p_pa (a_pl A)) 131072 x); [discriminate|]. unfold munrestrict. rewrite V1. exact Hx. }
      assert (MI5 : mem_inv rsegs m5).
      { intros a b Hab. subst m5. unfold mrestrict in Hab. destruct (hidc H1 a) eqn:V1; [discriminate|]. rewrite ZSPEC5 in Hab.
        destruct (in_range (p_pa (a_pl A)) 131072 a) eqn:IR.
        - unfold in_range in IR. apply andb_true_iff in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
          destruct (ro_addr rsegs a) eqn:RO; [| reflexivity]. exfalso. pose proof (proj1 (pa_ro_addr_iff _) RO) as ROr. clear - ROr I1 I2 GL Gp. lia.
        - unfold munrestrict in Hab. rewrite V1 in Hab. exact (MI4 a b Hab). }
      pose proof (sec_minv_commit A m md md1 n mbw key kChunksBlockCount AI SB1 NR30 GOK NRES' md4 (pa_eager A + ms) SB4 HI4 BR) as HI5. fold md5 in HI5.
      pose proof (c_halted A m md md1 n mbw AI SB1 md4 SB4) as HH5. fold md5 in HH5.
      (* [comment removed for export] *)
      clear MU13g WM13g. unfold kDepotNodesBlock, kStackStoreBlockBytes, kPtrArrayReserve in D14, D15, D17, D18.
      unfold ASecComb.LMA, ASecComb.LSTAT, ARtSf1m.LMA, ARtSf1m.LSTAT, ANodeA7.CF, off_th_stats, sh, kShadowOffset in *.
      pose proof (conj GL (conj Gp (conj Dm1 (conj D14 (conj Gt (conj MBI (conj TPL (conj TSDL (conj Gc (conj QSH (conj RUB (conj DCE (conj NDE0 (conj ER (conj OL D15))))))))))))))) as KEEP5.
      rewrite NRES0 in LREG4. rewrite NCHZ in LREG4.
      transport_keep_t rsegs m4 m5 MU45 WM45 ltac:(clear - GL Gp Dm1 D14 Gt MBI TPL TSDL Gc QSH RUB DCE NDE0 ER OL D15).
      assert (SHP5 : e <> 0 -> rw_cells rsegs m5 (q + 256 + d + 2147450880) [C1 oldp]).
      { intros NE0. specialize (SHP4 NE0). transport_keep_t rsegs m4 m5 MU45 WM45 ltac:(clear - GL Gp Dm1 D14 Gt MBI TPL TSDL Gc QSH RUB DCE NDE0 ER OL D15). exact SHP4. }
      assert (TC5 : thread_cells m5 (cl_tp LPA) pa_tsd (p_ctx (a_pl A)) thr).
      { (first [ dand6 TC4 as X1 X2 X3 X4 X5 X6 | destruct TC4 as (X1 & X2 & X3 & X4 & X5 & X6) ]).
        repeat match goal with |- _ => idtac end.
        eapply (ro_cells_transport rsegs _ m4 m5) in X1; [| exact MU45| cbn [disjoint_from]; simpl_sizes; clear - GL Gp; lia].
        eapply (ro_cells_transport rsegs _ m4 m5) in X2; [| exact MU45| cbn [disjoint_from]; simpl_sizes; clear - GL Gp; lia].
        eapply (ro_cells_transport rsegs _ m4 m5) in X3; [| exact MU45| cbn [disjoint_from]; simpl_sizes; clear - GL Gp TPL; lia].
        eapply (ro_cells_transport rsegs _ m4 m5) in X4; [| exact MU45| cbn [disjoint_from]; simpl_sizes; clear - GL Gp TSDL; lia].
        eapply (ro_cells_transport rsegs _ m4 m5) in X5; [| exact MU45| cbn [disjoint_from]; simpl_sizes; clear - GL Gp Gc D15; lia].
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 X6))))). }
      assert (PCo5 : poison_consts m5).
      { (first [ dand13 PCo4 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 | destruct PCo4 as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13) ]).
        Ltac trp X MU45 GL Gp := eapply (ro_cells_transport rsegs _ _ _) in X; [| exact MU45| cbn [disjoint_from]; simpl_sizes; clear - GL Gp; lia].
        trp X1 MU45 GL Gp. trp X2 MU45 GL Gp. trp X3 MU45 GL Gp. trp X4 MU45 GL Gp. trp X5 MU45 GL Gp. trp X6 MU45 GL Gp. trp X7 MU45 GL Gp.
        trp X8 MU45 GL Gp. trp X9 MU45 GL Gp. trp X10 MU45 GL Gp. trp X11 MU45 GL Gp. trp X12 MU45 GL Gp. trp X13 MU45 GL Gp.
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 (conj X9 (conj X10 (conj X11 (conj X12 X13)))))))))))). }
      assert (DR5 : depot_repL AL_pboth rsegs (a_depot A) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) m5).
      { apply (DRF _ m4 m5 DR4). intros a Ha. apply MU45.
        unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes, kDepotTabBytes in Ha.
        rewrite unsigned_lit by (clear - Ha GL Gn0 Gf0; lia). cbn [outside].
        pose proof (conj GL (conj Gp (conj D17 D18))) as KEEP3. unfold kDepotNodesBlock, kStackStoreBlockBytes in KEEP3.
        destruct Ha as [Ha|[Ha|Ha]]; (split; [lia2 Ha KEEP3| exact I]). }
      assert (Zp : zrange m5 (p_pa (a_pl A) + 8 * 0) (8 * Z.of_nat 1)) by (apply (zrange_sub _ _ _ _ _ Z5); clear; lia).
      pose proof (zrange_C8s m5 (p_pa (a_pl A) + 8 * 0) ltac:(clear - Gp NRu GL; lia) 1%nat ltac:(clear - GL; lia) Zp) as PAN. cbn [map repeat] in PAN.
      (* [comment removed for export] *)
      eapply (srz_evt_restrict rsegs H1 HOFF1 pa_wx _ (pa_eager A + ms + 0x20000) _ _ md5 T1 HI5 HH5).
      { rewrite restrict_MS. fold m5.
        eapply (sec_o4_a8 rac spa gp (cl_tp LPA) t0e t1e t2e s0 s1 (wz 0x20000) (wz 3) (wz 50) (wz (-1)) (wz 0) a6e (wz 222)
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3e t4e t5e t6e (wz (p_pa (a_pl A))) F fc m5 lo n stkobj canfill pa_tsd (p_ctx (a_pl A)) thr (a_sb A) mb
                  q d e dc ru (p_pa (a_pl A)) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) junk0 scrL key 0 0 cs
                  na nf ca mx (wz 0) (wz 0) sta stm v0 v1 v2 vl mm72 mm80 (wz 0) (wz 0) (wz 0) (wz 0) (wz 0)
                  (Z_to_bv 8 0) (Z_to_bv 8 0) bsl (a_depot A) olds oll (repeat (Z_to_bv 8 0) (Z.to_nat 4096)) olt scrX oldp depot_repL).
        all: try eassumption.
        all: o_sides GL CLO LOSA SAHI TH1 TH2 CT1 CT2 STM4 AOBJ MBC HB6 RSB SCE Dm0 Dm4 Dm5 Dm7 Dm8 Dm1 NC1 NC2 NC3 D14 D15 D17 D18 PA1 PA2 PA3 SOB DN01 DN02 DF01 DF02 NCHZ NRES0. }
      idtac "stage 4 ok".
      (* [comment removed for export] *)
      intros msr6 md6 Q6 HI6 SB6 CL6.
      (first [ dex23 Q6 as t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f ca' mx' sta' stm' v0' v1' v2' m6 md0; dand27 Q6 as -> MU56 WM56 MI6 ST6 P_reg P_sta P_mtx P_shdr P_cidx P_slot P_gst P_sts P_stm P_stl P_hdr P_lch P_usr P_sh512 P_shl P_sht P_shz P_wr P_she P_dr MUd WMd | dand36 Q6 as t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f ca' mx' sta' stm' v0' v1' v2' m6 md0 -> MU56 WM56 MI6 ST6 P_reg P_sta P_mtx P_shdr P_cidx P_slot P_gst dR_Q6_t0; dand15 dR_Q6_t0 as P_sts P_stm P_stl P_hdr P_lch P_usr P_sh512 P_shl P_sht P_shz P_wr P_she P_dr MUd WMd | destruct Q6 as (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & ca' & mx' & sta' & stm' & v0' & v1' & v2' & m6 & md0
                      & -> & MU56 & WM56 & MI6 & ST6 & P_reg & P_sta & P_mtx & P_shdr & P_cidx & P_slot & P_gst & P_sts & P_stm & P_stl & P_hdr & P_lch
                      & P_usr & P_sh512 & P_shl & P_sht & P_shz & P_wr & P_she & P_dr & MUd & WMd) ]).
      rewrite unrestrict_MS. cbn [ms_mem] in CL6.
      lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
      set (m' := munrestrict (hidc H1) M5 m6).
      assert (VIEW : aview_of H1 m' = m6).
      { unfold aview_of. subst m'. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL6. }
      pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM13 WM34) WM45) WM56) as WM06.
      pose proof (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM34 WM45) WM56) as WM36.
      assert (NN6 : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> vv (wz a) <> None -> m6 (wz a) <> None).
      { intros a Ha0 Ha1 Ha2. apply (wmono_NN _ _ a WM06); [exact Ha1| clear - Ha0 Ha2; lia]. }
      (* [comment removed for export] *)
      pose proof (conj GL (conj QSH (conj RUB (conj DCE (conj NDE0 (conj ER (conj NS2 (conj RGE (conj RLT (conj RUF (conj MSE (conj RU8 (conj ABQ (conj LOSA NCHZ)))))))))))))) as KEEP.
      assert (MU06 : munch (sec_W lo sa thr mb ms (p_pa (a_pl A)) nch pahi (p_nodes0 (a_pl A)) (p_frames0 (a_pl A))) vv m6).
      { apply (munch_trans _ vv m3 m6).
        - eapply (munch_weaken _ _ vv m3); [| exact MU13].
          unfold sub_fp, sec_W. rewrite INST_val. unfold off_th_stats, off_sec_n_reserved, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_sec_mutex, off_global_stats, sh.
          kung_all. cbn [outside]. (intros a; (first [ intro dR_32; dand12 dR_32 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 _ | intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & _) ])).
          split; [exact X1| split; [exact X10| split; [exact X11| exact I]]].
        - apply (munch_trans _ m3 m4 m6).
          + eapply (munch_weaken _ _ m3 m4); [| exact MU34].
            unfold sub_fp, sec_W. rewrite INST_val. unfold off_th_stats, off_sec_n_reserved, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_sec_mutex, off_global_stats, sh.
            kung_all. cbn [outside app]. (intros a; (first [ intro dR_33; dand12 dR_33 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 _ | intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & _) ])).
            solve_outs (1::1::11::11::10::2::4::1::nil)%Z X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 KEEP.
          + apply (munch_trans _ m4 m5 m6).
            * eapply (munch_weaken _ _ m4 m5); [| exact MU45].
              unfold sub_fp, sec_W. rewrite INST_val. kung_all. cbn [outside]. (intros a; (first [ intro dR_34; dand12 dR_34 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 _ | intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & _) ])).
              split; [lia2 X6 KEEP| exact I].
            * eapply (munch_weaken _ _ m5 m6); [| exact MU56].
              unfold sub_fp, sec_W, sec_fin_W. rewrite INST_val. unfold ASecComb.LMA, ASecComb.LSTAT, ARtSf1m.LMA, ARtSf1m.LSTAT, off_th_stats, off_sec_n_reserved, off_sec_chunks_sorted,
                off_sec_stat_n_allocs, off_sec_mutex, off_global_stats, sh. kung_all. cbn [outside app].
              (intros a; (first [ intro dR_35; dand12 dR_35 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 _ | intros (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & _) ])).
              solve_outs (1::3:: 1::3::4::4::10::6::5::10::7::8::9::10::11::11::11::11::2::2::10::10::10::nil)%Z X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 KEEP. }
      (* [comment removed for export] *)
      pose proof (b1_final_ok 0 ltac:(lia)) as [B1R B1M]. change (bv_unsigned (Z_to_bv 8 0)) with 0 in P_hdr.
      assert (IDR : 0 <= snd (depot_putC (a_depot A) key) < 2^32) by (pose proof (depot_putC_id_range (a_depot A) key); clear - H DLEN; lia).
      replace (0 + 1) with (nch + 1) in P_reg by (rewrite NCHZ; reflexivity).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 nch) in P_cidx by (rewrite NCHZ; reflexivity).
      replace (p_pa (a_pl A) + 8 * 0) with (p_pa (a_pl A) + 8 * nch) in P_slot by (rewrite NCHZ; reflexivity). rewrite (Z_to_bv_bv_unsigned mbw) in P_slot.
      assert (SHAB : q + 2147450880 = sh (sec_alloc_beg mb)) by (unfold sh, sec_alloc_beg, kPageSize, kShadowOffset; clear - ABQ; rewrite ABQ; rewrite (Z.mul_comm 8 q), Z.div_mul by lia; lia).
      unfold kShadowOffset in P_shl, P_shz, P_she, P_sht, P_wr. rewrite SHAB in P_shl.
      replace (q + 256 + 2147450880) with (sh (sec_alloc_beg mb) + 256) in P_shz by (clear - SHAB; lia).
      replace (q + 256 + 2147450880) with (sh (sec_alloc_beg mb) + 256) in P_wr by (clear - SHAB; lia).
      replace (q + 256 + d + 2147450880) with (sh (sec_alloc_beg mb) + 256 + d) in P_she by (clear - SHAB; lia).
      replace (q + 256 + dc + 2147450880) with (sh (sec_alloc_beg mb) + 256 + (n / 8 + Z.min (n mod 8) 1)) in P_sht by (clear - DCE SHAB; subst d e; lia).
      replace (ru - 256 - dc) with ((ms - 4096) / 8 - 256 - (n / 8 + Z.min (n mod 8) 1)) in P_sht by (clear - DCE; subst d e ru; lia).
      subst d e.
      assert (P_pamap : mapped m6 (p_pa (a_pl A)) (8 * kChunksBlockCount)).
      { intros i Hi. apply (wmono_NN m5 m6 _ WM56); [right; clear - Gp Hi NRu GL; kung_all; lia| clear - GL Hi; kung_all; lia|].
        unfold kChunksBlockCount in Hi. rewrite (Z5 i ltac:(clear - Hi; lia)). discriminate. }
      assert (P_mapall : mapped m6 mb ms).
      { intros i Hi. apply (wmono_NN m3 m6 _ WM36); [right; clear - MBI Hi; lia| clear - GL Hi; lia|]. rewrite (Z3 i Hi). discriminate. }
      pose proof SEP_n0t as Sn0t. pose proof SEP_f0t as Sf0t. unfold apart in Sn0t, Sf0t. unfold kDepotNodesBlock, kStackStoreBlockBytes in Sn0t, Sf0t.
      assert (P_mu2 : forall a, depot_foot AL_pboth (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a -> m6 (wz a) = md0 (wz a)).
      { intros a Ha. apply MUd. unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha.
        rewrite unsigned_lit by (clear - Ha GL Gn0 Gf0; lia). unfold sec_fin_W2. cbn [outside]. kung_all.
        pose proof (conj GL (conj Gm (conj Gn0 (conj Gf0 (conj Dm7 (conj Dm8 (conj Sn0t (conj Sf0t (conj QSH (conj RUB (conj DCE Gt))))))))))) as KEEP2.
        (* [comment removed for export] *) clear - Ha KEEP2; repeat match goal with H : _ /\ _ |- _ => destruct H end; destruct Ha as [Ha|[Ha|Ha]]; repeat match goal with H : _ /\ _ |- _ => destruct H end; split_all; try exact I; first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.rlia_loc_tiers | Zify.zify; xlia zchecker ]. }
      pose proof (sec_arepr A m md n mbw key lo sa m6 pahi AI NR30 CLO MBA MB0 MBC RF PAHI MU06 NN6 md0 _ _
                    P_reg P_mtx P_shdr P_cidx P_slot P_pamap P_mapall B1R B1M IDR P_hdr P_lch P_sh512 P_shl P_shz P_she P_sht P_dr P_mu2) as AREPR.
      (* [comment removed for export] *)
      (first [ pose proof ((sec_model_commit A m md md1 n mbw key kChunksBlockCount AI SB1 NR30 GOK NRES' md4 (pa_eager A + ms) SB4 HI4 md6 SB6)) as dR_30; dand5 dR_30 as LG CV TP FRm HH6 | destruct (sec_model_commit A m md md1 n mbw key kChunksBlockCount AI SB1 NR30 GOK NRES' md4 (pa_eager A + ms) SB4 HI4 md6 SB6) as (LG & CV & TP & FRm & HH6) ]).
      assert (EQE : pa_eager A' = pa_eager A + ms + 0x20000).
      { subst A'. rewrite sec_eager. rewrite NRES0. unfold kChunksBlockCount. clear. lia. }
      assert (AI' : @pa_ainv _ DepotRepL A' m' md6).
      { constructor.
        - exact WF'.
        - change (ahull_of pa_image_ivs AL_pboth A') with H1. rewrite VIEW. exact AREPR.
        - cbn [A' secA a_pl a_reg a_sec].
          apply (sec_hidden A m md n mbw key lo sa m6 pahi AI NR30 CLO MBA MB0 MBC RF PAHI MU06 NN6 P_sh512 P_shl P_shz P_she P_sht m').
          + intros a Ha. subst m'. unfold munrestrict at 1. replace (hidc H1 a) with true by (symmetry; exact Ha). rewrite ZSPEC5.
            destruct (in_range (p_pa (a_pl A)) 131072 a) eqn:IRp.
            * exfalso. unfold in_range in IRp. apply andb_true_iff in IRp as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
              pose proof (VISp (bv_unsigned a) (conj I1 I2)) as X. rewrite Z_to_bv_bv_unsigned in X. change (hidc H1 a = true) in Ha. rewrite X in Ha. discriminate.
            * unfold munrestrict at 1. replace (hidc H1 a) with true by (symmetry; exact Ha). rewrite ZSPEC.
              destruct (in_range mb ms a) eqn:IR.
              -- exfalso. unfold in_range in IR. apply andb_true_iff in IR as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
                 pose proof (VISg (bv_unsigned a) (conj I1 I2)) as X. rewrite Z_to_bv_bv_unsigned in X. change (hidc H1 a = true) in Ha. rewrite X in Ha. discriminate.
              -- change (hidc H1 a = true) in Ha. unfold munrestrict. rewrite (hidc_grow (pa_hull A) H1 SUB a Ha). reflexivity.
          + intros a Ha. subst m'. unfold munrestrict. replace (hidc H1 a) with false by (symmetry; exact Ha). reflexivity.
          + exact (ai_hidden _ _ _ _ _ _ _ AI).
        - cbn [A' secA a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
        - cbn [A' secA a_pl a_sec]. exact LG.
        - change (aeager_of A') with (pa_eager A'). rewrite EQE. exact HI6.
        - exact HH6.
        - cbn [A' secA a_pl a_sec]. exact CV.
        - exact TP. }
      (* [comment removed for export] *)
      replace (mb + 4096 + 2048) with (sec_user_beg mb) by (unfold sec_user_beg, kPageSize; lia).
      eapply (K1 t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f (sec_user_beg mb) A' m' md6 AI').
      + change (pa_hull A') with H1. rewrite VIEW. exact MI6.
      + exact FRm.
      + apply sec_hull_le.
      + intros ff. reflexivity.
      + reflexivity.
      + reflexivity.
      + intros c VG _. exact VG.
      + clear - GL; unfold sec_user_beg, kPageSize; lia.
      + exact (sec_live_old A vv mb n AR NR30 MBA APART).
      + apply sec_live_new.
      + intros q0 Hq. apply sec_live_other. exact Hq.
      + exact (sec_livebytes A vv mb n key kChunksBlockCount AR NR30 MBA APART).
      + apply sec_tinycred.
      + exact (sec_nlive A vv mb n key kChunksBlockCount AR NR30 MBA APART).
      + apply sec_seccred. exact NR30.
      + (* [comment removed for export] *)
        subst A'. unfold as_primcred. cbn [secA a_pcred]. rewrite (prim_cost_secondary n (proj1 NR30)). symmetry. apply Z.sub_0_r.
      + (* [comment removed for export] *)
        intros CF0 NRX. change (pa_hull A') with H1. rewrite VIEW. intros i Hi.
        destruct (Z_lt_le_dec i 4096) as [LT|GE].
        * destruct P_usr as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. unfold fill_result in B. rewrite CF0 in B. cbn [Z.eqb] in B.
          (first [ dand3 B as _ _ B | destruct B as (_ & _ & B) ]). specialize (B (Z.to_nat i) ltac:(rewrite repeat_length; clear - Hi LT; lia)). rewrite Z2Nat.id in B by (clear - Hi; lia).
          rewrite nth_error_repeat in B by (clear - Hi LT; lia). unfold mrd, wa in B.
          replace (sec_user_beg mb + i) with (mb + 4096 + 2048 + i) by (unfold sec_user_beg, kPageSize; lia).
          destruct (m6 (Z_to_bv 64 (mb + 4096 + 2048 + i))) eqn:EM6; [congruence|].
          exfalso. rewrite pa_rom_high in B; [discriminate| rewrite unsigned_lit; clear - GL MBI Hi; lia].
        * rewrite <- (Z3 (6144 + i)) by (clear - GL Hi NS2 RGE RUF MSE; lia). replace (sec_user_beg mb + i) with (mb + (6144 + i)) by (unfold sec_user_beg, kPageSize; lia).
          transitivity (m5 (Z_to_bv 64 (mb + (6144 + i)))); [| transitivity (m4 (Z_to_bv 64 (mb + (6144 + i))))].
          -- apply MU56. rewrite unsigned_lit by (clear - GL Hi; lia). unfold sec_fin_W, ASecComb.LMA, ASecComb.LSTAT, ARtSf1m.LMA, ARtSf1m.LSTAT, sh. kung_all. cbn [outside app].
            split_all; try exact I;
              first [ clear - GL Gm Gp Gn0 Gf0 Hi GE QSH RUB DCE NDE0 ER NS2 RGE RLT RUF MSE ABQ MBI NCHZ; lia
                    | clear - GL Hi GE Dm1 Dm4 Dm7 Dm8 NC1 NC2 NS2 RGE RUF MSE NCHZ NRES0; lia ].
          -- apply MU45. rewrite unsigned_lit by (clear - GL Hi; lia). cbn [outside]. split; [clear - GL Hi GE Dm1 NS2 RGE RUF MSE; lia| exact I].
          -- apply MU34. rewrite unsigned_lit by (clear - GL Hi; lia). unfold ASecComb.LMA, ASecComb.LSTAT, ARtSf1m.LMA, ARtSf1m.LSTAT, sh. kung_all. cbn [outside app].
            split_all; try exact I;
              first [ clear - GL Gm Gp Gn0 Gf0 Hi GE QSH RUB DCE NDE0 ER NS2 RGE RLT RUF MSE ABQ MBI; lia
                    | clear - GL Hi GE Dm1 Dm4 Dm7 Dm8 NC1 NC2 NS2 RGE RUF MSE; lia ].
      + split; intros X; exfalso; [clear - X NRu; unfold kMaxPrimaryUser in X; lia|].
        unfold sec_user_beg, kPageSize in X. change (p_sb (a_pl A)) with (a_sb A) in X. clear - X Dm0 HB6 RSB GL. lia.
      + change (pa_hull A') with H1. rewrite VIEW. exact (sec_frame_ok A m md n mbw key lo sa m6 pahi AI NR30 CLO MBA MB0 MBC RF PAHI MU06 NN6 hi ltac:(clear - SAHI; lia) SMW).
      + change (pa_hull A') with H1. rewrite VIEW. intros i Hi. cbn [cl_errno LPA]. unfold mrd. rewrite (MU06 (Z_to_bv 64 (6191924 + i))); [reflexivity|].
        rewrite unsigned_lit by (clear - Hi; lia). apply (W_shape A m md n mbw lo sa pahi AI NR30 CLO MBA MB0 MBC RF PAHI); rewrite ?INST_val; unfold sh, kShadowOffset; clear - Hi GL Gm Gt Gp Gn0 Gf0 NCHZ; lia.
      + change (pa_hull A') with H1. rewrite VIEW. intros a Ha. apply MU06.
        rewrite unsigned_lit by (clear - Ha GL; lia). apply (W_shape A m md n mbw lo sa pahi AI NR30 CLO MBA MB0 MBC RF PAHI); rewrite ?INST_val; unfold sh, kShadowOffset; clear - Ha GL Gm Gt Gp Gn0 Gf0 SAHI NCHZ; lia.
      + change (pa_hull A') with H1. rewrite VIEW. exact ST6.
  Qed.
End GrantC2A8.

Section G2A8ok.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Definition sec_grant2_a8_stmt : Prop :=
  forall (rac spa gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n lo hi stkobj canfill : Z) (key : list Z) (T1 : TSet),
    let v := aview_of (pa_hull A) m in let sa := bv_unsigned spa in let thr := p_thr (a_pl A) in
    @pa_ainv _ DepotRepL A m md ->
    kMaxPrimaryUser < n < 2^30 + 1 ->
    sa mod 16 = 0 -> 0 <= canfill <= 1 ->
    alloc_ceiling <= lo -> lo <= sa - 4096 -> sa <= hi <= 2^47 -> mapped v lo (hi - lo) ->
    sa <= stkobj /\ stkobj + 2064 <= hi ->
    ro_cells rsegs v stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))] ->
    bytes_at rsegs v (stkobj + 16) (u64s (map (Z_to_bv 64) key)) ->
    In key (p_dkeys (a_pl A)) -> Forall (fun w => 0 <= w < 2^64) key ->
    as_livebytes A + n <= LIVE_MAX -> as_nlive A + 1 <= NLIVE_MAX -> 1 <= as_seccred A ->
    lma_mid_stmt -> lma_tail_stmt -> thread_stats_stmt -> poison_stmt -> poison0_stmt -> depot_put_stmt depot_repL ->
    lma_esp_stmt -> mapfixed_pre_stmt -> lma_espost_stmt ->
    alloc_core_K1v rac spa gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T1 ->
    forall (m1 : mem) (md1 : Model) (t0' t1' t2' a6' t3' t4' t5' t6' : word) (junk0 scrL scrM : list byte),
    munch [(lo, sa)] v m1 -> wmono rsegs v m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo (sa + -128 + -48 + -96 + -48) ->
    MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1 -> same_but_materialized md md1 ->
    (forall a, hidc (pa_hull A) a = true -> m1 a = None) ->
    rw_cells rsegs m1 (sa + -128) (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0) ->
    rw_cells rsegs m1 (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3731c)) ->
    rw_cells rsegs m1 (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1558) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)) ->
    rw_cells rsegs m1 (sa + -128 + -48 + -96 + -48) [CB 12 scrM; C4 (wz 34); C8 (wz (map_size n)); C8 (wz ASecComb.LMA); C8 (wz ASecComb.LSTAT); C8 (wz lma_mapret)] ->
    forall mbw : word,
    grant_okf (wz 34) (wz 0) md1 mbw (map_size n) = true ->
    Z.of_nat (length (sr_chunks (a_sec A))) = 0 /\ sr_reserved (a_sec A) = 0 ->
    srealizes (cl_segs LPA)
      (mkCfg (MS (mkR (wz mmapordie_resume) (wz (sa + -128 + -48 + -96 + -48)) gp (cl_tp LPA) t0' t1' t2'
                      (wz lma_name) (wz (map_size n)) mbw (wz (map_size n)) (wz 3) (wz 34) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz ANodeA7.PSC) (wz (needed_size2 n)) (wz (rz_size n)) (wz 8) (wz 0xb1558) (wz stkobj) (wz 7) (wz 7) (wz thr) (wz 1)
                      t3' t4' t5' t6')
                 F (wz ANodeA7.mmap_after_pc) fc None (apply_zeros (munrestrict (hidc (pa_hull A)) m m1) [(mbw, wz (map_size n))]) (seg_rom (cl_segs LPA)))
             (grant_model (wz 34) mbw (wz (map_size n)) false md1)) T1.

  Theorem sec_grant2_a8_ok : sec_grant2_a8_stmt.
  Proof.
    unfold sec_grant2_a8_stmt. intros until T1. cbv zeta. intros AI NR SPA CFL CLO LOSA SAHI SMW SOB TRC TRB KEYU KR LIM NLV SCRED LMID LTAIL TSS PS P0 DPS LESP MFP LESPOST K1.
    intros until scrM. intros MU1 WM1 MI1 ST1 HI1 SB1 CL1 FRA FRC FRL FRM mbw GOK NCH0.
    eapply sec_grant2_a8; eassumption.
  Qed.
End G2A8ok.
End ASeczyk.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g.AMal5j7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecr83 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecSrz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecA1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecFinB.ASecFin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB5.ASecB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecZ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodd09 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecG2S OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecBG2.ASeczyk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize in *.
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
(* [comment removed for export] *)
Ltac lia2 X K := clear - X K; lia.
(* [comment removed for export] *)
Ltac pick_out i X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K :=
  lazymatch i with
  | 1 => lia2 X1 K | 2 => lia2 X2 K | 3 => lia2 X3 K | 4 => lia2 X4 K | 5 => lia2 X5 K | 6 => lia2 X6 K
  | 7 => lia2 X7 K | 8 => lia2 X8 K | 9 => lia2 X9 K | 10 => lia2 X10 K | 11 => lia2 X11 K
  end.
Ltac solve_outs idxs X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K :=
  lazymatch idxs with
  | @nil _ => first [exact I | idtac]
  | @cons _ ?i ?rest => split; [pick_out i X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K | solve_outs rest X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 K]
  end.
(* [comment removed for export] *)
Ltac transport_keep segs m m' MU WM KEEP :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | clear - KEEP; cbn [disjoint_from]; simpl_sizes; slia ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | clear - KEEP; cbn [disjoint_from]; simpl_sizes; slia ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | clear - KEEP; cbn [disjoint_from]; simpl_sizes; slia ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | clear - KEEP; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
  | H : stk segs m ?loq ?hiq |- _ =>
      apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | clear - KEEP; cbn [disjoint_from]; slia ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section G2ok.
Context {Clg : Ceiling}.
  Theorem sec_grant2_ok : sec_grant2_stmt.
  Proof.
    unfold sec_grant2_stmt. intros until T1. cbv zeta. intros AI NR SPA CFL CLO LOSA SAHI SMW SOB TRC TRB KEYU KR LIM NLV SCRED LMID LTAIL TSS PS P0 DPS LESP MFP LESPOST K1.
    intros until scrM. intros MU1 WM1 MI1 ST1 HI1 SB1 CL1 FRA FRC FRL FRM mbw GOK NCH0.
    assert (NRU : kMaxPrimaryUser < n < 2^30 + 1) by (clear - NR; lia).
    eapply sec_grant2_a8_ok; eassumption.
  Qed.
End G2ok.
