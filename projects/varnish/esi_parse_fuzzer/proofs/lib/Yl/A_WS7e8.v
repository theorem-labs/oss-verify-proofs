(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp0e6 AIcpnnp AIcpya4 AIcpw0i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_WSvfw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_WSvfw.

Module A_WSg84.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpinq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpinq.RA_sfkt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp0e6 AIcpnnp AIcpya4 AIcpii0 AIcpinq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpii0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpinq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Po6qc A_World A_Img A_Cocsh A_Tac A_WSvfw.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, asan_memset_post, strlen_icpt_post, strcpy_req_icpt_post,
  WSASSERT_STACK, WSEMU_STACK, ASAN_MEMSET_STACK, STRLEN_ICPT_STACK, STRCPY_ICPT_STACK, h_ws, h_wsbuf in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia02
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@G2_03; @ACV; @G3; @SR; @G0; @SZ; @LO; @G2_08; @G2_09; @SPR; @LO0; @CEIL; @G2_05; @K; @G2_06; @G2_07; @H0; @Ha__; @GLE; @GGE; @GCE; @KS2; @G2_01; @G2_13; @G2_14; @Hx__])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition REQ8 : list byte :=
  Eval vm_compute in match image_bytes rsegs 0x217c0 8 with Some bs => bs | None => [] end.
Lemma REQ8_ro : ro_bytes_b rsegs 0x217c0 REQ8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma REQ8_eq : REQ8 = [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 113] ++ Z_to_bv 8 0 :: skipn 4 REQ8.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ws_zero_cells : list cell :=
  [ C4 (w64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C8 (w64 0); C8 (w64 0); C8 (w64 0) ].
Lemma ws_zero_cells_bytes : cells_bytes ws_zero_cells = repeat (Z_to_bv 8 0) 32.
Proof. vm_compute. reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI"] Lemma WS_Init_ok : WS_Init_stmt.
  Proof.
    unfold WS_Init_stmt.
    intros H junk40 junk32 lo. intros until v. intros A0 A1 A2 A3 WSC WEC GLOB HSH HV HG CE ST LO CEIL MI.
    rewrite A0, A1, A2, A3. cbn [vi_wsid VIA]. unfold WS_Init_entry, WSINIT_STACK, ICPT_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts. (* [comment removed for export] *) pose proof G2 as G2x__; dand17 G2x__ as G2_01 G2_02 G2_03 G2_04 G2_05 G2_06 G2_07 G2_08 G2_09 G2_10 G2_11 G2_12 G2_13 G2_14 G2_15 G2_16 G2_17. hide G2.
    pose proof (hff_al8 H 2976 HG eq_refl) as AL1. pose proof (hff_al8 H 3152 HG eq_refl) as AL2.
    pose proof (hff_al8 H 1536 HG eq_refl) as AL3.
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as _ SHC _ _ _ _ SHW _ _ SHB | pose proof HSH as (_ & SHC & _ & _ & _ & _ & SHW & _ & _ & SHB) ]). fold_cl_segs.
    (first [ pose proof ((shadowed_bss_cp v (proj1 CE))) as dR_3; dand8 dR_3 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_cp v (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs.
    cbn [vi_bss_cp VIA] in GLE, GGE.
    pose proof (global_shadow_pat v 0x217c0 4 32 (proj1 CE) ltac:(gdesc_in)) as SHQ.
    unfold h_ws, h_wsbuf, h_cp in SHC, SHW, SHB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2976) 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHWR. rewrite SHMAX_val in SHWR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 3152) 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as SHBR. rewrite SHMAX_val in SHBR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 1536) 752 ltac:(lia) ltac:(lia) ltac:(lia)) as SHCR. rewrite SHMAX_val in SHCR.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    pose proof (shpat_sh_boundL (Clg:=Clg) 0x217c0 4 ltac:(lia) ltac:(lia) ltac:(lia)) as SHQR. rewrite SHMAX_val in SHQR.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFR.
    change ((8192 + 7) / 8) with 1024 in SHFR. rewrite SHMAX_val in SHFR.
    (* [comment removed for export] *)
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (got_cp_cell v (proj1 CE)) as GOTC. unfold GOTA_cp in GOTC. cbn [vi_bss_cp VIA] in GOTC.
    (first [ pose proof ((asan_memset_cells_of_consts v (proj1 CE))) as dR_4; dand4 dR_4 as Gric Cric Crms _ | destruct (asan_memset_cells_of_consts v (proj1 CE)) as (Gric & Cric & Crms & _) ]).
    (first [ pose proof ((strlen_icpt_cells_of_consts v (proj1 CE))) as dR_5; dand5 dR_5 as CI Crsl Gcf Ccf _ | destruct (strlen_icpt_cells_of_consts v (proj1 CE)) as (CI & Crsl & Gcf & Ccf & _) ]).
    (first [ pose proof ((strcpy_icpt_cells_of_consts v (proj1 CE))) as dR_6; dand5 dR_6 as _ Gaf Crs Crsc _ | destruct (strcpy_icpt_cells_of_consts v (proj1 CE)) as (_ & Gaf & Crs & Crsc & _) ]).
    unfold asan_inited_cell in CI.
    (first [ pose proof (GLOB) as dR_7; dand4 dR_7 as _ BSS CP _ | pose proof GLOB as (_ & BSS & CP & _) ]). fold_cl_segs. cbn [vi_bss_cp VIA] in BSS. unfold h_cp in BSS, CP.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    assert (RQ : range_ok v 0x217c0 4).
    { eapply (global_range_ok v 0x217c0 4 32); [exact CE| gdesc_in| lia| lia| lia| unfold pa_static; lia| unfold pa_static; lia]. }
    assert (RW32 : range_ok v (h_ff H + 2976) 32).
    { eapply (shadowed_range_ok _ _ _ (h_ff H + 2976) 40); [exact SHW| exact AL1| lia| lia| lia| lia| unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; lia
        | apply HV; unfold HOBJ_END; lia| apply HV; unfold HOBJ_END; lia]. }
    assert (RW4 : range_ok v (h_ff H + 2980) 4).
    { eapply (shadowed_range_ok _ _ _ (h_ff H + 2976) 40); [exact SHW| exact AL1| lia| lia| lia| lia| unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; lia
        | apply HV; unfold HOBJ_END; lia| apply HV; unfold HOBJ_END; lia]. }
    clear HV.
    pose proof (munch_refl [(bv_unsigned sp - 4672, bv_unsigned sp); (h_ff H + 2976, h_ff H + 2976 + 40);
                            (h_ff H + 3152, h_ff H + 3152 + 32)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB rsegs v (h_ff H + 2976) [] 40 junk40 [] [32; 8]%nat WSC eq_refl) as WS0. clear WSC.
    cbn [mk_CB_cells app] in WS0.
    pose proof (proj1 (rw_cells_app rsegs v (h_ff H + 2976) [CB 32 (firstn 32 junk40)] [CB 8 (firstn 8 (skipn 32 junk40))]) WS0) as [WSA WSE].
    clear WS0. cbn [cells_size csize Nat.add] in WSE.
    pose proof (rwc_eq _ _ _ (h_ff H + 3008) _ WSE ltac:(cbn; lia)) as WSE'. clear WSE. rename WSE' into WSE.
    pose proof (rw_cells_split_CB rsegs v (h_ff H + 3152) [] 32 junk32 [] [4; 4; 8; 8; 8]%nat WEC eq_refl) as WE1. clear WEC.
    cbn [mk_CB_cells app] in WE1.
    unfold h_ws, h_wsbuf, h_cp in *.
    open_map_cells MC.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_addr_at SHG 6191712 8.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    zstep. zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ] ].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. shadow_chk SHC 1 12. zstep. (* [comment removed for export] *) match goal with |- context [ zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn ?zk (repeat (Z_to_bv 8 0) ?zn))))) ] => replace (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn zk (repeat (Z_to_bv 8 0) zn)))))) with (Z_to_bv 64 0) by (vm_compute; reflexivity) end. zstep. zstep. kdead2.
    (* [comment removed for export] *)
    zstep. kdead. zstep. zstep. if_cases K; zify_cond K. { paok K HG. } clear K.
    zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    icall asan_memset_spec by
      (rewrite ?unsigned_lit by lia;
       first [ exact WSA | exact ST | exact CEIL | rebundle
             | unfold ASAN_MEMSET_STACK; lia
             | (left; lia)
             | lia
             | (right; eapply range_ok_high_munch; [exact RW32| exact MU| lia| lia| lia| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia])
             | assumption ]).
    lazymatch goal with X : rw_cells _ ?mx (h_ff H + 2976) [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into WSZ end.
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    change (Z.to_nat 32) with 32%nat in WSZ. change (0 mod 256) with 0 in WSZ.
    apply (rw_cells_recast rsegs _ _ _ ws_zero_cells) in WSZ; [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | exact ws_zero_cells_bytes].
    unfold ws_zero_cells in WSZ.
    (* [comment removed for export] *)
    shadow_chk SHW 4 11.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk0 SHW 8. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHW 8.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_addr_at SHQ 137152 1.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    lazymatch goal with |- evt ?segs ?Q _ =>
      eapply (evt_cut segs _ Q);
      [ zstep;
        let K := fresh "KS" in
        zstep; if_cases K; zify_cond K;
        [ first [ shadow_fast K; shadow_join 11 | shadow_dead | shadow_slow 11 ]
        | first [ shadow_fast K; shadow_join 11 | shadow_dead | shadow_slow 11 ] ]
      | let ms := fresh "ms" in let x := fresh "junk" in
        intros ms [x ->]; simp_regs ]
    end.
    shadow_cleanup.
    (* [comment removed for export] *)
    zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep.
    lazymatch goal with X : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (ro_bytes_at rsegs mx 0x217c0 REQ8 X ltac:(lia) ltac:(cbn; lia) (ro_bytes_b_sound _ _ _ REQ8_ro)) as STR;
      (first [ pose proof ((range_ok_high_munch (Clg:=Clg) _ v mx 0x217c0 4 RQ MU ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia))) as dR_8; dand4 dR_8 as IRq SOq Q1 Q2 | destruct (range_ok_high_munch (Clg:=Clg) _ v mx 0x217c0 4 RQ MU ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia)) as (IRq & SOq & Q1 & Q2) ]) end.
    rewrite REQ8_eq in STR.
    icall strlen_icpt_spec by
      (rewrite ?unsigned_lit by lia;
       first [ exact STR | exact ST | exact CEIL | exact IRq | exact SOq | exact Q1 | exact Q2 | assumption | rebundle
             | (cbn; intros [X|[X|[X|X]]]; try discriminate X; exact X)
             | (rewrite ?app_length; cbn [length skipn REQ8 app Z.of_nat Pos.of_succ_nat Pos.succ Nat.add];
                unfold STRLEN_ICPT_STACK; mlia) ]).
    try clear STR. clear IRq SOq Q1 Q2. try clear POST. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of WSZ with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
      pose proof (proj1 (rw_cells_app rsegs mx (h_ff H + 2976) [c0] (c1 :: c2 :: c3 :: c4 :: rest)) WSZ) as [WSa WSbc];
      pose proof (proj1 (rw_cells_app rsegs mx _ [c1; c2; c3; c4] rest) WSbc) as [WSb WSc] end.
    clear WSZ WSbc.
    pose proof (rwc_eq _ _ _ (h_ff H + 2980) _ WSb ltac:(cbn; lia)) as WSb'. clear WSb. rename WSb' into WSb.
    pose proof (rwc_eq _ _ _ (h_ff H + 2984) _ WSc ltac:(cbn; lia)) as WSc'. clear WSc. rename WSc' into WSc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (range_ok_high_munch (Clg:=Clg) _ v mx 0x217c0 4 RQ MU ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia)) as RQx;
      pose proof (range_ok_high_munch (Clg:=Clg) _ v mx (h_ff H + 2980) 4 RW4 MU ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia)) as RW4x end.
    icall (strcpy_req_icpt_spec) by
      (rewrite ?unsigned_lit by lia;
       first [ reflexivity | exact WSb | exact ST | exact CEIL | exact RQx | exact RW4x | rebundle
             | (unfold STRCPY_ICPT_STACK; lia)
             | (left; lia)
             | lia
             | assumption ]).
    clear RQx RW4x.
    lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 2980) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into WID end.
    cbn [map REQ_BYTES] in WID.   (* [comment removed for export] *)
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHB 8. zstep.
    (* [comment removed for export] *)
    shadow_chk SHB 4 21.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk0 SHB 8. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHB 8. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk SHB 4 12. zstep.
    (* [comment removed for export] *)
    do 9 zstep.
    try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    assert (WS0P : forall mq,
      rw_cells rsegs mq (h_ff H + 2976) [C4 (Z_to_bv 64 905626964)] ->
      rw_cells rsegs mq (h_ff H + 2980) (map C1 REQ_BYTES) ->
      rw_cells rsegs mq (h_ff H + 2984) [C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
      rw_cells rsegs mq (h_ff H + 3008) [C8 (Z_to_bv 64 (h_ff H + 4168))] ->
      rw_cells rsegs mq (h_ff H + 3152) [C4 (Z_to_bv 64 478787243); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 (h_ff H + 3168))] ->
      ws0_obj LPA H mq).
    { intros mq Xa Xb Xc Xe Xw.
      pose proof (rwc_eq _ _ _ (h_ff H + 2980 + Z.of_nat (cells_size (map C1 REQ_BYTES))) _ Xc ltac:(cbn; lia)) as Xc'.
      pose proof (proj2 (rw_cells_app rsegs mq (h_ff H + 2980) _ _) (conj Xb Xc')) as Xbc.
      pose proof (rwc_eq _ _ _ (h_ff H + 2976 + Z.of_nat (cells_size [C4 (Z_to_bv 64 905626964)])) _ Xbc ltac:(cbn; lia)) as Xbc'.
      pose proof (proj2 (rw_cells_app rsegs mq (h_ff H + 2976) _ _) (conj Xa Xbc')) as Xabc.
      pose proof (rwc_eq _ _ _ (h_ff H + 2976 + Z.of_nat (cells_size ([C4 (Z_to_bv 64 905626964)] ++ map C1 REQ_BYTES ++
                     [C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]))) _ Xe ltac:(cbn; lia)) as Xe'.
      pose proof (proj2 (rw_cells_app rsegs mq (h_ff H + 2976) _ _) (conj Xabc Xe')) as Xall.
      cbn [map app REQ_BYTES] in Xall.
      apply (ws0_obj_intro LPA H mq ws_id_req); [left; reflexivity| |].
      - unfold ws_cells, ws_rec_of, ws_id_req, WS_MAGIC. cbn [ws_id ws_s ws_f ws_r ws_e]. fold_cl_segs. unfold h_ws, h_wsbuf.
        replace (h_ff H + 3152 + 1016) with (h_ff H + 4168) by lia.
        apply (rw_cells_recast _ _ _ _ _ Xall); [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity| reflexivity].
      - unfold wsemu_cells, wsemu_WS0, WS_EMU_MAGIC. cbn [we_len we_ws we_first we_last]. fold_cl_segs. unfold h_wsbuf.
        replace (h_ff H + 3152 + 16) with (h_ff H + 3168) by lia. exact Xw. }
    icall (WS_Assert_ok H None lo) by
      (rewrite ?unsigned_lit by lia;
       first [ reflexivity
             | (hnf; apply WS0P; assumption)
             | (eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|
                  intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia])
             | (eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia])
             | exact HG
             | (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
             | exact ST
             | assumption
             | (unfold WSASSERT_STACK, WSEMU_STACK; lia) ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    apply evt_done. unfold WS_Init_post.
    hot_eexists_k16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [apply WS0P; assumption|].
    eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|].
    intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia.
  Qed.
End S.
End A_WSg84.

   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, WS_MarkOverflow_post, memset_icpt_post,
  WSASSERT_STACK, WSEMU_STACK, WSMARK_STACK, MEMSET_ICPT_STACK, h_ws, h_wsbuf in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Lemma pa_site_10e988 : In 0x88bb8 (cl_sites LPA). Proof. cbn. tauto. Qed.
Lemma pa_site_10e9ec : In 0x88c1c (cl_sites LPA). Proof. cbn. tauto. Qed.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ws_changed (H : henv) (a : Z) : Prop :=
    h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32.

  #[using="AI16"] Lemma ws_emu_alloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (H : henv) (lo : Z) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 312 ->
      ws0_obj LPA H v -> glob_ok LPA VIA H v -> hshadow LPA H v -> hframe LPA A H ->
      a_livebytes A + 352 <= LIVE_MAX -> a_nlive A + 2 <= NLIVE_MAX -> 448 <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSEMUALLOC_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          frames_same A A' -> a_tinycred A' = a_tinycred A -> a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A - 448 (* [comment removed for export] *) ->
          stk rsegs v' lo (bv_unsigned sp) -> glob_ok LPA VIA H v' -> hshadow LPA H v' ->
          (* [comment removed for export] *)
              (exists vep junk, r <> 0 /\ ws1_obj LPA H A' v' r vep /\ rw_cells rsegs v' vep [CB 312 junk] /\
               a_live A r = None /\ a_live A vep = None /\
               (forall p, p <> r -> p <> vep -> a_live A' p = a_live A p) /\ a_livebytes A' = a_livebytes A + 352 /\ a_nlive A' = a_nlive A + 2 /\
               cframe LPA (owned A) (owned A') (bv_unsigned sp) WSEMUALLOC_STACK (ws_changed H)
                      (fun a => newblk r 40 a \/ newblk vep 312 a) v v') ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 ws_emu_alloc_entry) fc None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. cbv zeta. intros AINV MI Ha0 Ha1 WS0 GLOB HSH HFR LBMAX NLVX PCM TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    rewrite Ha0, Ha1. unfold ws_emu_alloc_entry, WSEMUALLOC_STACK, ASTK in *.
    pose proof alloc_ceiling_num as ACV.
    pose proof (henv_geom_of_frame LPA A m md H AINV HFR) as HG.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts. (* [comment removed for export] *) pose proof G2 as G2x__; dand17 G2x__ as G2_01 G2_02 G2_03 G2_04 G2_05 G2_06 G2_07 G2_08 G2_09 G2_10 G2_11 G2_12 G2_13 G2_14 G2_15 G2_16 G2_17. hide G2.
    pose proof (hff_al8 H 2976 HG eq_refl) as AL1. pose proof (hff_al8 H 3152 HG eq_refl) as AL2.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFR.
    change ((8192 + 7) / 8) with 1024 in SHFR. rewrite SHMAX_val in SHFR.
    (* [comment removed for export] *)
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. fold_aview. open_map_cells MC.
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as _ _ _ _ _ _ SHW _ _ SHB | pose proof HSH as (_ & _ & _ & _ & _ & _ & SHW & _ & _ & SHB) ]). fold_cl_segs. fold_aview. unfold h_ws, h_wsbuf in SHW, SHB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2976) 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHWR. rewrite SHMAX_val in SHWR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 3152) 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as SHBR. rewrite SHMAX_val in SHBR.
    assert (ESW : sh (h_ff H + 2976) = sh (h_ff H) + 372) by (unfold sh; mlia).
    assert (ESB : sh (h_ff H + 3152) = sh (h_ff H) + 394) by (unfold sh; mlia).
    assert (LSW : Z.of_nat (length (shpat 40)) = 5) by reflexivity.
    assert (LSB : Z.of_nat (length (shpat 1024)) = 128) by reflexivity.
    (first [ pose proof (WS0) as dR_3; dex1 dR_3 as id; dand3 dR_3 as IDOK WSC WEC | pose proof (WS0) as dR_3; dand4 dR_3 as id IDOK WSC WEC | pose proof WS0 as (id & IDOK & WSC & WEC) ]). fold_cl_segs. fold_aview.
    assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
    unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
    unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
    unfold h_ws, h_wsbuf in WSC, WEC.
    (* [comment removed for export] *)
    assert (WS0P : forall mq,
      rw_cells rsegs mq (h_ff H + 2976) [C4 (Z_to_bv 64 WS_MAGIC); CB 4 id; C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_ff H + 3152 + 1016))] ->
      rw_cells rsegs mq (h_ff H + 3152) [C4 (Z_to_bv 64 WS_EMU_MAGIC); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 (h_ff H + 3152 + 16))] ->
      ws0_obj LPA H mq).
    { intros mq X1 X2. apply (ws0_obj_intro LPA H mq id IDOK); [exact X1| exact X2]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8272, bv_unsigned sp)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] | exact I]. }
    unfold h_ws, h_wsbuf in *.
    ago AINV. fold_cl_segs.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    icall (WS_Assert_ok H None lo) by (first [ (hnf; apply WS0P; assumption) | henv_side GLOB HSH HG CE MU WM ST ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHW 8. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep.
    icall (ws_emu_ok H (ws_rec_of H id) (wsemu_WS0 (h_ff H + 3152)) lo)
      by (first [ exact WSC | exact WEC | (cbn [ws_id ws_rec_of]; exact IDL) | henv_side GLOB HSH HG CE MU WM ST ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHB 8. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHB 8. zstep. shadow_chk0 SHB 8. zstep. zstep. kdead2.
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk SHB 4 12. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead2. zstep. first [if_true | if_false].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    pose proof HFR as [age HFR'].
    assert (GLOB0 : glob_ok LPA VIA H (aview A m0)).
    { eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|].
      intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia. }
    assert (HSH0 : hshadow LPA H (aview A m0)).
    { eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]. }
    ws_cranges H AINV0 HFR' FR.
    eapply (as_calloc_cps16 (AsanAlloc16:=AI16)) with (cnt := 1) (sz := 40);   (* [comment removed for export] *)
      [ exact AINV0 | exact MI | reflexivity | reflexivity | unfold REQ_MAX; lia | unfold REQ_MAX; lia | unfold REQ_MAX; lia | rewrite NREQ_CAP_eq; lia
      | lia | try (generalize alloc_ceiling_val); clear - NLVX; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; unfold kMaxPrimaryUser in X; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia
      | replace (1 * 40) with 40 by reflexivity; rewrite prim_cost_40; clear - PCM; lia (* [comment removed for export] *) | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; apply pa_site_10e988
      | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; unfold ASTK; lia
      | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r1 A1 m1 md1. cbv zeta.
    intros AINV1 MI1 MDF1 HLE1 FRS1 TCR1 OUT1 FRK1. change (1 * 40) with 40 in TCR1. cbn [Z.ltb] in TCR1. rewrite Z.sub_0_r in TCR1.
    fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK1 by lia. unfold ASTK in FRK1. change (1 * 40) with 40 in OUT1, FRK1.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
    assert (HFR1 : hframe LPA A1 H) by (eapply hframe_keep; [exact HFR| exact FRS1]). pose proof HFR1 as [age1 HFR1'].
    assert (GLOB1 : glob_ok LPA VIA H (aview A1 m1)).
    { eapply glob_ok_acall; [exact AINV0| exact HFR| apply (cframe_of_frame_ok LPA); exact FRK1| exact GLOB0| lia| intros a _ X; exact X]. }
    assert (HSH1 : hshadow LPA H (aview A1 m1)).
    { eapply hshadow_acall0; [exact AINV0| exact HFR| apply (cframe_of_frame_ok LPA); exact FRK1| exact HSH0| lia]. }
    pose proof (cenv_intro A1 m1 md1 AINV1) as CE1.
    destruct OUT1 as (NZ1 & FRESH1 & LIVEr1 & LIVEq1 & ZERO1 & LBY1 & NL1 & SC1 & PC1); cbn [Z.mul Z.ltb kMaxPrimaryUser] in SC1; rewrite ?Z.sub_0_r in SC1. cbn [Z.mul] in PC1; rewrite prim_cost_40 in PC1.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      acall_xfer FRK1.
      (first [ pose proof ((live_geomP LPA A1 m1 md1 r1 _ AINV1 LIVEr1)) as dR_4; dand7 dR_4 as _ R16 Rlo Rhi Rimg Rmap Rown | pose proof (live_geomP LPA A1 m1 md1 r1 _ AINV1 LIVEr1) as (_ & R16 & Rlo & Rhi & Rimg & Rmap & Rown) ]).
      unfold kHighMemBeg in Rlo. all_app_facts.
      pose proof (as_frame_blk_disjoint LPA A1 m1 md1 (h_ff H) HCLASS age1 r1 40 AINV1 HFR1' LIVEr1) as DJ1.
      change (fsize HCLASS) with 8192 in DJ1.
      (first [ pose proof ((newblock_cells (L:=LPA) A1 m1 md1 r1 _ AINV1 LIVEr1)) as dR_5; dex1 dR_5 as junk1; dand3 dR_5 as LJ1 NB1 CR1 | pose proof ((newblock_cells (L:=LPA) A1 m1 md1 r1 _ AINV1 LIVEr1)) as dR_5; dand4 dR_5 as junk1 LJ1 NB1 CR1 | destruct (newblock_cells (L:=LPA) A1 m1 md1 r1 _ AINV1 LIVEr1) as (junk1 & LJ1 & NB1 & CR1) ]).
      pose proof (all_zero_CB rsegs _ r1 _ junk1 NB1 ZERO1) as EJ. change (Z.to_nat 40) with 40%nat in EJ. subst junk1.
      apply (rw_cells_recast rsegs _ r1 _
               [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
                C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in NB1; [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | reflexivity].
      pose proof (as_live_shadow LPA A1 m1 md1 r1 40 AINV1 LIVEr1) as SHR1. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) r1 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHR1B. rewrite SHMAX_val in SHR1B.
      pose proof (sh_boundL (Clg:=Clg) r1 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHR1N. rewrite SHMAX_val in SHR1N.
      pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp); (r1, r1 + 40)] (aview A1 m1)) as MU2.
      pose proof (wmono_refl rsegs (aview A1 m1)) as WM2.
      assert (WMAP2 : mapped (aview A1 m1) (bv_unsigned sp - 8272) 8272).
      { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
      assert (CFP2 : client_fp LPA A1 (aview A1 m1) [(bv_unsigned sp - 8272, bv_unsigned sp); (r1, r1 + 40)]).
      { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8272)) with 8272 by lia; exact WMAP2 |].
        split; [right; left; exists r1, 40; split; [exact LIVEr1|lia]| exact I]. }
      pose proof (map_cells_of_consts _ (proj1 CE1)) as MC1. fold_aview. open_map_cells MC1.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. kdead. zstep. shadow_chk SHR1 4 11.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      shadow_chk SHR1 4 12. zstep.
      (* [comment removed for export] *)
      zstep. shadow_chk SHR1 4 12. zstep.
      (* [comment removed for export] *)
      zstep. first [if_true | if_false]. zstep. zstep. zstep.
      (* [comment removed for export] *)
      astop AINV1 MU2 WM2 CFP2. fold_cl_segs.
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      assert (GLOB2 : glob_ok LPA VIA H (aview A1 mx)) by
       (eapply glob_ok_munch; [exact GLOB1| exact MU2| exact WM2|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia);
      assert (HSH2 : hshadow LPA H (aview A1 mx)) by
       (eapply hshadow_munch; [exact HSH1| exact MU2| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia])
      end.
      ws_cranges H AINV2 HFR1' FR.
      pose proof (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ r1 40 r1 40 AINV2 LIVEr1 ltac:(lia) ltac:(lia) ltac:(lia)) as CR1'.
      (* [comment removed for export] *)
      lazymatch type of MU2 with munch _ _ ?mx =>
        assert (CFa : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8272 nowhere (newblk r1 40) (aview A m) mx)
      end.
      { eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A1 m1) _ _ _);
          [ exact MU | | exact FRK1 | lia | lia | intros a X; destruct X | intros a X; left; exact X
          | exact MU2 | | ].
        - intros a Ha NO. cbn [outside] in NO. lia.
        - intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
        - lazymatch goal with |- mapped ?v _ _ =>
            eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] end. }
      eapply (as_malloc_cps16 (AsanAlloc16:=AI16)) with (n := 312);   (* [comment removed for export] *)
        [ exact AINV2 | assumption | reflexivity | unfold REQ_MAX; lia | rewrite NREQ_CAP_eq; lia | rewrite LBY1; lia
        | try (generalize alloc_ceiling_val); clear - NL1 NLVX; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; unfold kMaxPrimaryUser in X; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia
        | rewrite prim_cost_312; clear - PCM PC1; lia (* [comment removed for export] *) | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; apply pa_site_10e9ec
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; unfold ASTK; lia
        | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
        | ].
      clear MU WM CFP FRK1 GLOB0 HSH0.
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' r2 A2 m4 md4. cbv zeta.
      intros AINV3 MI3 MDF3 HLE3 FRS3 TCR3 OUT3 FRK3. cbn [Z.ltb] in TCR3. rewrite Z.sub_0_r in TCR3.
      fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK3 by lia. unfold ASTK in FRK3.
      pose proof (as_minv LPA A1 _ _ AINV2) as [_ MH2].
      assert (HFR3 : hframe LPA A2 H) by (eapply hframe_keep; [exact HFR1| exact FRS3]).
      assert (GLOB3 : glob_ok LPA VIA H (aview A2 m4)).
      { eapply glob_ok_acall; [exact AINV2| exact HFR1| apply (cframe_of_frame_ok LPA); exact FRK3| exact GLOB2| lia| intros a _ X; exact X]. }
      assert (HSH3 : hshadow LPA H (aview A2 m4)).
      { eapply hshadow_acall0; [exact AINV2| exact HFR1| apply (cframe_of_frame_ok LPA); exact FRK3| exact HSH2| lia]. }
      pose proof (cenv_intro A2 m4 md4 AINV3) as CE3.
      destruct OUT3 as (NZ2 & FRESH2 & LIVEr2 & LIVEq3 & LBY3 & NL3 & SC3 & PC3); cbn [Z.ltb kMaxPrimaryUser] in SC3; rewrite ?Z.sub_0_r in SC3. rewrite prim_cost_312 in PC3.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      + (* [comment removed for export] *)
        acall_xfer FRK3.
        assert (NE12 : r1 <> r2) by (intros ->; rewrite FRESH2 in LIVEr1; discriminate).
        assert (LIVEr1' : a_live A2 r1 = Some 40) by (rewrite (LIVEq3 r1 NE12); exact LIVEr1).
        (first [ pose proof ((live_geomP LPA A2 m4 md4 r2 _ AINV3 LIVEr2)) as dR_7; dand7 dR_7 as _ B16 Blo Bhi Bimg Bmap Bown | pose proof (live_geomP LPA A2 m4 md4 r2 _ AINV3 LIVEr2) as (_ & B16 & Blo & Bhi & Bimg & Bmap & Bown) ]).
        unfold kHighMemBeg in Blo. all_app_facts.
        pose proof (as_live_disjoint LPA A2 m4 md4 r1 40 r2 312 AINV3 LIVEr1' LIVEr2 NE12) as DRB.
        pose proof HFR3 as [age3 HFR3'].
        pose proof (as_frame_blk_disjoint LPA A2 m4 md4 (h_ff H) HCLASS age3 r2 312 AINV3 HFR3' LIVEr2) as DJ2.
        change (fsize HCLASS) with 8192 in DJ2.
        (first [ pose proof ((newblock_cells (L:=LPA) A2 m4 md4 r2 _ AINV3 LIVEr2)) as dR_8; dex1 dR_8 as junkb; dand3 dR_8 as LJb NB2 CR2 | pose proof ((newblock_cells (L:=LPA) A2 m4 md4 r2 _ AINV3 LIVEr2)) as dR_8; dand4 dR_8 as junkb LJb NB2 CR2 | destruct (newblock_cells (L:=LPA) A2 m4 md4 r2 _ AINV3 LIVEr2) as (junkb & LJb & NB2 & CR2) ]).
        pose proof (as_live_shadow LPA A2 m4 md4 r1 40 AINV3 LIVEr1') as SHR3. fold_cl_segs. fold_aview.
        pose proof (sh_boundL (Clg:=Clg) r2 312 ltac:(lia) ltac:(lia) ltac:(lia)) as SHR2N. rewrite SHMAX_val in SHR2N.
        pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp); (r1, r1 + 40); (h_ff H + 3152, h_ff H + 3152 + 32)] (aview A2 m4)) as MU3.
        pose proof (wmono_refl rsegs (aview A2 m4)) as WM3.
        assert (WMAP3 : mapped (aview A2 m4) (bv_unsigned sp - 8272) 8272).
        { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
        assert (CFP3 : client_fp LPA A2 (aview A2 m4) [(bv_unsigned sp - 8272, bv_unsigned sp); (r1, r1 + 40); (h_ff H + 3152, h_ff H + 3152 + 32)]).
        { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8272)) with 8272 by lia; exact WMAP3 |].
          split; [right; left; exists r1, 40; split; [exact LIVEr1'|lia]|].
          split; [| exact I]. right. right. left. exists (h_ff H), HCLASS, age3. split; [exact HFR3'|]. change (fsize HCLASS) with 8192. lia. }
        pose proof (map_cells_of_consts _ (proj1 CE3)) as MC3. fold_aview. open_map_cells MC3.
        ago AINV3. fold_cl_segs.
        (* [comment removed for export] *)
        zstep. shadow_chk0 SHR3 8. zstep. zstep. kdead.
        (* [comment removed for export] *)
        zstep. shadow_chk0 SHR3 8. zstep.
        (* [comment removed for export] *)
        shadow_rechk0 SHB (h_ff H + 3176) 8. zstep. shadow_chk0 SHR3 8. zstep. zstep.
        (* [comment removed for export] *)
        shadow_chk0 SHB 8. zstep. zstep.
        (* [comment removed for export] *)
        zstep. do 8 zstep. zstep.
        try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        astop AINV3 MU3 WM3 CFP3.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r1 A2 mx mdx) end;
          [ assumption | assumption | | | | | | exact ST
          | eapply glob_ok_munch; [exact GLOB3| exact MU3| exact WM3|
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia]
          | eapply hshadow_munch; [exact HSH3| exact MU3| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]
          | ].
        { eapply amd_frame_sbm_l; [exact SBM | exact MH |].
          eapply amd_frame_trans; [exact MDF1|]. eapply amd_frame_sbm_l; [exact SBM0 | exact (proj2 (as_minv LPA A1 _ _ AINV1)) |].
          eapply amd_frame_sbm_r; [exact MDF3 | eassumption]. }
        { intros ff. rewrite FRS3. apply FRS1. }
        { rewrite TCR3, TCR1. reflexivity. }
        { rewrite SC3, SC1. reflexivity. }
        { rewrite PC3, PC1. clear; lia. }   (* [comment removed for export] *)
        exists r2, junkb. split; [exact NZ1|]. split; [|split; [|split; [exact FRESH1|]; split; [|split; [|split; [|split]]]]].
        * lazymatch goal with |- ws1_obj _ _ _ ?vfin _ _ =>
            lazymatch goal with X : rw_cells rsegs vfin r1 _ |- _ =>
              replace (h_ff H + 3168) with (h_ff H + 3152 + 16) in X by lia;
              eapply (ws1_obj_intro LPA H A2 vfin r1 r2 id [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] IDOK eq_refl);
                [exact WSC | exact WEC | exact LIVEr1' | exact X | exact LIVEr2]
            end end.
        * exact NB2.
        * rewrite <- (LIVEq1 r2 ltac:(intros E; exact (NE12 (eq_sym E)))). exact FRESH2.
        * intros q Q1 Q2. rewrite (LIVEq3 q Q2). apply LIVEq1, Q1.
        * rewrite LBY3, LBY1. lia.
        * rewrite NL3, NL1. lia.
        * lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
            lazymatch type of CFa with cframe _ _ _ _ _ _ _ _ (aview A1 ?mp) =>
            assert (CFb : cframe LPA (owned A1) (owned A2) (bv_unsigned sp) 8272 (fun a => newblk r1 40 a \/ ws_changed H a) (newblk r2 312) (aview A1 mp) vfin)
              by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A1 mp) (aview A1 mp) (aview A2 m4) _ [] _);
                  [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK3 | lia | lia
                  | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                  | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ];
                  intros a Ha NO; cbn [outside] in NO; unfold newblk, blk, ws_changed, h_ws, h_wsbuf; lia);
            eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A1 mp) vfin CFa CFb); [lia | lia
                | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]
                | intros a X; destruct X | intros a [X|X]; [left; exact X| right; exact X]
                | intros a [X|X]; [left; exact X| right; left; exact X] ]
          end end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16"] Lemma WS_Alloc_ok : WS_Alloc_stmt.
  Proof.
    unfold WS_Alloc_stmt, frames_same.
    intros H lo. intros until T. cbv zeta. intros AINV MI Ha0 Ha1 WS0 GLOB HSH HFR LBMAX NLVX PCM TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    rewrite Ha0, Ha1. unfold WS_Alloc_entry, WSALLOC_STACK, WSEMUALLOC_STACK, ASTK in *.
    pose proof alloc_ceiling_num as ACV.
    pose proof (henv_geom_of_frame LPA A m md H AINV HFR) as HG.
    (first [ pose proof (HG) as dR_9; dand3 dR_9 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts. (* [comment removed for export] *) pose proof G2 as G2x__; dand17 G2x__ as G2_01 G2_02 G2_03 G2_04 G2_05 G2_06 G2_07 G2_08 G2_09 G2_10 G2_11 G2_12 G2_13 G2_14 G2_15 G2_16 G2_17. hide G2.
    pose proof (hff_al8 H 1536 HG eq_refl) as AL3.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFR.
    change ((8192 + 7) / 8) with 1024 in SHFR. rewrite SHMAX_val in SHFR.
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. fold_aview. open_map_cells MC.
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8320, bv_unsigned sp)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] | exact I]. }
    unfold h_ws, h_wsbuf in *.
    ago AINV. fold_cl_segs.
    carve_frame 48%nat ST.
    do 7 zstep.
    (* [comment removed for export] *)
    zstep. first [if_true | if_false]. do 7 zstep.
    (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 48) 48 AINV0 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRF end.
    eapply ws_emu_alloc_cps;
      [ exact AINV0 | exact MI | reflexivity | reflexivity
      | eapply ws0_obj_munch; [exact WS0| exact MU| exact WM| intros a__ Ha__; unfold h_ws, h_wsbuf in Ha__; cbn; lia]
      | eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|
          intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia]
      | eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]
      | exact HFR | exact LBMAX | exact NLVX | exact PCM (* [comment removed for export] *) | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; unfold WSEMUALLOC_STACK, ASTK; lia
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 m1 md1. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 TCR1 SC1 PC1 ST1 GLOB1 HSH1 OUT1.   (* [comment removed for export] *)
    fold_cl_segs. fold_aview. rewrite unsigned_lit in ST1 by lia. unfold WSEMUALLOC_STACK, ASTK in OUT1. rewrite unsigned_lit in OUT1 by lia.
    assert (HFR1 : hframe LPA A1 H) by (eapply hframe_keep; [exact HFR| exact FRS1]). pose proof HFR1 as [age1 HFR1'].
    pose proof (cenv_intro A1 m1 md1 AINV1) as CE1.
    (first [ pose proof (HSH1) as dR_10; dand10 dR_10 as _ SHC1 _ _ _ _ SHW1 _ _ SHB1 | pose proof HSH1 as (_ & SHC1 & _ & _ & _ & _ & SHW1 & _ & _ & SHB1) ]). fold_cl_segs. fold_aview. unfold h_ws, h_wsbuf, h_cp in SHC1, SHW1, SHB1.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 1536) 752 ltac:(lia) ltac:(lia) ltac:(lia)) as SHCR. rewrite SHMAX_val in SHCR.
    destruct OUT1 as (vep & vjunk & NZ & WS1' & VEPC & FRESHr & FRESHv & LIVEq1 & LBY1 & NL1 & CF1).
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      clear ST. unfold ws_changed, h_ws, h_wsbuf in CF1.
      (first [ pose proof (WS1') as dR_11; dex2 dR_11 as id pad; dand7 dR_11 as IDOK PADL WSC1 WEC1 LIVEr WAC LIVEv | pose proof (WS1') as dR_11; dand9 dR_11 as id pad IDOK PADL WSC1 WEC1 LIVEr WAC LIVEv | pose proof WS1' as (id & pad & IDOK & PADL & WSC1 & WEC1 & LIVEr & WAC & LIVEv) ]). fold_cl_segs. fold_aview.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC. unfold h_ws, h_wsbuf in WSC1, WEC1, WAC.
      clear WSC1 WEC1.
      (first [ pose proof ((live_geomP LPA A1 m1 md1 r _ AINV1 LIVEr)) as dR_12; dand7 dR_12 as _ R16 Rlo Rhi _ _ _ | pose proof (live_geomP LPA A1 m1 md1 r _ AINV1 LIVEr) as (_ & R16 & Rlo & Rhi & _ & _ & _) ]).
      (first [ pose proof ((live_geomP LPA A1 m1 md1 vep _ AINV1 LIVEv)) as dR_13; dand7 dR_13 as _ V16 Vlo Vhi _ _ _ | pose proof (live_geomP LPA A1 m1 md1 vep _ AINV1 LIVEv) as (_ & V16 & Vlo & Vhi & _ & _ & _) ]).
      unfold kHighMemBeg in Rlo, Vlo. all_app_facts. pose proof (mod8_of_mod16 r R16) as R8.
      pose proof (as_live_shadow LPA A1 m1 md1 r 40 AINV1 LIVEr) as SHr. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) r 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHrB. rewrite SHMAX_val in SHrB.
      (first [ pose proof (GLOB1) as dR_14; dand4 dR_14 as _ BSS CP _ | pose proof GLOB1 as (_ & BSS & CP & _) ]). fold_cl_segs. fold_aview. cbn [vi_bss_cp VIA] in BSS. unfold h_cp in BSS, CP.
      (first [ pose proof ((shadowed_bss_cp _ (proj1 CE1))) as dR_15; dand8 dR_15 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_cp _ (proj1 CE1)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs. fold_aview.
      cbn [vi_bss_cp VIA] in GLE, GGE.
      pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
      pose proof (got_cp_cell _ (proj1 CE1)) as GOTC. unfold GOTA_cp in GOTC. cbn [vi_bss_cp VIA] in GOTC. fold_aview.
      acall_xfer CF1. rename ST1 into ST.
      pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp)] (aview A1 m1)) as MU2.
      pose proof (wmono_refl rsegs (aview A1 m1)) as WM2.
      assert (WMAP2 : mapped (aview A1 m1) (bv_unsigned sp - 8320) 8320).
      { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
      assert (CFP2 : client_fp LPA A1 (aview A1 m1) [(bv_unsigned sp - 8320, bv_unsigned sp)]).
      { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8320)) with 8320 by lia; exact WMAP2 | exact I]. }
      pose proof (map_cells_of_consts _ (proj1 CE1)) as MC1. fold_aview. open_map_cells MC1.
      ago AINV1. fold_cl_segs. fix_ret_pc.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      icall (WS_Assert_ok H (Some (A1, r, vep)) lo) by
        (first [ (hnf; split; [exact WS1'|]; split; [exists r, 40; split; [exact SHr| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia]|]; unfold kHighMemBeg; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia)
               | henv_side GLOB1 HSH1 HG CE1 MU2 WM2 ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. kdead. zstep. shadow_chk0 SHr 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      shadow_addr_at SHG 6191712 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K0; zify_cond K0;
        [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk SHC1 1 12. zstep. (* [comment removed for export] *) match goal with |- context [ zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn ?zk (repeat (Z_to_bv 8 0) ?zn))))) ] => replace (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn zk (repeat (Z_to_bv 8 0) zn)))))) with (Z_to_bv 64 0) by (vm_compute; reflexivity) end. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      shadow_rechk0 SHr (r + 16) 8. zstep. zstep.
      do 7 zstep. zstep.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      astop AINV1 MU2 WM2 CFP2.
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ vep A1 mx mdx) end;
        [ assumption | assumption
        | eapply amd_frame_sbm_l; [exact SBM | exact MH | eapply amd_frame_sbm_r; [exact MDF1 | eassumption]]
        | exact FRS1 | exact TCR1 | exact SC1 | exact PC1 (* [comment removed for export] *) | exact ST
        | eapply glob_ok_munch; [exact GLOB1| exact MU2| exact WM2|
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia]
        | eapply hshadow_munch; [exact HSH1| exact MU2| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]
        | ].
      exists r, vjunk. split; [lia|]. split; [|split; [assumption| split; [exact FRESHr| split; [exact FRESHv| split; [exact LIVEq1| split; [exact LBY1| split; [exact NL1|]]]]]]].
      { eapply ws1_obj_munch; [exact WS1'| exact MU2| exact WM2| intros a__ Ha__; unfold h_ws, h_wsbuf in Ha__; cbn; lia]. }
      lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
      eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A1 m1) vfin _ _);
        [ exact MU | | exact CF1 | lia | lia | intros a X; exact X | intros a X; left; exact X
        | exact MU2 | | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ] end.
      + intros a Ha NO. cbn [outside] in NO. lia.
      + intros a Ha NO. cbn [outside] in NO. lia.
  Qed.
End S.
