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
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp0e6 AIcpnnp AIcpya4 AIcpw0i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpw0i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WSvfw A_WSruy.

Module A_WSu0b.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp0e6 AIcpnnp AIcpya4 AIcpw0i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_WSvfw A_WSruy.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSvfw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSruy.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, memset_icpt_post,
  WSASSERT_STACK, WSEMU_STACK, MEMSET_ICPT_STACK, h_ws, h_wsbuf in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@G2_03; @ACV; @LO; @G3; @SPR; @G0; @IDL; @SZ; @SR; @CEIL; @G2_06; @G2_07; @G2_08; @G2_09; @LO0; @K0; @G2_05; @G2_13; @G2_14; @ESB; @Hx__; @Ha__; @H0; @GLE; @GGE; @GCE; @KG; @NO])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma WS_Rollback_none : forall H, WS_Rollback_at H None.
  Proof.
    intros H. unfold WS_Rollback_at, frames_same.
    set (E := None).
    intros lo SB N. intros until T. cbv zeta. intros AINV MI Ha0 Ha1 WSX GLOB HSH HFR TP SP16 ST CEIL LO SSH K.
    rewrite Ha0, Ha1. unfold WS_Rollback_entry, WSROLLBACK_STACK, WSRESET_STACK, WSAFREE_STACK, ASTK in *.
    pose proof alloc_ceiling_num as ACV.
    pose proof (henv_geom_of_frame LPA A m md H AINV HFR) as HG.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts. (* [comment removed for export] *) pose proof G2 as G2x__; dand17 G2x__ as G2_01 G2_02 G2_03 G2_04 G2_05 G2_06 G2_07 G2_08 G2_09 G2_10 G2_11 G2_12 G2_13 G2_14 G2_15 G2_16 G2_17. hide G2.
    pose proof (hff_al8 H 2976 HG eq_refl) as AL1. pose proof (hff_al8 H 3152 HG eq_refl) as AL2. pose proof (hff_al8 H 1536 HG eq_refl) as AL3.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFR.
    change ((8192 + 7) / 8) with 1024 in SHFR. rewrite SHMAX_val in SHFR.
    assert (ESW : sh (h_ff H + 2976) = sh (h_ff H) + 372) by (unfold sh; mlia).
    assert (ESB : sh (h_ff H + 3152) = sh (h_ff H) + 394) by (unfold sh; mlia).
    assert (LSW : Z.of_nat (length (shpat 40)) = 5) by reflexivity.
    assert (LSB : Z.of_nat (length (shpat 1024)) = 128) by reflexivity.
    pose proof HFR as [age HFR'].
    (* [comment removed for export] *)
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. fold_aview. open_map_cells MC.
    pose proof (got_cp_cell _ (proj1 CE)) as GOTC. unfold GOTA_cp in GOTC. cbn [vi_bss_cp VIA] in GOTC. fold_aview.
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as _ SHC _ _ _ _ SHW _ _ SHB | pose proof HSH as (_ & SHC & _ & _ & _ & _ & SHW & _ & _ & SHB) ]). fold_cl_segs. fold_aview. unfold h_ws, h_wsbuf, h_cp in SHC, SHW, SHB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2976) 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHWR. rewrite SHMAX_val in SHWR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 3152) 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as SHBR. rewrite SHMAX_val in SHBR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 1536) 752 ltac:(lia) ltac:(lia) ltac:(lia)) as SHCR. rewrite SHMAX_val in SHCR.
    (first [ pose proof ((shadowed_bss_cp _ (proj1 CE))) as dR_3; dand8 dR_3 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_cp _ (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs. fold_aview.
    cbn [vi_bss_cp VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (first [ pose proof (GLOB) as dR_4; dand4 dR_4 as _ BSS CP _ | pose proof GLOB as (_ & BSS & CP & _) ]). fold_cl_segs. fold_aview. cbn [vi_bss_cp VIA] in BSS. unfold h_cp in BSS, CP.
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (h_ff H + 2976, h_ff H + 2976 + 40); (h_ff H + 3152, h_ff H + 3152 + 32)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WMAP : mapped (aview A m) (bv_unsigned sp - 8320) 8320).
    { eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8320, bv_unsigned sp); (h_ff H + 2976, h_ff H + 2976 + 40); (h_ff H + 3152, h_ff H + 3152 + 32)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8320)) with 8320 by lia; exact WMAP |].
      split; [right; right; left; exists (h_ff H), HCLASS, age; split; [exact HFR'|]; change (fsize HCLASS) with 8192; lia|].
      split; [| exact I]. right. right. left. exists (h_ff H), HCLASS, age. split; [exact HFR'|]. change (fsize HCLASS) with 8192. lia. }
    unfold h_ws, h_wsbuf, h_cp in *.
    assert (WS0P : forall mq idq, ws_id_ok idq ->
      rw_cells rsegs mq (h_ff H + 2976) [C4 (Z_to_bv 64 WS_MAGIC); CB 4 idq; C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_ff H + 3152 + 1016))] ->
      rw_cells rsegs mq (h_ff H + 3152) [C4 (Z_to_bv 64 WS_EMU_MAGIC); C4 (Z_to_bv 64 1016); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 (h_ff H + 3152 + 16))] ->
      ws0_obj LPA H mq).
    { intros mq idq IDq X1 X2. apply (ws0_obj_intro LPA H mq idq IDq); [exact X1| exact X2]. }
    subst E.
      (first [ pose proof (WSX) as dR_5; dex1 dR_5 as id; dand3 dR_5 as IDOK WSC WEC | pose proof (WSX) as dR_5; dand4 dR_5 as id IDOK WSC WEC | pose proof WSX as (id & IDOK & WSC & WEC) ]). fold_cl_segs. fold_aview.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      (* [comment removed for export] *)
      assert (ID0 : exists b0, id = b0 :: [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0] /\ Z.lor (bv_unsigned b0) 32 = 114).
      { destruct IDOK as [-> | ->]; eexists; (split; [reflexivity| reflexivity]). }
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold h_ws, h_wsbuf in WSC, WEC.
      ago AINV. fold_cl_segs.
      carve_frame 32%nat ST.
      do 5 zstep.
      (* [comment removed for export] *)
      do 6 zstep.
      icall (WS_Assert_ok H None lo) by (first [ (hnf; apply (WS0P _ id IDOK); assumption) | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. first [if_true | if_false].
      zstep. if_cases KG; zify_cond KG. { exfalso. dead KG. } clear KG.
      zstep. zstep. if_cases KG; zify_cond KG. { paok KG HG. } clear KG.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep.
      zstep. zstep. first [if_true | if_false].
      (* [comment removed for export] *)
      shadow_chk SHW 4 11. zstep. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk SHW 1 12.
      (* [comment removed for export] *)
      (first [ dex1 ID0 as b0; destruct ID0 as [-> E114] | dand3 ID0 as b0 -> E114 | destruct ID0 as (b0 & -> & E114) ]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (rw_cells_split_CB rsegs mx (h_ff H + 2976) [C4 (Z_to_bv 64 WS_MAGIC)] 4 (b0 :: [Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0])
                    [C8 (Z_to_bv 64 (h_ff H + 3152)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (h_ff H + 3152 + 1016))]
                    [1; 3]%nat WSC eq_refl) as WSC1 end.
      clear WSC. cbn [mk_CB_cells firstn skipn app] in WSC1.
      zstep. zstep. rewrite E114. zstep. fix_bstore; mem_after_store.
      lazymatch type of WSC1 with rw_cells _ ?mx ?b (?c0 :: ?c1 :: ?c2 :: ?rest) =>
        pose proof (rw_cells_merge rsegs mx b [c0] [c1; c2] rest WSC1) as WSC end.
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in WSC. clear WSC1.
      (* [comment removed for export] *)
      do 7 zstep.
      try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      zstep.
      (* [comment removed for export] *)
      carve_frame 64%nat ST.
      do 8 zstep.
      (* [comment removed for export] *)
      do 6 zstep.
      icall (WS_Assert_ok H None lo) by (first [ (hnf; apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption) | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. kdead. zstep. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      shadow_addr_at SHG 6189664 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K0; zify_cond K0;
        [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk SHC 1 12. zstep. (* [comment removed for export] *) match goal with |- context [ zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn ?zk (repeat (Z_to_bv 8 0) ?zn))))) ] => replace (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn zk (repeat (Z_to_bv 8 0) zn)))))) with (Z_to_bv 64 0) by (vm_compute; reflexivity) end. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. kdead. zstep. zstep. if_cases KG; zify_cond KG. { paok KG HG. } clear KG.
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep.
      icall (ws_emu_ok H (ws_rec_of H ws_id_req) (wsemu_WS0 (h_ff H + 3152)) lo)
        by (first [ exact WSC | exact WEC | reflexivity | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KG; zify_cond KG. { paok KG HG. } clear KG. zstep. shadow_chk0 SHB 8. zstep. zstep. kdead. zstep. zstep. if_cases KG; zify_cond KG. { paok KG HG. } clear KG.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHB 8. zstep. zstep. kdead. zstep. zstep. if_cases KG; zify_cond KG. { paok KG HG. } clear KG. shadow_chk0 SHB 8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep.
      icall (WS_Assert_ok H None lo) by (first [ (hnf; apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption) | henv_side GLOB HSH HG CE MU WM ST ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      do 9 zstep.
      try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      lazymatch goal with X : rw_cells _ ?mx (bv_unsigned sp + -64) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into FR end.
      release_frame FR ST (bv_unsigned sp).
      astop AINV MU WM CFP.
      pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx mdx) end;
        [ assumption | assumption
        | eapply amd_frame_sbm_l; [exact SBM | exact MH | apply amd_frame_refl; exact MH0]
        | intros ff; reflexivity | reflexivity | reflexivity | reflexivity (* [comment removed for export] *) | exact ST
        | eapply glob_ok_munch; [exact GLOB| exact MU| exact WM|
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_cp, h_vsc in Ha__; cbn; lia]
        | eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia]
        | apply (WS0P _ ws_id_req (or_introl eq_refl)); assumption
        | split; [intros p; reflexivity| split; reflexivity]
        | ].
      eapply cframe_stores; [exact MU| | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]].
      intros a Ha NO. cbn [outside] in NO. unfold h_ws, h_wsbuf. lia.
  Qed.
End S.
End A_WSu0b.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSvfw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSruy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_WSmsm.A_WSu0b.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, memset_icpt_post,
  WSASSERT_STACK, WSEMU_STACK, MEMSET_ICPT_STACK, h_ws, h_wsbuf in H.


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma WS_Rollback_ok : WS_Rollback_stmt.
  Proof.
    unfold WS_Rollback_stmt. intros H [[wa vep]|].
    - exact (WS_Rollback_some H wa vep).
    - exact (WS_Rollback_none H).
  Qed.
End S.
