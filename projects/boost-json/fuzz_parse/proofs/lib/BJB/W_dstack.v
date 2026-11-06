(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import N8Store.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres BJIface AKitChk AKitCells BJIfaceTop BJIfacePW.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk14Somek14consk13nilk16option37Corelib4Init5Logicnd2eq01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsp9dov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~u05asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~hi3aaccessiblehi33mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hn62b846Stdlib6ZArith6BinInt1Zhr73addhr72lehr76shiftrhf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB9BJIfacePW~~~~~~hv0bdstack_stmt" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma ds_accessible_rd8 : ltac2:(zQ "h20!h9!jc!l9!m0!m7!me!n4!p1!p6!t0!hhb!hm1!hmf!hr1!hsf!ht6!htc!hu6>1m$c>1a$8>0@3$b^2^1+8>0@2$fZ^2@3$7@1$6@1$2@1$1@1$0#8@4$9$a^4@2$h1@1$0#k0@2$e@2$h0^3+3+nvvvogg0N1@2$3@1$2@1$1@1$0#8@3$4@1$1@1$0#8@1$dZ@1$5@1$1@1$0#8").
  Proof.
    intros m a AC A0.
    set (g := a / 8 * 8).
    assert (G8 : g mod 8 = 0) by (subst g; Z.div_mod_to_equations; lia).
    assert (GA : g <= a < g + 8) by (subst g; Z.div_mod_to_equations; lia).
    destruct (accessible_read1 m (g + 7) (accessible_sub _ _ _ (g + 7) 1 AC ltac:(lia) ltac:(lia) ltac:(lia))) as (v & V1 & OK & RD).
    assert (v = 0) as -> by (destruct OK as [->|OK]; [reflexivity| exfalso; Z.div_mod_to_equations; lia]).
    rewrite (sh_granule g 7 G8 ltac:(lia)) in RD.
    rewrite <- (sh_granule g (a - g) G8 ltac:(lia)) in RD. replace (g + (a - g)) with a in RD by lia.
    rewrite <- (sh_shiftr a) in RD by lia. rewrite ASHADOW_BASE_val in RD. exact RD.
  Qed.
  Ltac chk_acc ACC MU a :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let RD := fresh "RD" in
      pose proof (ds_accessible_rd8 mc a (accessible_sub _ _ _ a 8 (AsWalk.accessible_transport_hi _ _ _ _ _ ACC MU ltac:(hiw_tac)) ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as RD;
      chk_rd RD
    end.

  Theorem dstack_spec : ltac2:(zQ "10!ij0@1$0?5HCEIL").
  Proof.
    unfold dstack_stmt, dstack_post, dstack_cells, ADSTACK_STACK.
    intros until lo. intros MI ST CEIL ROOM AC CELLS APP ACC A8.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP; cbn in RSP.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0. acb.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5). unfold AIMG_TOP in APB1. unfold AAPP_HI in APB3.
    pose proof (ACONST_shbase _ AC) as [SB1 SB2]. unfold AGOT_SHBASE, ASHBASE_CELL, ASHADOW_BASE, wz in SB1, SB2.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned a0 + 16, bv_unsigned a0 + 24)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (ACW : Forall aconst_ok [(bv_unsigned sp - 48, bv_unsigned sp); (bv_unsigned a0 + 16, bv_unsigned a0 + 24)]%Z) by aconst_wins.
    replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in MU, ACW by lia.
    unfold A_DS_DTOR, wz. cbv delta [wz] in CELLS.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    st1. do 6 st1.
    st1. st1. st1.
    st1. st1. st1. st1. chk_acc ACC MU (bv_unsigned a0 + 24).
    st1. st1. livebr1.
    (* [comment removed for export] *)
    st1. st1. st1. chk_acc ACC MU (bv_unsigned a0 + 16).
    st1.
    (* [comment removed for export] *)
    st1. st1. st1. chk_acc ACC MU (bv_unsigned a0 + 32).
    st1. st1. st1. chk_acc ACC MU (bv_unsigned a0 + 40).
    st1. st1. st1. st1. livebr1.
    (* [comment removed for export] *)
    st1. chk_acc ACC MU (bv_unsigned a0).
    st1. st1. st1. livebr1.
    (* [comment removed for export] *)
    do 6 st1. st1. st1.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. neexists 16. split; [reflexivity|].
    split. { replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. exact MU. }
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact CELLS|].
    exact (ACONST_frame _ _ _ AC MU WM ACW).
  Qed.
End HCW.
