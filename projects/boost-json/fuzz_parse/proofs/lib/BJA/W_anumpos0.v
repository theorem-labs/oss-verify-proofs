(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg W_anum0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import N8Store.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z35stdpp9bitvectorbdefinitionsi22bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA6AKitRV~~~~~~k42rv37Corelib4Init5Logico62eqo63andi27Z_to_bvk43rs0k43rs1k43rs3k43rs4k43rsp" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs; try transport_cond_ro segs m a bs.
Local Ltac addr_diff E A ::=
  lazymatch A with
  | E => constr:(0%Z)
  | _ =>
    match E with
    | Z.add ?X ?c1 =>
        let c1 := zlit c1 in
        lazymatch A with
        | Z.add X ?c2 => let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end
  end.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
  (* [comment removed for export] *)
  Ltac chkjoinb t back :=
    pose_reg_shb; norm_s32;
    lazymatch goal with
    | |- evt ?segs _ (MS ?R ?F _ ?fc ?oe ?m ?rom) =>
        let p := eval vm_compute in (bv_key (Z_to_bv 5 t)) in
        let Rf := constr:(fun tv : word => ltac:(let r := eval cbv beta iota delta [tset] in (@tset word p tv R) in exact r)) in
        eapply (evt_cut segs (fun ms => exists tv : word, ms = MS (Rf tv) F (Z_to_bv 64 back) fc oe m rom));
        [ st1b; norm_lits; norm_s32;
          let K := fresh "K" in if_cases K; zify_cond K; try rewrite !unsigned_zb in K; box_ugly K;
          [ apply evt_done; cbv beta; eexists; reflexivity
          | first [ exfalso; clear - K; lia | idtac ];
            st1b; norm_lits; norm_s32; st1b; norm_lits; norm_s32; st1b; norm_lits; norm_s32;
            let K2 := fresh "K" in if_cases K2; zify_cond K2; try rewrite !unsigned_zb in K2; box_ugly K2;
            [ exfalso; unbox_shad_for K2; lia
            | st1b; norm_lits; apply evt_done; cbv beta; eexists; reflexivity ] ]
        | cbv beta; let ms1 := fresh "ms" in let tv := fresh "jt" in intros ms1 (tv & ->) ]
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac step_sltiu :=
    st1b; rewrite v_sltiu_b2z; change (bv_wrap 64 (-10)) with 18446744073709551606;
    match goal with |- context [Z.b2z (bv_unsigned ?x <? 18446744073709551606)] =>
      let K := fresh "K" in
      destruct (Z.ltb_spec0 (bv_unsigned x) 18446744073709551606) as [K|K];
      [ change (Z.b2z true) with 1 | change (Z.b2z false) with 0 ];
      rewrite Z_to_bv_unsigned in K; unfold bv_wrap in K; replace (bv_modulus 64) with 18446744073709551616%Z in K by reflexivity; box_ugly K
    end.
(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1082768 => step_sltiu   (* [comment removed for export] *)
    | 1083144 => step_sltiu   (* [comment removed for export] *)
    | 1079700 => chkjoinb 11 1079708   (* [comment removed for export] *)
    | 1079784 => chkjoinb 12 1079792   (* [comment removed for export] *)
    | 1079832 => chkjoinb 12 1079840   (* [comment removed for export] *)
    | 1079880 => chkjoinb 12 1079888   (* [comment removed for export] *)
    | 1079944 => chkjoinb 12 1079952   (* [comment removed for export] *)
    | 1080084 => chkjoin 28 1080088   (* [comment removed for export] *)
    | 1080196 => chkjoin 6 1080200   (* [comment removed for export] *)
    | 1080296 => chkjoin 13 1080300   (* [comment removed for export] *)
    | 1080344 => chkjoin 13 1080348   (* [comment removed for export] *)
    | 1080424 => chkjoin 12 1080428   (* [comment removed for export] *)
    | 1080464 => chkjoin 12 1080468   (* [comment removed for export] *)
    | 1080488 => chkjoin 15 1080492   (* [comment removed for export] *)
    | 1080524 => chkjoin 12 1080528   (* [comment removed for export] *)
    | 1080548 => chkjoin 16 1080552   (* [comment removed for export] *)
    | 1080572 => chkjoin 16 1080576   (* [comment removed for export] *)
    | 1080648 => chkjoin 11 1080652   (* [comment removed for export] *)
    | 1080680 => chkjoin 12 1080684   (* [comment removed for export] *)
    | 1080780 => chkjoin 12 1080784   (* [comment removed for export] *)
    | 1080840 => chkjoin 12 1080844   (* [comment removed for export] *)
    | 1080920 => chkjoin 5 1080924   (* [comment removed for export] *)
    | 1081020 => chkjoin 12 1081024   (* [comment removed for export] *)
    | 1081460 => chkjoin 15 1081464   (* [comment removed for export] *)
    | 1081504 => chkjoin 12 1081508   (* [comment removed for export] *)
    | 1081548 => chkjoin 15 1081552   (* [comment removed for export] *)
    | 1081592 => chkjoin 12 1081596   (* [comment removed for export] *)
    | 1081636 => chkjoin 15 1081640   (* [comment removed for export] *)
    | 1081680 => chkjoin 12 1081684   (* [comment removed for export] *)
    | 1081724 => chkjoin 15 1081728   (* [comment removed for export] *)
    | 1081760 => chkjoin 12 1081764   (* [comment removed for export] *)
    | 1081808 => chkjoin 14 1081812   (* [comment removed for export] *)
    | 1081872 => chkjoin 12 1081876   (* [comment removed for export] *)
    | 1081916 => chkjoin 15 1081920   (* [comment removed for export] *)
    | 1081960 => chkjoin 12 1081964   (* [comment removed for export] *)
    | 1082004 => chkjoin 15 1082008   (* [comment removed for export] *)
    | 1082048 => chkjoin 12 1082052   (* [comment removed for export] *)
    | 1082092 => chkjoin 15 1082096   (* [comment removed for export] *)
    | 1082136 => chkjoin 12 1082140   (* [comment removed for export] *)
    | 1082180 => chkjoin 15 1082184   (* [comment removed for export] *)
    | 1082252 => chkjoin 12 1082256   (* [comment removed for export] *)
    | 1082296 => chkjoin 15 1082300   (* [comment removed for export] *)
    | 1082364 => chkjoin 13 1082368   (* [comment removed for export] *)
    | 1082416 => chkjoin 12 1082420   (* [comment removed for export] *)
    | 1082460 => chkjoin 15 1082464   (* [comment removed for export] *)
    | 1082580 => chkjoin 12 1082584   (* [comment removed for export] *)
    | 1082624 => chkjoin 15 1082628   (* [comment removed for export] *)
    | 1082668 => chkjoin 12 1082672   (* [comment removed for export] *)
    | 1082712 => chkjoin 15 1082716   (* [comment removed for export] *)
    | 1082756 => chkjoin 12 1082760   (* [comment removed for export] *)
    | 1082816 => chkjoin 5 1082820   (* [comment removed for export] *)
    | 1082840 => chkjoin 7 1082844   (* [comment removed for export] *)
    | 1082864 => chkjoin 28 1082868   (* [comment removed for export] *)
    | 1082888 => chkjoin 29 1082892   (* [comment removed for export] *)
    | 1083028 => chkjoin 15 1083032   (* [comment removed for export] *)
    | 1083072 => chkjoin 15 1083076   (* [comment removed for export] *)
    | 1083132 => chkjoin 15 1083136   (* [comment removed for export] *)
    | 1083184 => chkjoin 12 1083188   (* [comment removed for export] *)
    | 1083260 => chkjoin 17 1083264   (* [comment removed for export] *)
    | 1083388 => chkjoin 7 1083392   (* [comment removed for export] *)
    | 1083416 => chkjoin 30 1083420   (* [comment removed for export] *)
    | 1083440 => chkjoin 31 1083444   (* [comment removed for export] *)
    | 1083464 => chkjoin 31 1083468   (* [comment removed for export] *)
    | 1083624 => chkjoin 14 1083628   (* [comment removed for export] *)
    | 1083676 => chkjoin 16 1083680   (* [comment removed for export] *)
    | 1083696 => chkjoin 16 1083700   (* [comment removed for export] *)
    | 1083784 => chkjoin 12 1083788   (* [comment removed for export] *)
    | 1083808 => chkjoin 16 1083812   (* [comment removed for export] *)
    | 1083828 => chkjoin 17 1083832   (* [comment removed for export] *)
    | 1083852 => chkjoin 17 1083856   (* [comment removed for export] *)
    | 1083928 => chkjoin 11 1083932   (* [comment removed for export] *)
    | 1083980 => chkjoin 13 1083984   (* [comment removed for export] *)
    | 1084220 => chkjoin 12 1084224   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pregs : ltac2:(zQ "40!h9!hf!jf!o1>1r$3>3sp'@1$2@1$0#k0>2pa@1$2@1$0#k0>1e$1>1p$1P") := ltac2:(zQ "c0!h9!jf!pa!pf!q5!hf!qf!r5!rb!s1!s7!o1\1r$b\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5\1p$5@2$3@3$2@1$1@1$0#k0@1$a^5^4@2$3@3$2@1$1@1$0#k0@1$6^5^3@2$3@3$2@1$1@1$0#k0@1$7^5@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$8^5@2$4@1$0#k0+nvvvogg0@3$2@1$1@1$0#k0@1$9^5@2$4@1$0#k0^2").
  Ltac open_pregs UR := box_post; destruct UR as (?U1 & ?U2 & ?U3 & ?U4 & ?U5).
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ _ => unfold uregs
    | |- pregs _ _ _ _ _ => unfold pregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- ucells _ _ _ _ => unfold ucells
    | |- uvs _ _ _ _ _ _ _ _ => unfold uvs
    end.
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe, uvs in *; unfold seg_post, uregs, pregs, uframe, ucells, uvs; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    acb;
    try (lazymatch goal with APP : aapp _ 280 |- _ =>
           pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5); unfold AIMG_TOP in APB1; unfold AAPP_HI in APB3 end);
    shad_bounds.
(* [comment removed for export] *)
