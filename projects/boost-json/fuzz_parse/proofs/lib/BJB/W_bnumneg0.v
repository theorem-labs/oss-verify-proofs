(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg W_bnum0.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import N8Store.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~m03mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~q34cellk14consq32C8q32C1q32C4q32CBk13nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hg75asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hkb8rw_cellshfbbv_unsigned01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB6AKitRV~~~~~~hq32rv37Corelib4Init5Logichu62eqhu63andhf7Z_to_bvhq33rs0hq33rs2hq33rs5hq33rsp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~iid3le4k13appk16option3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseindh0le_bytes_to_word" s.
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
  (* [comment removed for export] *)
  Definition nframe : ltac2:(zQ "40!h9!jc!l9!pd>1m$3>3sp'@1$1@1$0#k0>3j16@1$2@1$1@1$0#8>4mant@1$1@1$0#k0>4bias@1$1@1$0#k0>4expo@1$1@1$0#k0>4xneg@1$1@1$0#8>3neg@1$1@1$0#8>2j6@1$2@1$1@1$0#8>4fs0v@1$1@1$0#k0>3s6v@1$1@1$0#k0>3s5v@1$1@1$0#k0>3s4v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0P") := ltac2:(zQ "e0!h9!tf!jc!u6!ud!l9!v2!v7!vc!hg1!hk2!pd!ho6!hp2\1m$b\3sp'@1$2@1$0#k0\3j16@1$5@1$2@1$0#8\4mant@1$2@1$0#k0\4bias@1$2@1$0#k0\4expo@1$2@1$0#k0\4xneg@1$2@1$0#8\3neg@1$2@1$0#8\2j6@1$5@1$2@1$0#8\4fs0v@1$2@1$0#k0\3s6v@1$2@1$0#k0\3s5v@1$2@1$0#k0\3s4v@1$2@1$0#k0\3s3v@1$2@1$0#k0\3s2v@1$2@1$0#k0\3s1v@1$2@1$0#k0\3s0v@1$2@1$0#k0\3rav@1$2@1$0#k0@4$c$a^h2@2$d@1$0#k0^h1@3$3$1@2$8Nh0^h0@3$3$1@1$4^f@3$3$1@1$7^e@3$3$1@1$7^d@3$3$1@1$6^c@3$3$1@1$6^b@3$3$1@2$8N6^a@3$3$1@1$4^9@3$3$1@1$4^8@3$3$1@1$4^7@3$3$1@1$4^6@3$3$1@1$4^5@3$3$1@1$4^4@3$3$1@1$4^3@3$3$1@1$4^2@3$3$1@1$4^1@1$9$1").
  (* [comment removed for export] *)
  Definition nctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    aceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 112 <= 2^47 /\ aapp (bv_unsigned pa) 280 /\ bv_unsigned pa mod 16 = 0 /\ 0 <= e <= aceil.
  Ltac open_nctx UX := box_post; destruct UX as (CEIL & ROOM & SPT & APP & PA16 & EHI).
  (* [comment removed for export] *)
  Definition nregs : ltac2:(zQ "40!h9!jc!hq0!hu0>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "b0!h9!jc!hva!ig0!ig7!hq0!ih1!ih8!ihf!ii6!hu0\1r$a\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5@2$3@3$2@1$1@1$0#k0@1$9^4^3@2$3@3$2@1$1@1$0#k0@1$6^4^2@2$3@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0+nvvvogg0@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0^1").
  Ltac open_nregs UR := box_post; destruct UR as (?U1 & ?U2 & ?U3 & ?U4).
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ => unfold uregs
    | |- nregs _ _ _ _ => unfold nregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- nframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold nframe
    | |- ucells _ _ _ _ => unfold ucells
    | |- uvs _ _ _ _ _ _ _ _ => unfold uvs
    end.
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe, nframe, uvs in *; unfold seg_post, uregs, nregs, uframe, nframe, ucells, uvs; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    acb;
    try (lazymatch goal with APP : aapp _ 280 |- _ =>
           pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5); unfold AIMG_TOP in APB1; unfold AAPP_HI in APB3 end);
    shad_bounds.
  (* [comment removed for export] *)
  Lemma nframe_merge8 : ltac2:(zQ "h10!tf!u6!ud!h9!jc!v2!vc!l9!hg1!hk2!v7!im7!ho6!ime!in4!hq0!iqc>1m>0@1$4@1$3#k0@1$e@1$4@1$3#8>1A$f>3j16@1$7@1$4@1$3#8>2mw@1$4@1$3#k0>1b@1$4@1$3#k0>1x@1$4@1$3#k0>2xg@1$4@1$3#8>2ng@1$4@1$3#8>2j6@1$7@1$4@1$3#8>2f0@1$4@1$3#k0>3s6v@1$4@1$3#k0>3s5v@1$4@1$3#k0>3s4v@1$4@1$3#k0>3s3v@1$4@1$3#k0>3s2v@1$4@1$3#k0>3s1v@1$4@1$3#k0>3s0v@1$4@1$3#k0>3rav@1$4@1$3#k0>0@4$c$9^h2^h1@3$1$0@2$6Nh0^h0@3$1$0@1$2^f@3$1$0@1$a^e@3$1$0@1$a^d@3$1$0@1$5^c@3$1$0@1$5^b@3$1$0@2$6N6^a@3$1$0@1$2^9@3$1$0@1$2^8@3$1$0@1$2^7@3$1$0@1$2^6@3$1$0@1$2^5@3$1$0@1$2^4@3$1$0@1$2^3@3$1$0@1$2^2@3$1$0@1$2^1@1$8$0@4$c$9^h3^h2@3$1$0@2$6Nh0^h1@3$1$0@1$2^h0@3$1$0@1$2@1$h0@3$d@1$4@1$3#8@1$b^f@1$b^e@3$1$0@1$5^d@3$1$0@1$5^c@3$1$0@2$6N6^b@3$1$0@1$2^a@3$1$0@1$2^9@3$1$0@1$2^8@3$1$0@1$2^7@3$1$0@1$2^6@3$1$0@1$2^5@3$1$0@1$2^4@3$1$0@1$2^3@3$1$0@1$2^2@1$8$0").
  Proof.
    intros until rav. intros R. pose proof R as [[W _] _]. cbn in W.
    eapply rw_cells_rebytes; [exact R| | | reflexivity].
    - cbn. tauto.
    - cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by (rewrite length_app, !length_le4; reflexivity). rewrite <- ?app_assoc. reflexivity.
  Qed.
  Ltac merge8 ::=
    match goal with
    | UF : rw_cells _ ?m ?A [C8 _; C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply uframe_merge8 in UF
    | UF : rw_cells _ ?m ?A [CB 16 _; C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply nframe_merge8 in UF
    end.
  Ltac print_hyps ::=
    try (match goal with H : ?T |- _ =>
           lazymatch T with
           | boxP ?P => idtac "  " H ": BOX" P
           | rw_cells _ _ _ _ => idtac "  " H ":" T
           | ro_cells _ _ _ _ => idtac "  " H ":" T
           | @eq Z _ _ => idtac "  " H ":" T
           | Z.lt _ _ => idtac "  " H ":" T
           | Z.le _ _ => idtac "  " H ":" T
           | not _ => idtac "  " H ":" T
           | _ /\ _ => idtac "  " H ":" T
           | _ \/ _ => idtac "  " H ":" T
           | munch _ _ _ => idtac "  " H ":" T
           | stk _ _ _ _ => idtac "  " H ":" T
           | _ => fail
           end; fail end).

(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1045648 => chkjoin 11 1045652   (* [comment removed for export] *)
    | 1045708 => chkjoin 11 1045712   (* [comment removed for export] *)
    | 1045832 => chkjoin 6 1045836   (* [comment removed for export] *)
    | 1045972 => chkjoin 7 1045976   (* [comment removed for export] *)
    | 1046092 => chkjoin 12 1046096   (* [comment removed for export] *)
    | 1046152 => chkjoin 14 1046156   (* [comment removed for export] *)
    | 1046300 => chkjoin 11 1046304   (* [comment removed for export] *)
    | 1046384 => chkjoin 11 1046388   (* [comment removed for export] *)
    | 1046448 => chkjoin 5 1046452   (* [comment removed for export] *)
    | 1046760 => chkjoin 13 1046764   (* [comment removed for export] *)
    | 1046852 => chkjoin 12 1046856   (* [comment removed for export] *)
    | 1047016 => chkjoin 11 1047020   (* [comment removed for export] *)
    | 1047068 => chkjoin 12 1047072   (* [comment removed for export] *)
    | 1047148 => chkjoin 12 1047152   (* [comment removed for export] *)
    | 1047244 => chkjoin 6 1047248   (* [comment removed for export] *)
    | 1047476 => chkjoin 12 1047480   (* [comment removed for export] *)
    | 1047552 => chkjoin 11 1047556   (* [comment removed for export] *)
    | 1047616 => chkjoin 13 1047620   (* [comment removed for export] *)
    | 1047676 => chkjoin 12 1047680   (* [comment removed for export] *)
    | 1047900 => chkjoin 13 1047904   (* [comment removed for export] *)
    | 1048000 => chkjoin 12 1048004   (* [comment removed for export] *)
    | 1048652 => chkjoin 13 1048656   (* [comment removed for export] *)
    | 1048796 => chkjoin 12 1048800   (* [comment removed for export] *)
    | 1048920 => chkjoin 12 1048924   (* [comment removed for export] *)
    | 1048980 => chkjoin 12 1048984   (* [comment removed for export] *)
    | 1049008 => chkjoin 12 1049012   (* [comment removed for export] *)
    | 1049084 => chkjoin 13 1049088   (* [comment removed for export] *)
    | 1049240 => chkjoin 12 1049244   (* [comment removed for export] *)
    | 1049544 => chkjoin 12 1049548   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
