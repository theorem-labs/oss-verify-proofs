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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg W_anum0 W_apstring0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import N8Store.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4bool46Stdlib6ZArith6BinInt1Zjb3eqb04Npos35stdpp9bitvectorbdefinitionslf2bvhc4listhc6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~p15asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA8W_apkey0~~~~~~t45AK8JTjb2lejb3sublf7Z_to_bvhc4Some37Corelib4Init5Logichj73andhj72eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshl8dov_read_bytest4aak8_target79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hqd3le4hqd7mem_invjb3addjb3muljb2ltjb6modulojb3pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~ih93mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ild4cellhc4consild2C8hc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ir48rw_cellslfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA6AKitRV~~~~~~jg92rvjg93ra0jg93rs1jg93rs4jg93rs7jg93rsp" s.   (* [comment removed for export] *)
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
Definition AK8JT : Z := 0x25888.
Definition ak8_target : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "30!j4!h9!l3\1c$1M0\0$0$1@2$2^1+1+hgtrjcM0\0$0$1@2$2^1+2+hgtsj4M0\0$0$1@2$2^1+3+hgtrrcM0\0$0$1@2$2^1+4+hgtrv8M0\0$0$1@2$2^1+5+hgtrn0M0\0$0$1@2$2^1+6+hgtsn0+hgtsr8").

  Lemma ak8jt_read : ltac2:(zQ "h30!l9!nc!o1!o8!sc!hh3!hhb!hi0!hi6!hj0!hkb!hl2!h9!hof!hq0!hu7!hue!hv9!hvf>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1c$c>0@2$h0$4^2>0@2$a@2$6+1^2@2$6^2+7@3$b@1$3@1$2@1$1@1$0#8@4$d$4^4@2$8@1$0#k0@2$h1$5@2$h2+4@2$7^3+1N4@2$9@1$2@1$1@1$0#8@1$f@2$8@1$0#k0@2$7@1$e^3$5").
  Proof.
    intros m c MI HC.
    assert (K : exists k : nat, (k < 7)%nat /\ c = 1 + Z.of_nat k) by (exists (Z.to_nat (c - 1)); lia).
    ndestruct K as (k & Hk & ->). clear HC.
    do 7 (destruct k as [|k]; [ro_tbl_case MI 4%nat le4|]).
    exfalso. lia.
  Qed.
  Lemma ak8_target_range : ltac2:(zQ "90!hq0!hkb!h9!hh3!ig5!hl2!hv9!iga!ih3>1c$2@2$1@2$1@2$4$3@1$0^1@2$4@1$0^1@2$6$3@2$8+2+hf@3$5$2@2$7@1$0^1+2Z").
  Proof. intros c. unfold ak8_target, AK8JT. repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kframe : ltac2:(zQ "30!l9!nc!il6>1m$2>3sp'@1$1@1$0#k0>2x0@1$1@1$0#k0>2x8@1$1@1$0#k0>3x16@1$1@1$0#k0>3x24@1$1@1$0#k0>3x32@1$1@1$0#k0>3tot@1$1@1$0#k0>3j48@1$1@1$0#k0>3p56@1$1@1$0#k0>3p64@1$1@1$0#k0>3v72@1$1@1$0#k0>3v80@1$1@1$0#k0>4s11v@1$1@1$0#k0>4s10v@1$1@1$0#k0>3s9v@1$1@1$0#k0>3s8v@1$1@1$0#k0>3s7v@1$1@1$0#k0>3s6v@1$1@1$0#k0>3s5v@1$1@1$0#k0>3s4v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0P") := ltac2:(zQ "a0!l9!ip9!nc!iq1!iq8!iqe!sc!il6!iuf!ivb\1m$7\3sp'@1$2@1$0#k0\2x0@1$2@1$0#k0\2x8@1$2@1$0#k0\3x16@1$2@1$0#k0\3x24@1$2@1$0#k0\3x32@1$2@1$0#k0\3tot@1$2@1$0#k0\3j48@1$2@1$0#k0\3p56@1$2@1$0#k0\3p64@1$2@1$0#k0\3v72@1$2@1$0#k0\3v80@1$2@1$0#k0\4s11v@1$2@1$0#k0\4s10v@1$2@1$0#k0\3s9v@1$2@1$0#k0\3s8v@1$2@1$0#k0\3s7v@1$2@1$0#k0\3s6v@1$2@1$0#k0\3s5v@1$2@1$0#k0\3s4v@1$2@1$0#k0\3s3v@1$2@1$0#k0\3s2v@1$2@1$0#k0\3s1v@1$2@1$0#k0\3s0v@1$2@1$0#k0\3rav@1$2@1$0#k0@4$8$6^ha@2$9@1$0#k0^h9@3$3$1@1$4^h8@3$3$1@1$4^h7@3$3$1@1$4^h6@3$3$1@1$4^h5@3$3$1@1$4^h4@3$3$1@1$4^h3@3$3$1@1$4^h2@3$3$1@1$4^h1@3$3$1@1$4^h0@3$3$1@1$4^f@3$3$1@1$4^e@3$3$1@1$4^d@3$3$1@1$4^c@3$3$1@1$4^b@3$3$1@1$4^a@3$3$1@1$4^9@3$3$1@1$4^8@3$3$1@1$4^7@3$3$1@1$4^6@3$3$1@1$4^5@3$3$1@1$4^4@3$3$1@1$4^3@3$3$1@1$4^2@3$3$1@1$4^1@1$5$1").
  (* [comment removed for export] *)
  Definition kctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    aceil <= lo /\ lo <= bv_unsigned sp' /\ bv_unsigned sp' + 192 <= 2^47 /\ aapp (bv_unsigned pa) 280 /\ bv_unsigned pa mod 16 = 0 /\ 0 <= e <= aceil.
  Ltac open_kctx UX := box_post; destruct UX as (CEIL & ROOM & SPT & APP & PA16 & EHI).
  (* [comment removed for export] *)
  Definition kregs : ltac2:(zQ "40!l9!nc!h9!jk6>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "e0!l9!nc!hl2!hkb!hi6!h9!jkc!jl3!jla!jm1!jm8!jk6!hv9!ivb\1r$b\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5@2$3@3$2@1$1@1$0#k0@1$a^4^3@2$3@3$2@1$1@1$0#k0@1$6^4^2@2$3@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0@2$c@2$d@1$0#k0^2+1@3$2@1$1@1$0#k0@1$9^4@2$4@1$0#k0+nvvvogg0").
  Ltac open_kregs UR := box_post; destruct UR as (?U1 & ?U2 & ?U3 & ?U4 & ?U5).
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- kregs _ _ _ _ => unfold kregs
    | |- kframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold kframe
    | |- scells _ _ _ => unfold scells
    end.
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold kframe in *; unfold seg_post, kregs, kframe, scells; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      try (pose proof (bv_unsigned_in_range _ a0) as RA0; unfold bv_modulus in RA0; cbn in RA0) end;
    acb;
    try (lazymatch goal with APP : aapp _ 280 |- _ =>
           pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5); unfold AIMG_TOP in APB1; unfold AAPP_HI in APB3 end);
    shad_bounds.
(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1105404 => step_sll56   (* [comment removed for export] *)
    | 1104288 => chkjoin 13 1104292   (* [comment removed for export] *)
    | 1104376 => chkjoin 13 1104380   (* [comment removed for export] *)
    | 1104596 => chkjoin 13 1104600   (* [comment removed for export] *)
    | 1104704 => chkjoin 13 1104708   (* [comment removed for export] *)
    | 1104724 => chkjoin 14 1104728   (* [comment removed for export] *)
    | 1104756 => chkjoin 13 1104760   (* [comment removed for export] *)
    | 1104776 => chkjoin 14 1104780   (* [comment removed for export] *)
    | 1104832 => chkjoin 13 1104836   (* [comment removed for export] *)
    | 1104852 => chkjoin 14 1104856   (* [comment removed for export] *)
    | 1104892 => chkjoin 13 1104896   (* [comment removed for export] *)
    | 1104912 => chkjoin 14 1104916   (* [comment removed for export] *)
    | 1104952 => chkjoin 13 1104956   (* [comment removed for export] *)
    | 1104972 => chkjoin 14 1104976   (* [comment removed for export] *)
    | 1105012 => chkjoin 13 1105016   (* [comment removed for export] *)
    | 1105032 => chkjoin 14 1105036   (* [comment removed for export] *)
    | 1105084 => chkjoin 13 1105088   (* [comment removed for export] *)
    | 1105104 => chkjoin 14 1105108   (* [comment removed for export] *)
    | 1105392 => chkjoin 13 1105396   (* [comment removed for export] *)
    | 1105908 => chkjoin 12 1105912   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
