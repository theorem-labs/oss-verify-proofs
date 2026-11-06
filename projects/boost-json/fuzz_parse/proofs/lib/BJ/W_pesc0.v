(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJEhTabs BJKitW BJKitVS BJKitIn BJKitRV.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4bool46Stdlib6ZArith6BinInt1Zjb3addjb3ltbjb3sub04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJKitRV~~~~~~mb2rv35stdpp9bitvectorbdefinitionsqd2bv37Corelib4Init5Logicsf2eqsf3andqd7Z_to_bvmb3ra5mb3rs0mb4rs10mb4rs11mb3rs2mb3rs3mb3rs4mb3rs5mb3rs6mb3rs7mb3rs8mb3rs9mb3rspmb3rt2mb3rt4mb3rt5mb3rt6qdbbv_unsignedmb3rra79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7W_pesc0~~~~~~hn45pcorehc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hs13mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ih24cellhc4consih22C8hc3nilih22CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~imf8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~ir65rsegsih22C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jg12b8jb2ltimf8ro_cellsjb2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jl87v_sltiujl86v_sltujb6of_nathc6lengthhn47cond_rosf2or3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjsecwrite_to_memih2acells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ki32wajb3pow" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
(* [comment removed for export] *)
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
Definition pclip : ltac2:(zQ "10!h9>1q$0>1e$0$0") := ltac2:(zQ "50!h9!j4!l3!l9!lf\1q$0\1e$0M1\0$1$0@2$3+hg0@2$4^1^2@2$2^2+hg0^1").


  (* [comment removed for export] *)
  Definition pcore : ltac2:(zQ "40!h9!m5!q8!sa>1r$2>3sp'@1$3@1$1#k0>1e$0>1c$0P") := ltac2:(zQ "ha0!m5!sa!u3!u8!ue!h9!v8!ve!hg4!hgb!hh2!hh8!hhe!hi4!hia!hj0!hj6!hjc!hk2!hk8!hke!hl4!hla!q8!l3!hm0\1r$h7\3sp'@1$1@1$0#k0\1e$5\1c$5@2$3@3$2@1$1@1$0#k0@1$h2^4^3@2$3@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$h4^4@2$4@1$0#k0^2@2$3@3$2@1$1@1$0#k0@1$d^4@2$4@1$0#k0@2$h8@2$h9@1$0#k0^3+l0@2$3@3$2@1$1@1$0#k0@1$h3^4@2$4@1$0#k0+hg0@2$3@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0-og1@2$3@3$2@1$1@1$0#k0@1$a^4@2$4@1$0#k0+nf@2$3@3$2@1$1@1$0#k0@1$b^4@2$4@1$0#k0+5@2$3@3$2@1$1@1$0#k0@1$c^4@2$4@1$0#k0+lc@2$3@3$2@1$1@1$0#k0@1$e^4@2$4@1$0#k0+n5@2$3@3$2@1$1@1$0#k0@1$f^4@2$4@1$0#k0+b@2$3@3$2@1$1@1$0#k0@1$h0^4@2$4@1$0#k0+9@2$3@3$2@1$1@1$0#k0@1$h1^4@2$4@1$0#k0+a@2$3@3$2@1$1@1$0#k0@1$9^4@2$4@1$0#k0-ugg0@2$3@3$2@1$1@1$0#k0@1$h5^4@2$4@1$0#k0-1@2$3@3$2@1$1@1$0#k0@1$h6^4@2$4@1$0#k0+nvf@3$2@1$1@1$0#k0@1$6^4@2$4@1$0#k0Z").
  Definition pconsts : ltac2:(zQ "40!h9!m5!q8!sa>1r$2>3sp'@1$3@1$1#k0>1e$0>1c$0P") := ltac2:(zQ "90!m5!h9!sa!u8!u3!hme!q8!hr1!ue\1r$6\3sp'@1$2@1$0#k0\1e$1\1c$1@2$3@4$7^4^3^2^1@3$4@1$2@1$0#k0@1$5^4@2$8@1$0#k0+j7").
  (* [comment removed for export] *)
  Definition pframe : ltac2:(zQ "40!m5!sa!hra!igb>1m$3>3sp'@1$1@1$0#k0>2j8@1$2@1$1@1$0#8>3a1s@1$1@1$0#k0>3a5s@1$1@1$0#k0>3a0s@1$1@1$0#k0>3t4s@1$1@1$0#k0>3a2s@1$1@1$0#k0>3t3s@1$1@1$0#k0P") := ltac2:(zQ "d0!m5!ike!il6!ild!sa!ue!hra!im3!im9!iqa!igb!iv2!hm0\1m$a\3sp'@1$4@1$0#k0\2j8@1$6@1$4@1$0#8\3a1s@1$4@1$0#k0\3a5s@1$4@1$0#k0\3a0s@1$4@1$0#k0\3t4s@1$4@1$0#k0\3a2s@1$4@1$0#k0\3t3s@1$4@1$0#k0@4$9$b^9@2$c@1$0#k0^8@3$2$1@2$8N8^7@3$2$1@1$3^6@3$2$1@1$3^5@3$2$1@1$3^4@3$2$1@1$3^3@3$2$1@1$3^2@3$2$1@1$3^1@3$2$1@1$3@2$5@1$0#k0+rvuf@3$2$1@1$3@2$5@1$0#k0+vvvvvvvvvsqgikg0@3$2$1@1$3@2$5@1$0#k0+nvvvvvve@1$7$1").
  Definition psize : ltac2:(zQ "40!m5!h9!igb!sa>1m$2>3sp'@1$3@1$0#k0>2sz$1P") := ltac2:(zQ "d0!m5!ike!il6!im3!h9!ild!iqa!igb!iv2!l3!ue!sa!hm0\1m$7\3sp'@1$b@1$0#k0\2sz$4@4$6$8^3@2$9@2$c@1$0#k0^2+hl0@3$2$1@1$5@2$a@1$0#k0^1@1$3$1").
  (* [comment removed for export] *)
  Definition pcells : ltac2:(zQ "50!m5!sa!hra!h9!igb>1m$4>2pa@1$1@1$0#k0>1e$3>2sc@1$2@1$1@1$0#8>4pad7@1$2@1$1@1$0#8>2v1@1$1@1$0#k0>2v2@1$1@1$0#k0>2v3@1$1@1$0#k0P") := ltac2:(zQ "h20!m5!ike!il6!sa!im3!ild!iqa!iv2!l3!hm0!u8!hra!im9!h9!ivb!jjc!igb!ue\1m$h0\2pa@1$3@1$0#k0\1e$d\2sc@1$b@1$3@1$0#8\4pad7@1$b@1$3@1$0#8\2v1@1$3@1$0#k0\2v2@1$3@1$0#k0\2v3@1$3@1$0#k0@2$a@4$6$7^8@2$8@2$9@1$0#k0^7+q0@3$2$1@2$cNh0^5@1$4$1@2$a@4$6$7^8@2$8@2$9@1$0#k0^7+r0@3$2$1@1$e@1$fZ@3$2$1@2$cN7^4@1$4$1@2$a@4$6$7^8@2$8@2$9@1$0#k0^7+r8@3$2$1@1$5@2$h1@1$0#k0^6@1$4$1@4$6$7^8@2$8@2$9@1$0#k0^7+l8@3$2$1@1$5^3@3$2$1@1$5^2@3$2$1@1$5^1@1$4$1").
  (* [comment removed for export] *)
  Definition pctx {HCEIL : HeapCeil} (sp' pa ta : word) (lo e : Z) : Prop :=
    hceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 448 <= bv_unsigned ta /\ bv_unsigned ta + 8 <= bv_unsigned pa /\
    bv_unsigned pa + 280 <= 2^64 /\ e <= hceil.
  Ltac open_pctx PX := box_post; destruct PX as (CEIL & ROOM & TA1 & TA2 & A0HI & EH).
  Ltac open_pcore PC := box_post; destruct PC as (?C1 & ?C2 & ?C3 & ?C4 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C10 & ?C11 & ?C12 & ?C13 & ?C14 & ?C15 & ?C16 & ?C17).
  Ltac open_pconsts PC := box_post; let PCO := fresh "PCO" in destruct PC as [PCO ?C0]; open_pcore PCO.
  Ltac open_pcells PM := box_post; destruct PM as (SCR & MORE & END & EC).
  Ltac seg_begin r :=
    intro_rv r; subst; unfold pframe, psize in *; unfold seg_post, pconsts, pcore, pframe, psize, pcells; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ a0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    hcb.

  (* [comment removed for export] *)
  Definition pinput : ltac2:(zQ "40!h9!m5!igb!sa>1m$2>1q$0>1e$0>3inb>0$0@1$3@1$1#8P") := ltac2:(zQ "d0!h9!ike!jk2!il6!im3!m5!ivb!jk7!igb!iv2!l3!jl3!sa\1m$8\1q$0\1e$0\3inb>0$0@1$c@1$5#8>1x$0>0@2$b^4^1>0@2$2^2^4>0@2$2^3@2$a^6+c@4$7$9^8^4@3$3$1@1$6@1^5^4@1$4$1").

  (* [comment removed for export] *)

  Lemma sltiu_range : ltac2:(zQ "70!m5!jp7!jl3!hm0!u8!h9!sa>1x@1$6@1$0#k0>3imm$5@2$4@2$2Z@2$3@1$0#k0@2$1^2^1@2$2@2$3@1$0#k0@2$1^2^1+1").
  Proof. intros x imm. unfold v_sltiu. destruct (bv_unsigned x <? bv_wrap 64 imm); rewrite unsigned_lit by lia; lia. Qed.
  Lemma sltu_range : ltac2:(zQ "60!m5!jq2!jl3!sa!hm0!u8>1x@1$3@1$0#k0>1y@1$3@1$0#k0@2$5@2$2Z@2$4@1$0#k0@2$1^2^1@2$2@2$4@1$0#k0@2$1^2^1+1").
  Proof. intros x y. rewrite v_sltu_b2z. destruct (bv_unsigned x <? bv_unsigned y); cbn [Z.b2z]; rewrite unsigned_lit by lia; lia. Qed.
  (* [comment removed for export] *)
  Ltac sltiu_bounds :=
    repeat match goal with
    | |- context [bv_unsigned (v_sltiu ?a ?b)] =>
        pose proof (sltiu_range a b); let u := fresh "u" in set (u := bv_unsigned (v_sltiu a b)) in *; clearbody u
    | |- context [bv_unsigned (v_sltu ?a ?b)] =>
        pose proof (sltu_range a b); let u := fresh "u" in set (u := bv_unsigned (v_sltu a b)) in *; clearbody u
    end.
  Ltac fin_arith ::= first [ lia | rewrite ?unsigned_lit by lia; lia | sltiu_bounds; rewrite ?unsigned_lit by lia; lia ].
  (* [comment removed for export] *)
  Definition psregs : ltac2:(zQ "40!m5!h9!q8!sa>1r$2>3sp'@1$3@1$0#k0>1c$1P") := ltac2:(zQ "h50!m5!sa!u3!u8!ue!h9!ve!hg4!hgb!hh2!hh8!hhe!hi4!hia!hj0!hj6!hjc!hk2!q8!l3!hm0\1r$h2\3sp'@1$1@1$0#k0\1c$5@2$3@3$2@1$1@1$0#k0@1$h1^3^2@2$3@3$2@1$1@1$0#k0@1$7^3@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$c^3@2$4@1$0#k0@2$h3@2$h4@1$0#k0^2+l0@2$3@3$2@1$1@1$0#k0@1$6^3@2$4@1$0#k0-og1@2$3@3$2@1$1@1$0#k0@1$9^3@2$4@1$0#k0+nf@2$3@3$2@1$1@1$0#k0@1$a^3@2$4@1$0#k0+5@2$3@3$2@1$1@1$0#k0@1$b^3@2$4@1$0#k0+lc@2$3@3$2@1$1@1$0#k0@1$d^3@2$4@1$0#k0+n5@2$3@3$2@1$1@1$0#k0@1$e^3@2$4@1$0#k0+b@2$3@3$2@1$1@1$0#k0@1$f^3@2$4@1$0#k0+9@2$3@3$2@1$1@1$0#k0@1$h0^3@2$4@1$0#k0+a@3$2@1$1@1$0#k0@1$8^3@2$4@1$0#k0-ugg0").
  Ltac open_psregs PS := box_post; destruct PS as (?S1 & ?S2 & ?S3 & ?S4 & ?S5 & ?S6 & ?S7 & ?S8 & ?S9 & ?S10 & ?S11 & ?S12).
  Ltac seg_begin r ::=
    intro_rv r; subst; unfold pframe, psize in *; unfold seg_post, pconsts, pcore, psregs, pframe, psize, pcells; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ a0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    hcb.

  Ltac seg_unfold ::=
    lazymatch goal with
    | |- pconsts _ _ _ _ => unfold pconsts
    | |- pcore _ _ _ _ => unfold pcore
    | |- psregs _ _ _ => unfold psregs
    | |- pframe _ _ _ _ _ _ _ _ _ => unfold pframe
    | |- psize _ _ _ => unfold psize
    | |- pcells _ _ _ _ _ _ _ _ => unfold pcells
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cond_ro : ltac2:(zQ "40!hra!h9!ike!igb>1cP>1m$3>1A$1>2cs@1$0$2P") := ltac2:(zQ "60!hra!h9!ike!jk7!igb!iv2\1cP\1m$4\1A$1\2cs@1$0$2>0^4@4$3$5^4^3^2").
  Lemma cond_ro_frame : ltac2:(zQ "h00!jl3!m5!l3!jqc!sa!jr5!hra!h9!jre!js9!kg5!ike!kh5!kld!igb!km3>1cP>1m$e>1A$7>2cs@1$6$b>1a$7>2bs@1$6@1$4@1$1#8>0@4$8^6^5^4^3>0@2$0Z^3>0@2$0@2$2^4@1$3@2$5@1$4@1$1#8^3@2$f+2+k0>0@2$9@2$0@2$2^7@1$3@1$c^6^5@2$0@2$2^5@1$3@2$5@1$4@1$1#8^4^7@4$8^a@3$a^9@1$d^6^5^8^7").
  Proof. intros c m A cs a bs H Ha Hb Hd Hc. apply ro_cells_frame; auto. Qed.
  Ltac transport_cond_ro segs m a bs :=
    repeat match goal with
    | H : cond_ro ?c m ?A2 ?cs2 |- _ =>
        first [ apply (cond_ro_frame c m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping conditional input fact" H; clear H ]
    end.
  Ltac arm_inputs :=
    repeat match goal with
    | H : cond_ro ?c ?m ?A ?cs |- _ =>
        let Hc := fresh "Hc" in assert (Hc : c) by lia; unfold cond_ro in H; specialize (H Hc); clear Hc
    end.
  Ltac pose_cond_inputs INB q e :=
    try pose proof ((fun H : q < e => INB q ltac:(lia) H ltac:(lia)) : cond_ro (q < e) _ q _) as IR0;
    try pose proof ((fun H : q + 1 < e => INB (q + 1) ltac:(lia) H ltac:(lia)) : cond_ro (q + 1 < e) _ (q + 1) _) as IR1;
    try pose proof ((fun H : q + 2 < e => INB (q + 2) ltac:(lia) H ltac:(lia)) : cond_ro (q + 2 < e) _ (q + 2) _) as IR2;
    try pose proof ((fun H : q + 3 < e => INB (q + 3) ltac:(lia) H ltac:(lia)) : cond_ro (q + 3 < e) _ (q + 3) _) as IR3;
    try pose proof ((fun H : q + 4 < e => INB (q + 4) ltac:(lia) H ltac:(lia)) : cond_ro (q + 4 < e) _ (q + 4) _) as IR4;
    try pose proof ((fun H : q + 5 < e => INB (q + 5) ltac:(lia) H ltac:(lia)) : cond_ro (q + 5 < e) _ (q + 5) _) as IR5;
    try pose proof ((fun H : q + 6 < e => INB (q + 6) ltac:(lia) H ltac:(lia)) : cond_ro (q + 6 < e) _ (q + 6) _) as IR6;
    try pose proof ((fun H : q + 7 < e => INB (q + 7) ltac:(lia) H ltac:(lia)) : cond_ro (q + 7 < e) _ (q + 7) _) as IR7;
    try pose proof ((fun H : q + 8 < e => INB (q + 8) ltac:(lia) H ltac:(lia)) : cond_ro (q + 8 < e) _ (q + 8) _) as IR8;
    try pose proof ((fun H : q + 9 < e => INB (q + 9) ltac:(lia) H ltac:(lia)) : cond_ro (q + 9 < e) _ (q + 9) _) as IR9;
    try pose proof ((fun H : q + 10 < e => INB (q + 10) ltac:(lia) H ltac:(lia)) : cond_ro (q + 10 < e) _ (q + 10) _) as IR10;
    try pose proof ((fun H : q + 11 < e => INB (q + 11) ltac:(lia) H ltac:(lia)) : cond_ro (q + 11 < e) _ (q + 11) _) as IR11;
    arm_inputs.
  (* [comment removed for export] *)
  Ltac inputs INB q e tac := pose_cond_inputs INB q e; tac.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => first [ st1b | arm_inputs; st1b ]; gen_data
                end
            end).

(* [comment removed for export] *)
