(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJEhTabs BJKitW BJKitVS BJKitIn BJKitRV W_pesc0 W_pstr0.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJKitRV~~~~~~k42rv37Corelib4Init5Logico62eqo63andhf7Z_to_bvk43ra6k43ra7k43rrak43rs1k44rs10k44rs11k43rs3k43rs4k43rs5k43rs6k43rs7k43rs8k43rs9k43rspk43rt0k43rt1k43rt2k43rt3k43rt4k43rt5k43rt646Stdlib6ZArith6BinInt1Zhif3addhfbbv_unsigned37Corelib4Init9Datatypeshlc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hnc3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hsd4cellhlc4conshsd2C8hsd2CBhlc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iic8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~in35rsegshif4landhif2lehif2lt" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs; try transport_cond_ro segs m a bs.
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
  Definition kconsts : ltac2:(zQ "40!h9!jc!k1!o1>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "he0!h9!jc!pa!pf!q5!k1!qf!r5!rb!s1!s7!se!t5!tb!u1!u7!ud!v3!v9!vf!hg5!hgb!hh1!hh7!hhd!hi3!hi9!o1!hk7!hke\1r$hb\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5@2$3@3$2@1$1@1$0#k0@1$h3^4^3@2$3@3$2@1$1@1$0#k0@1$9^4@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0-jvjvghg0@2$3@3$2@1$1@1$0#k0@1$h4^4@2$4@1$0#k0+ogqgg0@2$3@3$2@1$1@1$0#k0@1$h5^4@2$4@1$0#k0+sgsgg0@2$3@3$2@1$1@1$0#k0@1$h6^4@2$4@1$0#k0+ogogg0@2$3@3$2@1$1@1$0#k0@1$c^4@2$4@1$0#k0+hmmm0@2$3@3$2@1$1@1$0#k0@1$d^4@2$4@1$0#k0+nvvvvvve@2$3@3$2@1$1@1$0#k0@1$e^4@2$4@1$0#k0@2$hc@2$hd@1$0#k0^2+1@2$3@3$2@1$1@1$0#k0@1$f^4@2$4@1$0#k0+i2@2$3@3$2@1$1@1$0#k0@1$h0^4@2$4@1$0#k0+lc@2$3@3$2@1$1@1$0#k0@1$h1^4@2$4@1$0#k0+i0@2$3@3$2@1$1@1$0#k0@1$h2^4@2$4@1$0#k0+6@2$3@3$2@1$1@1$0#k0@1$a^4@2$4@1$0#k0+ivg1@2$3@3$2@1$1@1$0#k0@1$b^4@2$4@1$0#k0+hkoqc@2$3@3$2@1$1@1$0#k0@1$h7^4@2$4@1$0#k0+nvnvngg0@2$3@3$2@1$1@1$0#k0@1$h8^4@2$4@1$0#k0-jvjvkgg0@2$3@3$2@1$1@1$0#k0@1$h9^4@2$4@1$0#k0-nvnvogg0@2$3@3$2@1$1@1$0#k0@1$ha^4@2$4@1$0#k0-kgg1@2$3@3$2@1$1@1$0#k0@1$6^4@2$4@1$0#k0-jvjvhgg0@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0+sgugg0").
  (* [comment removed for export] *)
  Definition ksregs : ltac2:(zQ "40!h9!jc!k1!o1>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "h40!h9!jc!pa!pf!q5!k1!s1!s7!se!t5!tb!u1!u7!ud!v3!v9!vf!o1!hk7!hke\1r$h1\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5@2$3@3$2@1$1@1$0#k0@1$h0^4^3@2$3@3$2@1$1@1$0#k0@1$6^4@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$9^4@2$4@1$0#k0+hmmm0@2$3@3$2@1$1@1$0#k0@1$a^4@2$4@1$0#k0+nvvvvvve@2$3@3$2@1$1@1$0#k0@1$b^4@2$4@1$0#k0@2$h2@2$h3@1$0#k0^2+1@2$3@3$2@1$1@1$0#k0@1$c^4@2$4@1$0#k0+i2@2$3@3$2@1$1@1$0#k0@1$d^4@2$4@1$0#k0+lc@2$3@3$2@1$1@1$0#k0@1$e^4@2$4@1$0#k0+i0@2$3@3$2@1$1@1$0#k0@1$f^4@2$4@1$0#k0+6@2$3@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0+ivg1@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0+hkoqc").
  Ltac open_kconsts SC := box_post; destruct SC as (?C1 & ?C2 & ?C3 & ?C4 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C10 & ?C11 & ?C12 & ?C13 & ?C14 & ?C15 & ?C16 & ?C17 & ?C18 & ?C19 & ?C20 & ?C21).
  Ltac open_ksregs SS := box_post; destruct SS as (?S1 & ?S2 & ?S3 & ?S4 & ?S5 & ?S6 & ?S7 & ?S8 & ?S9 & ?S10 & ?S11).
  (* [comment removed for export] *)
  Definition kframe : ltac2:(zQ "50!h9!jc!hn4!k1!hs6>1m$4>3sp'@1$1@1$0#k0>2j8@1$2@1$1@1$0#8>3ras@1$1@1$0#k0>3t6s@1$1@1$0#k0>3a5s@1$1@1$0#k0>3a0s@1$1@1$0#k0>3tot$3>3j40@1$2@1$1@1$0#8P") := ltac2:(zQ "e0!h9!ig9!ih1!jc!ih9!hn4!ihf!ii5!k1!im7!hs6!iqf!q5!hke\1m$a\3sp'@1$3@1$0#k0\2j8@1$5@1$3@1$0#8\3ras@1$3@1$0#k0\3t6s@1$3@1$0#k0\3a5s@1$3@1$0#k0\3a0s@1$3@1$0#k0\3tot$8\3j40@1$5@1$3@1$0#8@4$9$b^9@2$d@1$0#k0^8@3$2$1@2$6N8^7@3$2$1@1$4^6@3$2$1@1$4^5@3$2$1@1$4^4@3$2$1@1$4^3@3$2$1@1$4@2$c@1$0#k0^2@3$2$1@2$6Ni8^1@1$7$1").
  Ltac kseg_begin r :=
    intro_rv r; subst; unfold kframe in *; unfold seg_post, kconsts, ksregs, kframe, pcells; hide_post;
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
    | |- sconsts _ _ _ _ => unfold sconsts
    | |- ssregs _ _ _ _ => unfold ssregs
    | |- sframe _ _ _ _ _ _ _ => unfold sframe
    | |- kconsts _ _ _ _ => unfold kconsts
    | |- ksregs _ _ _ _ => unfold ksregs
    | |- kframe _ _ _ _ _ _ _ _ _ => unfold kframe
    end.
  (* [comment removed for export] *)
  Definition kctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    hceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 328 <= bv_unsigned pa /\ bv_unsigned pa + 280 <= 2^64 /\ e <= hceil.
  Ltac open_kctx SX := box_post; destruct SX as (CEIL & ROOM & SPA & A0HI & EHCL).
  Lemma land255_small : ltac2:(zQ "60!k1!pf!pa!ir8!is0!is6>1a$0>0@2$1@2$4Z^1@2$5^1+hg0@3$2$0@2$3^2+vf^2").
  Proof. intros a Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  (* [comment removed for export] *)
  Ltac fold_land255 :=
    repeat match goal with
    | |- context [Z_to_bv 64 (Z.land ?a 255)] => rewrite (land255_small a) by (rewrite ?unsigned_lit by lia; lia)
    end.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => first [ st1b | arm_inputs; st1b ]; norm_lits; fold_land255; gen_data
                end
            end).
