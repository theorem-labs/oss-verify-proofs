(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap BJIface BJEhTabs BJKitW BJKitVS BJKitIn BJKitRV BJKitStr BJKitSeg BJKitNum W_unum0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~m03mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~r14cellk14consr12C8r12C1r12C4r12CBk13nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hh58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hlc5rsegshfbbv_unsigned01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJKitRV~~~~~~hr32rv37Corelib4Init5Logichv72eqhv73andhr33rs0hr33rs4hr33rsphf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ij73le4k13appk16option3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseio7h0le_bytes_to_word" s.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


  (* [comment removed for export] *)
  Definition nframe : ltac2:(zQ "40!h9!jc!l9!qb>1m$3>3sp'@1$1@1$0#k0>3j16@1$2@1$1@1$0#8>4mant@1$1@1$0#k0>4bias@1$1@1$0#k0>4expo@1$1@1$0#k0>2fz@1$1@1$0#8>2ng@1$1@1$0#8>2j6@1$2@1$1@1$0#8>4fs0v@1$1@1$0#k0>3s4v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0P") := ltac2:(zQ "e0!h9!ud!jc!v4!vb!l9!hg0!hg5!hga!hgf!hl0!qb!hp9!hq2\1m$b\3sp'@1$2@1$0#k0\3j16@1$5@1$2@1$0#8\4mant@1$2@1$0#k0\4bias@1$2@1$0#k0\4expo@1$2@1$0#k0\2fz@1$2@1$0#8\2ng@1$2@1$0#8\2j6@1$5@1$2@1$0#8\4fs0v@1$2@1$0#k0\3s4v@1$2@1$0#k0\3s3v@1$2@1$0#k0\3s2v@1$2@1$0#k0\3s1v@1$2@1$0#k0\3s0v@1$2@1$0#k0\3rav@1$2@1$0#k0@4$a$c^h0@2$d@1$0#k0^f@3$3$1@2$8Nh0^e@3$3$1@1$4^d@3$3$1@1$7^c@3$3$1@1$7^b@3$3$1@1$6^a@3$3$1@1$6^9@3$3$1@2$8N6^8@3$3$1@1$4^7@3$3$1@1$4^6@3$3$1@1$4^5@3$3$1@1$4^4@3$3$1@1$4^3@3$3$1@1$4^2@3$3$1@1$4^1@1$9$1").
  Definition nregs : ltac2:(zQ "40!h9!jc!hr0!hv1>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "a0!h9!jc!igb!ih1!hr0!ih8!ihf!ii6!hv1!iid\1r$8\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$4@2$3@3$2@1$1@1$0#k0@1$7^4^3@2$3@3$2@1$1@1$0#k0@1$5^4^2@3$2@1$1@1$0#k0@1$6^4@2$9@1$0#k0^1").
  Ltac open_nregs UR := box_post; destruct UR as (?U1 & ?U2 & ?U3).
  Definition nctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    hceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 232 <= bv_unsigned pa /\ bv_unsigned pa + 280 <= 2^64 /\ e <= hceil.
  Ltac open_nctx UX := box_post; destruct UX as (CEIL & ROOM & SPA & A0HI & EHCL).
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ => unfold uregs
    | |- nregs _ _ _ _ => unfold nregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- nframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold nframe
    | |- ucells _ _ _ _ => unfold ucells
    | |- uvs _ _ _ _ _ _ _ _ => unfold uvs
    end.
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe, nframe, uvs in *; unfold seg_post, uregs, nregs, uframe, nframe, ucells, uvs; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    hcb.
  (* [comment removed for export] *)
  Lemma nframe_merge16 : ltac2:(zQ "h10!ud!v4!h9!vb!jc!hg0!hga!l9!hgf!hg5!in1!hl0!hp9!in8!ine!hr0!ir6>1m>0@1$4@1$2#k0@1$e@1$4@1$2#8>1A$f>3j16@1$7@1$4@1$2#8>2mw@1$4@1$2#k0>1b@1$4@1$2#k0>1x@1$4@1$2#k0>2xg@1$4@1$2#8>2ng@1$4@1$2#8>2j6@1$7@1$4@1$2#8>2f8@1$4@1$2#k0>3s4v@1$4@1$2#k0>3s3v@1$4@1$2#k0>3s2v@1$4@1$2#k0>3s1v@1$4@1$2#k0>3s0v@1$4@1$2#k0>3rav@1$4@1$2#k0>0@4$b$c^h0^f@3$1$0@2$6Nh0^e@3$1$0@1$3^d@3$1$0@1$9^c@3$1$0@1$9^b@3$1$0@1$5^a@3$1$0@1$5^9@3$1$0@2$6N6^8@3$1$0@1$3^7@3$1$0@1$3^6@3$1$0@1$3^5@3$1$0@1$3^4@3$1$0@1$3^3@3$1$0@1$3^2@3$1$0@1$3^1@1$8$0@4$b$c^h1^h0@3$1$0@2$6Nh0^f@3$1$0@1$3^e@3$1$0@1$3@1$h0@3$d@1$4@1$2#8@1$a^d@1$a^c@3$1$0@1$5^b@3$1$0@1$5^a@3$1$0@2$6N6^9@3$1$0@1$3^8@3$1$0@1$3^7@3$1$0@1$3^6@3$1$0@1$3^5@3$1$0@1$3^4@3$1$0@1$3^3@3$1$0@1$3^2@1$8$0").
  Proof.
    intros until rav. intros R. pose proof R as [[W _] _]. cbn in W.
    eapply rw_cells_rebytes; [exact R| | | reflexivity].
    - cbn. tauto.
    - cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by (rewrite length_app, !length_le4; reflexivity). rewrite <- ?app_assoc. reflexivity.
  Qed.
  Ltac merge16 ::=
    match goal with
    | UF : rw_cells _ ?m ?A [CB 8 _; C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply uframe_merge16 in UF
    | UF : rw_cells _ ?m ?A [CB 16 _; C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply nframe_merge16 in UF
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac prune_or' tac := first [ exfalso; lia | tac ].
  Ltac explore2' stops :=
    run_to stops;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        lazymatch stops with
        | context [pc] => first [fin_leaf | idtac "=== FINISHER FAILED at" pc; print_leaf]
        | _ => idtac "=== STUCK at" pc; print_leaf
        end
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "K" in if_cases K; zify_cond K; try rewrite !unsigned_zb in K; try box_ugly K;
        [ prune_or' ltac:(explore2' stops) | prune_or' ltac:(explore2' stops) ]
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => first [fin_leaf_ret | idtac "=== FINISHER FAILED at (nonliteral)" pc; print_leaf]
    end.
  Ltac explore2_1' stops := step1; explore2' stops.
  (* [comment removed for export] *)
  Ltac norm_irs :=
    repeat match goal with H : cond_ro _ _ (?q + ?a + ?b)%Z _ |- _ =>
      let a' := zlit a in let b' := zlit b in let c := eval vm_compute in (a' + b')%Z in
      replace (q + a + b)%Z with (q + c)%Z in H by lia end.
(* [comment removed for export] *)
