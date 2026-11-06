(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import N8Store.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc6shiftr37Corelib4Init5Logick32eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7W_bnum0~~~~~~lc3sh8hc2lek33andhc2lthc3pow04Npos35stdpp9bitvectorbdefinitionsrc2bv37Corelib4Init9Datatypeste4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~vd3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hk04cellte4conshk02C8hk02C1hk02C4te3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hq35asegshk02CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hud8rw_cellsrcbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ik22b8hud8ro_cellsrc7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB6AKitRV~~~~~~ip92rvip93rs0ip93rs2ip93rs4ip93rsphc3opprc8bv_swrap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jg94sx32rc9bv_signedhc3mulhc6modulok33iffk32orhc3subhc4lxorhc4landjg93le4te3appte6option3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejpbh0le_bytes_to_wordrc7bv_wrap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ju96v_sltite3natlc8POW10U_NlcaPOW10U_TBLlcbpow10u_oget79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Image~~~~~~klebimage_byteste6lengthlccpow10u_bytesjg98bytes_atjg97mem_invte4Some37Corelib5Lists7ListDefktf6firstnktf5skipn3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslg9dov_read_byteshc6to_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~lla2shjg93mrdjg92walc3shbllabaddressablella3memhc3divjg93sxblla4aapphc6of_natlc4pinblc4pshb36Stdlib5Lists4Listlv39nth_errorllaaaccessible79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mi13ivlmi15munchmi17outside" s.   (* [comment removed for export] *)
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
Ltac useg_begin r :=
  intro_rv r; subst; unfold seg_post; hide_post;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof (bv_unsigned_in_range _ a0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
  hcb.
(* [comment removed for export] *)
Definition sh8 : ltac2:(zQ "10!h9>1x$0$0") := ltac2:(zQ "30!h9!j4!ja\1x$0@2$1@2$2^1+3+nvvvogg0").
Arguments sh8 : simpl never.
Lemma sh8_eq : ltac2:(zQ "50!h9!l7!pa!j4!ja>1x$0@3$1$0@1$2^1@2$3@2$4^1+3+nvvvogg0"). Proof. reflexivity. Qed.
Lemma sh8_bound : ltac2:(zQ "70!q0!q5!pa!h9!j4!qb!r0>1x$3>0@2$1@2$0Z^1@2$5^1@2$6+2+j0@2$1@2$0+nvvvogg0@1$2^2@2$0@2$4@1$2^2+1+igggnvvvogg1").
Proof. intros x Hx. rewrite sh8_eq. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Ltac fold_sh8 := repeat match goal with |- context [Z.shiftr ?x 3 + 2147450880] => rewrite <- (sh8_eq x) end.
  (* [comment removed for export] *)
  Definition uframe : ltac2:(zQ "40!r6!t9!v6!hja>1m$3>3sp'@1$1@1$0#k0>3pad@1$1@1$0#k0>4mant@1$1@1$0#k0>4bias@1$1@1$0#k0>4expo@1$1@1$0#k0>4xneg@1$1@1$0#8>3neg@1$1@1$0#8>2j6@1$2@1$1@1$0#8>4fs0v@1$1@1$0#k0>3s5v@1$1@1$0#k0>3s4v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0P") := ltac2:(zQ "e0!r6!hnc!t9!ho4!hob!hp1!hp7!v6!hpd!hte!hja!hu7!ii8!ij4\1m$a\3sp'@1$2@1$0#k0\3pad@1$2@1$0#k0\4mant@1$2@1$0#k0\4bias@1$2@1$0#k0\4expo@1$2@1$0#k0\4xneg@1$2@1$0#8\3neg@1$2@1$0#8\2j6@1$7@1$2@1$0#8\4fs0v@1$2@1$0#k0\3s5v@1$2@1$0#k0\3s4v@1$2@1$0#k0\3s3v@1$2@1$0#k0\3s2v@1$2@1$0#k0\3s1v@1$2@1$0#k0\3s0v@1$2@1$0#k0\3rav@1$2@1$0#k0@4$c$9^h1@2$d@1$0#k0^h0@3$3$1@1$4^f@3$3$1@1$4^e@3$3$1@1$6^d@3$3$1@1$6^c@3$3$1@1$5^b@3$3$1@1$5^a@3$3$1@2$bN6^9@3$3$1@1$4^8@3$3$1@1$4^7@3$3$1@1$4^6@3$3$1@1$4^5@3$3$1@1$4^4@3$3$1@1$4^3@3$3$1@1$4^2@3$3$1@1$4^1@1$8$1").
  (* [comment removed for export] *)
  Definition ucells : ltac2:(zQ "50!r6!t9!v6!h9!hja>1m$4>2pa@1$1@1$0#k0>1e$3>4pad7@1$2@1$1@1$0#8P") := ltac2:(zQ "h40!hnc!r6!ho4!hpd!hte!j4!ij4!q5!hp1!ii8!ind!t9!v6!h9!pa!hja!hob!hu7!io3!iof\1m$f\2pa@1$b@1$1#k0\1e$d\4pad7@1$c@1$b@1$1#8@2$7@4$9$4^4@2$5@2$6@1$1#k0^3+r8@3$2$0@1$h0@2$h3@1$1#k0^2@1$3$0@2$7@4$9$4^4@2$5@2$6@1$1#k0^3+r0@3$2$0@1$8@1$aZ@3$2$0@2$h1N7^1@1$3$0@4$h2$4^4@1$e@2$5@2$6@1$1#k0^3+r0@3$2$0@1$8@1$aZ@1$3$0").
  Ltac open_ucells UC := box_post; destruct UC as (END & MORE & PS176).
  (* [comment removed for export] *)
  Definition uctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    aceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 96 <= 2^47 /\ aapp (bv_unsigned pa) 280 /\ bv_unsigned pa mod 16 = 0 /\ 0 <= e <= aceil.
  Ltac open_uctx UX := box_post; destruct UX as (CEIL & ROOM & SPT & APP & PA16 & EHI).
  (* [comment removed for export] *)
  Definition uregs : ltac2:(zQ "40!r6!t9!h9!it6>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "b0!r6!t9!l7!q5!iof!h9!itc!iu3!iua!iv1!it6\1r$a\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5@2$3@3$2@1$1@1$0#k0@1$9^4^3@2$3@3$2@1$1@1$0#k0@1$6^4^2@2$3@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0+nvvvogg0@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0^1").
  Ltac open_uregs UR := box_post; destruct UR as (?U1 & ?U2 & ?U3 & ?U4).
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe in *; unfold seg_post, uregs, uframe, ucells; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    acb.
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ => unfold uregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- ucells _ _ _ _ => unfold ucells
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
  Lemma swrap32_of_u64 : ltac2:(zQ "c0!j4!r6!h9!r0!q5!l7!q0!qb!iv8!iof!ive!ij4>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
  Proof.
    intros b k Hbk. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32). change (2^32 * 2^32 / 2) with (2^63). change (2 ^ 32 / 2) with (2^31).
    replace (b mod (2 ^ 32 * 2 ^ 32) + k + 2 ^ 31) with ((k + 2 ^ 31) + b mod (2 ^ 32 * 2 ^ 32)) by lia.
    rewrite Z.add_mod by lia. rewrite Z.mod_mod_divide by (exists (2^32); lia).
    rewrite <- Z.add_mod by lia. replace (k + 2 ^ 31 + b) with (b + k + 2^31) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma swrap32_of_u64_0 : ltac2:(zQ "b0!r6!h9!r0!q5!l7!q0!qb!iv8!iof!ive!ij4>1b$1>0@2$3@2$5@1$7@2$2+2+hf^1@2$6^1@2$2+2+hf@3$4$1@2$9@1$0#i0@2$a@1$0#k0@2$8@1$0#k0^2^2").
  Proof. intros b Hb. rewrite <- (Z.add_0_r (bv_unsigned (Z_to_bv 64 b))). rewrite swrap32_of_u64 by lia. lia. Qed.
  Lemma sx32_ssmall : ltac2:(zQ "b0!r6!r0!iof!q5!l7!h9!jk3!q0!qb!iv8!t9>1b$5>0@2$3@2$7@1$9@2$1+2+hf^1@2$8^1@2$1+2+hf@3$4@1$a@1$0#k0@1$6@2$2@1$0#k0^2@2$2@1$0#k0^2").
  Proof. intros b Hb. unfold sx32. rewrite swrap32_of_u64_0 by lia. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma signed_of_small : ltac2:(zQ "a0!r6!h9!r0!q5!l7!q0!qb!iv8!iof!jkb>1b$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
  Proof.
    intros b Hb. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 / 2) with (2^63). lia.
  Qed.
  Lemma swrap32_mul_u64 : ltac2:(zQ "c0!jl7!r6!h9!r0!q5!l7!q0!qb!iv8!iof!ive!ij4>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
  Proof.
    intros b k Hbk. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 / 2) with (2^31).
    rewrite Z.add_mod by lia. rewrite <- Z.mul_mod_idemp_l by lia. rewrite Z.mod_mod_divide by (exists (2^32); lia).
    rewrite Z.mul_mod_idemp_l by lia. rewrite <- Z.add_mod by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma mod64_of_small_nonneg : ltac2:(zQ "70!h9!q5!l7!q0!qb!jld!r0>1x$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+hggggggggggggggg0^2").
  Proof. intros x Hx. apply Z.mod_small. lia. Qed.
  Lemma mod64_of_small_neg : ltac2:(zQ "90!h9!r0!q5!l7!j4!q0!qb!jld!iv8>1x$0>0@2$2@2$5@1$8@2$1+2+k0^1@2$6^1Z@3$3$0@2$7^2+hggggggggggggggg0@2$4^2@2$1+2+k0").
  Proof. intros x Hx. rewrite <- (Z.mod_add x 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia. Qed.
  Lemma mod64_le_iff : ltac2:(zQ "80!q0!q5!r0!h9!qb!jm6!jld!iv8>1x$3>1c$3>0@2$1@2$0@1$7@2$2+2+jf^2@2$4^2@2$2+2+jf>0@2$1@2$0Z^2@2$4^2@2$2+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$0Z^4@2$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_lt_iff : ltac2:(zQ "80!qb!q5!q0!r0!h9!jm6!jld!iv8>1x$4>1c$4>0@2$1@2$2@1$7@2$3+2+jf^2@2$0^2@2$3+2+jf>0@2$1@2$2Z^2@2$0^2@2$3+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$2Z^4@2$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_ge_iff : ltac2:(zQ "90!q0!qb!r0!q5!h9!jm6!jmc!jld!iv8>1x$4>1c$4>0@2$3@2$0@1$8@2$2+2+jf^2@2$1^2@2$2+2+jf>0@2$3@2$0Z^2@2$1^2@2$2+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$1^4Z@2$0^3^4").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_gt_iff : ltac2:(zQ "90!qb!r0!q5!h9!q0!jm6!jmc!jld!iv8>1x$3>1c$3>0@2$2@2$4@1$8@2$1+2+jf^2@2$0^2@2$1+2+jf>0@2$2@2$4Z^2@2$0^2@2$1+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$0^4Z@2$0^3^4").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  (* [comment removed for export] *)
  Lemma mod64_geh_iff : ltac2:(zQ "90!r0!q0!q5!qb!h9!jm6!jld!iv8!jn1>1x$4>1c$4>0@2$2@2$1@1$7@2$0+2+jf^2@2$3^2@2$0+2+jf>0@2$2@2$1@2$0+2+jf^2@2$3^2@2$0+2+k0@2$5@2$1^3@2$6^4+hggggggggggggggg0@2$2@2$1@2$8^3@2$0+2+k0^4@2$3^4Z").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_lth_iff : ltac2:(zQ "a0!r0!qb!q0!q5!h9!jm6!jmc!jld!iv8!jn1>1x$4>1c$4>0@2$3@2$2@1$8@2$0+2+jf^2@2$1^2@2$0+2+jf>0@2$3@2$2@2$0+2+jf^2@2$1^2@2$0+2+k0@2$5@2$1@2$7^4+hggggggggggggggg0^3@2$6@2$2Z^4@2$1^4@2$9^3@2$0+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_leh_iff : ltac2:(zQ "a0!q0!r0!q5!h9!qb!jm6!jmc!jld!iv8!jn1>1x$3>1c$3>0@2$2@2$0@1$8@2$1+2+jf^2@2$4^2@2$1+2+jf>0@2$2@2$0@2$1+2+jf^2@2$4^2@2$1+2+k0@2$5@2$0@2$7^4+hggggggggggggggg0^3@2$6@2$0Z^4@2$0^4@2$9^3@2$1+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_gth_iff : ltac2:(zQ "90!qb!r0!q5!h9!q0!jm6!jld!iv8!jn1>1x$3>1c$3>0@2$2@2$4@1$7@2$1+2+jf^2@2$0^2@2$1+2+jf>0@2$2@2$4@2$1+2+jf^2@2$0^2@2$1+2+k0@2$5@2$0^3@2$6^4+hggggggggggggggg0@2$2@2$0@2$8^3@2$1+2+k0^4@2$0^4Z").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_eq_iff : ltac2:(zQ "90!h9!r0!q5!l7!q0!qb!jm6!jld!iv8>1x$0>1c$0>0@2$2@2$4@1$8@2$1+2+jf^2@2$5^2@2$1+2+jf>0@2$2@2$4Z^2@2$5^2@2$1+2+jf@2$6@3$3$0@2$7^4+hggggggggggggggg0^3@3$3$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_eqh_iff : ltac2:(zQ "a0!r0!h9!q5!l7!q0!qb!jm6!jld!iv8!jn1>1x$1>1c$1>0@2$2@2$4@1$8@2$0+2+jf^2@2$5^2@2$0+2+jf>0@2$2@2$4@2$0+2+jf^2@2$5^2@2$0+2+k0@2$6@3$3$1@2$7^4+hggggggggggggggg0^3@3$3$1^4@2$9^3@2$0+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma byte_range : ltac2:(zQ "60!r6!ij4!q5!q0!qb!t9>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
  Proof. intros b. pose proof (bv_unsigned_in_range _ b) as R. unfold bv_modulus in R; cbn in R. lia. Qed.
  Ltac pose_byte_ranges K :=
    repeat match type of K with
    | context [bv_unsigned (?b : bv 8)] =>
        lazymatch goal with
        | _ : 0 <= bv_unsigned b < 256 |- _ => fail
        | _ => pose proof (byte_range b)
        end
    end.
  (* [comment removed for export] *)
  Lemma lxor_m1_64 : ltac2:(zQ "80!h9!q5!l7!q0!qb!jn7!r0!jn1>1w$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+vvvvvvvvvvvvvvvf@2$7+vvvvvvvvvvvvvvvf^2").
  Proof.
    intros w Hw. rewrite lnot_mod64 by lia. pose proof (Z.add_lnot_diag w) as D.
    replace (Z.lnot w) with (-w - 1) by lia. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma swrap32_id : ltac2:(zQ "90!h9!r0!q5!l7!r6!q0!qb!iv8!ive>1x$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
  Proof. intros x Hx. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2) with (2^31). lia. Qed.
  Lemma mod64_eq_mod64_iff : ltac2:(zQ "90!h9!l7!qb!jld!r0!jn1!q5!jm6!iv8>1x$0>1y$0>0@2$6@2$2@1$8@2$4+2+k0@2$5^2^1@2$2@2$5^2^1@2$4+2+k0@2$7@3$1$0@2$3^3+hggggggggggggggg0@2$3^2+hggggggggggggggg0@3$1$0^3^2").
  Proof.
    intros x y Hxy. split; intros E; [| now subst].
    pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)) as Dx. pose proof (Z.div_mod y 18446744073709551616 ltac:(lia)) as Dy.
    pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)) as Bx. pose proof (Z.mod_pos_bound y 18446744073709551616 ltac:(lia)) as By.
    assert (Q : x / 18446744073709551616 = y / 18446744073709551616) by nia. rewrite Q, E in Dx. lia.
  Qed.
  (* [comment removed for export] *)
  Ltac unmod64 K :=
    pose_byte_ranges K;
    repeat match type of K with
    | context [?x mod 18446744073709551616 = ?y mod 18446744073709551616] => rewrite (mod64_eq_mod64_iff x y) in K by (clear K; lia)
    | context [?x mod 18446744073709551616 <= ?c] => first [rewrite (mod64_le_iff x c) in K by (clear K; lia) | rewrite (mod64_leh_iff x c) in K by (clear K; lia)]
    | context [?x mod 18446744073709551616 < ?c] => first [rewrite (mod64_lt_iff x c) in K by (clear K; lia) | rewrite (mod64_lth_iff x c) in K by (clear K; lia)]
    | context [?c <= ?x mod 18446744073709551616] => first [rewrite (mod64_ge_iff x c) in K by (clear K; lia) | rewrite (mod64_geh_iff x c) in K by (clear K; lia)]
    | context [?c < ?x mod 18446744073709551616] => first [rewrite (mod64_gt_iff x c) in K by (clear K; lia) | rewrite (mod64_gth_iff x c) in K by (clear K; lia)]
    | context [?x mod 18446744073709551616 = ?c] => first [rewrite (mod64_eq_iff x c) in K by (clear K; lia) | rewrite (mod64_eqh_iff x c) in K by (clear K; lia)]
    | context [?x mod 18446744073709551616] => first [rewrite (mod64_of_small_nonneg x) in K by (clear K; lia) | rewrite (mod64_of_small_neg x) in K by (clear K; lia)]
    end.
  Lemma land1_small : ltac2:(zQ "50!h9!q0!q5!l7!jne>1x$0>0@2$2@2$1Z^1@2$1^1+1@3$3$0@2$4^2+1^2").
  Proof. intros x Hx. change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  Lemma swrap32_id_m64 : ltac2:(zQ "a0!r0!jn1!h9!q5!l7!r6!q0!qb!iv8!ive>1x$2>0@2$3@2$6@1$8@2$0+2+hf@2$1^1@2$0+2+k0@2$7@2$1^1@2$0+2+k0@2$0+2+hf@3$4$2@2$9@1$5#i0^2@2$1^2@2$0+2+k0").
  Proof.
    intros x Hx. rewrite (bv_swrap_congr 32 x (x - 2^64)). apply swrap32_id; lia.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
    replace x with ((x - 2^64) + (2^32 * 2^32)) at 1 by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma uframe_merge8 : ltac2:(zQ "h10!hnc!ho4!hob!r6!t9!hp1!hpd!hte!hp7!hu7!jo5!ii8!joc!v6!jp2!h9!jsa>1m>0@1$4@1$3#k0@1$e@1$4@1$3#8>1A$f>2pd@1$4@1$3#k0>2mw@1$4@1$3#k0>1b@1$4@1$3#k0>1x@1$4@1$3#k0>2xg@1$4@1$3#8>2ng@1$4@1$3#8>2j6@1$d@1$4@1$3#8>2f0@1$4@1$3#k0>3s5v@1$4@1$3#k0>3s4v@1$4@1$3#k0>3s3v@1$4@1$3#k0>3s2v@1$4@1$3#k0>3s1v@1$4@1$3#k0>3s0v@1$4@1$3#k0>3rav@1$4@1$3#k0>0@4$b$7^h1^h0@3$1$0@1$2^f@3$1$0@1$2^e@3$1$0@1$8^d@3$1$0@1$8^c@3$1$0@1$5^b@3$1$0@1$5^a@3$1$0@2$9N6^9@3$1$0@1$2^8@3$1$0@1$2^7@3$1$0@1$2^6@3$1$0@1$2^5@3$1$0@1$2^4@3$1$0@1$2^3@3$1$0@1$2^2@3$1$0@1$2^1@1$6$0@4$b$7^h2^h1@3$1$0@1$2^h0@3$1$0@1$2^f@3$1$0@1$2@1$h0@3$c@1$4@1$3#8@1$a^e@1$a^d@3$1$0@1$5^c@3$1$0@1$5^b@3$1$0@2$9N6^a@3$1$0@1$2^9@3$1$0@1$2^8@3$1$0@1$2^7@3$1$0@1$2^6@3$1$0@1$2^5@3$1$0@1$2^4@3$1$0@1$2^3@3$1$0@1$2^2@1$6$0").
  Proof.
    intros until rav. intros R. pose proof R as [[W _] _]. cbn in W.
    eapply rw_cells_rebytes; [exact R| | | reflexivity].
    - cbn. tauto.
    - cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by (rewrite length_app, !length_le4; reflexivity). rewrite <- ?app_assoc. reflexivity.
  Qed.
  Ltac merge8 :=
    match goal with
    | UF : rw_cells _ ?m ?A [C8 _; C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply uframe_merge8 in UF
    end.
  Ltac norm_s32 :=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    end.
  (* [comment removed for export] *)
  Ltac achk := fail.
  (* [comment removed for export] *)
  Ltac norm_retpc :=
    try (lazymatch goal with
         | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
             replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | first [assumption | reflexivity | lia]])
         end).
  Ltac step1 := first [ achk | st1b | arm_inputs; st1b | merge8; st1b ]; norm_lits; fold_sh8; norm_s32; gen_data; norm_retpc.
  Ltac box_ugly K ::=
    try (rewrite !signed_lit in K by (clear K; lia)); try (rewrite !signed_of_small in K by (clear K; lia));
    try (rewrite !wz_unsigned in K by (clear K; lia)); try (rewrite !b8_unsigned in K by (clear K; lia));
    try (rewrite !lxor_m1_64 in K by (clear K; lia)); try (rewrite !swrap32_id in K by (clear K; lia)); try (rewrite !swrap32_id_m64 in K by (clear K; lia));
    try unmod64 K;
    try (rewrite !signed_of_small in K by (clear K; lia));
    lazymatch type of K with
    | context [Z.lor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.land _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.lxor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftl _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftr _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.modulo _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [bv_swrap _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [bv_signed _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | _ => idtac
    end.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => step1
                end
            end).
  (* [comment removed for export] *)
  Ltac explore2_1 stops := step1; explore2 stops.
  (* [comment removed for export] *)
  Definition uvs : ltac2:(zQ "50!h9!r6!t9!v6!hja>1m$4>2pa@1$2@1$1#k0>4temp$0>2Bg$0>1T$0>2EE$0>2ch$0>2j7@1$3@1$2@1$1#8P") := ltac2:(zQ "h00!r6!hnc!ho4!hob!iof!h9!t9!v6!hpd!hte!hja!hp1!hu7!ii8!ind!ij4\1m$a\2pa@1$6@1$0#k0\4temp$5\2Bg$5\1T$5\2EE$5\2ch$5\2j7@1$7@1$6@1$0#8@4$d$9^8@2$f@1$0#k0^7@3$2$1@1$3@2$4@1$0#k0Z@3$2$1@1$3@2$4@1$0#k0^6@3$2$1@1$3@2$4@1$0#k0^5@3$2$1@1$3@2$4@1$0#k0^4@3$2$1@1$3@2$4@1$0#k0^3@3$2$1@1$3@2$4@1$0#k0^2@3$2$1@1$b@1$e+1@3$2$1@2$cN7^1@3$2$1@1$3@2$4@1$0#k0Z@1$8$1").
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ => unfold uregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- ucells _ _ _ _ => unfold ucells
    | |- uvs _ _ _ _ _ _ _ _ => unfold uvs
    end.
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe, uvs in *; unfold seg_post, uregs, uframe, ucells, uvs; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    acb.
  Lemma land7_mod8 : ltac2:(zQ "50!h9!l7!jne!q0!jld>1x$0>0@2$3Z^1@3$1$0@2$2^2+7@2$4^2+8").
  Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
  Ltac box_ugly K ::=
    try (rewrite !signed_lit in K by (clear K; lia)); try (rewrite !signed_of_small in K by (clear K; lia));
    try (rewrite !wz_unsigned in K by (clear K; lia)); try (rewrite !b8_unsigned in K by (clear K; lia));
    try (rewrite !lxor_m1_64 in K by (clear K; lia)); try (rewrite !swrap32_id in K by (clear K; lia)); try (rewrite !swrap32_id_m64 in K by (clear K; lia));
    try (rewrite !land7_mod8 in K by (clear K; lia));
    try unmod64 K;
    try (rewrite !signed_of_small in K by (clear K; lia));
    lazymatch type of K with
    | context [Z.lor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.land _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.lxor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftl _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftr _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.modulo _ 18446744073709551616] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [bv_swrap _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [bv_signed _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | _ => idtac
    end.
  (* [comment removed for export] *)
  Ltac fin_atom ::=
    first [ eassumption
          | reflexivity
          | lazymatch goal with
            | |- @eq Z _ _ => rv_cbv; fin_arith
            | |- (_ <= _)%Z => rv_cbv; fin_arith
            | |- (_ < _)%Z => rv_cbv; fin_arith
            | |- not _ => rv_cbv; fin_arith
            | |- _ \/ _ => rv_cbv; first [ eassumption | lia ]
            | |- @eq _ _ _ => rv_cbv; first [ reflexivity | eassumption | f_equal; lia | apply bv_eq; rewrite ?unsigned_lit by lia; lia
                                             | lazymatch goal with |- Z_to_bv _ ?a = Z_to_bv _ ?b =>
                                                 let a' := zlit a in let b' := zlit b in apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity end ]
            | |- _ => rv_cbv; first [ reflexivity | eassumption ]
            end ].
  Ltac norm_s32 ::=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 7)] => rewrite (land7_mod8 a) by lia
    end.
  (* [comment removed for export] *)
  Lemma wrap32_of_u64 : ltac2:(zQ "60!r6!h9!jtf!l7!iof!ij4>1a$1@3$3$1@2$2@1$0#i0@2$5@1$0#k0@2$4@1$0#k0^1@2$2@1$0#i0^1").
  Proof.
    intros a. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32).
    rewrite Z.mod_mod_divide by (exists (2^32); lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_2 : ltac2:(zQ "c0!r6!j4!h9!r0!iof!ij4!q5!l7!q0!qb!iv8!ive>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
  Proof.
    intros a b H. rewrite (bv_swrap_congr 32 _ (a + b)); [apply swrap32_id; lia|].
    unfold bv_wrap. rewrite Z.add_mod by (unfold bv_modulus; lia). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 a))). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 b))).
    rewrite !wrap32_of_u64. unfold bv_wrap. rewrite <- Z.add_mod by (unfold bv_modulus; lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_sub : ltac2:(zQ "c0!r6!jn1!h9!r0!iof!ij4!q5!l7!q0!qb!iv8!ive>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
  Proof.
    intros a b H. rewrite (bv_swrap_congr 32 _ (a - b)); [apply swrap32_id; lia|].
    unfold bv_wrap. rewrite Zminus_mod by (unfold bv_modulus; lia). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 a))). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 b))).
    rewrite !wrap32_of_u64. unfold bv_wrap. rewrite <- Zminus_mod by (unfold bv_modulus; lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_rsub : ltac2:(zQ "c0!jn1!r6!h9!r0!q5!l7!q0!qb!iv8!iof!ive!ij4>1k$2>1b$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0^3@2$b@1$1#k0@2$9@1$1#k0^2@2$0^3^2").
  Proof.
    intros k b H. rewrite (bv_swrap_congr 32 _ (k - b)); [apply swrap32_id; lia|].
    unfold bv_wrap. rewrite Zminus_mod by (unfold bv_modulus; lia). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 b))).
    rewrite !wrap32_of_u64. unfold bv_wrap. rewrite <- Zminus_mod by (unfold bv_modulus; lia). reflexivity.
  Qed.
  Ltac norm_s32 ::=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) + bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_2 a b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_sub a b) by lia
    | |- context [bv_swrap 32 (?k - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_rsub k b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 7)] => rewrite (land7_mod8 a) by lia
    end.
  Lemma v_slti_true : ltac2:(zQ "b0!r6!h9!qb!r0!iof!q5!l7!ki8!q0!iv8!t9>1v$1>3imm$1>0@2$5@2$8@1$9@2$3+2+jf^2@2$2^2@2$3+2+jf>0@2$2^3^2@3$6@1$a@1$0#k0@2$7@2$4@1$0#k0^4^3@2$4@1$0#k0+1").
  Proof. intros v imm Hv H. unfold v_slti, zsig. rewrite signed_of_small by lia. destruct (Z.ltb_spec0 v imm); [reflexivity| lia]. Qed.
  Lemma v_slti_false : ltac2:(zQ "b0!r6!h9!q0!r0!iof!q5!l7!ki8!qb!iv8!t9>1v$1>3imm$1>0@2$5@2$2@1$9@2$3+2+jf^2@2$8^2@2$3+2+jf>0@2$2^2^3@3$6@1$a@1$0#k0@2$7@2$4@1$0#k0^4^3@2$4@1$0#k0Z").
  Proof. intros v imm Hv H. unfold v_slti, zsig. rewrite signed_of_small by lia. destruct (Z.ltb_spec0 v imm); [lia| reflexivity]. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition POW10U_TBL : Z := 0x27720.   (* [comment removed for export] *)
  Definition POW10U_N : nat := 4936.
  (* [comment removed for export] *)
  Definition pow10u_oget : ltac2:(zQ "40!v6!r6!t9!jp2>1o@1$3@1$0@1$2@1$1#8@1$0@1$2@1$1#8") := ltac2:(zQ "50!r6!t9!v6!jp2!hpd\1o@1$3@1$2@1$1@1$0#8M3\1o@1$3@1$2@1$1@1$0#8@1$2@1$1@1$0#8^1\2bs@1$2@1$1@1$0#8^1@1$4@1$1@1$0#8").
  Definition pow10u_bytes : ltac2:(zQ "30!v6!r6!t9@1$0@1$2@1$1#8") := ltac2:(zQ "50!kj8!kk3!kl0!hte!kpa@1$2@3$4$3$1$0").
  Lemma pow10u_len : ltac2:(zQ "70!kq9!kj2!l7!r6!kj8!kr2!t9@3$2$1@2$0@1$6@1$3#8$5$4").
  Proof. vm_compute. reflexivity. Qed.
  Lemma pow10u_ro_cells_bytes_at : ltac2:(zQ "d0!r6!t9!hte!hnc!ho4!v6!kj2!hpd!jp2!h9!hu7!ks1!io3>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$9>1n$6>2bs@1$5@1$1@1$0#8>0@4$c$2^4^3@3$4$3@2$a^2^1@1$7$3@4$b$2^5^4^2").
  Proof. intros m A n bs [_ RB]. cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB. exact RB. Qed.
  Lemma pow10u_ro : ltac2:(zQ "80!r6!hte!t9!jp2!kk3!kr2!ks1!ksd>1m>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@2$7$1^1@4$6$1^2$4$5").
  Proof.
    intros m MI. apply (pow10u_ro_cells_bytes_at m POW10U_TBL (length pow10u_bytes)).
    apply (ro_cells_image asegs m POW10U_TBL pow10u_bytes MI); [vm_compute; reflexivity| unfold POW10U_TBL; lia| rewrite pow10u_len; unfold POW10U_TBL, POW10U_N; lia].
  Qed.
  Lemma pow10u_read : ltac2:(zQ "h50!r6!t9!v6!jp2!hte!jl7!kt8!q5!l7!kv6!lg0!h9!lk0!kk3!kr2!ksd!j4!q0!qb!ll1!iof>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1k$b>0@2$f$4^2>0@2$7@2$h1Z^2@2$h2^2+im9@3$8@1$3@1$2@1$1@1$0#8@4$c$4^4@2$h4@1$0#k0@2$h0$d@2$5+8^3N8@2$6@1$2@1$1@1$0#8@3$9@1$1@1$0#8N8@3$a@1$1@1$0#8@1$h3@2$5+8^3$e").
  Proof.
    intros m k MI HK. replace (Z_to_bv 64 (POW10U_TBL + 8 * k)) with (wa (POW10U_TBL + 8 * k)) by reflexivity.
    apply (bytes_at_read asegs m POW10U_TBL pow10u_bytes (8 * k) 8 (pow10u_ro m MI)); [lia|]. rewrite pow10u_len. unfold POW10U_N. lia.
  Qed.

(* [comment removed for export] *)
Ltac br K := if_cases K; zify_cond K; box_ugly K; [ first [exfalso; lia | idtac] | first [exfalso; lia | idtac] ].
Ltac brp K := if_cases K; zify_cond K; box_ugly K; try (exfalso; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shb : ltac2:(zQ "20!h9!hja>1m$1>1x$0$0") := ltac2:(zQ "a0!r6!jp2!h9!t9!hte!hja!lp8!lpe!lq5!ij4\1m$5\1x$2M1\1x@1$1@1$3@1$0#8$2@3$7$4^2@1$8@1$6^1\1b@1$3@1$0#8@2$9@1$0#8^1Z").
Lemma shaddr_eq : ltac2:(zQ "60!h9!l7!lp8!j4!q0!ja>1x$0>0@2$4Z^1@3$1$0@2$3@2$5^2+3+nvvvogg0@1$2^2").
Proof. intros x Hx. unfold sh. rewrite ASHADOW_BASE_val, Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma ro_cells_C1_of_mrd : ltac2:(zQ "h10!r6!t9!jp2!hte!hnc!q0!kt8!ho4!hpd!l7!h9!hp1!lpe!lq5!io3!j4!r0>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1A$a>1b@1$1@1$0#8>0@2$5Z^2>0@2$5@2$f^3+1@2$h0+2+k0>0@3$9@1$2@1$1@1$0#8@3$c$3^5@1$d^4@2$6@1$1@1$0#8^3@4$e$3^6^5@3$7$4@1$b^4@1$8$4").
Proof.
  intros m A b H0 H1 RD. split; [cbn; tauto|]. split; [exact H0|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. destruct i; [| lia]. cbn. rewrite Z.add_0_r. exact RD.
Qed.
Definition pshad : ltac2:(zQ "20!h9!hja>1m$1>2p0$0>1e$0P") := ltac2:(zQ "h20!lqb!h9!q5!q0!hnc!qb!ho4!hpd!l7!jmc!pa!hte!hja!hp1!io3!ind!j4!jld\1m$c\2p0$1\1e$1>1x$1>0@2$3^3^1>0@2$5^2^3@2$2@4$e$b^6@1$a^3@3$6$4@1$d@1$f@2$0^6^3@1$7$4@2$2@2$2@2$3Z@2$0^6^3@2$5@2$0^6^3+8@2$9@3$8$1@2$0^6^3Z@2$3@2$h0@2$h1^3+8+1@2$0^6^3").
(* [comment removed for export] *)
Lemma addressable_shro0 : ltac2:(zQ "f0!h9!hnc!j4!q0!ho4!hpd!pa!hte!lr1!ls0!hp1!io3!ind!ls7!jl7>1m$9>1A$0>1n$0>1a$0>0@3$8^4^3^2>0@2$3^4^2>0@2$3@2$2^3+1@2$2^5@2$e+8@2$d^4+8@4$b$7^7@1$6^4@3$4$1@1$a@1$cZ@1$5$1").
Proof.
  intros m A n a AD HA HB. rewrite sh8_eq. pose proof (addressable_rd m A n a 1 AD HA ltac:(lia) HB) as RD.
  pose proof AD as [Hn [A0 X]]. rewrite ov_rdn in RD. cbn [rdn] in RD.
  assert (RD1 : mrd asegs m (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) = Some (b8 0)).
  { unfold mrd. destruct (m (Z_to_bv 64 (Z.shiftr a 3 + 2147450880))) as [b|]; [injection RD as ->; reflexivity|].
    destruct (seg_rom asegs (Z_to_bv 64 (Z.shiftr a 3 + 2147450880))) as [b|]; [injection RD as ->; reflexivity| discriminate RD]. }
  destruct X as [A8 [[U0 [U1 U2]] _]]. rewrite shadow_of_length in U1 by lia.
  apply ro_cells_C1_of_mrd.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold sh, nsh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
  - unfold wa. exact RD1.
Qed.
(* [comment removed for export] *)
Lemma sxb_b8_small : ltac2:(zQ "a0!r6!q5!l7!h9!lsd!ind!q0!qb!iof!t9>1v$3>0@2$1@2$6Z^1@2$7^1+o0@3$2@1$9@1$0#k0@1$4@1$5^2@2$8@1$0#k0^2").
Proof.
  intros v Hv. unfold sxb, b8. rewrite Z_to_bv_signed. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.
(* [comment removed for export] *)
Ltac norm_s32 ::=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) + bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_2 a b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_sub a b) by lia
    | |- context [bv_swrap 32 (?k - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_rsub k b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 7)] => rewrite (land7_mod8 a) by lia
    | |- context [sxb (b8 ?v)] => rewrite (sxb_b8_small v) by lia
    (* [comment removed for export] *)
    | |- context [sx32 (Z_to_bv 64 ?b)] =>
        lazymatch isZcst b with
        | true => let v := eval vm_compute in (bv_swrap 32 b) in
                  replace (sx32 (Z_to_bv 64 b)) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
        end
    end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac arm_inputs ::=
  repeat match goal with
  | H : cond_ro ?c ?m ?A ?cs |- _ =>
      let Hc := fresh "Hc" in assert (Hc : c) by lia; unfold cond_ro in H; specialize (H Hc);
      try (lazymatch A with
           | sh8 ?x =>
               lazymatch goal with SHB : pshad _ _ _ |- _ =>
                 let B := fresh "SBL" in let D := fresh "SBD" in let A := fresh "SBA" in
                 pose proof (proj1 (proj2 (SHB x ltac:(clear - Hc; lia) Hc))) as B;
                 pose proof ((proj2 (proj2 (SHB x ltac:(clear - Hc; lia) Hc))) : boxP (shb _ x = 0 \/ x mod 8 + 1 <= shb _ x)) as D;
                 pose proof (sh8_bound x ltac:(lia)) as A
               end
           end);
      clear Hc
  end.
(* [comment removed for export] *)
Ltac unbox_shad_for K2 :=
  lazymatch type of K2 with
  | context [?x mod 8] =>
      repeat match goal with
      | H : boxP ?P |- _ => lazymatch P with context [shb _ x] => unfold boxP in H | _ => clear H end
      end
  end.
Ltac shad_bounds :=
  repeat match goal with
  | H : ro_cells _ _ (sh8 ?x) _ |- _ =>
      lazymatch goal with
      | _ : 2147450880 <= sh8 x /\ _ |- _ => fail
      | _ => pose proof (sh8_bound x ltac:(lia))
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac useg_begin r ::=
  intro_rv r; subst; unfold uframe, uvs in *; unfold seg_post, uregs, uframe, ucells, uvs; hide_post;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
  acb;
  try (lazymatch goal with APP : aapp _ 280 |- _ =>
         pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5); unfold AIMG_TOP in APB1; unfold AAPP_HI in APB3 end);
  shad_bounds.

(* [comment removed for export] *)
Section SHDJ.
  Context {HCEIL : HeapCeil}.
Lemma aapp_sh8_disj : ltac2:(zQ "90!q0!h9!j4!pa!q5!jmc!lt4!qb!r0>1A$1>1n$1>1x$1>1a$1>1k$1>0@3$6?5HCEIL^5^4>0@2$4@2$0Z^4@2$7^4@2$8+2+if>0@2$0^7^4>0@2$0Z^4>0@2$0@2$2^6^5@2$2^9^8@2$5@2$0@2$2@1$3^8+1^7@2$0@2$2^7^6@1$3^8").
Proof.
  intros A n x a k APP XR HA HK HB. rewrite sh8_eq. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in APP. Z.div_mod_to_equations. lia.
Qed.
Lemma aapp_sh8_window : ltac2:(zQ "90!q0!h9!j4!pa!q5!jmc!lt4!qb!r0>1A$1>1n$1>1a$1>1k$1>0@3$6?5HCEIL^4^3>0@2$0^5^3>0@2$0Z^3>0@2$0@2$2^5^4@2$2^7^6>1x$1>0@2$4@2$0Z^1@2$7^1@2$8+2+if@2$5@2$0@2$2@1$3^2+1^8@2$0@2$2^8^7@1$3^2").
Proof. intros A n a k APP HA HK HB x XR. exact (aapp_sh8_disj A n x a k APP XR HA HK HB). Qed.
End SHDJ.
Ltac pose_shdj SH A S xs :=
  lazymatch xs with
  | nil => idtac
  | cons ?x ?rest =>
      let D := fresh "DJs" in
      assert (D : chunk_disj (sh8 x) 1 A S) by (unfold chunk_disj; pose proof (SH x ltac:(lia)); lia);
      pose_shdj SH A S rest
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shaddr_lt : ltac2:(zQ "80!q0!h9!q5!pa!j4!qb!ltc!r0>1x$1>1a$1>0@2$2@2$0Z^2@2$5^2@2$7+2+j0>0@2$0+igggnvvvogg1^2@2$0@2$4@1$3^4@1$6N1^3").
Proof. intros x a Hx Ha. pose proof (sh8_bound x Hx). cbn [Z.of_nat Pos.of_succ_nat]. lia. Qed.
Ltac transport_cond_ro segs m a bs ::=
  repeat match goal with
  | H : cond_ro ?c m ?A2 ?cs2 |- _ =>
      first [ apply (cond_ro_frame c m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia
              | simpl_sizes; first [ lazymatch A2 with sh8 ?x => left; apply (shaddr_lt x); lia end | slia ] ]
            | idtac "note: dropping conditional input fact" H; clear H ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pinb : ltac2:(zQ "40!h9!r6!hja!t9>1m$2>1q$0>1e$0>3inb>0$0@1$3@1$1#8P") := ltac2:(zQ "e0!h9!r6!q0!t9!q5!kt8!jp2!l7!hte!hja!lpe!lq5!qb!r0\1m$9\1q$0\1e$0\3inb>0$0@1$3@1$1#8@2$4@2$2Z^3@2$4@2$2^2@2$d+2+if>1x$0>0@2$2^4^1>0@2$c^2^4@3$7@1$6@1$3@1$1#8@3$a$8^7@1$b^3@2$5@1$3@1$1#8@1^4^3").
Definition pshb : ltac2:(zQ "20!h9!hja>1m$1>1q$0>1e$0P") := ltac2:(zQ "h30!lqb!h9!q5!q0!l7!r6!qb!t9!kt8!jp2!jmc!pa!hte!hja!lpe!lq5!ind!j4!jld\1m$d\1q$1\1e$1>1x$1>0@2$3^3^1>0@2$6^2^3@2$2@3$4@1$9@1$7@1$5#8@3$e$c^6@1$f@1$b^3@2$8@1$7@1$5#8@1$h0@2$0^6^3@2$2@2$2@2$3Z@2$0^6^3@2$6@2$0^6^3+8@2$a@3$4$1@2$0^6^3Z@2$3@2$h1@2$h2^3+8+1@2$0^6^3").
Lemma pinb_sub : ltac2:(zQ "60!h9!lu5!q0!r6!hja!t9>1m$4>1q$0>1e$0>3inb>0$0@1$5@1$3#8>2q'$0>2e'$0>0@4$1^6^5^4^3>0@2$2^6^3>0@2$2^3^6@4$1^9^5^4^6").
Proof. (intros m q e inb q' e' nd_i2 H1 H2; ndestruct nd_i2 as (A & B & P)). split; [lia|]. split; [lia|]. intros x X1 X2. apply P; lia. Qed.
Lemma pshb_sub : ltac2:(zQ "40!h9!luc!q0!hja>1m$3>1q$0>1e$0>2q'$0>2e'$0>0@3$1^5^4^3>0@2$2^5^3>0@2$2^3^5@3$1^8^5^4").
Proof. intros m q e q' e' P H1 H2 x X1 X2. apply P; lia. Qed.
Lemma pinb_of_bytes_at : ltac2:(zQ "h30!r6!t9!h9!jp2!l7!q0!kt8!kq9!v6!lu5!hte!ks1!mg6!j4!qb!ltc!r0!jn1!ll1>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>2p0$2>2bs@1$8@1$1@1$0#8>1e$2>3inb>1x$2@1$1@1$0#8>0@4$b$a^5^4^3>0@3$4$2^3@2$d^5@1$f@2$7@1$1@1$0#8^4>0@2$5^4@2$h0+2+if>0>1x$2>0@2$5^8^1>0@2$e^2^7@3$4@1$3@1$1@1$0#8@3$c@1$1@1$0#8^9@1$h2@2$h1^3^a@2$6@1$1@1$0#8@1^7^3@4$9^9^8^6^5").
Proof.
  (intros m p0 bs e inb nd_i3 E HE HI; ndestruct nd_i3 as (B0 & B1 & BY)). split; [exact B0|]. split; [exact HE|]. intros x X1 X2.
  rewrite <- (HI x X1 X2). replace x with (p0 + Z.of_nat (Z.to_nat (x - p0))) at 1 by lia. apply BY. lia.
Qed.
Lemma pshb_of_accessible : ltac2:(zQ "50!h9!luc!mh3!ls0!j4>1m$3>2p0$0>3len$0>0@3$2^3^2^1@3$1^4^3@2$4^3^2").
Proof.
  (intros m p0 len nd_i4 x Hx He; ndestruct nd_i4 as (A0 & AH & AC)). ndestruct (AC x ltac:(lia)) as (v & V0 & RD & OK).
  assert (E : shb m x = v) by (unfold shb; rewrite RD; apply b8_unsigned; lia).
  rewrite E. split; [| split; [exact V0| unfold byte_ok in OK; exact OK]].
  rewrite sh8_eq, shaddr_eq by lia. exact RD.
Qed.
Lemma ov_read1_of_mrd : ltac2:(zQ "b0!r6!t9!jp2!kt8!v6!l7!hte!ho4!hpd!lk0!lpe>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1b@1$1@1$0#8>0@3$5@1$2@1$1@1$0#8@3$a$6^3^2@2$3@1$1@1$0#8^1@3$5@1$2@1$4@1$1@1$0#8@4$9$6^4^3N1@2$3@1$4@1$1@1$0#8@3$7@1$1@1$0#8^2@1$8@1$1@1$0#8").
Proof. intros m a b RD. rewrite ov_rdn. cbn [rdn]. unfold mrd in RD. rewrite RD. reflexivity. Qed.
Lemma munch_mrd : ltac2:(zQ "h01!r6!t9!jp2!hte!lpe!lq5!v6!q5!l7!h9!mld!mm4!mmd!q0!qb!r0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$6$a>1m~0>2mc~0>1y$9>0@3$b^4^3^2>0@2$c^5^2>0@2$7@2$dZ^3@2$e^3@2$f+2+k0@3$8@1$2@1$1@1$0#8@3$4$3^5@1$5^4@3$4$3^6@1$5^4").
Proof. intros W m mc y MU OUT R. unfold mrd. rewrite (MU (wa y)); [reflexivity|]. rewrite wa_unsigned by lia. exact OUT. Qed.
Lemma pinb_rd : ltac2:(zQ "h30!r6!t9!h9!v6!jp2!kt8!ho4!hpd!l7!lk0!lu5!hte!hja!mld!mm4!mmd!q0!qb!iof>1m$c>2mc>0@1$1@1$0#k0@1$4@1$1@1$0#8>1W@1$3$d>1q$2>1e$2>3inb>0$2@1$1@1$0#8>1x$2>0@4$a^7^4^3^2>0@3$e^6^8^7>0@2$f^7^3>0@2$h0^7^4>0@2$h1^5^7@3$8@1$4@1$3@1$1@1$0#8@4$9$b^b@2$h2@1$0#k0^6N1@2$5@1$3@1$1@1$0#8@3$6@1$1@1$0#8@1^7^6@1$7@1$1@1$0#8").
Proof.
  (intros m mc W q e inb x nd_i5 MU OUT X1 X2; ndestruct nd_i5 as (Q0 & EH & P)). apply ov_read1_of_mrd. change (Z_to_bv 64 x) with (wa x).
  rewrite (munch_mrd W m mc x MU OUT ltac:(lia)). apply P; lia.
Qed.
Lemma pshb_rd : ltac2:(zQ "h70!r6!t9!v6!h9!q0!jp2!pa!kt8!ho4!hpd!l7!lk0!luc!lqb!hte!hja!mld!mm4!mmd!ind!qb!r0!iof>1m$f>2mc>0@1$1@1$0#k0@1$5@1$1@1$0#8>1W@1$2$h0>1q$3>1e$3>1x$3>0@3$c^6^3^2>0@3$h1^5^7^6>0@2$h2^6@1$6^3>0@2$4^6^4>0@2$h4^5^6>0@2$4Z^8>0@2$4^8@2$h5+2+if@3$a@1$5@1$2@1$1@1$0#8@4$b$e^c@2$h6@1$0#k0@1$6^8N1@2$7@1$2@1$1@1$0#8@3$8@1$1@1$0#8@1$h3@2$d^d^8@1$9@1$1@1$0#8").
Proof.
  intros m mc W q e x P MU OUT X1 X2 Q0 EH. apply ov_read1_of_mrd. change (Z_to_bv 64 (sh8 x)) with (wa (sh8 x)).
  pose proof (sh8_bound x ltac:(lia)).
  rewrite (munch_mrd W m mc (sh8 x) MU OUT ltac:(lia)). apply (proj1 (P x X1 X2)).
Qed.
(* [comment removed for export] *)
Ltac pose_shb_facts SHB x :=
  lazymatch goal with
  | _ : 0 <= shb _ x < 8 |- _ => idtac
  | _ => lazymatch type of SHB with pshb ?m ?q ?e =>
           let B := fresh "SBL" in let D := fresh "SBD" in
           pose proof (proj1 (proj2 (SHB x ltac:(lia) ltac:(lia)))) as B;
           pose proof ((proj2 (proj2 (SHB x ltac:(lia) ltac:(lia)))) : boxP (shb m x = 0 \/ x mod 8 + 1 <= shb m x)) as D
         end
  end.
Ltac outside_tac := cbn [outside fst snd]; lia.
Ltac solve_load_anum :=
  match goal with
  | |- context [ov_read_bytes ?segs ?mc ?a 1%nat] =>
      let E := addr_expr a in
      lazymatch goal with MU : munch ?W ?m0 mc |- _ =>
        lazymatch E with
        | sh8 ?x =>
            lazymatch goal with SHB : pshb m0 ?q ?e |- _ =>
              pose_shb_facts SHB x;
              replace (ov_read_bytes segs mc a 1%nat) with (Some [b8 (shb m0 x)])
                by (symmetry; pose proof (sh8_bound x ltac:(lia)); exact (pshb_rd m0 mc W q e x SHB MU ltac:(outside_tac) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))
            end
        | _ =>
            lazymatch goal with INB : pinb m0 ?q ?e ?inb |- _ =>
              replace (ov_read_bytes segs mc a 1%nat) with (Some [inb E])
                by (symmetry; exact (pinb_rd m0 mc W q e inb E INB MU ltac:(outside_tac) ltac:(lia) ltac:(lia)))
            end
        end
      end
  end; load_post.
Ltac solve_load ::= first [ solve_load_base | solve_load_anum | solve_load_image ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_shb_facts :=
  repeat match goal with
  | H : boxP (shb _ _ = 0 \/ _) |- _ => clear H
  | H : 0 <= shb _ _ < 8 |- _ => clear H
  end.
(* [comment removed for export] *)
Ltac pose_reg_shb :=
  lazymatch goal with
  | SHB : pshb _ _ _ |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      repeat (match R with context [shb _ ?x] =>
                lazymatch goal with
                | _ : 0 <= shb _ x < 8 |- _ => fail
                | _ => pose_shb_facts SHB x
                end
              end)
  | |- _ => idtac
  end.
Ltac chkjoin t back :=
  pose_reg_shb; norm_s32;
  lazymatch goal with
  | |- evt ?segs _ (MS ?R ?F _ ?fc ?oe ?m ?rom) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 t)) in
      let Rf := constr:(fun tv : word => ltac:(let r := eval cbv beta iota delta [tset] in (@tset word p tv R) in exact r)) in
      eapply (evt_cut segs (fun ms => exists tv : word, ms = MS (Rf tv) F (Z_to_bv 64 back) fc oe m rom));
      [ st1b; norm_lits; norm_s32;
        let K := fresh "K" in if_cases K; zify_cond K; try rewrite !unsigned_zb in K; box_ugly K;
        [ (* [comment removed for export] *)
          first [ exfalso; clear - K; lia | idtac ];
          st1b; norm_lits; norm_s32; st1b; norm_lits; norm_s32;
          let K2 := fresh "K" in if_cases K2; zify_cond K2; try rewrite !unsigned_zb in K2; box_ugly K2;
          [ apply evt_done; cbv beta; eexists; reflexivity
          | exfalso; unbox_shad_for K2; lia ]
        | apply evt_done; cbv beta; eexists; reflexivity ] 
      | cbv beta; let ms1 := fresh "ms" in let tv := fresh "jt" in intros ms1 (tv & ->); clear_shb_facts ]
  end.

(* [comment removed for export] *)
Ltac gen_data ::=
  repeat (lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with
      | context [Z_to_bv 64 (Z.lor ?a ?b)] => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.lor a b)) in |- *; clearbody w
      | context [Z_to_bv 64 (Z.land ?a ?b)] => lazymatch b with 7 => fail | 1 => fail | _ => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.land a b)) in |- *; clearbody w end
      | context [Z_to_bv 64 (Z.shiftl ?a ?b)] => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.shiftl a b)) in |- *; clearbody w
      | context [Z_to_bv 64 (Z.shiftr ?a ?b)] => lazymatch b with 3 => fail | _ => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.shiftr a b)) in |- *; clearbody w end
      | context [Z_to_bv 64 (?a * ?b)] =>      (* [comment removed for export] *)
          lazymatch a with context [bv_unsigned _] => let w := fresh "dw" in set (w := Z_to_bv 64 (a * b)) in |- *; clearbody w end
      end
  end).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1032816 => chkjoin 11 1032820   (* [comment removed for export] *)
    | 1032936 => chkjoin 11 1032940   (* [comment removed for export] *)
    | 1033008 => chkjoin 11 1033012   (* [comment removed for export] *)
    | 1033056 => chkjoin 11 1033060   (* [comment removed for export] *)
    | 1033124 => chkjoin 6 1033128   (* [comment removed for export] *)
    | 1033272 => chkjoin 12 1033276   (* [comment removed for export] *)
    | 1033356 => chkjoin 12 1033360   (* [comment removed for export] *)
    | 1033432 => chkjoin 15 1033436   (* [comment removed for export] *)
    | 1033596 => chkjoin 12 1033600   (* [comment removed for export] *)
    | 1033692 => chkjoin 6 1033696   (* [comment removed for export] *)
    | 1033892 => chkjoin 12 1033896   (* [comment removed for export] *)
    | 1034100 => chkjoin 13 1034104   (* [comment removed for export] *)
    | 1034636 => chkjoin 13 1034640   (* [comment removed for export] *)
    | 1034772 => chkjoin 12 1034776   (* [comment removed for export] *)
    | 1034836 => chkjoin 12 1034840   (* [comment removed for export] *)
    | 1035060 => chkjoin 13 1035064   (* [comment removed for export] *)
    | 1035152 => chkjoin 13 1035156   (* [comment removed for export] *)
    | 1035664 => chkjoin 14 1035668   (* [comment removed for export] *)
    | 1035724 => chkjoin 14 1035728   (* [comment removed for export] *)
    | 1035788 => chkjoin 14 1035792   (* [comment removed for export] *)
    | 1035852 => chkjoin 14 1035856   (* [comment removed for export] *)
    | 1035916 => chkjoin 14 1035920   (* [comment removed for export] *)
    | 1035980 => chkjoin 14 1035984   (* [comment removed for export] *)
    | 1036044 => chkjoin 14 1036048   (* [comment removed for export] *)
    | 1036108 => chkjoin 14 1036112   (* [comment removed for export] *)
    | 1036172 => chkjoin 14 1036176   (* [comment removed for export] *)
    | 1036236 => chkjoin 14 1036240   (* [comment removed for export] *)
    | 1036300 => chkjoin 14 1036304   (* [comment removed for export] *)
    | 1036364 => chkjoin 14 1036368   (* [comment removed for export] *)
    | 1036428 => chkjoin 14 1036432   (* [comment removed for export] *)
    | 1036492 => chkjoin 14 1036496   (* [comment removed for export] *)
    | 1036556 => chkjoin 14 1036560   (* [comment removed for export] *)
    | 1036620 => chkjoin 12 1036624   (* [comment removed for export] *)
    | 1036984 => chkjoin 7 1036988   (* [comment removed for export] *)
    | 1037008 => chkjoin 29 1037012   (* [comment removed for export] *)
    | 1037032 => chkjoin 30 1037036   (* [comment removed for export] *)
    | 1037056 => chkjoin 31 1037060   (* [comment removed for export] *)
    | 1037208 => chkjoin 13 1037212   (* [comment removed for export] *)
    | 1037276 => chkjoin 13 1037280   (* [comment removed for export] *)
    | 1037300 => chkjoin 14 1037304   (* [comment removed for export] *)
    | 1037376 => chkjoin 13 1037380   (* [comment removed for export] *)
    | 1037400 => chkjoin 16 1037404   (* [comment removed for export] *)
    | 1037424 => chkjoin 15 1037428   (* [comment removed for export] *)
    | 1037868 => chkjoin 12 1037872   (* [comment removed for export] *)
    | 1038192 => chkjoin 12 1038196   (* [comment removed for export] *)
    | 1038332 => chkjoin 12 1038336   (* [comment removed for export] *)
    | 1038824 => chkjoin 13 1038828   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
