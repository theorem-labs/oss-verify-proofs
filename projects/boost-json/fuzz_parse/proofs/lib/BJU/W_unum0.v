(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap BJIface BJEhTabs BJKitW BJKitVS BJKitIn BJKitRV BJKitStr BJKitSeg BJKitNum.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~m03mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~r14cellk14consr12C8r12C1r12C4r12CBk13nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hh58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hlc5rsegshfbbv_unsigned01Z46Stdlib6ZArith6BinInt1Zhr33add37Corelib4Init5Logicht23and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hud2b8hf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJKitRV~~~~~~ij82rvht22eqij83rs0ij83rs3ij83rsphr33powhr32lehr32lthr33opphf8bv_swrap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~irc4sx32hf9bv_signedhr33mulhr36moduloht23iffht22orhr33subhr34lxorhr34landirc3le4k13appk16option3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejl5h0le_bytes_to_wordhf7bv_wrap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jq36v_sltik13nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7W_unum0~~~~~~jv28POW10U_Njv2aPOW10U_TBLjv2bpow10u_oget79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Image~~~~~~kl9bimage_bytesk16lengthjv2cpow10u_bytesirc8bytes_athh58ro_cellsirc7mem_invk14Some37Corelib5Lists7ListDefku76firstnku75skipn3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslh1dov_read_byteshr36to_nat" s.
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
  Definition uframe : ltac2:(zQ "40!h9!jc!l9!qb>1m$3>3sp'@1$1@1$0#k0>2j8@1$2@1$1@1$0#8>4mant@1$1@1$0#k0>4bias@1$1@1$0#k0>4expo@1$1@1$0#k0>4xneg@1$1@1$0#8>3neg@1$1@1$0#8>2j6@1$2@1$1@1$0#8>4fs0v@1$1@1$0#k0>3s3v@1$1@1$0#k0>3s2v@1$1@1$0#k0>3s1v@1$1@1$0#k0>3s0v@1$1@1$0#k0>3rav@1$1@1$0#k0P") := ltac2:(zQ "e0!h9!ud!jc!v4!vb!l9!hg0!hg5!hga!hgf!hl0!qb!hp9!hq2\1m$b\3sp'@1$2@1$0#k0\2j8@1$5@1$2@1$0#8\4mant@1$2@1$0#k0\4bias@1$2@1$0#k0\4expo@1$2@1$0#k0\4xneg@1$2@1$0#8\3neg@1$2@1$0#8\2j6@1$5@1$2@1$0#8\4fs0v@1$2@1$0#k0\3s3v@1$2@1$0#k0\3s2v@1$2@1$0#k0\3s1v@1$2@1$0#k0\3s0v@1$2@1$0#k0\3rav@1$2@1$0#k0@4$a$c^f@2$d@1$0#k0^e@3$3$1@2$8N8^d@3$3$1@1$4^c@3$3$1@1$7^b@3$3$1@1$7^a@3$3$1@1$6^9@3$3$1@1$6^8@3$3$1@2$8N6^7@3$3$1@1$4^6@3$3$1@1$4^5@3$3$1@1$4^4@3$3$1@1$4^3@3$3$1@1$4^2@3$3$1@1$4^1@1$9$1").
  (* [comment removed for export] *)
  Definition ucells : ltac2:(zQ "50!h9!jc!l9!hr0!qb>1m$4>2pa@1$1@1$0#k0>1e$3>4pad7@1$2@1$1@1$0#8P") := ltac2:(zQ "h20!h9!ud!v4!hgf!hl0!hp9!hsb!jc!hq2!l9!hu6!hr0!hg0!vb!hga!ii8!qb!iie\1m$h0\2pa@1$7@1$0#k0\1e$b\4pad7@1$9@1$7@1$0#8@2$a@4$4$5^4@2$6@2$8@1$0#k0^3+r8@3$2$1@1$d@2$h1@1$0#k0^2@1$3$1@4$4$5^4@2$6@2$8@1$0#k0^3+r0@3$2$1@1$c@1$fZ@3$2$1@2$eN7^1@1$3$1").
  Ltac open_ucells UC := box_post; destruct UC as (END & MORE).
  (* [comment removed for export] *)
  Definition uctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    hceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 216 <= bv_unsigned pa /\ bv_unsigned pa + 280 <= 2^64 /\ e <= hceil.
  Ltac open_uctx UX := box_post; destruct UX as (CEIL & ROOM & SPA & A0HI & EHCL).
  (* [comment removed for export] *)
  Definition uregs : ltac2:(zQ "40!h9!jc!hr0!in6>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "a0!h9!jc!inc!hu6!hr0!io2!io9!ip0!in6!iie\1r$8\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$4@2$3@3$2@1$1@1$0#k0@1$7^4^3@2$3@3$2@1$1@1$0#k0@1$5^4^2@3$2@1$1@1$0#k0@1$6^4@2$9@1$0#k0^1").
  Ltac open_uregs UR := box_post; destruct UR as (?U1 & ?U2 & ?U3).
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe in *; unfold seg_post, uregs, uframe, ucells; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    hcb.
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ => unfold uregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
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
  Lemma swrap32_of_u64 : ltac2:(zQ "c0!hsb!h9!hr0!ip7!hu6!inc!ipe!iq4!iqa!iie!ir1!hq2>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
  Proof.
    intros b k Hbk. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32). change (2^32 * 2^32 / 2) with (2^63). change (2 ^ 32 / 2) with (2^31).
    replace (b mod (2 ^ 32 * 2 ^ 32) + k + 2 ^ 31) with ((k + 2 ^ 31) + b mod (2 ^ 32 * 2 ^ 32)) by lia.
    rewrite Z.add_mod by lia. rewrite Z.mod_mod_divide by (exists (2^32); lia).
    rewrite <- Z.add_mod by lia. replace (k + 2 ^ 31 + b) with (b + k + 2^31) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma swrap32_of_u64_0 : ltac2:(zQ "b0!h9!hr0!ip7!hu6!inc!ipe!iq4!iqa!iie!ir1!hq2>1b$1>0@2$3@2$5@1$7@2$2+2+hf^1@2$6^1@2$2+2+hf@3$4$1@2$9@1$0#i0@2$a@1$0#k0@2$8@1$0#k0^2^2").
  Proof. intros b Hb. rewrite <- (Z.add_0_r (bv_unsigned (Z_to_bv 64 b))). rewrite swrap32_of_u64 by lia. lia. Qed.
  Lemma sx32_ssmall : ltac2:(zQ "b0!h9!ip7!iie!hu6!inc!hr0!iv6!ipe!iq4!iqa!jc>1b$5>0@2$3@2$7@1$9@2$1+2+hf^1@2$8^1@2$1+2+hf@3$4@1$a@1$0#k0@1$6@2$2@1$0#k0^2@2$2@1$0#k0^2").
  Proof. intros b Hb. unfold sx32. rewrite swrap32_of_u64_0 by lia. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma signed_of_small : ltac2:(zQ "a0!h9!hr0!ip7!hu6!inc!ipe!iq4!iqa!iie!ive>1b$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
  Proof.
    intros b Hb. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 / 2) with (2^63). lia.
  Qed.
  Lemma swrap32_mul_u64 : ltac2:(zQ "c0!jga!h9!hr0!ip7!hu6!inc!ipe!iq4!iqa!iie!ir1!hq2>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
  Proof.
    intros b k Hbk. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 / 2) with (2^31).
    rewrite Z.add_mod by lia. rewrite <- Z.mul_mod_idemp_l by lia. rewrite Z.mod_mod_divide by (exists (2^32); lia).
    rewrite Z.mul_mod_idemp_l by lia. rewrite <- Z.add_mod by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma mod64_of_small_nonneg : ltac2:(zQ "70!hr0!hu6!inc!ipe!iq4!jh1!ip7>1x$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+hggggggggggggggg0^2").
  Proof. intros x Hx. apply Z.mod_small. lia. Qed.
  Lemma mod64_of_small_neg : ltac2:(zQ "90!hr0!ip7!hu6!inc!hsb!ipe!iq4!jh1!iqa>1x$0>0@2$2@2$5@1$8@2$1+2+k0^1@2$6^1Z@3$3$0@2$7^2+hggggggggggggggg0@2$4^2@2$1+2+k0").
  Proof. intros x Hx. rewrite <- (Z.mod_add x 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia. Qed.
  Lemma mod64_le_iff : ltac2:(zQ "80!ipe!hu6!ip7!hr0!iq4!jhb!jh1!iqa>1x$3>1c$3>0@2$1@2$0@1$7@2$2+2+jf^2@2$4^2@2$2+2+jf>0@2$1@2$0Z^2@2$4^2@2$2+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$0Z^4@2$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_lt_iff : ltac2:(zQ "80!iq4!hu6!ipe!ip7!hr0!jhb!jh1!iqa>1x$4>1c$4>0@2$1@2$2@1$7@2$3+2+jf^2@2$0^2@2$3+2+jf>0@2$1@2$2Z^2@2$0^2@2$3+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$2Z^4@2$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_ge_iff : ltac2:(zQ "90!ipe!iq4!ip7!hu6!hr0!jhb!ji2!jh1!iqa>1x$4>1c$4>0@2$3@2$0@1$8@2$2+2+jf^2@2$1^2@2$2+2+jf>0@2$3@2$0Z^2@2$1^2@2$2+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$1^4Z@2$0^3^4").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_gt_iff : ltac2:(zQ "90!iq4!ip7!hu6!hr0!ipe!jhb!ji2!jh1!iqa>1x$3>1c$3>0@2$2@2$4@1$8@2$1+2+jf^2@2$0^2@2$1+2+jf>0@2$2@2$4Z^2@2$0^2@2$1+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$0^4Z@2$0^3^4").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  (* [comment removed for export] *)
  Lemma mod64_geh_iff : ltac2:(zQ "90!ip7!ipe!hu6!iq4!hr0!jhb!jh1!iqa!ji8>1x$4>1c$4>0@2$2@2$1@1$7@2$0+2+jf^2@2$3^2@2$0+2+jf>0@2$2@2$1@2$0+2+jf^2@2$3^2@2$0+2+k0@2$5@2$1^3@2$6^4+hggggggggggggggg0@2$2@2$1@2$8^3@2$0+2+k0^4@2$3^4Z").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_lth_iff : ltac2:(zQ "a0!ip7!iq4!ipe!hu6!hr0!jhb!ji2!jh1!iqa!ji8>1x$4>1c$4>0@2$3@2$2@1$8@2$0+2+jf^2@2$1^2@2$0+2+jf>0@2$3@2$2@2$0+2+jf^2@2$1^2@2$0+2+k0@2$5@2$1@2$7^4+hggggggggggggggg0^3@2$6@2$2Z^4@2$1^4@2$9^3@2$0+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_eq_iff : ltac2:(zQ "90!hr0!ip7!hu6!inc!ipe!iq4!jhb!jh1!iqa>1x$0>1c$0>0@2$2@2$4@1$8@2$1+2+jf^2@2$5^2@2$1+2+jf>0@2$2@2$4Z^2@2$5^2@2$1+2+jf@2$6@3$3$0@2$7^4+hggggggggggggggg0^3@3$3$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_eqh_iff : ltac2:(zQ "a0!ip7!hr0!hu6!inc!ipe!iq4!jhb!jh1!iqa!ji8>1x$1>1c$1>0@2$2@2$4@1$8@2$0+2+jf^2@2$5^2@2$0+2+jf>0@2$2@2$4@2$0+2+jf^2@2$5^2@2$0+2+k0@2$6@3$3$1@2$7^4+hggggggggggggggg0^3@3$3$1^4@2$9^3@2$0+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma byte_range : ltac2:(zQ "60!h9!hq2!hu6!ipe!iq4!jc>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
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
  Lemma lxor_m1_64 : ltac2:(zQ "80!hr0!hu6!inc!ipe!iq4!jif!ip7!ji8>1w$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+vvvvvvvvvvvvvvvf@2$7+vvvvvvvvvvvvvvvf^2").
  Proof.
    intros w Hw. rewrite lnot_mod64 by lia. pose proof (Z.add_lnot_diag w) as D.
    replace (Z.lnot w) with (-w - 1) by lia. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma swrap32_id : ltac2:(zQ "90!hr0!ip7!hu6!inc!h9!ipe!iq4!iqa!ir1>1x$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
  Proof. intros x Hx. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2) with (2^31). lia. Qed.
  Lemma mod64_eq_mod64_iff : ltac2:(zQ "90!hr0!inc!iq4!jh1!ip7!ji8!hu6!jhb!iqa>1x$0>1y$0>0@2$6@2$2@1$8@2$4+2+k0@2$5^2^1@2$2@2$5^2^1@2$4+2+k0@2$7@3$1$0@2$3^3+hggggggggggggggg0@2$3^2+hggggggggggggggg0@3$1$0^3^2").
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
    | context [?x mod 18446744073709551616 <= ?c] => rewrite (mod64_le_iff x c) in K by (clear K; lia)
    | context [?x mod 18446744073709551616 < ?c] => first [rewrite (mod64_lt_iff x c) in K by (clear K; lia) | rewrite (mod64_lth_iff x c) in K by (clear K; lia)]
    | context [?c <= ?x mod 18446744073709551616] => first [rewrite (mod64_ge_iff x c) in K by (clear K; lia) | rewrite (mod64_geh_iff x c) in K by (clear K; lia)]
    | context [?c < ?x mod 18446744073709551616] => rewrite (mod64_gt_iff x c) in K by (clear K; lia)
    | context [?x mod 18446744073709551616 = ?c] => first [rewrite (mod64_eq_iff x c) in K by (clear K; lia) | rewrite (mod64_eqh_iff x c) in K by (clear K; lia)]
    | context [?x mod 18446744073709551616] => first [rewrite (mod64_of_small_nonneg x) in K by (clear K; lia) | rewrite (mod64_of_small_neg x) in K by (clear K; lia)]
    end.
  Lemma land1_small : ltac2:(zQ "50!hr0!ipe!hu6!inc!jj7>1x$0>0@2$2@2$1Z^1@2$1^1+1@3$3$0@2$4^2+1^2").
  Proof. intros x Hx. change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  Lemma swrap32_id_m64 : ltac2:(zQ "a0!ip7!ji8!hr0!hu6!inc!h9!ipe!iq4!iqa!ir1>1x$2>0@2$3@2$6@1$8@2$0+2+hf@2$1^1@2$0+2+k0@2$7@2$1^1@2$0+2+k0@2$0+2+hf@3$4$2@2$9@1$5#i0^2@2$1^2@2$0+2+k0").
  Proof.
    intros x Hx. rewrite (bv_swrap_congr 32 x (x - 2^64)). apply swrap32_id; lia.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
    replace x with ((x - 2^64) + (2^32 * 2^32)) at 1 by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma uframe_merge16 : ltac2:(zQ "h10!ud!v4!h9!jc!vb!hg0!hga!l9!hgf!hg5!jjf!hl0!hp9!jk6!jkc!hr0!jo4>1m>0@1$3@1$2#k0@1$e@1$3@1$2#8>1A$f>2j8@1$7@1$3@1$2#8>2mw@1$3@1$2#k0>1b@1$3@1$2#k0>1x@1$3@1$2#k0>2xg@1$3@1$2#8>2ng@1$3@1$2#8>2j6@1$7@1$3@1$2#8>2f8@1$3@1$2#k0>3s3v@1$3@1$2#k0>3s2v@1$3@1$2#k0>3s1v@1$3@1$2#k0>3s0v@1$3@1$2#k0>3rav@1$3@1$2#k0>0@4$b$c^f^e@3$1$0@2$6N8^d@3$1$0@1$4^c@3$1$0@1$9^b@3$1$0@1$9^a@3$1$0@1$5^9@3$1$0@1$5^8@3$1$0@2$6N6^7@3$1$0@1$4^6@3$1$0@1$4^5@3$1$0@1$4^4@3$1$0@1$4^3@3$1$0@1$4^2@3$1$0@1$4^1@1$8$0@4$b$c^h0^f@3$1$0@2$6N8^e@3$1$0@1$4^d@3$1$0@1$4@1$h0@3$d@1$3@1$2#8@1$a^c@1$a^b@3$1$0@1$5^a@3$1$0@1$5^9@3$1$0@2$6N6^8@3$1$0@1$4^7@3$1$0@1$4^6@3$1$0@1$4^5@3$1$0@1$4^4@3$1$0@1$4^3@3$1$0@1$4^2@1$8$0").
  Proof.
    intros until rav. intros R. pose proof R as [[W _] _]. cbn in W.
    eapply rw_cells_rebytes; [exact R| | | reflexivity].
    - cbn. tauto.
    - cbn [cells_bytes cbytes app]. rewrite le8_of_bytes by (rewrite length_app, !length_le4; reflexivity). rewrite <- ?app_assoc. reflexivity.
  Qed.
  Ltac merge16 :=
    match goal with
    | UF : rw_cells _ ?m ?A [CB 8 _; C8 _; C4 _; C4 _; C1 _; C1 _; CB 6 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- evt _ _ (MS _ _ _ _ _ ?m _) =>
        apply uframe_merge16 in UF
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
  Ltac step1 := first [ st1b | arm_inputs; st1b | merge16; st1b ]; norm_lits; norm_s32; gen_data.
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
  Definition uvs : ltac2:(zQ "50!hr0!h9!jc!l9!qb>1m$4>2pa@1$2@1$1#k0>4temp$0>2Bg$0>1T$0>2EE$0>2ch$0>2j7@1$3@1$2@1$1#8P") := ltac2:(zQ "h00!h9!ud!v4!vb!iie!hr0!jc!l9!hgf!hg0!hga!hl0!ii8!qb!hp9!hq2\1m$d\2pa@1$6@1$0#k0\4temp$5\2Bg$5\1T$5\2EE$5\2ch$5\2j7@1$7@1$6@1$0#8@4$b$e^8@2$f@1$0#k0^7@3$2$1@1$3@2$4@1$0#k0Z@3$2$1@1$3@2$4@1$0#k0^6@3$2$1@1$3@2$4@1$0#k0^5@3$2$1@1$3@2$4@1$0#k0^4@3$2$1@1$3@2$4@1$0#k0^3@3$2$1@1$3@2$4@1$0#k0^2@3$2$1@1$9@1$c+1@3$2$1@2$aN7^1@3$2$1@1$3@2$4@1$0#k0Z@1$8$1").
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- uregs _ _ _ _ => unfold uregs
    | |- uframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold uframe
    | |- ucells _ _ _ _ => unfold ucells
    | |- uvs _ _ _ _ _ _ _ _ => unfold uvs
    end.
  Ltac useg_begin r ::=
    intro_rv r; subst; unfold uframe, uvs in *; unfold seg_post, uregs, uframe, ucells, uvs; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ ?s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ s0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    hcb.
  Lemma land7_mod8 : ltac2:(zQ "50!hr0!inc!jj7!ipe!jh1>1x$0>0@2$3Z^1@3$1$0@2$2^2+7@2$4^2+8").
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
  Lemma wrap32_of_u64 : ltac2:(zQ "60!h9!hr0!jp9!inc!iie!hq2>1a$1@3$3$1@2$2@1$0#i0@2$5@1$0#k0@2$4@1$0#k0^1@2$2@1$0#i0^1").
  Proof.
    intros a. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32).
    rewrite Z.mod_mod_divide by (exists (2^32); lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_2 : ltac2:(zQ "c0!h9!hsb!hr0!ip7!iie!hq2!hu6!inc!ipe!iq4!iqa!ir1>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
  Proof.
    intros a b H. rewrite (bv_swrap_congr 32 _ (a + b)); [apply swrap32_id; lia|].
    unfold bv_wrap. rewrite Z.add_mod by (unfold bv_modulus; lia). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 a))). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 b))).
    rewrite !wrap32_of_u64. unfold bv_wrap. rewrite <- Z.add_mod by (unfold bv_modulus; lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_sub : ltac2:(zQ "c0!h9!ji8!hr0!ip7!iie!hq2!hu6!inc!ipe!iq4!iqa!ir1>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
  Proof.
    intros a b H. rewrite (bv_swrap_congr 32 _ (a - b)); [apply swrap32_id; lia|].
    unfold bv_wrap. rewrite Zminus_mod by (unfold bv_modulus; lia). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 a))). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 b))).
    rewrite !wrap32_of_u64. unfold bv_wrap. rewrite <- Zminus_mod by (unfold bv_modulus; lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_rsub : ltac2:(zQ "c0!ji8!h9!hr0!ip7!hu6!inc!ipe!iq4!iqa!iie!ir1!hq2>1k$2>1b$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0^3@2$b@1$1#k0@2$9@1$1#k0^2@2$0^3^2").
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
  Lemma v_slti_true : ltac2:(zQ "b0!h9!hr0!iq4!ip7!iie!hu6!inc!ju2!ipe!iqa!jc>1v$1>3imm$1>0@2$5@2$8@1$9@2$3+2+jf^2@2$2^2@2$3+2+jf>0@2$2^3^2@3$6@1$a@1$0#k0@2$7@2$4@1$0#k0^4^3@2$4@1$0#k0+1").
  Proof. intros v imm Hv H. unfold v_slti, zsig. rewrite signed_of_small by lia. destruct (Z.ltb_spec0 v imm); [reflexivity| lia]. Qed.
  Lemma v_slti_false : ltac2:(zQ "b0!h9!hr0!ipe!ip7!iie!hu6!inc!ju2!iq4!iqa!jc>1v$1>3imm$1>0@2$5@2$2@1$9@2$3+2+jf^2@2$8^2@2$3+2+jf>0@2$2^2^3@3$6@1$a@1$0#k0@2$7@2$4@1$0#k0^4^3@2$4@1$0#k0Z").
  Proof. intros v imm Hv H. unfold v_slti, zsig. rewrite signed_of_small by lia. destruct (Z.ltb_spec0 v imm); [lia| reflexivity]. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition POW10U_TBL : Z := 0x151a0.
  Definition POW10U_N : nat := 4936.
  (* [comment removed for export] *)
  Definition pow10u_oget : ltac2:(zQ "40!l9!h9!jc!jkc>1o@1$3@1$0@1$2@1$1#8@1$0@1$2@1$1#8") := ltac2:(zQ "50!h9!jc!l9!jkc!hgf\1o@1$3@1$2@1$1@1$0#8M3\1o@1$3@1$2@1$1@1$0#8@1$2@1$1@1$0#8^1\2bs@1$2@1$1@1$0#8^1@1$4@1$1@1$0#8").
  Definition pow10u_bytes : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#8") := ltac2:(zQ "50!kj0!kjc!kka!kp5!hp9@1$2@3$3$4$1$0").
  Lemma pow10u_len : ltac2:(zQ "70!kq4!juc!inc!h9!kj0!kqd!jc@3$2$1@2$0@1$6@1$3#8$5$4").
  Proof. vm_compute. reflexivity. Qed.
  Lemma pow10u_ro_cells_bytes_at : ltac2:(zQ "d0!h9!jc!ud!hp9!v4!l9!juc!hgf!jkc!hr0!hga!krd!ks9>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$9>1n$6>2bs@1$5@1$1@1$0#8>0@4$c$3^4^3@3$4$2@2$a^2^1@1$7$2@4$b$3^5^4^2").
  Proof. intros m A n bs [_ RB]. cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB. exact RB. Qed.
  Lemma pow10u_ro : ltac2:(zQ "80!h9!hp9!jc!jkc!kjc!kqd!krd!kt5>1m>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@2$7$1^1@4$6$1^2$4$5").
  Proof.
    intros m MI. apply (pow10u_ro_cells_bytes_at m POW10U_TBL (length pow10u_bytes)).
    apply (ro_cells_image rsegs m POW10U_TBL pow10u_bytes MI); [vm_compute; reflexivity| unfold POW10U_TBL; lia| rewrite pow10u_len; unfold POW10U_TBL, POW10U_N; lia].
  Qed.
  Lemma pow10u_read : ltac2:(zQ "h50!h9!jc!l9!jkc!hp9!jga!ku0!hu6!inc!kve!lg8!hr0!lk8!kjc!kqd!kt5!hsb!ipe!iq4!ll9!iie>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1k$b>0@2$f$4^2>0@2$7@2$h1Z^2@2$h2^2+im9@3$8@1$3@1$2@1$1@1$0#8@4$c$4^4@2$h4@1$0#k0@2$h0$d@2$5+8^3N8@2$6@1$2@1$1@1$0#8@3$9@1$1@1$0#8N8@3$a@1$1@1$0#8@1$h3@2$5+8^3$e").
  Proof.
    intros m k MI HK. replace (Z_to_bv 64 (POW10U_TBL + 8 * k)) with (wa (POW10U_TBL + 8 * k)) by reflexivity.
    apply (bytes_at_read rsegs m POW10U_TBL pow10u_bytes (8 * k) 8 (pow10u_ro m MI)); [lia|]. rewrite pow10u_len. unfold POW10U_N. lia.
  Qed.

(* [comment removed for export] *)
Ltac br K := if_cases K; zify_cond K; box_ugly K; [ first [exfalso; lia | idtac] | first [exfalso; lia | idtac] ].
Ltac brp K := if_cases K; zify_cond K; box_ugly K; try (exfalso; lia).
(* [comment removed for export] *)
