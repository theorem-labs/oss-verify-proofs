(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import N8Store.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc6shiftr37Corelib4Init5Logick32eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA8W_apesc0~~~~~~lc3sh8hc2lek33andhc2lthc3powhc3divhc6modulok32exhc3mul04Nposhc3opp35stdpp9bitvectorbdefinitionstd7Z_to_bvtd8bv_swraptdbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hhd4sx32td2bvtd9bv_signedk33iffk32orhc3subhc4lxorhc4landtd7bv_wrap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~hp93mem37Corelib4Init9Datatypeshtd6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hvf5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~ik32shhhd3mrdhhd2wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ip44cellhtd4Somehtd4conshtd3nilip42C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iv58ro_cellsik3baddressableik33mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~jl22b8hhd3sxbhc6of_natlc3shbhtd6lengthhtd4listlc4pinbhhd8bytes_at36Stdlib5Lists4Listjse9nth_errorhc6to_natik3aaccessiblelc4pshb3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskgcdov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kl43ivlkl45munchkl47outsidehc3lor79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA6AKitRV~~~~~~kr12rvkr13rs0kr13rs1kr14rs10kr14rs11kr13rs2kr13rs3kr13rs4kr13rs5kr13rs6kr13rs7kr13rs8kr13rspip42C8ip42CBiv58rw_cellsip42C4ik37AAPP_HIlc4ptsh" s.   (* [comment removed for export] *)
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
Lemma sh8_eq : ltac2:(zQ "50!h9!l7!pb!j4!ja>1x$0@3$1$0@1$2^1@2$3@2$4^1+3+nvvvogg0"). Proof. reflexivity. Qed.
Lemma sh8_bound : ltac2:(zQ "70!q1!q6!pb!h9!j4!qc!r1>1x$3>0@2$1@2$0Z^1@2$5^1@2$6+2+j0@2$1@2$0+nvvvogg0@1$2^2@2$0@2$4@1$2^2+1+igggnvvvogg1").
Proof. intros x Hx. rewrite sh8_eq. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma sh8_bound47 : ltac2:(zQ "60!q1!q6!pb!h9!j4!qc>1x$3>0@2$1@2$0Z^1@2$5^1+ogggggggggg0@2$1@2$0+nvvvogg0@1$2^2@2$0@2$4@1$2^2+1+hgggnvvvogg0").
Proof. intros x Hx. rewrite sh8_eq. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Ltac fold_sh8 := repeat match goal with |- context [Z.shiftr ?x 3 + 2147450880] => rewrite <- (sh8_eq x) end.
(* [comment removed for export] *)
Lemma sh8_off8 : ltac2:(zQ "70!h9!l7!pb!j4!q1!r7!rd>1a$0>1c$0>1k$0>0@2$4Z^3>0@3$1$0@2$6^4+8Z>0@2$4Z^4>0@3$1$0^4@2$5^5+8@3$1$0@1$2@2$3^7^6@2$3@1$2^7^5").
Proof. intros a c k Ha H8 Hc ->. rewrite !sh8_eq, !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.
(* [comment removed for export] *)
Lemma mod0_lin : ltac2:(zQ "60!h9!l7!s6!qc!rd!sb>1a$0>1n$0>0@2$3Z^1>0@3$1$0@2$4^3^2Z@2$2$0\1k$0@3$1$0^5@2$5^4^1").
Proof. intros a n Hn Hm. exists (a / n). pose proof (Z.div_mod a n ltac:(lia)). lia. Qed.
Lemma sh8_off16k : ltac2:(zQ "70!h9!l7!pb!j4!q1!r7!sb>1a$0>1k$0>1c$0>1j$0>0@3$1$0^4@2$6+h0^3>0@2$4Z^5>0@2$4Z^4>0@3$1$0^4@2$5^5+8@3$1$0@1$2@2$3^8^6@2$3@1$2^8^5").
Proof. intros a k c j E Ha Hc Hj. apply (sh8_off8 a c j Ha); [| exact Hc| exact Hj]. subst a. replace (16 * k) with ((2 * k) * 8) by lia. apply Z_mod_mult. Qed.
Ltac norm_shpa :=
  repeat match goal with
  | EPA : bv_unsigned ?pa = 16 * ?kp |- context [sh8 (bv_unsigned ?pa' + ?c)] => constr_eq pa pa';
      let j := eval vm_compute in (c / 8) in
      rewrite (sh8_off16k (bv_unsigned pa) kp c j EPA ltac:(lia) ltac:(lia) eq_refl)
  end.
  Lemma swrap32_of_u64 : ltac2:(zQ "c0!j4!t1!h9!r1!q6!l7!q1!qc!t7!va!hg4!hgf>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
  Proof.
    intros b k Hbk. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32). change (2^32 * 2^32 / 2) with (2^63). change (2 ^ 32 / 2) with (2^31).
    replace (b mod (2 ^ 32 * 2 ^ 32) + k + 2 ^ 31) with ((k + 2 ^ 31) + b mod (2 ^ 32 * 2 ^ 32)) by lia.
    rewrite Z.add_mod by lia. rewrite Z.mod_mod_divide by (exists (2^32); lia).
    rewrite <- Z.add_mod by lia. replace (k + 2 ^ 31 + b) with (b + k + 2^31) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma swrap32_of_u64_0 : ltac2:(zQ "b0!t1!h9!r1!q6!l7!q1!qc!t7!va!hg4!hgf>1b$1>0@2$3@2$5@1$7@2$2+2+hf^1@2$6^1@2$2+2+hf@3$4$1@2$9@1$0#i0@2$a@1$0#k0@2$8@1$0#k0^2^2").
  Proof. intros b Hb. rewrite <- (Z.add_0_r (bv_unsigned (Z_to_bv 64 b))). rewrite swrap32_of_u64 by lia. lia. Qed.
  Lemma sx32_ssmall : ltac2:(zQ "b0!t1!r1!va!q6!l7!h9!hl7!q1!qc!t7!hlf>1b$5>0@2$3@2$7@1$9@2$1+2+hf^1@2$8^1@2$1+2+hf@3$4@1$a@1$0#k0@1$6@2$2@1$0#k0^2@2$2@1$0#k0^2").
  Proof. intros b Hb. unfold sx32. rewrite swrap32_of_u64_0 by lia. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma signed_of_small : ltac2:(zQ "a0!t1!h9!r1!q6!l7!q1!qc!t7!va!hm4>1b$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
  Proof.
    intros b Hb. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 / 2) with (2^63). lia.
  Qed.
  Lemma swrap32_mul_u64 : ltac2:(zQ "c0!sb!t1!h9!r1!q6!l7!q1!qc!t7!va!hg4!hgf>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
  Proof.
    intros b k Hbk. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32). change (2 ^ 32 / 2) with (2^31).
    rewrite Z.add_mod by lia. rewrite <- Z.mul_mod_idemp_l by lia. rewrite Z.mod_mod_divide by (exists (2^32); lia).
    rewrite Z.mul_mod_idemp_l by lia. rewrite <- Z.add_mod by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma mod64_of_small_nonneg : ltac2:(zQ "70!h9!q6!l7!q1!qc!rd!r1>1x$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+hggggggggggggggg0^2").
  Proof. intros x Hx. apply Z.mod_small. lia. Qed.
  Lemma mod64_of_small_neg : ltac2:(zQ "90!h9!r1!q6!l7!j4!q1!qc!rd!t7>1x$0>0@2$2@2$5@1$8@2$1+2+k0^1@2$6^1Z@3$3$0@2$7^2+hggggggggggggggg0@2$4^2@2$1+2+k0").
  Proof. intros x Hx. rewrite <- (Z.mod_add x 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia. Qed.
  Lemma mod64_le_iff : ltac2:(zQ "80!q1!q6!r1!h9!qc!hn0!rd!t7>1x$3>1c$3>0@2$1@2$0@1$7@2$2+2+jf^2@2$4^2@2$2+2+jf>0@2$1@2$0Z^2@2$4^2@2$2+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$0Z^4@2$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_lt_iff : ltac2:(zQ "80!qc!q6!q1!r1!h9!hn0!rd!t7>1x$4>1c$4>0@2$1@2$2@1$7@2$3+2+jf^2@2$0^2@2$3+2+jf>0@2$1@2$2Z^2@2$0^2@2$3+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$2Z^4@2$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_ge_iff : ltac2:(zQ "90!q1!qc!r1!q6!h9!hn0!hn6!rd!t7>1x$4>1c$4>0@2$3@2$0@1$8@2$2+2+jf^2@2$1^2@2$2+2+jf>0@2$3@2$0Z^2@2$1^2@2$2+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$1^4Z@2$0^3^4").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_gt_iff : ltac2:(zQ "90!qc!r1!q6!h9!q1!hn0!hn6!rd!t7>1x$3>1c$3>0@2$2@2$4@1$8@2$1+2+jf^2@2$0^2@2$1+2+jf>0@2$2@2$4Z^2@2$0^2@2$1+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$0^4Z@2$0^3^4").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  (* [comment removed for export] *)
  Lemma mod64_geh_iff : ltac2:(zQ "90!r1!q1!q6!qc!h9!hn0!rd!t7!hnb>1x$4>1c$4>0@2$2@2$1@1$7@2$0+2+jf^2@2$3^2@2$0+2+jf>0@2$2@2$1@2$0+2+jf^2@2$3^2@2$0+2+k0@2$5@2$1^3@2$6^4+hggggggggggggggg0@2$2@2$1@2$8^3@2$0+2+k0^4@2$3^4Z").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_lth_iff : ltac2:(zQ "a0!r1!qc!q1!q6!h9!hn0!hn6!rd!t7!hnb>1x$4>1c$4>0@2$3@2$2@1$8@2$0+2+jf^2@2$1^2@2$0+2+jf>0@2$3@2$2@2$0+2+jf^2@2$1^2@2$0+2+k0@2$5@2$1@2$7^4+hggggggggggggggg0^3@2$6@2$2Z^4@2$1^4@2$9^3@2$0+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_leh_iff : ltac2:(zQ "a0!q1!r1!q6!h9!qc!hn0!hn6!rd!t7!hnb>1x$3>1c$3>0@2$2@2$0@1$8@2$1+2+jf^2@2$4^2@2$1+2+jf>0@2$2@2$0@2$1+2+jf^2@2$4^2@2$1+2+k0@2$5@2$0@2$7^4+hggggggggggggggg0^3@2$6@2$0Z^4@2$0^4@2$9^3@2$1+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_gth_iff : ltac2:(zQ "90!qc!r1!q6!h9!q1!hn0!rd!t7!hnb>1x$3>1c$3>0@2$2@2$4@1$7@2$1+2+jf^2@2$0^2@2$1+2+jf>0@2$2@2$4@2$1+2+jf^2@2$0^2@2$1+2+k0@2$5@2$0^3@2$6^4+hggggggggggggggg0@2$2@2$0@2$8^3@2$1+2+k0^4@2$0^4Z").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_eq_iff : ltac2:(zQ "90!h9!r1!q6!l7!q1!qc!hn0!rd!t7>1x$0>1c$0>0@2$2@2$4@1$8@2$1+2+jf^2@2$5^2@2$1+2+jf>0@2$2@2$4Z^2@2$5^2@2$1+2+jf@2$6@3$3$0@2$7^4+hggggggggggggggg0^3@3$3$0^4^3").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma mod64_eqh_iff : ltac2:(zQ "a0!r1!h9!q6!l7!q1!qc!hn0!rd!t7!hnb>1x$1>1c$1>0@2$2@2$4@1$8@2$0+2+jf^2@2$5^2@2$0+2+jf>0@2$2@2$4@2$0+2+jf^2@2$5^2@2$0+2+k0@2$6@3$3$1@2$7^4+hggggggggggggggg0^3@3$3$1^4@2$9^3@2$0+2+k0").
  Proof. intros x c Hx Hc. destruct (Z.lt_ge_cases x 0); [rewrite mod64_of_small_neg by lia| rewrite mod64_of_small_nonneg by lia]; lia. Qed.
  Lemma byte_range : ltac2:(zQ "60!t1!hgf!q6!q1!qc!hlf>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
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
  Lemma lxor_m1_64 : ltac2:(zQ "80!h9!q6!l7!q1!qc!ho1!r1!hnb>1w$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+vvvvvvvvvvvvvvvf@2$7+vvvvvvvvvvvvvvvf^2").
  Proof.
    intros w Hw. rewrite lnot_mod64 by lia. pose proof (Z.add_lnot_diag w) as D.
    replace (Z.lnot w) with (-w - 1) by lia. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma swrap32_id : ltac2:(zQ "90!h9!r1!q6!l7!t1!q1!qc!t7!hg4>1x$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
  Proof. intros x Hx. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2) with (2^31). lia. Qed.
  Lemma mod64_eq_mod64_iff : ltac2:(zQ "90!h9!l7!qc!rd!r1!hnb!q6!hn0!t7>1x$0>1y$0>0@2$6@2$2@1$8@2$4+2+k0@2$5^2^1@2$2@2$5^2^1@2$4+2+k0@2$7@3$1$0@2$3^3+hggggggggggggggg0@2$3^2+hggggggggggggggg0@3$1$0^3^2").
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
  Lemma land1_small : ltac2:(zQ "50!h9!q1!q6!l7!ho8>1x$0>0@2$2@2$1Z^1@2$1^1+1@3$3$0@2$4^2+1^2").
  Proof. intros x Hx. change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
  Lemma swrap32_id_m64 : ltac2:(zQ "a0!r1!hnb!h9!q6!l7!t1!q1!qc!t7!hg4>1x$2>0@2$3@2$6@1$8@2$0+2+hf@2$1^1@2$0+2+k0@2$7@2$1^1@2$0+2+k0@2$0+2+hf@3$4$2@2$9@1$5#i0^2@2$1^2@2$0+2+k0").
  Proof.
    intros x Hx. rewrite (bv_swrap_congr 32 x (x - 2^64)). apply swrap32_id; lia.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
    replace x with ((x - 2^64) + (2^32 * 2^32)) at 1 by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.
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
  (* [comment removed for export] *)
  Ltac achk := fail.
  Ltac step1 := first [ achk | st1b | arm_inputs; st1b ]; norm_lits; fold_sh8; norm_shpa; norm_s32; gen_data.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => step1
                end
            end).
  (* [comment removed for export] *)
  Lemma land7_mod8 : ltac2:(zQ "50!h9!l7!ho8!q1!rd>1x$0>0@2$3Z^1@3$1$0@2$2^2+7@2$4^2+8").
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
  Lemma wrap32_of_u64 : ltac2:(zQ "60!t1!h9!hof!l7!va!hgf>1a$1@3$3$1@2$2@1$0#i0@2$5@1$0#k0@2$4@1$0#k0^1@2$2@1$0#i0^1").
  Proof.
    intros a. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2^32 * 2^32). change (2 ^ Z.of_N 32) with (2^32).
    rewrite Z.mod_mod_divide by (exists (2^32); lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_2 : ltac2:(zQ "c0!t1!j4!h9!r1!va!hgf!q6!l7!q1!qc!t7!hg4>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
  Proof.
    intros a b H. rewrite (bv_swrap_congr 32 _ (a + b)); [apply swrap32_id; lia|].
    unfold bv_wrap. rewrite Z.add_mod by (unfold bv_modulus; lia). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 a))). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 b))).
    rewrite !wrap32_of_u64. unfold bv_wrap. rewrite <- Z.add_mod by (unfold bv_modulus; lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_sub : ltac2:(zQ "c0!t1!hnb!h9!r1!va!hgf!q6!l7!q1!qc!t7!hg4>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
  Proof.
    intros a b H. rewrite (bv_swrap_congr 32 _ (a - b)); [apply swrap32_id; lia|].
    unfold bv_wrap. rewrite Zminus_mod by (unfold bv_modulus; lia). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 a))). fold (bv_wrap 32 (bv_unsigned (Z_to_bv 64 b))).
    rewrite !wrap32_of_u64. unfold bv_wrap. rewrite <- Zminus_mod by (unfold bv_modulus; lia). reflexivity.
  Qed.
  Lemma swrap32_of_u64_rsub : ltac2:(zQ "c0!hnb!t1!h9!r1!q6!l7!q1!qc!t7!va!hg4!hgf>1k$2>1b$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0^3@2$b@1$1#k0@2$9@1$1#k0^2@2$0^3^2").
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
  (* [comment removed for export] *)

Ltac brp K := if_cases K; zify_cond K; box_ugly K; try (exfalso; lia).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shb : ltac2:(zQ "20!h9!ht6>1m$1>1x$0$0") := ltac2:(zQ "a0!t1!hv5!h9!hlf!ija!ht6!io1!io7!ioe!hgf\1m$5\1x$2M1\1x@1$1@1$3@1$0#8$2@3$7$4^2@1$8@1$6^1\1b@1$3@1$0#8@2$9@1$0#8^1Z").
Lemma shaddr_eq : ltac2:(zQ "60!h9!l7!io1!j4!q1!ja>1x$0>0@2$4Z^1@3$1$0@2$3@2$5^2+3+nvvvogg0@1$2^2").
Proof. intros x Hx. unfold sh. rewrite ASHADOW_BASE_val, Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma ro_cells_C1_of_mrd : ltac2:(zQ "h10!t1!hlf!hv5!ija!it0!q1!it8!iu0!iu8!l7!h9!iuf!io7!ioe!jj0!j4!r1>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1A$a>1b@1$1@1$0#8>0@2$5Z^2>0@2$5@2$f^3+1@2$h0+2+k0>0@3$9@1$2@1$1@1$0#8@3$c$3^5@1$d^4@2$6@1$1@1$0#8^3@4$e$3^6^5@3$7$4@1$b^4@1$8$4").
Proof.
  intros m A b H0 H1 RD. split; [cbn; tauto|]. split; [exact H0|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. destruct i; [| lia]. cbn. rewrite Z.add_0_r. exact RD.
Qed.
(* [comment removed for export] *)
Lemma addressable_shro0 : ltac2:(zQ "f0!h9!it0!j4!q1!iu0!iu8!ija!jjc!jkb!pb!iuf!jj0!jod!r7!sb>1m$8>1A$0>1n$0>1a$0>0@3$7^4^3^2>0@2$3^4^2>0@2$3@2$2^3+1@2$2^5@2$e+8@2$d^4+8@4$b$6^7@1$9^4@3$4$1@1$a@1$cZ@1$5$1").
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
Lemma unsigned_wrap64 : ltac2:(zQ "90!t1!h9!q6!l7!q1!qc!hnb!va!hgf>1x$1>0@2$2@2$4+hggggggggggggggg0^1@2$5^1+iggggggggggggggg0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2@2$6^2+hggggggggggggggg0").
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite <- (Z.mod_add x (-1) 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma sxb_b8_small : ltac2:(zQ "a0!t1!q6!l7!h9!jp3!jod!q1!qc!va!hlf>1v$3>0@2$1@2$6Z^1@2$7^1+o0@3$2@1$9@1$0#k0@1$4@1$5^2@2$8@1$0#k0^2").
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
    | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_wrap64 x) by lia
    end.
(* [comment removed for export] *)
(* [comment removed for export] *)
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
      | _ => pose proof (sh8_bound47 x ltac:(lia))
      end
  | H : rw_cells _ _ (sh8 ?x) _ |- _ =>
      lazymatch goal with
      | _ : 2147450880 <= sh8 x /\ _ |- _ => fail
      | _ => pose proof (sh8_bound47 x ltac:(lia))
      end
  | H : ro_cells _ _ (sh8 ?x + _) _ |- _ =>
      lazymatch goal with
      | _ : 2147450880 <= sh8 x /\ _ |- _ => fail
      | _ => pose proof (sh8_bound47 x ltac:(lia))
      end
  end.

(* [comment removed for export] *)
Lemma shaddr_lt : ltac2:(zQ "80!q1!h9!q6!pb!j4!qc!jpa!r1>1x$1>1a$1>0@2$2@2$0Z^2@2$5^2@2$7+2+j0>0@2$0+igggnvvvogg1^2@2$0@2$4@1$3^4@1$6N1^3").
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
Definition pinb : ltac2:(zQ "40!h9!t1!ht6!hlf>1m$2>1q$0>1e$0>3inb>0$0@1$3@1$1#8P") := ltac2:(zQ "e0!h9!t1!q1!hlf!q6!it8!hv5!l7!ija!ht6!io7!ioe!qc!r1\1m$9\1q$0\1e$0\3inb>0$0@1$3@1$1#8@2$4@2$2Z^3@2$4@2$2^2@2$d+2+if>1x$0>0@2$2^4^1>0@2$c^2^4@3$7@1$6@1$3@1$1#8@3$a$8^7@1$b^3@2$5@1$3@1$1#8@1^4^3").
Definition pshb : ltac2:(zQ "20!h9!ht6>1m$1>1q$0>1e$0P") := ltac2:(zQ "h30!jq3!h9!q6!q1!l7!t1!qc!hlf!it8!hv5!hn6!ija!ht6!pb!io7!ioe!jod!j4!rd\1m$c\1q$1\1e$1>1x$1>0@2$3^3^1>0@2$6^2^3@2$2@3$4@1$9@1$7@1$5#8@3$e$b^6@1$f@1$d^3@2$8@1$7@1$5#8@1$h0@2$0^6^3@2$2@2$2@2$3Z@2$0^6^3@2$6@2$0^6^3+8@2$a@3$4$1@2$0^6^3Z@2$3@2$h1@2$h2^3+8+1@2$0^6^3").
Lemma pinb_of_bytes_at : ltac2:(zQ "h30!t1!hlf!h9!hv5!l7!q1!it8!jq9!jr3!ija!jrb!js2!ju1!j4!qc!jpa!r1!hnb!jue>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>2p0$2>2bs@1$8@1$1@1$0#8>1e$2>3inb>1x$2@1$1@1$0#8>0@4$b$9^5^4^3>0@3$4$2^3@2$d^5@1$f@2$7@1$1@1$0#8^4>0@2$5^4@2$h0+2+if>0>1x$2>0@2$5^8^1>0@2$e^2^7@3$4@1$3@1$1@1$0#8@3$c@1$1@1$0#8^9@1$h2@2$h1^3^a@2$6@1$1@1$0#8@1^7^3@4$a^9^8^6^5").
Proof.
  (intros m p0 bs e inb nd_i3 E HE HI; ndestruct nd_i3 as (B0 & B1 & BY)). split; [exact B0|]. split; [exact HE|]. intros x X1 X2.
  rewrite <- (HI x X1 X2). replace x with (p0 + Z.of_nat (Z.to_nat (x - p0))) at 1 by lia. apply BY. lia.
Qed.
Lemma pshb_of_accessible : ltac2:(zQ "50!h9!jv7!jkb!kg5!j4>1m$2>2p0$0>3len$0>0@3$1^3^2^1@3$3^4^3@2$4^3^2").
Proof.
  (intros m p0 len nd_i4 x Hx He; ndestruct nd_i4 as (A0 & AH & AC)). ndestruct (AC x ltac:(lia)) as (v & V0 & RD & OK).
  assert (E : shb m x = v) by (unfold shb; rewrite RD; apply b8_unsigned; lia).
  rewrite E. split; [| split; [exact V0| unfold byte_ok in OK; exact OK]].
  rewrite sh8_eq, shaddr_eq by lia. exact RD.
Qed.
Lemma ov_read1_of_mrd : ltac2:(zQ "b0!t1!hlf!hv5!it8!jr3!l7!ija!iu0!iu8!kk3!io7>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1b@1$1@1$0#8>0@3$5@1$2@1$1@1$0#8@3$a$6^3^2@2$3@1$1@1$0#8^1@3$5@1$2@1$4@1$1@1$0#8@4$9$6^4^3N1@2$3@1$4@1$1@1$0#8@3$7@1$1@1$0#8^2@1$8@1$1@1$0#8").
Proof. intros m a b RD. rewrite ov_rdn. cbn [rdn]. unfold mrd in RD. rewrite RD. reflexivity. Qed.
Lemma munch_mrd : ltac2:(zQ "h01!t1!hlf!hv5!ija!io7!ioe!jr3!q6!l7!h9!kp0!kp7!kq0!q1!qc!r1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$6$a>1m~0>2mc~0>1y$9>0@3$b^4^3^2>0@2$c^5^2>0@2$7@2$dZ^3@2$e^3@2$f+2+k0@3$8@1$2@1$1@1$0#8@3$4$3^5@1$5^4@3$4$3^6@1$5^4").
Proof. intros W m mc y MU OUT R. unfold mrd. rewrite (MU (wa y)); [reflexivity|]. rewrite wa_unsigned by lia. exact OUT. Qed.
Lemma pinb_rd : ltac2:(zQ "h30!t1!hlf!h9!jr3!hv5!it8!iu0!iu8!l7!kk3!ija!ht6!jrb!kp0!kp7!kq0!q1!qc!va>1m$b>2mc>0@1$1@1$0#k0@1$4@1$1@1$0#8>1W@1$3$d>1q$2>1e$2>3inb>0$2@1$1@1$0#8>1x$2>0@4$c^7^4^3^2>0@3$e^6^8^7>0@2$f^7^3>0@2$h0^7^4>0@2$h1^5^7@3$8@1$4@1$3@1$1@1$0#8@4$9$a^b@2$h2@1$0#k0^6N1@2$5@1$3@1$1@1$0#8@3$6@1$1@1$0#8@1^7^6@1$7@1$1@1$0#8").
Proof.
  (intros m mc W q e inb x nd_i5 MU OUT X1 X2; ndestruct nd_i5 as (Q0 & EH & P)). apply ov_read1_of_mrd. change (Z_to_bv 64 x) with (wa x).
  rewrite (munch_mrd W m mc x MU OUT ltac:(lia)). apply P; lia.
Qed.
Lemma pshb_rd : ltac2:(zQ "h70!t1!hlf!jr3!h9!q1!hv5!pb!it8!iu0!iu8!l7!kk3!ija!ht6!kg5!jq3!kp0!kp7!kq0!jod!qc!r1!va>1m$d>2mc>0@1$1@1$0#k0@1$5@1$1@1$0#8>1W@1$2$h0>1q$3>1e$3>1x$3>0@3$e^6^3^2>0@3$h1^5^7^6>0@2$h2^6@1$6^3>0@2$4^6^4>0@2$h4^5^6>0@2$4Z^8>0@2$4^8@2$h5+2+if@3$a@1$5@1$2@1$1@1$0#8@4$b$c^c@2$h6@1$0#k0@1$6^8N1@2$7@1$2@1$1@1$0#8@3$8@1$1@1$0#8@1$h3@2$f^d^8@1$9@1$1@1$0#8").
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
      (* [comment removed for export] *)
      end
  end).



(* [comment removed for export] *)
(* [comment removed for export] *)
  Lemma land223_range : ltac2:(zQ "50!ho8!q1!q6!h9!qc>1x$3>0@2$1Z^1@2$2@2$1Z@2$0^2+tf@2$4@2$0^2+tf+hg0").
  Proof. intros x Hx. rewrite Z.land_comm. apply (land_lt_pow2 223 x 8); lia. Qed.
  Lemma land255_range : ltac2:(zQ "50!ho8!q1!q6!h9!qc>1x$3>0@2$1Z^1@2$2@2$1Z@2$0^2+vf@2$4@2$0^2+vf+hg0").
  Proof. intros x Hx. rewrite Z.land_comm. apply (land_lt_pow2 255 x 8); lia. Qed.
  Ltac wrange w := try (let H := fresh "WR" in pose proof (bv_unsigned_in_range _ w) as H; unfold bv_modulus in H;
                        change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in H).
  Ltac zpos x := lazymatch x with bv_unsigned ?w => wrange w | _ => idtac end.
  Lemma land223_255 : ltac2:(zQ "30!ho8!h9!l7>1x$1@3$2$1@2$0^1+tf@2$0@2$0^1+vf+tf").
  Proof. intros x. rewrite <- Z.land_assoc. reflexivity. Qed.
  Lemma lor_m1_l : ltac2:(zQ "60!h9!q6!l7!q1!kqb!qc>1y$0>0@2$1@2$3Z^1@2$5^1+hggggggggggggggg0@3$2$0@2$4+vvvvvvvvvvvvvvvf^2+vvvvvvvvvvvvvvvf").
  Proof.
    intros y Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
    destruct (Z_lt_le_dec n 64) as [L|L].
    - replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia. reflexivity.
    - replace 18446744073709551615 with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
      assert (LG : Z.log2 y < 64).
      { destruct (Z.eq_dec y 0) as [->|NZ]. cbn; lia. apply (proj1 (Z.log2_lt_pow2 y 64 ltac:(lia))). lia. }
      rewrite (Z.bits_above_log2 y n); [reflexivity| lia| lia].
  Qed.
  Lemma lor_m1_r : ltac2:(zQ "60!h9!q6!l7!q1!kqb!qc>1x$0>0@2$1@2$3Z^1@2$5^1+hggggggggggggggg0@3$2$0@2$4^2+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
  Proof. intros x Hx. rewrite Z.lor_comm. apply lor_m1_l. exact Hx. Qed.
  Lemma lor_bound32 : ltac2:(zQ "51!q6!q1!qc!h9!kqb&@2$0@2$1Z^2@2$2^2+hggggggg0>1x$3>1y$3>0~0>0~0@2$0@2$1Z@2$4^4^3@2$2@2$4^4^3+hggggggg0").
  Proof. intros x y Hx Hy. apply (lor_lt_pow2 x y 32); assumption. Qed.
  Lemma shiftr_small0 : ltac2:(zQ "70!h9!q1!q6!l7!qc!r1!ja>1x$0>1n$0>0@2$1Z^1>0@2$2@2$1Z^3@2$4^3@2$5+2^2@3$3$0@2$6^4^3Z").
  Proof. intros x n Hn Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
  Lemma wrap32_small : ltac2:(zQ "70!h9!q6!l7!t1!q1!qc!hof>1x$0>0@2$1@2$4Z^1@2$5^1+hggggggg0@3$2$0@2$6@1$3#i0^2^2").
  Proof. intros x Hx. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
  Definition hxeq : ltac2:(zQ "10!h9>1a$0>1b$0P") := ltac2:(zQ "20!h9!l7\1a$0\1b$0@3$1$0^2^1").
  Ltac hx_name_b t :=
    let b := fresh "bx" in let E := fresh "EQ" in
    pose proof (eq_refl t : hxeq t t) as E; set (b := t) in |- *; change (hxeq t b) in E; clearbody b.
  Ltac hx_name_h t :=
    let b := fresh "hx" in let E := fresh "EQ" in
    pose proof (eq_refl t : hxeq t t) as E; set (b := t) in |- *; change (hxeq t b) in E; clearbody b.
  Ltac hx_reuse R :=
    match goal with
    | E : hxeq ?t ?v |- _ => lazymatch R with context [t] => unfold hxeq in E; rewrite !E; change (hxeq t v) in E end
    end.
  (* [comment removed for export] *)
  Ltac pose_branges x :=
    repeat (match x with context [bv_unsigned ?b] =>
              lazymatch type of b with byte =>
                lazymatch goal with
                | _ : 0 <= bv_unsigned b < 256 |- _ => fail
                | _ => pose proof (byte_range b)
                end
              end
            end).
  Ltac hex_norm1 R :=
    first
    [ hx_reuse R
    | match R with
      | context [bv_unsigned (v_sltiu ?a ?b)] =>
          let u := fresh "u" in let H := fresh "U" in
          pose proof (sltiu_range a b) as H; set (u := bv_unsigned (v_sltiu a b)) in *; clearbody u
      | context [bv_unsigned (v_sltu ?a ?b)] =>
          let u := fresh "u" in let H := fresh "U" in
          pose proof (sltu_range a b) as H; set (u := bv_unsigned (v_sltu a b)) in *; clearbody u
      | context [Z.land ?x 255] =>
          first [ rewrite (land255_small x) by lia
                | zpos x; let H := fresh "BX" in pose proof (land255_range x ltac:(lia)) as H;
                  hx_name_b (Z.land x 255);
                  lazymatch goal with E : hxeq (Z.land x 255) ?b |- _ => unfold hxeq in E; rewrite E in H; change (hxeq (Z.land x 255) b) in E end ]
      | context [Z.land ?x 223] =>
          first [ let H := fresh "HX" in pose proof (land223_range x ltac:(lia)) as H;
                  first [ assert (x < 256)%Z by lia | fail 1 ];
                  match goal with T : (x < 256)%Z |- _ => clear T end;
                  hx_name_h (Z.land x 223);
                  lazymatch goal with E : hxeq (Z.land x 223) ?b |- _ => unfold hxeq in E; rewrite E in H; change (hxeq (Z.land x 223) b) in E end
                | rewrite (land223_255 x) ]
      | context [Z.lor 18446744073709551615 ?y] => rewrite (lor_m1_l y) by lia
      | context [Z.lor ?x 18446744073709551615] => rewrite (lor_m1_r x) by lia
      | context [Z.lor ?x ?y] =>
          pose_branges x; pose_branges y;
          let H := fresh "OR" in pose proof (lor_bound32 x y ltac:(lia) ltac:(lia)) as H;
          let o := fresh "ox" in set (o := Z.lor x y) in *; clearbody o
      | context [bv_wrap 32 ?y] => rewrite (wrap32_small y) by lia
      | context [bv_swrap 32 ?y] => rewrite (swrap32_id y) by lia
      | context [Z.shiftr ?x ?n] =>
          lazymatch n with 3%Z => fail | _ => idtac end;    (* [comment removed for export] *)
          pose_branges x;
          first [ rewrite (shiftr_small0 x n) by lia
                | first [ assert (0 <= x < 1099511627776)%Z by lia | fail 1 ];
                  match goal with T : (0 <= x < 1099511627776)%Z |- _ => clear T end;
                  rewrite (Z.shiftr_div_pow2 x n) by lia;
                  let v := eval vm_compute in (2^n)%Z in change (2^n)%Z with v ]
      | context [Z.shiftl ?x ?n] =>
          pose_branges x;
          first [ assert (-1099511627776 <= x < 1099511627776)%Z by lia | fail 1 ];
          match goal with T : (-1099511627776 <= x < 1099511627776)%Z |- _ => clear T end;
          rewrite (Z.shiftl_mul_pow2 x n) by lia;
          let v := eval vm_compute in (2^n)%Z in change (2^n)%Z with v
      end ].
  Ltac hex_norm :=
    repeat lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => hex_norm1 R end.

  (* [comment removed for export] *)
  Ltac prune_or K tac ::=
    lazymatch type of K with
    | boxP _ => tac
    | _ => first [ exfalso; unfold hxeq in *; lia | tac ]
    end.
  Ltac pose_branges_regs := try (lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => pose_branges R end).
  Ltac step1_hex := first [ achk | st1b | arm_inputs; st1b ]; pose_branges_regs; norm_lits; fold_sh8; norm_shpa; norm_s32; hex_norm; gen_data.
  Ltac step1_std := first [ achk | st1b | arm_inputs; st1b ]; norm_lits; fold_sh8; norm_shpa; norm_s32; gen_data.
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition pecore : ltac2:(zQ "40!h9!t1!kue!hlf>1r$2>3sp'@1$3@1$1#k0>3s0v$0>2ff$0>1c$0P") := ltac2:(zQ "h40!t1!hlf!l7!q6!va!h9!kv4!kvb!lg2!lga!lh2!lh9!li0!li7!lie!lj5!ljc!lk3!kue!pb\1r$h2\3sp'@1$1@1$0#k0\3s0v$5\2ff$5\1c$5@2$3@3$2@1$1@1$0#k0@1$h1^5^4@2$3@3$2@1$1@1$0#k0@1$7^5^4@2$3@3$2@1$1@1$0#k0@1$6^5@2$4@1$0#k0^3@2$3@3$2@1$1@1$0#k0@1$a^5@2$4@1$0#k0@1$h3^2@2$3@3$2@1$1@1$0#k0@1$b^5@2$4@1$0#k0^2@2$3@3$2@1$1@1$0#k0@1$c^5@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$d^5@2$4@1$0#k0+nvvvogg0@2$3@3$2@1$1@1$0#k0@1$e^5@2$4@1$0#k0+n5@2$3@3$2@1$1@1$0#k0@1$f^5@2$4@1$0#k0+vvvvvvvvvvvvvnvf@2$3@3$2@1$1@1$0#k0@1$h0^5@2$4@1$0#k0+5@2$3@3$2@1$1@1$0#k0@1$8^5@2$4@1$0#k0+9@3$2@1$1@1$0#k0@1$9^5@2$4@1$0#k0+lc").
Ltac open_pecore PC := box_post; destruct PC as (?C1 & ?C2 & ?C3 & ?C4 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C10 & ?C11 & ?C12).

(* [comment removed for export] *)
Definition peframe : ltac2:(zQ "50!t1!hlf!jr3!h9!ht6>1m$4>3sp'@1$1@1$0#k0>3t0w@1$1@1$0#k0>3t8w@1$1@1$0#k0>3s16@1$1@1$0#k0>3s24@1$1@1$0#k0>3s32@1$1@1$0#k0>3s40@1$1@1$0#k0>3s48@1$1@1$0#k0>3s56@1$1@1$0#k0>2ff$3>3j16@1$2@1$1@1$0#8P") := ltac2:(zQ "e0!t1!it0!iu0!lka!hlf!va!jr3!iu8!h9!ija!ht6!ll0!ll6!hgf\1m$a\3sp'@1$4@1$0#k0\3t0w@1$4@1$0#k0\3t8w@1$4@1$0#k0\3s16@1$4@1$0#k0\3s24@1$4@1$0#k0\3s32@1$4@1$0#k0\3s40@1$4@1$0#k0\3s48@1$4@1$0#k0\3s56@1$4@1$0#k0\2ff$8\3j16@1$6@1$4@1$0#8@4$c$9^c@2$d@1$0#k0^b@3$2$1@1$3^a@3$2$1@1$3^9@3$2$1@1$3^8@3$2$1@1$3^7@3$2$1@1$3^6@3$2$1@1$3^5@3$2$1@1$3^4@3$2$1@1$3^3@3$2$1@1$3@2$5@1$0#k0Z@3$2$1@1$3@2$5@1$0#k0+vvvvvvvvvsqgikg0@3$2$1@1$3@2$5@1$0#k0+nvvvvvve@3$2$1@1$3@2$5@1$0#k0^2@3$2$1@2$bNh0^1@3$2$1@1$3@2$5@1$0#k0^2@1$7$1").
(* [comment removed for export] *)
Definition pespill : ltac2:(zQ "30!t1!hlf!h9>2pa@1$1@1$0#k0>2ta@1$1@1$0#k0>1e$2>3isk$2>3s16@1$1@1$0#k0>3s24@1$1@1$0#k0>3s32@1$1@1$0#k0>3s40@1$1@1$0#k0>3s48@1$1@1$0#k0>3s56@1$1@1$0#k0P") := ltac2:(zQ "90!t1!hlf!l7!q6!va!h9!j4!hgf!ho1\2pa@1$1@1$0#k0\2ta@1$1@1$0#k0\1e$5\3isk$5\3s16@1$1@1$0#k0\3s24@1$1@1$0#k0\3s32@1$1@1$0#k0\3s40@1$1@1$0#k0\3s48@1$1@1$0#k0\3s56@1$1@1$0#k0@2$3@3$2@1$1@1$0#k0^6@2$4@1$0#k0@2$8^7+d@2$3@3$2@1$1@1$0#k0^5^9@2$3@3$2@1$1@1$0#k0^4@2$4@1$0#k0@2$6@2$7@1$0#k0^a+qc@2$3@3$2@1$1@1$0#k0^3@2$4@1$0#k0^8@2$3@3$2@1$1@1$0#k0^2@2$4@1$0#k0@2$6@2$7@1$0#k0^a+q8@3$2@1$1@1$0#k0^1^a").
(* [comment removed for export] *)
Definition pesize : ltac2:(zQ "20!h9!ht6>1m$1>2ff$0>2sz$0P") := ltac2:(zQ "b0!h9!it0!iu0!iu8!t1!ija!ht6!lka!ll6!j4!va\1m$6\2ff$0\2sz$0@4$8$5^3@2$9^2+hi0@3$2$1@1$7@2$a@1$4#k0^1@1$3$1").
(* [comment removed for export] *)
Definition pecells : ltac2:(zQ "50!t1!hlf!jr3!h9!ht6>1m$4>2pa@1$1@1$0#k0>1e$3>2sc@1$2@1$1@1$0#8>3u1w@1$1@1$0#k0>3u2w@1$1@1$0#k0P") := ltac2:(zQ "h50!it0!t1!iu0!iu8!ija!j4!hlf!hgf!q6!pb!iuf!lm2!jj0!ll6!jod!jr3!h9!ht6!lka!ll0!va\1m$h1\2pa@1$6@1$1#k0\1e$h0\2sc@1$f@1$6@1$1#8\3u1w@1$6@1$1#k0\3u2w@1$6@1$1#k0@2$8@4$d$4^6@2$5@2$7@1$1#k0^5+q0@3$2$0@2$h3N8^3@3$2$0@1$b^2@3$2$0@1$b^1@1$3$0@2$8@4$d$4^6@2$5@2$7@1$1#k0^5+r8@3$2$0@1$h2@2$h4@1$1#k0^4@1$3$0@2$8@4$c$4^6@2$5@1$9@2$7@1$1#k0^5+h5@3$2$0@1$a@1$eZ@1$3$0@4$c$4^6@2$5@1$9@2$7@1$1#k0^5+h7@3$2$0@1$a@1$eZ@1$3$0").
Ltac open_pecells PM := box_post; destruct PM as (SCR & END & PS21 & PS23).
(* [comment removed for export] *)
Definition petot : ltac2:(zQ "40!t1!h9!ht6!hlf>1m$2>2ta@1$3@1$0#k0>3tot$1P") := ltac2:(zQ "h10!t1!it0!iu0!iu8!ija!hgf!q6!h9!ht6!pb!iuf!lka!jj0!ll6!jod!va!hlf\1m$8\2ta@1$h0@1$0#k0\3tot$7@2$6@4$d$4^3@2$5@1$0#k0^2@3$2$1@1$b@2$f@1$0#k0^1@1$3$1@4$c$4^3@1$9@2$5@1$0#k0^2@3$2$1@1$a@1$eZ@1$3$1").
Ltac open_petot PT := box_post; destruct PT as (TOT & TSH).
(* [comment removed for export] *)
Definition ptsh : ltac2:(zQ "20!h9!ht6>1m$1>2ff$0P") := ltac2:(zQ "f0!t1!h9!j4!hlf!it8!hv5!l7!ija!ht6!pb!io7!ioe!jod!q1!qc\1m$8\2ff$1>1x$1>0@2$d@2$2^2+i0^1>0@2$e^2@2$2^3+hi8@3$6@1$5@1$3@1$0#8@3$a$7^5@1$b@1$9^3@2$4@1$3@1$0#8@1$cZ").
(* [comment removed for export] *)
Definition pectx {HCEIL : HeapCeil} (sp' : word) (s0v : Z) (pa ta : word) (ff fsb lo e p0 : Z) : Prop :=
  aceil <= lo /\ lo <= bv_unsigned sp' /\ bv_unsigned sp' + 224 <= s0v /\ (bv_unsigned sp' = s0v - 224 \/ bv_unsigned sp' = s0v - 240) /\
  s0v <= bv_unsigned ta /\ bv_unsigned ta + 8 <= AAPP_HI /\ bv_unsigned ta mod 8 = 0 /\
  aapp (bv_unsigned pa) 280 /\ bv_unsigned pa mod 16 = 0 /\ fsb + AFS_HDR <= bv_unsigned pa /\ bv_unsigned pa + 280 <= fsb + AFS_SIZE /\
  aapp ff 512 /\ ff mod 32 = 0 /\ fsb + AFS_HDR <= ff /\ ff + 512 <= fsb + AFS_SIZE /\
  (bv_unsigned pa + 280 <= ff \/ ff + 512 <= bv_unsigned pa) /\
  AIMG_TOP <= fsb /\ fsb + AFS_SIZE <= aceil /\
  0 < p0 /\ p0 <= e /\ e <= aceil /\ (e + 16 <= fsb \/ fsb + AFS_SIZE + 16 <= p0) /\
  (fsb + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= fsb).
Ltac open_pectx PX := box_post; destruct PX as (CEIL & ROOM & S0A & S0B & TA1 & TA2 & TA8 & APP & PA16 & PAF1 & PAF2 & APF & FF32 & FFF1 & FFF2 & PAFF & FSB1 & FSB2 &
                                    P00 & P0E & EHI & INF & FSIDE); unfold ALOWSH_LO, AHI_LO, AFS_SIZE in FSIDE.

Lemma ptsh_rd : ltac2:(zQ "h70!t1!hlf!jr3!j4!q1!hv5!h9!pb!it8!iu0!iu8!l7!kk3!ija!ht6!lm8!ln3!kp0!kp7!kq0!jod!qc!va>1m$e>2mc>0@1$1@1$0#k0@1$5@1$1@1$0#8>1W@1$2$h1>2ff$6>1x$6>0@2$h0^5^2>0@3$h2^4^6^5>0@2$h3^5@1$7^3>0@2$4@2$3^5+i0^4>0@2$h5^5@2$3^6+hi8>0@2$4Z^7>0@2$4@2$3^8+hi8$f@3$b@1$5@1$2@1$1@1$0#8@4$c$d^b@2$h6@1$0#k0@1$7^8N1@2$8@1$2@1$1@1$0#8@3$9@1$1@1$0#8@1$h4Z@1$a@1$1@1$0#8").
Proof.
  intros m mc W ff x P MU OUT X1 X2 F0 FH. apply ov_read1_of_mrd. change (Z_to_bv 64 (sh8 x)) with (wa (sh8 x)).
  pose proof (sh8_bound x ltac:(unfold AAPP_HI in FH; lia)).
  rewrite (munch_mrd W m mc (sh8 x) MU OUT ltac:(lia)). apply P; lia.
Qed.
(* [comment removed for export] *)
Ltac outside_sh_tac x :=
  cbn [outside fst snd]; pose proof (sh8_bound47 x ltac:(unfold AAPP_HI in *; lia)); lia.
Ltac solve_load_anum ::=
  match goal with
  | |- context [ov_read_bytes ?segs ?mc ?a 1%nat] =>
      let E := addr_expr a in
      lazymatch goal with MU : munch ?W ?m0 mc |- _ =>
        lazymatch E with
        | sh8 ?x =>
            first
              [ lazymatch goal with TS : ptsh m0 ?ff |- _ =>
                  lazymatch x with context [ff] => idtac end;     (* [comment removed for export] *)
                  replace (ov_read_bytes segs mc a 1%nat) with (Some [b8 0])
                    by (symmetry; exact (ptsh_rd m0 mc W ff x TS MU ltac:(outside_sh_tac x) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)))
                end
              | lazymatch goal with SHB : pshb m0 ?q ?e |- _ =>
                  pose_shb_facts SHB x;
                  replace (ov_read_bytes segs mc a 1%nat) with (Some [b8 (shb m0 x)])
                    by (symmetry; pose proof (sh8_bound x ltac:(lia)); exact (pshb_rd m0 mc W q e x SHB MU ltac:(outside_sh_tac x) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))
                end ]
        | _ =>
            lazymatch goal with INB : pinb m0 ?q ?e ?inb |- _ =>
              replace (ov_read_bytes segs mc a 1%nat) with (Some [inb E])
                by (symmetry; exact (pinb_rd m0 mc W q e inb E INB MU ltac:(outside_tac) ltac:(lia) ltac:(lia)))
            end
        end
      end
  end; load_post.
Ltac solve_load ::= first [ solve_load_base | solve_load_anum | solve_load_image ].

Ltac seg_unfold ::=
  lazymatch goal with
  | |- pecore _ _ _ _ _ => unfold pecore
  | |- peframe _ _ _ _ _ _ _ _ _ _ _ _ => unfold peframe
  | |- pespill _ _ _ _ _ _ _ _ _ _ => unfold pespill
  | |- pesize _ _ _ => unfold pesize
  | |- pecells _ _ _ _ _ _ => unfold pecells
  | |- petot _ _ _ => unfold petot
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
Ltac useg_begin r ::=
  intro_rv r; subst; unfold peframe, pesize, petot in *; unfold seg_post, pecore, peframe, pesize, pecells, petot; hide_post;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  try (lazymatch goal with |- context [bv_unsigned ?pa + 160] =>
    lazymatch type of pa with word => pose proof (bv_unsigned_in_range _ pa) as RA0; unfold bv_modulus in RA0; cbn in RA0 end end);
  acb;
  try (lazymatch goal with APP : aapp _ 280 |- _ =>
         pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5); unfold AIMG_TOP in APB1; unfold AAPP_HI in APB3 end);
  try (lazymatch goal with APF : aapp _ 512 |- _ =>
         pose proof (aapp_bounds _ _ APF ltac:(lia)) as (AFB1 & AFB2 & AFB3 & AFB4 & AFB5); unfold AIMG_TOP in AFB1; unfold AAPP_HI in AFB3 end);
  try (unfold AFS_HDR, AFS_SIZE, AIMG_TOP, AAPP_HI in *|-);
  try (lazymatch goal with PA16 : bv_unsigned ?pa mod 16 = 0 |- _ => let k := fresh "kpa" in destruct (mod0_lin _ 16 ltac:(lia) PA16) as [k EPA]; clear PA16 end);
  try (lazymatch goal with TA8 : bv_unsigned ?ta mod 8 = 0 |- _ => let k := fresh "kta" in destruct (mod0_lin _ 8 ltac:(lia) TA8) as [k ETA]; clear TA8 end);
  try (lazymatch goal with FF32 : ?ff mod 32 = 0 |- _ => let k := fresh "kff" in destruct (mod0_lin _ 32 ltac:(lia) FF32) as [k EFF]; clear FF32 end);
  shad_bounds.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1095728 => chkjoin 13 1095732   (* [comment removed for export] *)
    | 1095764 => chkjoin 14 1095768   (* [comment removed for export] *)
    | 1095784 => chkjoin 16 1095788   (* [comment removed for export] *)
    | 1096112 => chkjoin 14 1096116   (* [comment removed for export] *)
    | 1096140 => chkjoin 16 1096144   (* [comment removed for export] *)
    | 1096192 => chkjoin 16 1096196   (* [comment removed for export] *)
    | 1096212 => chkjoin 17 1096216   (* [comment removed for export] *)
    | 1096472 => chkjoin 13 1096476   (* [comment removed for export] *)
    | 1096576 => chkjoin 17 1096580   (* [comment removed for export] *)
    | 1096676 => chkjoin 17 1096680   (* [comment removed for export] *)
    | 1096776 => chkjoin 17 1096780   (* [comment removed for export] *)
    | 1097196 => chkjoin 13 1097200   (* [comment removed for export] *)
    | 1097224 => chkjoin 14 1097228   (* [comment removed for export] *)
    | 1097252 => chkjoin 13 1097256   (* [comment removed for export] *)
    | 1097356 => chkjoin 11 1097360   (* [comment removed for export] *)
    | 1097404 => chkjoin 11 1097408   (* [comment removed for export] *)
    | 1097444 => chkjoin 12 1097448   (* [comment removed for export] *)
    | 1097560 => chkjoin 16 1097564   (* [comment removed for export] *)
    | 1097668 => chkjoin 16 1097672   (* [comment removed for export] *)
    | 1097776 => chkjoin 16 1097780   (* [comment removed for export] *)
    | 1097900 => chkjoin 13 1097904   (* [comment removed for export] *)
    | 1097928 => chkjoin 16 1097932   (* [comment removed for export] *)
    | 1097956 => chkjoin 13 1097960   (* [comment removed for export] *)
    | 1098376 => chkjoin 14 1098380   (* [comment removed for export] *)
    | 1098404 => chkjoin 15 1098408   (* [comment removed for export] *)
    | 1098432 => chkjoin 14 1098436   (* [comment removed for export] *)
    | 1098796 => chkjoin 14 1098800   (* [comment removed for export] *)
    | 1098828 => chkjoin 14 1098832   (* [comment removed for export] *)
    | 1098860 => chkjoin 14 1098864   (* [comment removed for export] *)
    | 1098952 => chkjoin 14 1098956   (* [comment removed for export] *)
    | 1098984 => chkjoin 6 1098988   (* [comment removed for export] *)
    | 1099012 => chkjoin 5 1099016   (* [comment removed for export] *)
    | 1099052 => chkjoin 14 1099056   (* [comment removed for export] *)
    | 1099080 => chkjoin 6 1099084   (* [comment removed for export] *)
    | 1099108 => chkjoin 6 1099112   (* [comment removed for export] *)
    | 1099144 => chkjoin 5 1099148   (* [comment removed for export] *)
    | 1099184 => chkjoin 14 1099188   (* [comment removed for export] *)
    | 1099236 => chkjoin 13 1099240   (* [comment removed for export] *)
    | 1099288 => chkjoin 14 1099292   (* [comment removed for export] *)
    | 1099328 => chkjoin 14 1099332   (* [comment removed for export] *)
    | 1099368 => chkjoin 14 1099372   (* [comment removed for export] *)
    | 1099408 => chkjoin 14 1099412   (* [comment removed for export] *)
    | 1099452 => chkjoin 14 1099456   (* [comment removed for export] *)
    | 1099492 => chkjoin 14 1099496   (* [comment removed for export] *)
    | 1099540 => chkjoin 14 1099544   (* [comment removed for export] *)
    | 1099740 => chkjoin 14 1099744   (* [comment removed for export] *)
    | 1099788 => chkjoin 14 1099792   (* [comment removed for export] *)
    | 1099816 => chkjoin 15 1099820   (* [comment removed for export] *)
    | 1099844 => chkjoin 14 1099848   (* [comment removed for export] *)
    | 1099916 => chkjoin 15 1099920   (* [comment removed for export] *)
    | 1099944 => chkjoin 16 1099948   (* [comment removed for export] *)
    | 1099972 => chkjoin 15 1099976   (* [comment removed for export] *)
    | 1100056 => chkjoin 14 1100060   (* [comment removed for export] *)
    | 1100088 => chkjoin 14 1100092   (* [comment removed for export] *)
    | 1100236 => chkjoin 6 1100240   (* [comment removed for export] *)
    | 1100260 => chkjoin 17 1100264   (* [comment removed for export] *)
    | 1100288 => chkjoin 12 1100292   (* [comment removed for export] *)
    | 1100312 => chkjoin 6 1100316   (* [comment removed for export] *)
    | 1100336 => chkjoin 5 1100340   (* [comment removed for export] *)
    | 1100368 => chkjoin 16 1100372   (* [comment removed for export] *)
    | 1100400 => chkjoin 12 1100404   (* [comment removed for export] *)
    | 1100584 => chkjoin 12 1100588   (* [comment removed for export] *)
    | 1100612 => chkjoin 13 1100616   (* [comment removed for export] *)
    | 1100640 => chkjoin 12 1100644   (* [comment removed for export] *)
    | 1100704 => chkjoin 14 1100708   (* [comment removed for export] *)
    | 1100732 => chkjoin 15 1100736   (* [comment removed for export] *)
    | 1100760 => chkjoin 14 1100764   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
