(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac TacX Bytes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3andhc2eq46Stdlib6ZArith6BinInt1Zjb4landjb2lejb2lt04Nposjb3pow35stdpp9bitvectorbdefinitionsn07Z_to_bvn09bv_signedjb3oppn08bv_swrap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~r44zx32n02bvr44sx32r43le437Corelib4Init9Datatypeshg74listjb4lxorjb3sub" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land63_small : ltac2:(zQ "60!h9!j0!j6!l3!la!lf>1k$0>0@2$1@2$4Z^1@2$5^1+k0@3$2$0@2$3^2+jf^2").
Proof. intros k Hk. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma signed_small : ltac2:(zQ "90!m4!h9!j0!j6!la!lf!ma!od!p7>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+jf@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Lemma swrap32_small : ltac2:(zQ "90!h9!ma!j0!j6!m4!la!lf!q3!q9>1x$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
Proof. intros x Hx. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 / 2) with (2^31). lia. Qed.
Lemma zx32_small : ltac2:(zQ "a0!m4!od!j0!j6!h9!ue!la!lf!ma!v5>1x$4>0@2$2@2$6Z^1@2$7^1@2$8+2+i0@3$3@1$9@1$0#k0@1$5@2$1@1$0#k0^2@2$1@1$0#k0^2").
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_small : ltac2:(zQ "a0!m4!od!j0!j6!h9!va!la!lf!ma!v5>1x$4>0@2$2@2$6Z^1@2$7^1@2$8+2+hf@3$3@1$9@1$0#k0@1$5@2$1@1$0#k0^2@2$1@1$0#k0^2").
Proof. intros x Hx. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma le4_sx32 : ltac2:(zQ "c0!m4!hg1!od!hhf!j0!j6!h9!va!la!lf!ma!v5>1z$6>0@2$4@2$8Z^1@2$9^1@2$a+2+i0@3$5@1$3@1$b@1$0#8@1$1@1$7@2$2@1$0#k0^2@1$1@2$2@1$0#k0^2").
Proof.
  intros z Hz. unfold le4, sx32. rewrite !Z_to_bv_unsigned.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_wrap 64 (bv_swrap 32 (bv_wrap 64 z))) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_wrap 64 z) 32) by (cbn; lia). f_equal.
  unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  rewrite (Z.mod_small z 18446744073709551616) by lia.
  destruct (Z.ltb_spec z 2147483648) as [L|L].
  - rewrite (Z.mod_small (z + 2147483648) 4294967296) by lia. replace (z + 2147483648 - 2147483648) with z by lia.
    rewrite (Z.mod_small z 18446744073709551616) by lia. reflexivity.
  - replace ((z + 2147483648) mod 4294967296) with (z + 2147483648 - 4294967296) by (apply Z.mod_unique with (q := 1); lia).
    replace ((z + 2147483648 - 4294967296 - 2147483648) mod 18446744073709551616) with (z - 4294967296 + 18446744073709551616) by (apply Z.mod_unique with (q := -1); lia).
    replace (z - 4294967296 + 18446744073709551616) with (z + 4294967295 * 4294967296) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma not64 : ltac2:(zQ "80!h9!j0!j6!la!lf!hi7!ma!hie>1w$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+vvvvvvvvvvvvvvvf@2$7+vvvvvvvvvvvvvvvf^2").
Proof.
  intros w Hw. rewrite lnot_mod64 by lia. unfold Z.lnot, Z.pred. symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.
(* [comment removed for export] *)
