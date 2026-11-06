(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq01Z46Stdlib6ZArith6BinInt1Zld3addld2leld3mulhf7Z_to_bvhfbbv_unsigned37Corelib4Init9Datatypespe4listpe6length37Corelib5Lists7ListDefs63map3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseu3dZ_to_le_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Bytes~~~~~~hi26le_valpe3natu3h0le_bytes_to_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ho23le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~hs35blockpe4conshs3cas_lb_removehs34bptrk13noths36blk_idpe4prodpe4pairhs38as_RHEAPhs35as_Sths33mem36Stdlib5Lists4Listim22Inhs33asrhs3casan_rt_hyps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_bv8_low : ltac2:(zQ "90!h9!jc!l5!la!n5!nb!o0!o6!p0>1b@1$1@1$0#8>1r$3>0@2$5Z^1@3$2@1$1@1$0#8@2$7@1$0#8@2$4@2$8@1$0#8^3@2$6+hg0^2^3").
Proof.
  intros b r Hr. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  Z.div_mod_to_equations. nia.
Qed.

Lemma Z_to_le_bytes_le_val : ltac2:(zQ "a0!h9!jc!r6!rd!l5!td!la!hh2!hle!p0>2bs@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@2$7@2$3@1$1@1$0#8^1@1$8@4$5@1$1@1$0#8$6@1$9@1$0#8^1^1").
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length map le_val Z_to_le_bytes].
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R.
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  f_equal; [apply Z_to_bv8_low; lia|].
  rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace ((bv_unsigned b + 256 * le_val (map bv_unsigned bs)) / 256) with (le_val (map bv_unsigned bs)) by (Z.div_mod_to_equations; nia).
  exact IH.
Qed.

Lemma le8_le_bytes_to_word : ltac2:(zQ "80!h9!jc!r6!l5!rd!hm8!hme!hrc>2bs@1$2@1$1@1$0#8>0@3$3$5@2$4@1$1@1$0#8^1N8@3$3@1$2@1$1@1$0#8@1$7@1$6^2^2").
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R. rewrite length_map, L in R. change (256 ^ Z.of_nat 8) with (2^64) in R.
  rewrite (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). rewrite <- L. apply Z_to_le_bytes_le_val.
Qed.

Section HH.
  Variable H : ltac2:(zQ "10!inb$0").
  Hypothesis HH : ltac2:(zQ "10!io2@2$0?5HCEIL?1H").

  Lemma ah_lb_remove_cons_ne : ltac2:(zQ "80!ig0!ig9!r6!l5!ih0!ii0!ii8!iie>1p$5>1b$0>2LB@1$2$0>0@1$6@3$3$5@1$7^2^3@3$3@1$2$0@3$4?1H^4@3$1$0^3^2@3$1$0^3@3$4?1H^4^2").
  Proof. intros. apply (proj1 (proj2 (ah_lb_remove H HH))). assumption. Qed.

  (* [comment removed for export] *)
  Lemma ah_lb_remove_fresh : ltac2:(zQ "f1!la!ii0!ij8!ijf!ig9!r6!ih0!ig0!l5!td!ik6!il2!iie!ilb!in5&@4$3@2$2$1$0$0@4$3$1$0^6^5^4>1s@1$b?1H>2LB@1$5@2$2@2$2$1$0$0>1m$d>2p'$1>2A'$0>2n'$0>1p$1>0@4$a?1H^7@3$4@2$2@2$2$1$0$0@4$3@2$2$1$0$0@4$3$1$0^4^3^2^6^5>0@3$e$1^2@4$9$7$1$c^7@3$8@1$5$7@3$6?1H^3@3$4@2$2@2$2$1$0$0~0^8@3$4@2$2@2$2$1$0$0~0@3$6?1H^3^8").
  Proof.
    intros s LB m p' A' n' p HP Hin. apply ah_lb_remove_cons_ne. cbn.
    pose proof (ah_nodup H HH _ _ _ HP) as ND. cbn in ND. inversion ND; subst. congruence.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End HH.

End HCW.

(* [comment removed for export] *)
