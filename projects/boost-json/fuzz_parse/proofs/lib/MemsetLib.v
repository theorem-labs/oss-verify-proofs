(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MemSplit MmapSim RefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4boolhc4prodhc3fsthc4andbhc3snd46Stdlib6ZArith6BinInt1Zl53addl53lebl53ltbhc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9MemsetLib4FPX1~~~~~~o66ms_inb36Stdlib5Lists4Listt07existsbhc4pairhc4true37Corelib4Init5Logicvb3andvb2eqvb3iffl52lel52lto66ms_covhc4conshc3orbt02Invb2exo68ms_chaint04incl04Npos35stdpp9bitvectorbdefinitionshm22bvhc6optionhm2bbv_unsignedhc4Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9MemsetLib~~~~~~hq46ms_covl53subhc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9MemsetLib5CFill~~~~~~hv65cfill69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~ik19mem_growsl56of_nathc3nat37Corelib5Lists7ListDefip76repeat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ir86wbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~ivc3at_l56to_nathq48ms_chain3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjl08store_ok3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejp37Segmenthm27Z_to_bvl56modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9MemsetLib4FPX2~~~~~~ju73cbzl53mull53powju75cbyteju77ms_repl3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasekkfdZ_to_le_bytesju73c32ju74c32hju73c64jl0h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~kra6v_sllikra7v_mulhukra6v_srlil53lorkra4v_orkra6v_andikra6v_subwl53oppl54landvb2orkra5v_addkra5v_subkra6v_addi3h5LinuxProcessSemantics5Riscv5Instrlm45instrhc5falsejl0dmachine_statekra4getrkra4mkstvb1Ijl09MachineOkjl0afetch_wordjl08is_ecalljl0emachine_resultjl04step3h5LinuxProcessSemantics5Riscv7DecodeClvfadecode_anylm47M_MULHUlm43Mul3h5LinuxProcessSemantics5Riscv7Preludemk56bv_eqbmk55bvmapkra6regupdhm22BVhm24BvWflm46ALU_ORlm42Ophq45cbytehq45cfilllm43SZ1lm45Storehm29bv_signedlm43SZ4lm43SZ8ivcaregs_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9MemsetLib4FPX3~~~~~~mv17ms_clobmv18ms_agree" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition ms_inb : ltac2:(zQ "30!h9!j4!jb>1i$0>2iv@2$2$0$0$1") := ltac2:(zQ "80!h9!k2!k8!jb!kf!md!n3!n9\1i$0\2iv@2$3$0$0@2$2@2$6@3$1$0$0^1^2@2$7^2@2$5@3$1$0$0^1@3$4$0$0^1").
Definition ms_cov : ltac2:(zQ "40!h9!j4!nf!jb>1L@1$2@2$3$0$0>1i$0$1") := ltac2:(zQ "50!h9!jb!nf!s7!u3\1L@1$2@2$1$0$0\1i$0@3$4@2$1$0$0@1$3^1^2").

Lemma ms_inb_true : ltac2:(zQ "b0!h9!j4!ud!v4!hgf!hh5!hha!s7!md!hi0!hi5>1i$0>1o$0>1m$0@2$6@3$5$1@2$7^3@4$2$0$0^2^1$3@2$4@2$9^2^3@2$a^3@2$8^2^1").
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : ltac2:(zQ "90!h9!jb!hia!j4!hj3!nf!hja!hh5!s7>2iv@2$1$0$0>1L@1$5@2$1$0$0>1i$0@3$7$3@2$2@3$4@2$1$0$0^3^2^1@2$6@2$8^1^3@2$2^2^1").
Proof. reflexivity. Qed.

Lemma ms_cov_In : ltac2:(zQ "d0!h9!jb!j4!nf!ud!v4!hgf!hh5!hia!hk0!md!hi0!hi5>1L@1$3@2$1$0$0>1i$0>1o$0>1m$0>0@3$9@2$1$0$0@4$4$0$0^2^1^4>0@2$6@2$b^3^4@2$c^4@2$a^3^2@3$7$2@2$8^6^5$5").
Proof.
  intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
  apply ms_inb_true. exact Hi.
Qed.

(* [comment removed for export] *)
Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
  match L with
  | [] => to <= from
  | (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
  end.

Lemma ms_chain_cov : ltac2:(zQ "b0!h9!hgf!jb!hk5!hi0!hi5!nf!ud!hka!hk0!md>1L@1$6@2$2$0$0>4from$0>2to$0>1i$0>0@3$8^3^2^4>0@2$1@2$4^4^2@2$5^2^3@2$3$0\1o$0@2$3$0\1m$0@2$1@3$9@2$2$0$0@4$7$0$0^2^1^8@2$1@2$4^2^5@2$5^5@2$a^2^1").
Proof.
  induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
  - lia.
  - destruct Hc as [Ho Hc].
    destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
    + exists o, m. split; [left; reflexivity | lia].
    + ndestruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
      exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.

(* [comment removed for export] *)
Lemma ms_cov_by_chain : ltac2:(zQ "c0!h9!jb!nf!j4!v4!hgf!hh5!hka!hia!hl5!hi0!hi5>1L@1$2@2$1$0$0>2L'@1$2@2$1$0$0>1n$0>0@3$9@2$1$0$0^2^3>0@3$7Z^2^3>1i$0>0@2$5@2$aZ^1@2$b^1^4@3$6$3@2$8^7^2$4").
Proof.
  intros L L' n Hincl Hc i Hi.
  ndestruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CFill.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable mem0 : ltac2:(zQ "30!hlc!hnf!ho5>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable d : word.
  Variable n : Z.
  Variable c : ltac2:(zQ "20!hlc!hnf@1$1@1$0#8").
  Hypothesis Hn : ltac2:(zQ "10!hi0@2$0Z?1n").
  Hypothesis Hnw : ltac2:(zQ "50!hlc!md!hi5!kj5!hoe@2$2@2$1@2$4@1$0#k0?1d?1n@2$3+2+k0").

  Definition cfill : ltac2:(zQ "60!hlc!h9!hnf!nf!ho5!jb>1L@1$3@2$5$1$1>0@1$2@1$0#k0@1$4@1$2@1$0#8") := ltac2:(zQ "f0!hlc!hoe!hnf!k8!j4!h9!hpd!nf!ho5!jb!hu0!md!n3!n9!hua\1L@1$7@2$9$5$5\1x@1$2@1$0#k0M4\0$4@1$8@1$2@1$0#8@2$3@2$3@2$c@2$1@1$0#k0?1d@2$1@1$0#k0^1@2$d@2$1@1$0#k0^1@2$b@2$1@1$0#k0?1d?1n@2$a^2@2$e@2$1@1$0#k0^1@2$1@1$0#k0?1d@2$6@1$2@1$0#8?1c@1?4mem0^1").

  Lemma cfill_nil : ltac2:(zQ "80!hlc!h9!hnf!hv0!ho5!jb!hh5!ij8@3$6>0@1$2@1$0#k0@1$4@1$2@1$0#8@1$7@1$3@2$5$1$1?4mem0").
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  Lemma cfill_grows : ltac2:(zQ "50!h9!nf!jb!ij8!inb>1L@1$1@2$2$0$0@2$4?4mem0@1$3^1").
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_ext : ltac2:(zQ "d0!h9!nf!jb!hh5!hlc!ij8!hu0!hnf!j4!ho5!hgf!hi0!hi5>2L1@1$1@2$2$0$0>2L2@1$1@2$2$0$0>0>1i$0>0@2$a@2$bZ^1@2$c^1?1n@3$3$8@2$6^4^2@2$6^3^2@3$3>0@1$7@1$4#k0@1$9@1$7@1$4#8@1$5^3@1$5^2").
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_store : ltac2:(zQ "h10!h9!hlc!hnf!jb!ij8!hi0!io8!hj3!nf!ip1!ho5!ud!hh5!iqe!iv2!jj4!md>1L@1$8@2$3$0$0>1o$0>1m$9>0@2$5Z^2>0@2$5@2$h0^3@1$6^2?1n@3$c>0@1$2@1$1#k0@1$a@1$2@1$1#8@3$e@1$4^5@2$f?1d^4@3$d@1$2@1$1#8?1c^3@1$4@3$7@2$3$0$0@4$b$0$0^4@1$6^3^5").
  Proof.
    intros L o m Ho Hm. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
    - rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
      rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
        by (symmetry; apply ms_inb_true; lia).
      destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
      reflexivity.
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_full : ltac2:(zQ "h10!hlc!h9!hnf!hh5!j4!nf!ho5!jb!v4!hgf!iqe!iv2!ij8!hu0!hi0!hi5!jjb>1L@1$5@2$7$1$1>0>1i$1>0@2$9@2$eZ^1@2$f^1?1n@3$3$4@2$d^3^2$8@3$3>0@1$2@1$0#k0@1$6@1$2@1$0#8@1$c^2@3$b?4mem0?1d@3$a@1$2@1$0#8?1c@1$h0?1n").
  Proof.
    intros L Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
      + rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
        rewrite nth_repeat_lt by lia. reflexivity.
      + rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
    - cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
  Qed.

  Lemma cfill_full_chain : ltac2:(zQ "d0!h9!jb!hlc!hnf!nf!ho5!hh5!iqe!iv2!ij8!jk4!hl5!jjb>1L@1$4@2$1$0$0>2L'@1$4@2$1$0$0>0@3$b@2$1$0$0^1^2>0@3$aZ?1n^2@3$6>0@1$3@1$2#k0@1$5@1$3@1$2#8@1$9^4@3$8?4mem0?1d@3$7@1$3@1$2#8?1c@1$c?1n").
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  (* [comment removed for export] *)
  Lemma cfill_store_ok : ltac2:(zQ "f0!h9!j4!nf!v4!hh5!jo7!hi0!ip1!jb!js8!jj4!ij8!md!io8!jjb>4segs@1$2$9>1L@1$2@2$8$0$0>1o$0>1m$7>0@3$4$1@4$5^4?4mem0?1d@1$e?1n$3>0@2$6Z^3>0@2$6@2$c^4@1$d^3?1n@3$4$1@4$5^7@1$b^6@2$a?1d^5^4$3").
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
Definition cbyte : ltac2:(zQ "20!hlc!hnf>2cv@1$1@1$0#k0@1$1@1$0#8") := ltac2:(zQ "40!hlc!jt3!hnf!hoe\2cv@1$2@1$0#k0@2$1@1$0#8@2$3@1$0#k0^1").
(* [comment removed for export] *)
Definition cbz : ltac2:(zQ "30!hlc!h9!hnf>2cv@1$2@1$0#k0$1") := ltac2:(zQ "40!hlc!jte!hnf!hoe\2cv@1$2@1$0#k0@2$1@2$3@1$0#k0^1+hg0").
(* [comment removed for export] *)
Definition c32 : ltac2:(zQ "20!hlc!hnf>2cv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!hlc!ki8!kif!jt3!hnf\2cv@1$4@1$0#k0@2$3@1$0#k0@2$2@1$1^1+hghghg1").
(* [comment removed for export] *)
Definition c32h : ltac2:(zQ "20!hlc!hnf>2cv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!hlc!kif!ki8!kj5!jt3!hnf\2cv@1$5@1$0#k0@2$4@1$0#k0@2$1@2$1@1$2^1+hghghg1@2$3+2+i0").
(* [comment removed for export] *)
Definition c64 : ltac2:(zQ "20!hlc!hnf>2cv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!hlc!ki8!kif!jt3!hnf\2cv@1$4@1$0#k0@2$3@1$0#k0@2$2@1$1^1+hghghghghghghg1").

Lemma cbz_range : ltac2:(zQ "60!ki8!hgf!hlc!hi0!hi5!hnf>2cv@1$5@1$2#k0@2$1@2$3Z@1$0^1@2$4@1$0^1+hg0").
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : ltac2:(zQ "70!hlc!hnf!hh5!kjb!jte!jt3!hoe>2cv@1$1@1$0#k0@3$2@1$1@1$0#8@2$5@1$0#8@2$4@2$6@1$0#k0^1+hg0@1$3^1").
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : ltac2:(zQ "60!hlc!hnf!hh5!kjb!ki8!jt3>2cv@1$1@1$0#k0@3$2@1$1@1$0#8@1$3^1@2$5@1$0#8@1$4^1").
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : ltac2:(zQ "30!ip1!kk4!hi0>1k$0@2$2Z@1$1^1").
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : ltac2:(zQ "e0!hlc!hnf!nf!ip1!hgf!hh5!iqe!h9!kne!kk4!hi0!hi5!kif!jt3>1k$3>1z$7>0@2$4@2$aZ^1@2$b^1+hg0@3$5@1$2@1$1@1$0#8@2$8^3@2$c^2@1$9^3@3$6@1$1@1$0#8@2$d@1$0#8^2^3").
Proof.
  induction k as [|k IH]; intros z Hz; [reflexivity|].
  cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.

Lemma u_c32 : ltac2:(zQ "80!hlc!hh5!h9!kof!ki8!kif!hnf!hoe>2cv@1$6@1$0#k0@3$1$2@2$7@1$0#k0@1$3^1@2$5@1$4^1+hghghg1").
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : ltac2:(zQ "90!hlc!kif!hh5!h9!kp6!ki8!kj5!hnf!hoe>2cv@1$7@1$0#k0@3$2$3@2$8@1$0#k0@1$4^1@2$1@2$1@1$5^1+hghghg1@2$6+2+i0").
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : ltac2:(zQ "80!hlc!hh5!h9!kpe!ki8!kif!hnf!hoe>2cv@1$6@1$0#k0@3$1$2@2$7@1$0#k0@1$3^1@2$5@1$4^1+hghghghghghghg1").
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : ltac2:(zQ "80!hlc!hnf!nf!hh5!iqe!kq5!kof!kjb>2cv@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$5N4@1$6^1@3$4@1$1@1$0#8@1$7^1N4").
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : ltac2:(zQ "80!hlc!hnf!nf!hh5!iqe!kq5!kpe!kjb>2cv@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$5N8@1$6^1@3$4@1$1@1$0#8@1$7^1N8").
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

(* [comment removed for export] *)
Lemma u_slli56 : ltac2:(zQ "90!hlc!hh5!h9!ki8!kv5!kif!kj5!hnf!hoe>2cv@1$7@1$0#k0@3$1$2@2$8@1$0#k0@2$4^1+j8@2$5@1$3^1@2$6+2+j8").
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_c32 : ltac2:(zQ "80!hlc!hnf!hh5!h9!kof!kvf!kv5!hoe>2cv@1$1@1$0#k0>1m@1$1@1$0#k0>0@3$2$3@2$7@1$0#k0^1+hghghghg0@3$2@1$1@1$0#k0@2$5@2$6^3+j8^2@1$4^3").
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : ltac2:(zQ "60!hlc!hnf!hh5!kof!kp6!kv5>2cv@1$1@1$0#k0@3$2@1$1@1$0#k0@2$5@1$3^1+i0@1$4^1").
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : ltac2:(zQ "60!hlc!hnf!hh5!kof!kp6!lga>2cv@1$1@1$0#k0@3$2@1$1@1$0#k0@2$5@1$4^1+i0@1$3^1").
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : ltac2:(zQ "90!h9!kj5!hi0!kif!hgf!hh5!md!lh4!hi5>1a$0>1b$0>0@2$2Z^2>0@2$4@2$2Z^2@2$8^2@2$1+2+i0@3$5$0@2$7@2$3^4@2$1+2+i0^3@2$6@2$3^4@2$1+2+i0^3").
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : ltac2:(zQ "70!hlc!hnf!hh5!kof!kp6!kpe!lha>2cv@1$1@1$0#k0@3$2@1$1@1$0#k0@2$6@1$4^1@1$3^1@1$5^1").
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2' : ltac2:(zQ "50!h9!jte!hh5!hi0!kj5>1t$0>1k$0>0@2$3+2^1@3$2$0@2$1@2$1^3@2$4+2^2+4@2$1^3+4").
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : ltac2:(zQ "90!hlc!jt3!hnf!hh5!li2!lic!jte!lj6!hoe>1x@1$2@1$0#k0@3$3@1$2@1$0#k0@2$4@2$5@2$1@1$0#k0Z^1+3@2$1@1$0#k0@2$6@1$7@2$8@1$0#k0^1+4").
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
  rewrite Z.mod_add by lia.
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma neg_mod4_range : ltac2:(zQ "50!hi0!jte!lj6!hgf!h9>1u$4@2$3@2$0Z@2$1@1$2^1+4@2$0@2$1@1$2^1+4+3").
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.

(* [comment removed for export] *)
Lemma land_trunc4 : ltac2:(zQ "90!h9!kj5!hua!hgf!hh5!ljc!hi0!hi5!jte>1a$0>0@2$3@2$6Z^1@2$7^1@2$1+2+k0@3$4$0@2$5^2@2$2@2$1+2+k0+4@2$2^2@2$8^2+4").
Proof.
  intros a Ha.
  replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.

Lemma andi_m4 : ltac2:(zQ "c0!hlc!jt3!hgf!hh5!h9!li2!hi0!hi5!jte!kj5!hua!hnf>1m$4>0@2$2@2$6Z^1@2$7^1@2$9+2+k0@3$3@1$b@1$0#k0@2$5@2$1@1$0#k0^2-4@2$1@1$0#k0@2$a^2@2$8^2+4").
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : ltac2:(zQ "50!h9!hh5!ljc!lk3!hi0>1a$0>0@2$4Z^1@2$3@3$1$0@2$2^2+4Z@3$1$0@2$2^2+4+4").
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : ltac2:(zQ "90!h9!hh5!hlc!hnf!hgf!hk5!lk3!li2!jt3>1x@1$3@1$2#k0@2$5$0\2s4$0@2$4@3$1@1$3@1$2#k0@2$7^2+4@2$8@1$2#k0^1@2$6@3$1$0^1Z@3$1$0^1+4").
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma ms_v_add_Z : ltac2:(zQ "b0!hlc!hnf!hgf!hh5!h9!jj4!lk8!hi0!hi5!kj5!jt3>1x@1$1@1$0#k0>1z$4>0@2$2@2$7Z^1@2$8^1@2$9+2+k0@3$3@1$1@1$0#k0@2$6^3@2$a@1$0#k0^2@2$5^3^2").
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : ltac2:(zQ "c0!hlc!h9!jj4!hnf!hgf!hh5!lk8!md!hi0!hi5!kj5!jt3>1x@1$3@1$0#k0>1o$1>1z$1>0@2$4@2$8Z^1@2$9^1@2$a+2+k0@3$5@1$3@1$0#k0@2$6@2$2^4^3@2$b@1$0#k0^2@2$2^4@2$7^3^2").
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : ltac2:(zQ "b0!hlc!jt3!h9!hi0!hgf!hh5!ll1!hi5!kj5!hua!hnf>1a$2>1b$2>0@2$4@2$3Z^1@2$3^1^2>0@2$7^3@2$8+2+k0@3$5@1$a@1$0#k0@2$6@2$1@1$0#k0^4@2$1@1$0#k0^3@2$1@1$0#k0@2$9^4^3").
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : ltac2:(zQ "b0!hlc!h9!jt3!hgf!hh5!lla!md!hi0!hi5!kj5!hnf>1a$1>1i$1>0@2$3@2$7Z^2@2$8^2@2$9+2+k0@3$4@1$a@1$0#k0@2$5@2$2@1$0#k0^3^2@2$2@1$0#k0@2$6^3^2").
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_step_mulhu_at : ltac2:(zQ "i01!hlc!hnf!hh5!ho5!h9!lo8!hpd!j4!lp1!jb!lp9!lqa!lr2!nf!ud!lra!js8!lre!lsb!lt9!lu5!lv7!mi5!mj3!mje!mmb!mn5!mne!lla!kvf!mo8!moe&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : ltac2:(zQ "i01!hlc!hnf!hh5!ho5!h9!lo8!hpd!j4!lp1!jb!lp9!lqa!lr2!nf!ud!lra!js8!lre!lsb!lt9!lu5!lv7!mi5!mp6!mq0!mmb!mn5!mne!lla!lha!mo8!moe&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!nf!js8@1$0$1").
  Variable mem0 : ltac2:(zQ "30!hlc!hnf!ho5>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : ltac2:(zQ "50!hlc!md!hi5!kj5!hoe@2$2@2$1@2$4@1$0#k0?1d?1n@2$3+2+k0").
  Hypothesis Hok : ltac2:(zQ "50!j4!v4!hh5!jo7!jjb@3$2$0@4$3?4segs?4mem0?1d@1$4?1n$1").

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  Lemma cf_sb : ltac2:(zQ "i00!hlc!h9!hnf!hh5!jb!ho5!lo8!hpd!ud!lp9!mq6!mqf!lqa!lr2!md!hi0!j4!hj3!lp1!nf!lre!lsb!lt9!lu5!lv7!mi5!mr8!mrf!mn5!jj4!lla!ms8>4regs@2$hc@1$0#5@1$2@1$0#k0>2pc@1$2@1$0#k0>3rom>0@1$2@1$0#k0@1$5@1$2@1$0#8>1w@1$2@1$0#i0>3rs1@1$2@1$0#5>3rs2@1$2@1$0#5>3imm@1$2@1$0#c>1L@1$h3@2$4$1$1>2o0$1>1o$1>0@3$3@1$5@1$2@1$0#i0@2$h5?4segs^9@2$7@1$2@1$0#i0^7>0@3$3$h0@1$h6^8$h2>0@3$3@1$5@2$4$6$1@1$h9^9@2$7@2$4$6$1@4$8$6$1@4$hb$ha^8^7^6+4>0@3$3@1$2@1$0#k0@2$c^d^9@2$hd?1d^5>0@3$3$1@2$e^6@2$hf@1$0#c^8^5>0@3$3@1$2@1$0#k0@2$c^f^a?2cv>0@2$fZ^7>0@2$f@2$e^8+1?1n@3$3@1$h7$9@2$h8?4segs@5$d?2fx^h2^h1@5$b?4mem0?1d?1n@1$a?2cv^b^h0@2$h4$9@5$d?2fx^h2@2$he^h1+4@5$b?4mem0?1d?1n@1$a?2cv@3$h1@2$4$1$1@4$8$1$1^9+1^b^h0").
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sw : ltac2:(zQ "i20!hlc!hnf!h9!hh5!jb!ho5!lo8!mq6!hpd!nf!ud!lp9!mqf!lqa!lr2!md!hi0!j4!hj3!lp1!iqe!lre!lsb!lt9!lu5!lv7!kq5!mi5!mt5!mrf!mn5!jj4!lla!ms8>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3rom>0@1$1@1$0#k0@1$5@1$1@1$0#8>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1L@1$9@2$4$2$2>2o0$2>1o$2>1v@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#i0@2$h6?4segs^a@2$8@1$1@1$0#i0^8>0@3$3$h1@1$h7^9$h3>0@3$3@1$5@2$4$6$2@1$hb^a@2$8@2$4$6$2@4$a$6$2@4$hd$hc^9^8^7+4>0@3$3@1$1@1$0#k0@2$d^e^a@2$hf?1d^6>0@3$3$2@2$f^7@2$i1@1$0#c^9^6>0@3$3@1$1@1$0#k0@2$d^h0^b^6>0@3$3@1$9@1$1@1$0#8@2$haN4^7@3$h4@1$1@1$0#8@1$7?2cvN4>0@2$h0Z^9>0@2$h0@2$f^a+4?1n@3$3@1$h8$b@2$h9?4segs@5$e?2fx^h4^h3@5$c?4mem0?1d?1n@1$7?2cv^d^h2@2$h5$b@5$e?2fx^h4@2$i0^h3+4@5$c?4mem0?1d?1n@1$7?2cv@3$h2@2$4$2$2@4$a$2$2^b+4^d^h2").
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sd : ltac2:(zQ "i20!hlc!hnf!h9!hh5!jb!ho5!lo8!mq6!hpd!nf!ud!lp9!mqf!lqa!lr2!md!hi0!j4!hj3!lp1!iqe!lre!lsb!lt9!lu5!lv7!kq5!mi5!mtc!mrf!mn5!jj4!lla!ms8>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3rom>0@1$1@1$0#k0@1$5@1$1@1$0#8>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1L@1$9@2$4$2$2>2o0$2>1o$2>1v@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#i0@2$h6?4segs^a@2$8@1$1@1$0#i0^8>0@3$3$h1@1$h7^9$h3>0@3$3@1$5@2$4$6$2@1$hb^a@2$8@2$4$6$2@4$a$6$2@4$hd$hc^9^8^7+4>0@3$3@1$1@1$0#k0@2$d^e^a@2$hf?1d^6>0@3$3$2@2$f^7@2$i1@1$0#c^9^6>0@3$3@1$1@1$0#k0@2$d^h0^b^6>0@3$3@1$9@1$1@1$0#8@2$haN8^7@3$h4@1$1@1$0#8@1$7?2cvN8>0@2$h0Z^9>0@2$h0@2$f^a+8?1n@3$3@1$h8$b@2$h9?4segs@5$e?2fx^h4^h3@5$c?4mem0?1d?1n@1$7?2cv^d^h2@2$h5$b@5$e?2fx^h4@2$i0^h3+4@5$c?4mem0?1d?1n@1$7?2cv@3$h2@2$4$2$2@4$a$2$2^b+8^d^h2").
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
    rewrite <- Hv.
    eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition ms_clob : ltac2:(zQ "30!nf!hlc!hnf@1$0@1$2@1$1#5") := ltac2:(zQ "70!hlc!hnf!hj3!lra!mo8!moe!hv0@3$2@1$1@1$0#5@3$4@1$0#5+bKv$3@2$5@1$0#5+b@3$2@1$1@1$0#5@3$4@1$0#5+cKv$3@2$5@1$0#5+c@3$2@1$1@1$0#5@3$4@1$0#5+dKv$3@2$5@1$0#5+d@3$2@1$1@1$0#5@3$4@1$0#5+eKv$3@2$5@1$0#5+e@3$2@1$1@1$0#5@3$4@1$0#5+fKv$3@2$5@1$0#5+f@3$2@1$1@1$0#5@3$4@1$0#5+h0Kv$3@2$5@1$0#5+h0@1$6@1$1@1$0#5").
Definition ms_agree : ltac2:(zQ "30!hlc!mn5!hnf>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "60!hlc!hnf!mn5!mu3!nj2!hk0\4regs@2$2@1$0#5@1$1@1$0#k0\5regs'@2$2@1$0#5@1$1@1$0#k0@3$3\1r@1$1@1$0#5@3$5@1$1@1$0#5^1$4^2^1").

Lemma ms_agree_refl : ltac2:(zQ "40!hlc!mn5!njd!hnf>4regs@2$1@1$0#5@1$3@1$0#k0@2$2^1^1").
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : ltac2:(zQ "40!hlc!mn5!njd!hnf>2r1@2$1@1$0#5@1$3@1$0#k0>2r2@2$1@1$0#5@1$3@1$0#k0>2r3@2$1@1$0#5@1$3@1$0#k0>0@2$2^3^2>0@2$2^3^2@2$2^5^3").
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : ltac2:(zQ "70!hlc!hnf!mn5!njd!nj2!mne!hk0>4regs@2$2@1$0#5@1$1@1$0#k0>5regs'@2$2@1$0#5@1$1@1$0#k0>2rd@1$1@1$0#5>1v@1$1@1$0#k0>0@2$3^4^3>0@3$6@1$1@1$0#5^3$4@2$3^6@3$5^5^4^3").
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.

End FPX3.

Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
(* [comment removed for export] *)
