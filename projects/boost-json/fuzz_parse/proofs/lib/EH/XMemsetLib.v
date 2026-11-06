(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStepTac XHoare XStoreOk XMemSplit XRefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4boolhc4prodhc3fsthc4andbhc3snd46Stdlib6ZArith6BinInt1Zl53addl53lebl53ltbhc4list89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXMemsetLib5FPX_1~~~~~~o66ms_inb36Stdlib5Lists4Listt57existsbhc4pairhc4true37Corelib4Init5Logichg03andhg02eqhg03iffl52lel52lto66ms_covhc4conshc3orbt52Inhg02exo68ms_chaint54incl04Npos35stdpp9bitvectorbdefinitionshmb2bvhc6optionhmbbbv_unsignedhc4Somel53subhc3nil99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXMemsetLib5FPX_15CFill~~~~~~hr95cfill79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~ige9mem_growsl56of_nathc3nat37Corelib5Lists7ListDefim86repeat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XCatExec~~~~~~io96wbytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6XHoare~~~~~~it13at_l56to_nat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjhd8store_ok3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejm07Segmenthmb7Z_to_bvl56moduloo63cbzl53mull53powo65cbyteo67ms_repl3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejt8dZ_to_le_byteso63c32o64c32ho63c64jhdh0word_to_le_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~kk06v_sllikk07v_mulhukk06v_srlil53lorkk04v_orkk06v_andikk06v_subwl53oppl54landhg02orkk05v_addkk05v_subkk06v_addi3h5LinuxProcessSemantics5Riscv5Instrkuf5instrhc5falsejhddmachine_statekk04getrkk04mksthg01Ijhd9MachineOkjhdafetch_wordjhd8is_ecalljhdemachine_resultjhd4step3h5LinuxProcessSemantics5Riscv7DecodeClobadecode_anykuf7M_MULHUkuf3Mul3h5LinuxProcessSemantics5Riscv7Preludelt16bv_eqblt15bvmapkk06regupdhmb2BVhmb4BvWfkuf6ALU_ORkuf2Opo65cfillkuf3SZ1kuf5Storehmb9bv_signedkuf3SZ4kuf3SZ8it1aregs_agreeo67ms_clobo68ms_agree" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Section FPX_1. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_inb : ltac2:(zQ "30!h9!j4!jb>1i$0>2iv@2$2$0$0$1") := ltac2:(zQ "80!h9!k2!k8!jb!kf!md!n3!n9\1i$0\2iv@2$3$0$0@2$2@2$6@3$1$0$0^1^2@2$7^2@2$5@3$1$0$0^1@3$4$0$0^1").
Definition ms_cov : ltac2:(zQ "40!h9!j4!nf!jb>1L@1$2@2$3$0$0>1i$0$1") := ltac2:(zQ "50!h9!jb!nf!sc!u8\1L@1$2@2$1$0$0\1i$0@3$4@2$1$0$0@1$3^1^2").

Lemma ms_inb_true : ltac2:(zQ "b0!h9!j4!v2!v9!hh4!hhb!hi1!sc!md!hi8!hid>1i$0>1o$0>1m$0@2$6@3$5$1@2$7^3@4$2$0$0^2^1$3@2$4@2$9^2^3@2$a^3@2$8^2^1").
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : ltac2:(zQ "90!h9!jb!hj2!j4!hjb!nf!hk2!hhb!sc>2iv@2$1$0$0>1L@1$5@2$1$0$0>1i$0@3$7$3@2$2@3$4@2$1$0$0^3^2^1@2$6@2$8^1^3@2$2^2^1").
Proof. reflexivity. Qed.

Lemma ms_cov_In : ltac2:(zQ "d0!h9!jb!j4!nf!v2!v9!hh4!hhb!hj2!hk8!md!hi8!hid>1L@1$3@2$1$0$0>1i$0>1o$0>1m$0>0@3$9@2$1$0$0@4$4$0$0^2^1^4>0@2$6@2$b^3^4@2$c^4@2$a^3^2@3$7$2@2$8^6^5$5").
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

Lemma ms_chain_cov : ltac2:(zQ "b0!h9!hh4!jb!hkd!hi8!hid!nf!v2!hl3!hk8!md>1L@1$6@2$2$0$0>4from$0>2to$0>1i$0>0@3$8^3^2^4>0@2$1@2$4^4^2@2$5^2^3@2$3$0\1o$0@2$3$0\1m$0@2$1@3$9@2$2$0$0@4$7$0$0^2^1^8@2$1@2$4^2^5@2$5^5@2$a^2^1").
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
Lemma ms_cov_by_chain : ltac2:(zQ "c0!h9!jb!nf!j4!v9!hh4!hhb!hl3!hj2!hle!hi8!hid>1L@1$2@2$1$0$0>2L'@1$2@2$1$0$0>1n$0>0@3$9@2$1$0$0^2^3>0@3$7Z^2^3>1i$0>0@2$5@2$aZ^1@2$b^1^4@3$6$3@2$8^7^2$4").
Proof.
  intros L L' n Hincl Hc i Hi.
  ndestruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CFill.
  Variable mem0 : ltac2:(zQ "30!hm5!ho8!hoe>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable d : word.
  Variable n : Z.
  Variable c : ltac2:(zQ "20!hm5!ho8@1$1@1$0#8").
  Hypothesis Hn : ltac2:(zQ "10!hi8@2$0Z?1n").
  Hypothesis Hnw : ltac2:(zQ "50!hm5!md!hid!js0!hp7@2$2@2$1@2$4@1$0#k0?1d?1n@2$3+2+k0").

  Definition cfill : ltac2:(zQ "60!hm5!h9!ho8!nf!hoe!jb>1L@1$3@2$5$1$1>0@1$2@1$0#k0@1$4@1$2@1$0#8") := ltac2:(zQ "f0!hm5!hp7!ho8!k8!j4!h9!hq6!nf!hoe!jb!hj2!md!n3!n9!hqd\1L@1$7@2$9$5$5\1x@1$2@1$0#k0M4\0$4@1$8@1$2@1$0#8@2$3@2$3@2$c@2$1@1$0#k0?1d@2$1@1$0#k0^1@2$d@2$1@1$0#k0^1@2$b@2$1@1$0#k0?1d?1n@2$a^2@2$e@2$1@1$0#k0^1@2$1@1$0#k0?1d@2$6@1$2@1$0#8?1c@1?4mem0^1").

  Lemma cfill_nil : ltac2:(zQ "80!hm5!h9!ho8!hr3!hoe!jb!hhb!ig5@3$6>0@1$2@1$0#k0@1$4@1$2@1$0#8@1$7@1$3@2$5$1$1?4mem0").
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  Lemma cfill_grows : ltac2:(zQ "50!h9!nf!jb!ig5!ikc>1L@1$1@2$2$0$0@2$4?4mem0@1$3^1").
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_ext : ltac2:(zQ "d0!h9!nf!jb!hhb!hm5!ig5!hj2!ho8!j4!hoe!hh4!hi8!hid>2L1@1$1@2$2$0$0>2L2@1$1@2$2$0$0>0>1i$0>0@2$a@2$bZ^1@2$c^1?1n@3$3$8@2$6^4^2@2$6^3^2@3$3>0@1$7@1$4#k0@1$9@1$7@1$4#8@1$5^3@1$5^2").
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_store : ltac2:(zQ "h10!h9!hm5!ho8!jb!ig5!hi8!il9!hjb!nf!im2!hoe!v2!hhb!inf!is7!jgd!md>1L@1$8@2$3$0$0>1o$0>1m$9>0@2$5Z^2>0@2$5@2$h0^3@1$6^2?1n@3$c>0@1$2@1$1#k0@1$a@1$2@1$1#8@3$e@1$4^5@2$f?1d^4@3$d@1$2@1$1#8?1c^3@1$4@3$7@2$3$0$0@4$b$0$0^4@1$6^3^5").
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
  Lemma cfill_full : ltac2:(zQ "h10!hm5!h9!ho8!hhb!j4!nf!hoe!jb!v9!hh4!inf!is7!ig5!hj2!hi8!hid!jh4>1L@1$5@2$7$1$1>0>1i$1>0@2$9@2$eZ^1@2$f^1?1n@3$3$4@2$d^3^2$8@3$3>0@1$2@1$0#k0@1$6@1$2@1$0#8@1$c^2@3$b?4mem0?1d@3$a@1$2@1$0#8?1c@1$h0?1n").
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

  Lemma cfill_full_chain : ltac2:(zQ "d0!h9!jb!hm5!ho8!nf!hoe!hhb!inf!is7!ig5!hl3!hle!jh4>1L@1$4@2$1$0$0>2L'@1$4@2$1$0$0>0@3$b@2$1$0$0^1^2>0@3$aZ?1n^2@3$6>0@1$3@1$2#k0@1$5@1$3@1$2#8@1$9^4@3$8?4mem0?1d@3$7@1$3@1$2#8?1c@1$c?1n").
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  (* [comment removed for export] *)
  Lemma cfill_store_ok : ltac2:(zQ "f0!h9!j4!nf!v9!hhb!jl4!hi8!im2!jb!jp5!jgd!ig5!md!il9!jh4>4segs@1$2$9>1L@1$2@2$8$0$0>1o$0>1m$7>0@3$4$1@4$5^4?4mem0?1d@1$e?1n$3>0@2$6Z^3>0@2$6@2$c^4@1$d^3?1n@3$4$1@4$5^7@1$b^6@2$a?1d^5^4$3").
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cbyte : ltac2:(zQ "20!hm5!ho8>2cv@1$1@1$0#k0@1$1@1$0#8") := ltac2:(zQ "40!hm5!jq0!ho8!hp7\2cv@1$2@1$0#k0@2$1@1$0#8@2$3@1$0#k0^1").
(* [comment removed for export] *)
Definition cbz : ltac2:(zQ "30!hm5!h9!ho8>2cv@1$2@1$0#k0$1") := ltac2:(zQ "40!hm5!jqb!ho8!hp7\2cv@1$2@1$0#k0@2$1@2$3@1$0#k0^1+hg0").
(* [comment removed for export] *)
Definition c32 : ltac2:(zQ "20!hm5!ho8>2cv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!hm5!jr4!jra!jq0!ho8\2cv@1$4@1$0#k0@2$3@1$0#k0@2$2@1$1^1+hghghg1").
(* [comment removed for export] *)
Definition c32h : ltac2:(zQ "20!hm5!ho8>2cv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!hm5!jra!jr4!js0!jq0!ho8\2cv@1$5@1$0#k0@2$4@1$0#k0@2$1@2$1@1$2^1+hghghg1@2$3+2+i0").
(* [comment removed for export] *)
Definition c64 : ltac2:(zQ "20!hm5!ho8>2cv@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!hm5!jr4!jra!jq0!ho8\2cv@1$4@1$0#k0@2$3@1$0#k0@2$2@1$1^1+hghghghghghghg1").

Lemma cbz_range : ltac2:(zQ "60!jr4!hh4!hm5!hi8!hid!ho8>2cv@1$5@1$2#k0@2$1@2$3Z@1$0^1@2$4@1$0^1+hg0").
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : ltac2:(zQ "70!hm5!ho8!hhb!js6!jqb!jq0!hp7>2cv@1$1@1$0#k0@3$2@1$1@1$0#8@2$5@1$0#8@2$4@2$6@1$0#k0^1+hg0@1$3^1").
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : ltac2:(zQ "60!hm5!ho8!hhb!js6!jr4!jq0>2cv@1$1@1$0#k0@3$2@1$1@1$0#8@1$3^1@2$5@1$0#8@1$4^1").
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : ltac2:(zQ "30!im2!jse!hi8>1k$0@2$2Z@1$1^1").
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : ltac2:(zQ "e0!hm5!ho8!nf!im2!hh4!hhb!inf!h9!kg7!jse!hi8!hid!jra!jq0>1k$3>1z$7>0@2$4@2$aZ^1@2$b^1+hg0@3$5@1$2@1$1@1$0#8@2$8^3@2$c^2@1$9^3@3$6@1$1@1$0#8@2$d@1$0#8^2^3").
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

Lemma u_c32 : ltac2:(zQ "80!hm5!hhb!h9!kh8!jr4!jra!ho8!hp7>2cv@1$6@1$0#k0@3$1$2@2$7@1$0#k0@1$3^1@2$5@1$4^1+hghghg1").
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : ltac2:(zQ "90!hm5!jra!hhb!h9!khe!jr4!js0!ho8!hp7>2cv@1$7@1$0#k0@3$2$3@2$8@1$0#k0@1$4^1@2$1@2$1@1$5^1+hghghg1@2$6+2+i0").
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : ltac2:(zQ "80!hm5!hhb!h9!ki5!jr4!jra!ho8!hp7>2cv@1$6@1$0#k0@3$1$2@2$7@1$0#k0@1$3^1@2$5@1$4^1+hghghghghghghg1").
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : ltac2:(zQ "80!hm5!ho8!nf!hhb!inf!kib!kh8!js6>2cv@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$5N4@1$6^1@3$4@1$1@1$0#8@1$7^1N4").
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : ltac2:(zQ "80!hm5!ho8!nf!hhb!inf!kib!ki5!js6>2cv@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$5N8@1$6^1@3$4@1$1@1$0#8@1$7^1N8").
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

(* [comment removed for export] *)
Lemma u_slli56 : ltac2:(zQ "90!hm5!hhb!h9!jr4!knf!jra!js0!ho8!hp7>2cv@1$7@1$0#k0@3$1$2@2$8@1$0#k0@2$4^1+j8@2$5@1$3^1@2$6+2+j8").
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_c32 : ltac2:(zQ "80!hm5!ho8!hhb!h9!kh8!ko9!knf!hp7>2cv@1$1@1$0#k0>1m@1$1@1$0#k0>0@3$2$3@2$7@1$0#k0^1+hghghghg0@3$2@1$1@1$0#k0@2$5@2$6^3+j8^2@1$4^3").
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : ltac2:(zQ "60!hm5!ho8!hhb!kh8!khe!knf>2cv@1$1@1$0#k0@3$2@1$1@1$0#k0@2$5@1$3^1+i0@1$4^1").
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : ltac2:(zQ "60!hm5!ho8!hhb!kh8!khe!kp4>2cv@1$1@1$0#k0@3$2@1$1@1$0#k0@2$5@1$4^1+i0@1$3^1").
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : ltac2:(zQ "90!h9!js0!hi8!jra!hh4!hhb!md!kpe!hid>1a$0>1b$0>0@2$2Z^2>0@2$4@2$2Z^2@2$8^2@2$1+2+i0@3$5$0@2$7@2$3^4@2$1+2+i0^3@2$6@2$3^4@2$1+2+i0^3").
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : ltac2:(zQ "70!hm5!ho8!hhb!kh8!khe!ki5!kq4>2cv@1$1@1$0#k0@3$2@1$1@1$0#k0@2$6@1$4^1@1$3^1@1$5^1").
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2' : ltac2:(zQ "50!h9!jqb!hhb!hi8!js0>1t$0>1k$0>0@2$3+2^1@3$2$0@2$1@2$1^3@2$4+2^2+4@2$1^3+4").
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : ltac2:(zQ "90!hm5!jq0!ho8!hhb!kqc!kr6!jqb!ks0!hp7>1x@1$2@1$0#k0@3$3@1$2@1$0#k0@2$4@2$5@2$1@1$0#k0Z^1+3@2$1@1$0#k0@2$6@1$7@2$8@1$0#k0^1+4").
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

Lemma neg_mod4_range : ltac2:(zQ "50!hi8!jqb!ks0!hh4!h9>1u$4@2$3@2$0Z@2$1@1$2^1+4@2$0@2$1@1$2^1+4+3").
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.

(* [comment removed for export] *)
Lemma land_trunc4 : ltac2:(zQ "90!h9!js0!hqd!hh4!hhb!ks6!hi8!hid!jqb>1a$0>0@2$3@2$6Z^1@2$7^1@2$1+2+k0@3$4$0@2$5^2@2$2@2$1+2+k0+4@2$2^2@2$8^2+4").
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

Lemma andi_m4 : ltac2:(zQ "c0!hm5!jq0!hh4!hhb!h9!kqc!hi8!hid!jqb!js0!hqd!ho8>1m$4>0@2$2@2$6Z^1@2$7^1@2$9+2+k0@3$3@1$b@1$0#k0@2$5@2$1@1$0#k0^2-4@2$1@1$0#k0@2$a^2@2$8^2+4").
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : ltac2:(zQ "50!h9!hhb!ks6!ksd!hi8>1a$0>0@2$4Z^1@2$3@3$1$0@2$2^2+4Z@3$1$0@2$2^2+4+4").
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : ltac2:(zQ "90!h9!hhb!hm5!ho8!hh4!hkd!ksd!kqc!jq0>1x@1$3@1$2#k0@2$5$0\2s4$0@2$4@3$1@1$3@1$2#k0@2$7^2+4@2$8@1$2#k0^1@2$6@3$1$0^1Z@3$1$0^1+4").
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma ms_v_add_Z : ltac2:(zQ "b0!hm5!ho8!hh4!hhb!h9!jgd!kt3!hi8!hid!js0!jq0>1x@1$1@1$0#k0>1z$4>0@2$2@2$7Z^1@2$8^1@2$9+2+k0@3$3@1$1@1$0#k0@2$6^3@2$a@1$0#k0^2@2$5^3^2").
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : ltac2:(zQ "c0!hm5!h9!jgd!ho8!hh4!hhb!kt3!md!hi8!hid!js0!jq0>1x@1$3@1$0#k0>1o$1>1z$1>0@2$4@2$8Z^1@2$9^1@2$a+2+k0@3$5@1$3@1$0#k0@2$6@2$2^4^3@2$b@1$0#k0^2@2$2^4@2$7^3^2").
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : ltac2:(zQ "b0!hm5!jq0!h9!hi8!hh4!hhb!ktc!hid!js0!hqd!ho8>1a$2>1b$2>0@2$4@2$3Z^1@2$3^1^2>0@2$7^3@2$8+2+k0@3$5@1$a@1$0#k0@2$6@2$1@1$0#k0^4@2$1@1$0#k0^3@2$1@1$0#k0@2$9^4^3").
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : ltac2:(zQ "b0!hm5!h9!jq0!hh4!hhb!ku5!md!hi8!hid!js0!ho8>1a$1>1i$1>0@2$3@2$7Z^2@2$8^2@2$9+2+k0@3$4@1$a@1$0#k0@2$5@2$2@1$0#k0^3^2@2$2@1$0#k0@2$6^3^2").
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_step_mulhu_at : ltac2:(zQ "i01!hm5!ho8!hhb!hoe!h9!lh3!hq6!j4!lhc!jb!li4!lj5!ljd!nf!v2!lk5!jp5!lka!ll7!lm5!ln1!lo3!lr1!lrf!lsa!lv7!mg1!mga!ku5!ko9!mh4!mha&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : ltac2:(zQ "i01!hm5!ho8!hhb!hoe!h9!lh3!hq6!j4!lhc!jb!li4!lj5!ljd!nf!v2!lk5!jp5!lka!ll7!lm5!ln1!lo3!lr1!mi2!mic!lv7!mg1!mga!ku5!kq4!mh4!mha&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$ha@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$8>0@3$2@1$3@2$9$5$4@1$h6^7@2$6@2$9$5$4@4$e$5$4@4$h8$h7^6^5^4+4>0@3$2$7@3$h9@1$0#5^7@3$he@1$0#5ZKv$f@2$hf@1$0#5Z$8>0@3$2@1$1@1$0#k0@2$hd@2$b^d^7@2$b^d^6^5@3$2@1$h4$a@2$h5^f@5$c?2fx^e^d^c^b@2$h1$a@5$c?2fx@3$hb^e^9^6@2$hc^d+4^c^b").
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
  Variable segs : ltac2:(zQ "20!nf!jp5@1$0$1").
  Variable mem0 : ltac2:(zQ "30!hm5!ho8!hoe>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : ltac2:(zQ "50!hm5!md!hid!js0!hp7@2$2@2$1@2$4@1$0#k0?1d?1n@2$3+2+k0").
  Hypothesis Hok : ltac2:(zQ "50!j4!v9!hhb!jl4!jh4@3$2$0@4$3?4segs?4mem0?1d@1$4?1n$1").

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  Lemma cf_sb : ltac2:(zQ "i00!hm5!h9!ho8!hhb!jb!hoe!lh3!hq6!v2!li4!js6!mj2!lj5!ljd!md!hi8!j4!hjb!lhc!nf!lka!ll7!lm5!ln1!lo3!lr1!mja!mk1!mg1!jgd!ku5!mka>4regs@2$hc@1$0#5@1$2@1$0#k0>2pc@1$2@1$0#k0>3rom>0@1$2@1$0#k0@1$5@1$2@1$0#8>1w@1$2@1$0#i0>3rs1@1$2@1$0#5>3rs2@1$2@1$0#5>3imm@1$2@1$0#c>1L@1$h3@2$4$1$1>2o0$1>1o$1>0@3$3@1$5@1$2@1$0#i0@2$h5?4segs^9@2$7@1$2@1$0#i0^7>0@3$3$h0@1$h6^8$h2>0@3$3@1$5@2$4$6$1@1$h9^9@2$7@2$4$6$1@4$8$6$1@4$hb$ha^8^7^6+4>0@3$3@1$2@1$0#k0@2$c^d^9@2$hd?1d^5>0@3$3$1@2$e^6@2$hf@1$0#c^8^5>0@3$3@1$2@1$0#k0@2$c^f^a?2cv>0@2$fZ^7>0@2$f@2$e^8+1?1n@3$3@1$h7$9@2$h8?4segs@5$d?2fx^h2^h1@5$b?4mem0?1d?1n@1$a?2cv^b^h0@2$h4$9@5$d?2fx^h2@2$he^h1+4@5$b?4mem0?1d?1n@1$a?2cv@3$h1@2$4$1$1@4$8$1$1^9+1^b^h0").
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sw : ltac2:(zQ "i20!hm5!ho8!h9!hhb!jb!hoe!lh3!js6!hq6!nf!v2!li4!mj2!lj5!ljd!md!hi8!j4!hjb!lhc!inf!lka!ll7!lm5!ln1!lo3!kib!lr1!ml7!mk1!mg1!jgd!ku5!mka>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3rom>0@1$1@1$0#k0@1$5@1$1@1$0#8>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1L@1$9@2$4$2$2>2o0$2>1o$2>1v@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#i0@2$h6?4segs^a@2$8@1$1@1$0#i0^8>0@3$3$h1@1$h7^9$h3>0@3$3@1$5@2$4$6$2@1$hb^a@2$8@2$4$6$2@4$a$6$2@4$hd$hc^9^8^7+4>0@3$3@1$1@1$0#k0@2$d^e^a@2$hf?1d^6>0@3$3$2@2$f^7@2$i1@1$0#c^9^6>0@3$3@1$1@1$0#k0@2$d^h0^b^6>0@3$3@1$9@1$1@1$0#8@2$haN4^7@3$h4@1$1@1$0#8@1$7?2cvN4>0@2$h0Z^9>0@2$h0@2$f^a+4?1n@3$3@1$h8$b@2$h9?4segs@5$e?2fx^h4^h3@5$c?4mem0?1d?1n@1$7?2cv^d^h2@2$h5$b@5$e?2fx^h4@2$i0^h3+4@5$c?4mem0?1d?1n@1$7?2cv@3$h2@2$4$2$2@4$a$2$2^b+4^d^h2").
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sd : ltac2:(zQ "i20!hm5!ho8!h9!hhb!jb!hoe!lh3!js6!hq6!nf!v2!li4!mj2!lj5!ljd!md!hi8!j4!hjb!lhc!inf!lka!ll7!lm5!ln1!lo3!kib!lr1!mle!mk1!mg1!jgd!ku5!mka>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3rom>0@1$1@1$0#k0@1$5@1$1@1$0#8>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#c>1L@1$9@2$4$2$2>2o0$2>1o$2>1v@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#i0@2$h6?4segs^a@2$8@1$1@1$0#i0^8>0@3$3$h1@1$h7^9$h3>0@3$3@1$5@2$4$6$2@1$hb^a@2$8@2$4$6$2@4$a$6$2@4$hd$hc^9^8^7+4>0@3$3@1$1@1$0#k0@2$d^e^a@2$hf?1d^6>0@3$3$2@2$f^7@2$i1@1$0#c^9^6>0@3$3@1$1@1$0#k0@2$d^h0^b^6>0@3$3@1$9@1$1@1$0#8@2$haN8^7@3$h4@1$1@1$0#8@1$7?2cvN8>0@2$h0Z^9>0@2$h0@2$f^a+8?1n@3$3@1$h8$b@2$h9?4segs@5$e?2fx^h4^h3@5$c?4mem0?1d?1n@1$7?2cv^d^h2@2$h5$b@5$e?2fx^h4@2$i0^h3+4@5$c?4mem0?1d?1n@1$7?2cv@3$h2@2$4$2$2@4$a$2$2^b+8^d^h2").
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

Definition ms_clob : ltac2:(zQ "30!nf!hm5!ho8@1$0@1$2@1$1#5") := ltac2:(zQ "70!hm5!ho8!hjb!lk5!mh4!mha!hr3@3$2@1$1@1$0#5@3$4@1$0#5+bKv$3@2$5@1$0#5+b@3$2@1$1@1$0#5@3$4@1$0#5+cKv$3@2$5@1$0#5+c@3$2@1$1@1$0#5@3$4@1$0#5+dKv$3@2$5@1$0#5+d@3$2@1$1@1$0#5@3$4@1$0#5+eKv$3@2$5@1$0#5+e@3$2@1$1@1$0#5@3$4@1$0#5+fKv$3@2$5@1$0#5+f@3$2@1$1@1$0#5@3$4@1$0#5+h0Kv$3@2$5@1$0#5+h0@1$6@1$1@1$0#5").
Definition ms_agree : ltac2:(zQ "30!hm5!mg1!ho8>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "60!hm5!ho8!mg1!mm5!mn3!hk8\4regs@2$2@1$0#5@1$1@1$0#k0\5regs'@2$2@1$0#5@1$1@1$0#k0@3$3\1r@1$1@1$0#5@3$5@1$1@1$0#5^1$4^2^1").

Lemma ms_agree_refl : ltac2:(zQ "40!hm5!mg1!mnd!ho8>4regs@2$1@1$0#5@1$3@1$0#k0@2$2^1^1").
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : ltac2:(zQ "40!hm5!mg1!mnd!ho8>2r1@2$1@1$0#5@1$3@1$0#k0>2r2@2$1@1$0#5@1$3@1$0#k0>2r3@2$1@1$0#5@1$3@1$0#k0>0@2$2^3^2>0@2$2^3^2@2$2^5^3").
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : ltac2:(zQ "70!hm5!ho8!mg1!mnd!mn3!mga!hk8>4regs@2$2@1$0#5@1$1@1$0#k0>5regs'@2$2@1$0#5@1$1@1$0#k0>2rd@1$1@1$0#5>1v@1$1@1$0#k0>0@2$3^4^3>0@3$6@1$1@1$0#5^3$4@2$3^6@3$5^5^4^3").
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.

End FPX_1.


Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
(* [comment removed for export] *)
