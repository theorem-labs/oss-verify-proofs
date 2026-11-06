(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~07FPState37Corelib7Numbers7BinNumsk44Npos3h5LinuxProcessSemantics5Riscv7Preludem4bbvmap_empty04mkFP35stdpp9bitvectorbdefinitionspe7Z_to_bvpe2bvm45bvmap37Corelib4Init9Datatypest24bool37Corelib4Init5Logicv11Im46bv_eqb3h5LinuxProcessSemantics5Riscv3Semhh27reg_getpe2BVpe4BvWfm49bvmap_setv12eqhh25is_x0t24truek41Z46Stdlib6ZArith6BinInt1Zhn06modulohn03powpe7bv_wraphn03addhn06of_nathn02let25falsev13andhn02lthn07testbithn04landhn03lorhn04lxorhn06shiftrpe8bv_swrapk41Npe9bv_signedpebbv_unsignedhn03subhn03mulm46bv_ltsm46bv_ltu79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec4FPX1~~~~~~ik36v_addiik34zsighn03ltbik35c_ltsik35c_ltuhn06shiftlhn03eqbhn04quothn03remhn03divik39jalr_tgtZt24listt26option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeiv27Segmentt24Nonet24Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjk0bmemory_readt23natjk0dov_read_bytesik33rdnt24const23nil3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejr1h0le_bytes_to_wordjr1dbytes_le_to_Zk42N0peabv_extractm44sextik34v_lbik34v_lhik34v_lwt26lengtht23apppe6bv_add3h5LinuxProcessSemantics5Riscv5Instrkkf7ALU_SLThh25alu64ik36v_sltikkf7ALU_ADDik35v_addkkf7ALU_SUBik35v_subik35v_sltkkf8ALU_SLTUik36v_sltukkf7ALU_ANDik35v_andkkf6ALU_ORik34v_orkkf7ALU_XORik35v_xorm44zextpe6bv_andkkf7ALU_SLLik36v_sllikkf7ALU_SRLik36v_srlikkf7ALU_SRAik36v_sraiik35v_sllik35v_srlik35v_srahh25low32hh25alu32ik37v_addiwik37v_slliwik37v_srliwik37v_sraiwik36v_addwik36v_subwik36v_sllwik36v_srlwik36v_srawkkf5M_MULhh27mul_divik35v_mulkkf6M_MULHik36v_mulhkkf8M_MULHSUik38v_mulhsukkf7M_MULHUik37v_mulhukkf5M_DIVik35v_divkkf5M_REMik35v_remik36v_mulwik36v_divwik36v_remwkkf6M_DIVUik37v_divuwkkf6M_REMUik37v_remuwpeabv_modulusv13notpefbv_half_modulusik35v_luipe9bv_concatik37v_auipcik38jalr_tgtpe6bv_notkkf5instrt24prodjk0dmachine_state04mkstt24pairjk09MachineOkjk0afetch_wordjk08is_ecalljk0emachine_resultjk04step3h5LinuxProcessSemantics5Riscv7DecodeCno0adecode_anykkf5OpImmkkf5aluop04getr06regupd06v_addikkf8ShiftImmkkf2Opkkf7OpImm32kkfaShiftImm32kkf4Op32kkf3Mulkkf5mulopkkf5Mul32kkf6Branchkkfbbranch_condhh2cbranch_taken04btgt06v_andi05v_ori06v_xori07v_sltiu06v_slti06v_slli06v_srli06v_srai05v_add05v_sub05v_slt06v_sltu05v_and04v_or05v_xor05v_sll05v_srl05v_sra07v_addiw07v_slliw07v_srliw07v_sraiw06v_addw06v_subw06v_sllw06v_srlw06v_sraw05v_mul06v_mulh08v_mulhsu07v_mulhu05v_div05v_rem06v_mulw06v_divw07v_divuw06v_remw07v_remuwkkf5BC_EQ04c_eqkkf5BC_NEkkf5BC_LT05c_ltskkf5BC_GEkkf6BC_LTU05c_ltukkf6BC_GEUkkf3Lui05v_luikkf5Auipc07v_auipckkf3Jalkkf4Jalr08jalr_tgtjk0h3Build_machine_state06fp_csr07fp_regskkf|41L1o1a1dkkf3SZ103rdn04v_lbkkf3SZ204v_lhkkf3SZ404v_lwkkf3SZ8jr1dZ_to_le_bytesjk0h0word_to_le_bytesjr18word_le8hn06to_nat37Corelib4Init3Natqqd3add37Corelib4Init5Peanoqs62le37Corelib5Lists7ListDefqu06firstnqu05skipn3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutrgacstack_to_memqqd3mul36Stdlib5Lists4Listrl58flat_maprl5afold_right3h5LinuxProcessSemanticsfLinuxProcessSem3Runro2ftotal_arg_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec4FPX3~~~~~~rs1h3total_arg_bytes_natrgafflatten_stringsjr1bnat_to_wordt23fstrgacstring_addrsjr18len_wordiv28PhdrInforo2h0entry_stack_spanrga9EntryDrawrgah1build_stack_bytesv12exro2fentry_block_topro2h1entry_stack_imageqs62ltqu03ntht24andb3h5LinuxProcessSemanticsfLinuxProcessSem5Statesu3estack_max_sizehn03lebro2h2init_machine_staters18wrap_mem03fx007seg_romhn04of_N" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac bvwf_has_var t := match t with context [?x] => is_var x end.
Ltac solve_BvWf_fast :=
  lazymatch goal with
  | |- BvWf ?n ?v =>
      tryif bvwf_has_var v then fail else
      tryif bvwf_has_var n then fail else
      tryif has_evar v then fail else
      tryif has_evar n then fail else
      (vm_compute; exact I)
  end.
#[global] Hint Extern 9 (BvWf _ _) => solve_BvWf_fast : typeclass_instances.

(* [comment removed for export] *)
Ltac noncert_clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac noncert_goal_has_var :=
  match goal with |- ?G => match G with context [?x] => is_var x end end.
Ltac lia ::=
  tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
  else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker]
             | Zify.zify; xlia zchecker ].
Ltac nia ::=
  tryif noncert_goal_has_var then (Zify.zify; xnia zchecker)
  else first [ solve [noncert_clear_all; Zify.zify; xnia zchecker]
             | Zify.zify; xnia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Class FPState := mkFP { fp_regs : bvmap 5 word; fp_csr : bv 32 }.
Definition fx0 : ltac2:(zQ "10!jb$0") := ltac2:(zQ "50!ld!oa!p8!rb!s5@2$2@2$1@1$0#5@1$4@1$0#k0@2$3@1$0#i0Z").

Definition mkst `{fx : FPState} (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := None; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Section FPX1. Context {fx : FPState}.

(* [comment removed for export] *)
Definition getr : ltac2:(zQ "30!ld!s5!sa>4regs@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5@1$1@1$0#k0") := ltac2:(zQ "a0!ld!s5!ua!hg5!hg9!sa!hj4!hjf!hk4!rb\4regs@2$5@1$0#5@1$1@1$0#k0\1r@1$1@1$0#5M2\0$2@1$1@1$0#k0@3$4@1$0#5^1@3$7@1$0#5ZKv$3@2$8@1$0#5Z@2$9@1$0#k0Z@2$6^2^1").
Definition regupd : ltac2:(zQ "30!ld!s5!sa>4regs@2$2@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0@2$2@1$0#5@1$1@1$0#k0") := ltac2:(zQ "40!ld!s5!sa!hkb\4regs@2$2@1$0#5@1$1@1$0#k0\1r@1$1@1$0#5\1v@1$1@1$0#k0@5$3@1$0#5@1$1@1$0#k0^2^1^3").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb0_is_x0 : ltac2:(zQ "90!ld!ua!hg5!hl7!hg9!hlc!hjf!hk4!s5>1r@1$8@1$0#5@3$3$1@3$4@1$0#5^1@3$6@1$0#5ZKv$2@2$7@1$0#5Z@1$5^1").
Proof. reflexivity. Qed.

Lemma is_x0_0 : ltac2:(zQ "80!ld!ua!hm5!hg5!hl7!hlc!hjf!hk4@3$4$1@1$5@3$6@1$0#5ZKv$3@2$7@1$0#5Z$2").
Proof. reflexivity. Qed.

Lemma bv_wrap64_mod : ltac2:(zQ "60!hmc!hl7!ld!ho8!hp2!hp9>1z$0@3$1$0@2$5@1$2#k0^1@2$3^1@2$4+2+k0").
Proof. reflexivity. Qed.

Lemma bv_wrap32_mod : ltac2:(zQ "60!hmc!hl7!ld!ho8!hp2!hp9>1z$0@3$1$0@2$5@1$2#i0^1@2$3^1@2$4+2+i0").
Proof. reflexivity. Qed.

Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof. intros n a. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma bv_eqb_neq : forall {n} (a b : bv n), a <> b -> bv_eqb a b = false.
Proof.
  intros n a b Hne. unfold bv_eqb. apply Z.eqb_neq.
  intro Hu. apply Hne. apply bv_eq. exact Hu.
Qed.

(* [comment removed for export] *)
Lemma arg_reg_0 : ltac2:(zQ "90!ld!s5!hg5!hl7!hq3!hqa!hjf!hk4!rb@3$3@1$1@1$0#5@2$8@1$0#5@2$4+a@1$5N0Kd@3$6@1$0#5+aKv$2@2$7@1$0#5+a@1$1@1$0#5").
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_1 : ltac2:(zQ "90!ld!s5!hg5!hl7!hq3!hqa!hjf!hk4!rb@3$3@1$1@1$0#5@2$8@1$0#5@2$4+a@1$5N1Kd@3$6@1$0#5+bKv$2@2$7@1$0#5+b@1$1@1$0#5").
Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_2 : ltac2:(zQ "90!ld!s5!hg5!hl7!hq3!hqa!hjf!hk4!rb@3$3@1$1@1$0#5@2$8@1$0#5@2$4+a@1$5N2Kd@3$6@1$0#5+cKv$2@2$7@1$0#5+c@1$1@1$0#5").
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_testbit_high : ltac2:(zQ "90!hmc!hr4!ua!hra!hs2!hl7!hs8!hp2!hse>1n$0>1a$0>1k$0>0@2$1Z^3>0@2$4@2$1Z^3@2$6^3@2$7+2^4>0@2$1^5^3@3$5$2@2$8^5^4$3").
Proof.
  intros n a k Hn [Ha1 Ha2] Hk.
  exact (proj1 (Z.bounded_iff_bits_nonneg n a Hn Ha1) Ha2 k Hk).
Qed.

Lemma Z_bounded_by_bits : ltac2:(zQ "80!hmc!hr4!ua!hra!hl7!hs8!hp2!hse>1n$0>1a$0>0@2$1Z^2>0@2$1Z^2>0>1k$0>0@2$1^5^1@3$4$2@2$7^5^2$3@2$5^4@2$6+2^5").
Proof.
  intros n a Hn Ha Hb. exact (proj2 (Z.bounded_iff_bits_nonneg n a Hn Ha) Hb).
Qed.

Lemma Z_land_range : ltac2:(zQ "60!hr4!hs2!hmc!ht9!hs8!hp2>1a$2>1b$2>0@2$1@2$0Z^2@2$4^2@2$5+2+k0>0@2$0Z^2@2$1@2$0Z@2$3^4^3@2$4@2$3^4^3@2$5+2+k0").
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.land_nonneg; lia |].
  intros k Hk. rewrite Z.land_spec.
  rewrite (Z_testbit_high 64 a k) by lia. reflexivity.
Qed.

Lemma Z_lor_range : ltac2:(zQ "61!hs2!hr4!hs8!hp2!hmc!hu1&@2$0@2$1Z^2@2$2^2@2$3+2+k0>1a$4>1b$4>0~0>0~0@2$0@2$1Z@2$5^4^3@2$2@2$5^4^3@2$3+2+k0").
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lor_nonneg; lia |].
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high 64 a k) by lia.
  rewrite (Z_testbit_high 64 b k) by lia.
  reflexivity.
Qed.

Lemma Z_lxor_range : ltac2:(zQ "61!hs2!hr4!hs8!hp2!hmc!hu8&@2$0@2$1Z^2@2$2^2@2$3+2+k0>1a$4>1b$4>0~0>0~0@2$0@2$1Z@2$5^4^3@2$2@2$5^4^3@2$3+2+k0").
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia| apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec.
  rewrite (Z_testbit_high 64 a k) by lia.
  rewrite (Z_testbit_high 64 b k) by lia.
  reflexivity.
Qed.

Lemma Z_shiftr_range : ltac2:(zQ "60!hr4!hs2!hmc!hs8!hp2!hv0>1a$2>1k$2>0@2$1@2$0Z^2@2$3^2@2$4+2+k0>0@2$0Z^2@2$1@2$0Z@2$5^4^3@2$3@2$5^4^3@2$4+2+k0").
Proof.
  intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with a; [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

(* [comment removed for export] *)
Lemma bv_swrap_add_idemp_l : ltac2:(zQ "60!hmc!hq3!hva!hl7!ig5!hp9>1n$4>1x$0>1y$0@3$3$0@2$2^3@2$1@2$5^3^2^1@2$2^3@2$1^2^1").
Proof.
  intros n x y. unfold bv_swrap. f_equal.
  replace (bv_wrap n x + y + bv_half_modulus n)%Z
    with (bv_wrap n x + (y + bv_half_modulus n))%Z by lia.
  rewrite bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma bv_swrap_add_idemp_r : ltac2:(zQ "60!hmc!hq3!hva!hl7!ig5!hp9>1n$4>1x$0>1y$0@3$3$0@2$2^3@2$1^2@2$5^3^1@2$2^3@2$1^2^1").
Proof.
  intros n x y. rewrite Z.add_comm, bv_swrap_add_idemp_l, Z.add_comm. reflexivity.
Qed.

Lemma bv_swrap_wrap' : ltac2:(zQ "50!hmc!hva!hl7!ig5!hp9>1n$3>1z$0@3$2$0@2$1^2@2$4^2^1@2$1^2^1").
Proof. intros. apply bv_swrap_wrap. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zsig : ltac2:(zQ "30!ld!hmc!s5>1x@1$2@1$0#k0$1") := ltac2:(zQ "30!ld!s5!ig9\1x@1$1@1$0#k0@2$2@1$0#k0^1").

Definition v_addi : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "60!ld!hmc!hq3!rb!s5!ih5\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_add : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ih5!hq3!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_sub : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ih5!ii3!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_mul : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ih5!iia!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_andi : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!ld!hmc!ht9!rb!s5!ih5!hp9\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_ori : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!ld!hmc!hu1!rb!s5!ih5!hp9\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_xori : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!ld!hmc!hu8!rb!s5!ih5!hp9\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1").
Definition v_and : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ih5!ht9!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_or : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ih5!hu1!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_xor : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ih5!hu8!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").

Definition c_eq : ltac2:(zQ "30!ld!s5!ua>1x@1$1@1$0#k0>1y@1$1@1$0#k0$2") := ltac2:(zQ "30!ld!s5!hg9\1x@1$1@1$0#k0\1y@1$1@1$0#k0@3$2@1$0#k0^2^1").
Definition c_lts : ltac2:(zQ "30!ld!s5!ua>1x@1$1@1$0#k0>1y@1$1@1$0#k0$2") := ltac2:(zQ "30!ld!s5!ij1\1x@1$1@1$0#k0\1y@1$1@1$0#k0@3$2@1$0#k0^2^1").
Definition c_ltu : ltac2:(zQ "30!ld!s5!ua>1x@1$1@1$0#k0>1y@1$1@1$0#k0$2") := ltac2:(zQ "30!ld!s5!ija\1x@1$1@1$0#k0\1y@1$1@1$0#k0@3$2@1$0#k0^2^1").

Definition btgt : ltac2:(zQ "30!ld!s5!hmc>2pc@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "40!ld!hmc!io3!s5\2pc@1$3@1$0#k0\3imm$1@2$2^2^1").

(* [comment removed for export] *)
Definition v_slti : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!ld!ua!rb!s5!hmc!iod!ip5\1x@1$3@1$0#k0\3imm$4M1\0$1@1$3@1$0#k0@2$6@1$5^2^1@2$2@1$0#k0+1@2$2@1$0#k0Z").
Definition v_sltiu : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "80!ld!ua!rb!s5!hmc!ip5!ih5!hp9\1x@1$3@1$0#k0\3imm$4M1\0$1@1$3@1$0#k0@2$5@2$6@1$0#k0^2@2$7@1$0#k0^1@2$2@1$0#k0+1@2$2@1$0#k0Z").
Definition v_slt : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ua!rb!ipc\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4^2^1@2$3@1$0#k0+1@2$3@1$0#k0Z").
Definition v_sltu : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!s5!ua!rb!iq5\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4^2^1@2$3@1$0#k0+1@2$3@1$0#k0Z").

(* [comment removed for export] *)
Definition v_slli : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!ld!hmc!iqe!rb!s5!ih5\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_srli : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!ld!hmc!hv0!rb!s5!ih5\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").
Definition v_srai : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "60!ld!hmc!hv0!rb!s5!ig9\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$2@2$5@1$0#k0^2^1").

(* [comment removed for export] *)
Definition v_sll : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!ld!s5!ih5!ho8!iqe!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+k0").
Definition v_srl : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!ld!s5!ih5!ho8!hv0!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+k0").
Definition v_sra : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!ld!s5!ho8!hv0!rb!ig9!ih5\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$5@1$0#k0^2@2$2@2$6@1$0#k0^1+k0").

(* [comment removed for export] *)
Definition v_lui : ltac2:(zQ "30!ld!hmc!s5>3imm$1@1$2@1$0#k0") := ltac2:(zQ "30!ld!hmc!rb\3imm$1@2$2@1$0#k0^1").
Definition v_auipc : ltac2:(zQ "30!ld!s5!hmc>2pc@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "60!ld!hmc!hq3!rb!s5!ih5\2pc@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2^1@2$5@1$0#k0^2").

(* [comment removed for export] *)
Definition v_addiw : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "70!ld!hmc!hq3!rb!s5!hva!ih5\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$6@1$0#k0^2^1").
Definition v_slliw : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "70!ld!hmc!iqe!rb!s5!hva!ih5\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$6@1$0#k0^2^1").
Definition v_srliw : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "80!ld!hmc!hv0!rb!s5!hva!ih5!hp9\1x@1$4@1$0#k0\2sh$1@2$3@1$0#k0@2$5@1$0#i0@2$2@2$7@1$0#i0@2$6@1$0#k0^2^1").
Definition v_sraiw : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>2sh$2@1$1@1$0#k0") := ltac2:(zQ "70!ld!hva!hmc!hv0!rb!s5!ih5\1x@1$5@1$0#k0\2sh$2@2$4@1$0#k0@2$1@1$0#i0@2$3@2$1@1$0#i0@2$6@1$0#k0^2^1").
Definition v_addw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!ld!s5!ih5!hq3!rb!hva\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_subw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!ld!s5!ih5!ii3!rb!hva\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition v_sllw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!ld!s5!ih5!ho8!iqe!rb!hva\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$6@1$0#i0@2$4@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+i0").
Definition v_srlw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!ld!s5!ih5!ho8!hv0!rb!hva!hp9\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$6@1$0#i0@2$4@2$7@1$0#i0@2$2@1$0#k0^2@2$3@2$2@1$0#k0^1+i0").
Definition v_sraw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!ld!s5!hva!ih5!ho8!hv0!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$6@1$0#k0@2$2@1$0#i0@2$5@2$2@1$0#i0@2$3@1$0#k0^2@2$4@2$3@1$0#k0^1+i0").

(* [comment removed for export] *)
Definition v_mulh : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!ld!s5!ig9!iia!hv0!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1+k0").
Definition v_mulhsu : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "70!ld!s5!iia!hv0!rb!ig9!ih5\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$3@2$2@2$5@1$0#k0^2@2$6@1$0#k0^1+k0").
Definition v_mulhu : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!ld!s5!ih5!iia!hv0!rb\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$5@1$0#k0@2$4@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1+k0").
Definition v_mulw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!ld!s5!ih5!iia!rb!hva\1x@1$1@1$0#k0\1y@1$1@1$0#k0@2$4@1$0#k0@2$5@1$0#i0@2$3@2$2@1$0#k0^2@2$2@1$0#k0^1").

(* [comment removed for export] *)
Definition v_div : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!ld!s5!ua!iod!rb!ir8!irf!ih5\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$5@2$7@1$0#k0^1Z@2$4@1$0#k0-1@2$4@1$0#k0@2$6@1$3^2@1$3^1").
Definition v_rem : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!ld!s5!ua!iod!ir8!is7!rb!ih5\1x@1$1@1$0#k0\1y@1$1@1$0#k0M2\0$2@1$1@1$0#k0@2$4@2$7@1$0#k0^1Z^2@2$6@1$0#k0@2$5@1$3^2@1$3^1").
Definition v_divw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "90!ld!s5!hva!ih5!ua!rb!ir8!irf!hp9\1x@1$1@1$0#k0\1y@1$1@1$0#k0M4\0$4@1$1@1$0#k0@2$6@2$8@1$0#i0@2$3@1$0#k0^1Z@2$5@1$0#k0-1@2$5@1$0#k0@2$2@1$0#i0@2$7@2$2@1$0#i0@2$3@1$0#k0^2@2$2@1$0#i0@2$3@1$0#k0^1").
Definition v_remw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!ld!hva!ih5!s5!ua!rb!ir8!is7!hp9&@2$1@1$0#i0@2$2@1$0#k0^2\1x@1$3@1$0#k0\1y@1$3@1$0#k0M4\0$4@1$3@1$0#k0@2$6@2$8@1$0#i0@2$2@1$0#k0^1Z@2$5@1$0#k0~0@2$5@1$0#k0@2$1@1$0#i0@2$7~0@2$1@1$0#i0@2$2@1$0#k0^1").
Definition v_divuw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!ld!s5!ih5!hp9!ua!rb!ise!ir8!hva&@2$3@1$0#i0@2$2@1$0#k0^1\1x@1$1@1$0#k0\1y@1$1@1$0#k0M4\0$4@1$1@1$0#k0@2$7~0Z@2$5@1$0#k0-1@2$5@1$0#k0@2$8@1$0#i0@2$6@2$3@1$0#i0@2$2@1$0#k0^2~0").
Definition v_remuw : ltac2:(zQ "20!ld!s5>1x@1$1@1$0#k0>1y@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "91!ld!ih5!s5!hp9!ua!rb!hva!ir8!ho8&@2$3@1$0#i0@2$1@1$0#k0^1\1x@1$2@1$0#k0\1y@1$2@1$0#k0M4\0$4@1$2@1$0#k0@2$7~0Z@2$5@1$0#k0@2$6@1$0#i0@2$1@1$0#k0^2@2$5@1$0#k0@2$6@1$0#i0@2$8@2$3@1$0#i0@2$1@1$0#k0^2~0").

(* [comment removed for export] *)
Definition v_lb : ltac2:(zQ "20!ld!s5>1b@1$1@1$0#8@1$1@1$0#k0") := ltac2:(zQ "40!ld!rb!s5!ig9\1b@1$2@1$0#8@2$1@1$0#k0@2$3@1$0#8^1").
Definition v_lh : ltac2:(zQ "20!ld!s5>1v@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!rb!s5!hva!ih5\1v@1$2@1$0#k0@2$1@1$0#k0@2$3@1$0#h0@2$4@1$0#k0^1").
Definition v_lw : ltac2:(zQ "20!ld!s5>1v@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "50!ld!rb!s5!hva!ih5\1v@1$2@1$0#k0@2$1@1$0#k0@2$3@1$0#i0@2$4@1$0#k0^1").

(* [comment removed for export] *)
Definition jalr_tgtZ : ltac2:(zQ "30!hmc!ld!s5>1x@1$2@1$1#k0>3imm$0$0") := ltac2:(zQ "60!ld!hmc!hq3!ht9!s5!ih5\1x@1$4@1$0#k0\3imm$1@2$3@2$2@2$5@1$0#k0^2^1-2").
Definition jalr_tgt : ltac2:(zQ "30!ld!s5!hmc>1x@1$1@1$0#k0>3imm$2@1$1@1$0#k0") := ltac2:(zQ "50!ld!hmc!it5!rb!s5\1x@1$4@1$0#k0\3imm$1@2$3@1$0#k0@2$2^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg_rom : ltac2:(zQ "50!ld!s5!iu2!iu9!ji7>4segs@1$2$4>0@1$1@1$0#k0@1$3@1$1@1$0#8") := ltac2:(zQ "80!ld!s5!iu2!iu9!jj2!jj9!ji7!jn7\4segs@1$2$6\4addr@1$1@1$0#k0M3\1x@1$3@1$2@1$1@1$0#8@1$3@1$1@1$0#8@3$7^2^1@1$0#1\1l@1$2@1$1@1$0#8M2\1l@1$2@1$1@1$0#8@1$3@1$1@1$0#8^1@1$4@1$1@1$0#8\1b@1$1@1$0#8\2l0@1$2@1$1@1$0#8@2$5@1$1@1$0#8^2@1$4@1$1@1$0#8").

Fixpoint rdn (segs : list Segment) (mem : word -> option byte) (a : word) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' =>
    match (match mem a with Some b => Some b | None => seg_rom segs a end) with
    | Some b => match rdn segs mem (a+1) n' with Some rest => Some (b :: rest) | None => None end
    | None => None
    end
  end.

(* [comment removed for export] *)
Lemma ov_rdn : ltac2:(zQ "90!ld!s5!iu2!iu9!jo6!hl7!ji7!joc!jpd>4segs@1$2$6>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1n$4>1a@1$1@1$0#k0@3$5@1$3@1$2@1$1@1$0#8@4$7^4^3^1^2@4$8^4^3^1^2").
Proof.
  intros segs mem n. induction n as [|n' IH]; intro a; [reflexivity|].
  simpl. unfold seg_rom.
  destruct (mem a) as [b|].
  - rewrite IH. reflexivity.
  - destruct (memory_read segs a 1) as [[|b rest]|]; [reflexivity| rewrite IH; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma le_word_1 : ltac2:(zQ "80!ld!s5!jq4!jqb!hl7!ju0!rb!ih5>1b@1$1@1$0#8@3$4@1$1@1$0#k0@1$5@3$2@1$1@1$0#8^1@1$3@1$1@1$0#8@2$6@1$0#k0@2$7@1$0#8^1").
Proof.
  intro b. unfold le_bytes_to_word. cbn [bytes_le_to_Z].
  rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

Lemma le_word_v : ltac2:(zQ "80!ld!s5!hl7!iu2!hmc!jv5!ju0!ih5>2bs@1$3@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2$4@1$5^2@2$7@1$0#k0^1@3$2@1$1@1$0#k0@1$6^3^2").
Proof.
  intros bs v Hv. unfold le_bytes_to_word. rewrite Hv.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma b_extract8_id : ltac2:(zQ "70!ld!s5!hl7!kg6!rb!kgb!ih5>1b@1$1@1$0#8@3$2@1$1@1$0#8@4$5@1$0#k0$3@1$0#8@2$4@1$0#k0@2$6@1$0#8^1^1").
Proof.
  intro b. apply bv_eq.
  rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r.
  pose proof (bv_unsigned_in_range _ b) as Hb.
  change (bv_modulus 8) with 256%Z in Hb.
  rewrite (bv_wrap_small 64) by (change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma b_lb_val : ltac2:(zQ "a0!ld!s5!jq4!jqb!hl7!kg6!ju0!kh8!khf!kgb>1b@1$1@1$0#8@3$4@1$1@1$0#k0@3$7@1$0#8@1$0#k0@4$9@1$0#k0$5@1$0#8@1$6@3$2@1$1@1$0#8^1@1$3@1$1@1$0#8@1$8^1").
Proof.
  intro b. rewrite le_word_1, b_extract8_id. apply bv_eq.
  unfold sext, v_lb. rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  reflexivity.
Qed.

Lemma b_lh_val : ltac2:(zQ "70!ld!s5!hl7!kg6!kh8!ki7!kgb>1v@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4@1$0#h0@1$0#k0@4$6@1$0#k0$3@1$0#h0^1@1$5^1").
Proof.
  intro v. apply bv_eq. unfold sext, v_lh.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  f_equal. unfold bv_signed.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_swrap_wrap.
Qed.

Lemma b_lw_val : ltac2:(zQ "70!ld!s5!hl7!kg6!kh8!kif!kgb>1v@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@4$6@1$0#k0$3@1$0#i0^1@1$5^1").
Proof.
  intro v. apply bv_eq. unfold sext, v_lw.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  f_equal. unfold bv_signed.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_swrap_wrap.
Qed.

Lemma rdn_length : ltac2:(zQ "a0!ld!s5!iu2!jo6!iu9!hl7!jj9!kj7!ji7!jpd>4segs@1$2$8>3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8>1n$3>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>0@3$5@1$4@1$2@1$1@1$0#8@4$9^5^4^2^3@2$6@1$2@1$1@1$0#8^1@3$5$3@2$7@1$1@1$0#8^2^4").
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs H; cbn in H.
  - inversion H; reflexivity.
  - destruct (match mem a with Some b => Some b | None => seg_rom segs a end); [|discriminate].
    destruct (rdn segs mem (a+1) n) eqn:E; [|discriminate].
    inversion H; subst; cbn. f_equal. eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_nonneg : ltac2:(zQ "50!iu2!ld!jv5!hr4!s5>2bs@1$0@1$4@1$1#8@2$3Z@1$2^1").
Proof.
  induction bs as [|b bs IH]; cbn; [lia|].
  apply Z.lor_nonneg. split.
  - pose proof (bv_unsigned_in_range _ b). lia.
  - apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma bytes_le_to_Z_bound : ltac2:(zQ "90!ld!s5!kj7!iu2!jv5!hs8!iia!hqa!hp2>2bs@1$3@1$1@1$0#8@2$5@1$4^1@2$8+2@2$6+8@1$7@2$2@1$1@1$0#8^1").
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bytes_le_to_Z_nonneg bs).
  pose proof (bv_unsigned_in_range _ b) as Hb.
  change (bv_modulus 8) with 256%Z in Hb.
  apply Z_bounded_by_bits; [lia| |].
  { apply Z.lor_nonneg. split; [lia|]. apply Z.shiftl_nonneg. lia. }
  intros k Hk. rewrite Z.lor_spec.
  rewrite (Z_testbit_high 8 (bv_unsigned b) k) by lia.
  rewrite Z.shiftl_spec by lia.
  rewrite (Z_testbit_high (8 * Z.of_nat (length bs)) (bytes_le_to_Z bs) (k - 8)) by lia.
  reflexivity.
Qed.

Lemma bytes_le_app : ltac2:(zQ "c0!ld!s5!jv5!iu2!kk0!kj7!hl7!hmc!hu1!iia!hqa!iqe>2xs@1$3@1$1@1$0#8>2ys@1$3@1$1@1$0#8@3$6$7@1$2@3$4@1$1@1$0#8^2^1@2$8@1$2^2@2$b@1$2^1@2$9+8@1$a@2$5@1$1@1$0#8^2").
Proof.
  induction xs as [|x xs IH]; intro ys; cbn [bytes_le_to_Z app length].
  - rewrite Z.mul_0_r, Z.shiftl_0_r, Z.lor_0_l. reflexivity.
  - rewrite IH.
    rewrite Z.shiftl_lor, Z.shiftl_shiftl by lia.
    rewrite Z.lor_assoc. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_range : ltac2:(zQ "70!ld!ih5!hs2!hr4!hs8!hp2!s5>1x@1$6@1$0#k0@2$2@2$3Z@2$1@1$0#k0^1@2$4@2$1@1$0#k0^1@2$5+2+k0").
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.

Lemma u8_range : ltac2:(zQ "60!ld!ih5!hs2!hr4!hs8!s5>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
Proof. intro b. exact (bv_unsigned_in_range _ b). Qed.

Lemma u6_range : ltac2:(zQ "60!ld!ih5!hs2!hr4!hs8!s5>1s@1$5@1$0#6@2$2@2$3Z@2$1@1$0#6^1@2$4@2$1@1$0#6^1+k0").
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.

Lemma u5_range : ltac2:(zQ "60!ld!ih5!hs2!hr4!hs8!s5>1s@1$5@1$0#5@2$2@2$3Z@2$1@1$0#5^1@2$4@2$1@1$0#5^1+i0").
Proof. intro s. exact (bv_unsigned_in_range _ s). Qed.

Lemma wrap64_range : ltac2:(zQ "70!ld!hp9!hs2!hmc!hr4!hs8!hp2>1z$3@2$2@2$4Z@2$1@1$0#k0^1@2$5@2$1@1$0#k0^1@2$6+2+k0").
Proof. intro z. exact (bv_wrap_in_range 64 z). Qed.

(* [comment removed for export] *)
Lemma bv_swrap_congr : ltac2:(zQ "50!hmc!hl7!hva!hp9!ig5>1n$4>1x$0>1y$0>0@3$1$0@2$3^3^2@2$3^3^1@3$1$0@2$2^4^3@2$2^4^2").
Proof.
  intros n x y H. unfold bv_swrap. f_equal.
  rewrite <- (bv_wrap_add_idemp_l n x), H, bv_wrap_add_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma b_addsext : forall (a : word) {n} (imm : bv n),
  a + sext 64 imm = v_addi a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_addi, sext.
  rewrite bv_add_unsigned, bv_sign_extend_unsigned, Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

Lemma b_npc4 : ltac2:(zQ "60!ld!s5!hl7!io3!rb!kk6>1p@1$1@1$0#k0@3$2@1$1@1$0#k0@3$5@1$0#k0^1@2$4@1$0#k0+4@2$3^1+4").
Proof.
  intros. apply bv_eq. unfold v_addi.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  apply bv_wrap_add_idemp_r.
Qed.

Lemma alu_addi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_ADD a (sext 64 imm) = v_addi a (bv_signed imm).
Proof. intros. apply b_addsext. Qed.

Lemma alu_andi : forall (a : word) {n} (imm : bv n),
  alu64 ALU_AND a (sext 64 imm) = v_andi a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_andi.
  change (alu64 ALU_AND a (sext 64 imm)) with (bv_and a (sext 64 imm)).
  rewrite bv_and_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_land_range; [apply u64_range | apply wrap64_range].
Qed.

Lemma alu_ori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_OR a (sext 64 imm) = v_ori a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_ori.
  change (alu64 ALU_OR a (sext 64 imm)) with (bv_or a (sext 64 imm)).
  rewrite bv_or_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lor_range; [apply u64_range | apply wrap64_range].
Qed.

Lemma alu_xori : forall (a : word) {n} (imm : bv n),
  alu64 ALU_XOR a (sext 64 imm) = v_xori a (bv_signed imm).
Proof.
  intros. apply bv_eq. unfold v_xori.
  change (alu64 ALU_XOR a (sext 64 imm)) with (bv_xor a (sext 64 imm)).
  rewrite bv_xor_unsigned. unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lxor_range; [apply u64_range | apply wrap64_range].
Qed.

Lemma alu_slti : ltac2:(zQ "80!ld!s5!hl7!kn3!kh8!kne!ko7!ig9>1a@1$1@1$0#k0>3imm@1$1@1$0#c@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#c@1$0#k0^1@2$6^2@2$7@1$0#c^1").
Proof.
  intros. unfold v_slti, zsig.
  change (alu64 ALU_SLT a (sext 64 imm))
    with (if bv_lts a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0).
  unfold bv_lts, sext.
  rewrite bv_sign_extend_signed by lia.
  reflexivity.
Qed.

Lemma alu_sltiu : forall (a : word) {n} (imm : bv n),
  alu64 ALU_SLTU a (sext 64 imm) = v_sltiu a (bv_signed imm).
Proof.
  intros. unfold v_sltiu.
  change (alu64 ALU_SLTU a (sext 64 imm))
    with (if bv_ltu a (sext 64 imm) then Z_to_bv 64 1 else Z_to_bv 64 0).
  unfold bv_ltu, sext.
  rewrite bv_sign_extend_unsigned.
  reflexivity.
Qed.

Lemma alu_add : ltac2:(zQ "60!ld!s5!hl7!kp1!kne!kpc>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma alu_sub : ltac2:(zQ "60!ld!s5!hl7!kq5!kne!kr0>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma alu_slt : ltac2:(zQ "60!ld!s5!hl7!kn3!kne!kr9>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma alu_sltu : ltac2:(zQ "60!ld!s5!hl7!ks2!kne!kse>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma alu_and : ltac2:(zQ "60!ld!s5!hl7!kt8!kne!ku3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
  intros. apply bv_eq. unfold v_and.
  change (alu64 ALU_AND a b) with (bv_and a b).
  rewrite bv_and_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_land_range; [apply u64_range | apply u64_range].
Qed.

Lemma alu_or : ltac2:(zQ "60!ld!s5!hl7!kuc!kne!kv6>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
  intros. apply bv_eq. unfold v_or.
  change (alu64 ALU_OR a b) with (bv_or a b).
  rewrite bv_or_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lor_range; apply u64_range.
Qed.

Lemma alu_xor : ltac2:(zQ "60!ld!s5!hl7!kve!kne!lg9>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
  intros. apply bv_eq. unfold v_xor.
  change (alu64 ALU_XOR a b) with (bv_xor a b).
  rewrite bv_xor_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  apply Z_lxor_range; apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma shamt6_mask : ltac2:(zQ "80!ld!ih5!hl7!hmc!lh2!rb!s5!lh9>1s@1$6@1$0#6@3$2$3@2$1@1$0#k0@3$7@1$0#k0@3$4@1$0#6@1$0#k0^1@2$5@1$0#k0+jf@2$1@1$0#6^1").
Proof.
  intro s. rewrite bv_and_unsigned. unfold zext.
  rewrite bv_zero_extend_unsigned by lia.
  rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
  change 63%Z with (Z.ones 6).
  rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2^6)%Z with 64%Z. apply u6_range.
Qed.

Lemma regamt64_mask : ltac2:(zQ "80!ld!ih5!hl7!hmc!ho8!rb!s5!lh9>1b@1$6@1$0#k0@3$2$3@2$1@1$0#k0@3$7@1$0#k0^1@2$5@1$0#k0+jf@2$4@2$1@1$0#k0^1+k0").
Proof.
  intro b. rewrite bv_and_unsigned.
  rewrite Z_to_bv_small by (change (bv_modulus 64) with (2^64)%Z; lia).
  change 63%Z with (Z.ones 6).
  rewrite Z.land_ones by lia.
  reflexivity.
Qed.

Lemma alu_slli : ltac2:(zQ "80!ld!s5!hl7!li2!lh2!kne!lid!ih5>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
  intros. apply bv_eq. unfold v_slli.
  change (alu64 ALU_SLL a (zext 64 s)) with (a ≪ bv_and (zext 64 s) (Z_to_bv 64 63)).
  rewrite bv_shiftl_unsigned, Z_to_bv_unsigned, shamt6_mask.
  reflexivity.
Qed.

Lemma alu_srli : ltac2:(zQ "80!ld!s5!hl7!lj7!lh2!kne!lk2!ih5>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
  intros. apply bv_eq. unfold v_srli.
  change (alu64 ALU_SRL a (zext 64 s)) with (a ≫ bv_and (zext 64 s) (Z_to_bv 64 63)).
  rewrite bv_shiftr_unsigned, Z_to_bv_unsigned, shamt6_mask.
  symmetry; apply bv_wrap_small.
  apply Z_shiftr_range; [apply u64_range | apply u6_range].
Qed.

Lemma alu_srai : ltac2:(zQ "80!ld!s5!hl7!lkc!lh2!kne!ll7!ih5>1a@1$1@1$0#k0>1s@1$1@1$0#6@3$2@1$1@1$0#k0@3$5$3^2@3$4@1$0#6@1$0#k0^1@2$6^2@2$7@1$0#6^1").
Proof.
  intros. apply bv_eq. unfold v_srai.
  change (alu64 ALU_SRA a (zext 64 s))
    with (bv_ashiftr a (bv_and (zext 64 s) (Z_to_bv 64 63))).
  rewrite bv_ashiftr_unsigned, Z_to_bv_unsigned, shamt6_mask.
  reflexivity.
Qed.

Lemma alu_sll : ltac2:(zQ "60!ld!s5!hl7!li2!kne!lm1>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
  intros. apply bv_eq. unfold v_sll.
  change (alu64 ALU_SLL a b) with (a ≪ bv_and b (Z_to_bv 64 63)).
  rewrite bv_shiftl_unsigned, Z_to_bv_unsigned, regamt64_mask.
  reflexivity.
Qed.

Lemma alu_srl : ltac2:(zQ "60!ld!s5!hl7!lj7!kne!lma>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
  intros. apply bv_eq. unfold v_srl.
  change (alu64 ALU_SRL a b) with (a ≫ bv_and b (Z_to_bv 64 63)).
  rewrite bv_shiftr_unsigned, Z_to_bv_unsigned, regamt64_mask.
  symmetry; apply bv_wrap_small.
  apply Z_shiftr_range; [apply u64_range |].
  pose proof (Z.mod_pos_bound (bv_unsigned b) 64 ltac:(lia)). lia.
Qed.

Lemma alu_sra : ltac2:(zQ "60!ld!s5!hl7!lkc!kne!ln3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4$3^2^1@2$5^2^1").
Proof.
  intros. apply bv_eq. unfold v_sra.
  change (alu64 ALU_SRA a b) with (bv_ashiftr a (bv_and b (Z_to_bv 64 63))).
  rewrite bv_ashiftr_unsigned, Z_to_bv_unsigned, regamt64_mask.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma low32_unsigned : ltac2:(zQ "70!ld!ih5!hl7!hmc!lnc!s5!hp9>1a@1$5@1$0#k0@3$2$3@2$1@1$0#i0@1$4^1@2$6@1$0#i0@2$1@1$0#k0^1").
Proof.
  intro a. unfold low32. rewrite bv_extract_unsigned.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma low32_signed : ltac2:(zQ "80!ld!hl7!hmc!lnc!s5!ig9!hva!ih5>1a@1$4@1$0#k0@3$1$2@2$5@1$0#i0@1$3^1@2$6@1$0#i0@2$7@1$0#k0^1").
Proof.
  intro a. unfold low32. rewrite bv_extract_signed.
  change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shamt5_mask : ltac2:(zQ "80!ld!ih5!hl7!hmc!lh2!rb!s5!lh9>1s@1$6@1$0#5@3$2$3@2$1@1$0#i0@3$7@1$0#i0@3$4@1$0#5@1$0#i0^1@2$5@1$0#i0+hf@2$1@1$0#5^1").
Proof.
  intro s. rewrite bv_and_unsigned. unfold zext.
  rewrite bv_zero_extend_unsigned by lia.
  rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
  change 31%Z with (Z.ones 5).
  rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2^5)%Z with 32%Z. apply u5_range.
Qed.

Lemma regamt32_mask : ltac2:(zQ "90!ld!ih5!hl7!hmc!lnc!ho8!rb!s5!lh9>1b@1$7@1$0#k0@3$2$3@2$1@1$0#i0@3$8@1$0#i0@1$4^1@2$6@1$0#i0+hf@2$5@2$1@1$0#k0^1+i0").
Proof.
  intro b. rewrite bv_and_unsigned, low32_unsigned.
  rewrite Z_to_bv_small by (change (bv_modulus 32) with (2^32)%Z; lia).
  change 31%Z with (Z.ones 5).
  rewrite Z.land_ones by lia.
  rewrite bv_wrap32_mod.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia|lia|].
  exists (2^27)%Z. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sext32_unsigned : ltac2:(zQ "80!ld!ih5!hl7!hmc!kh8!s5!hva!hp9>1v@1$5@1$0#i0@3$2$3@2$1@1$0#k0@3$4@1$0#i0@1$0#k0^1@2$7@1$0#k0@2$6@1$0#i0@2$1@1$0#i0^1").
Proof.
  intro v. unfold sext. rewrite bv_sign_extend_unsigned. reflexivity.
Qed.

Lemma w_addiw : ltac2:(zQ "90!ld!s5!kh8!hl7!kp1!lo5!lnc!loe!ig9>1a@1$1@1$0#k0>3imm@1$1@1$0#c@3$3@1$1@1$0#k0@3$2@1$0#i0@1$0#k0@3$5$4@1$6^2@3$2@1$0#c@1$0#i0^1@2$7^2@2$8@1$0#c^1").
Proof.
  intros. apply bv_eq. unfold v_addiw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_ADD (low32 a) (sext 32 imm)) with (low32 a + sext 32 imm).
  rewrite bv_add_unsigned, low32_unsigned.
  unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r.
  reflexivity.
Qed.

Lemma w_slliw : ltac2:(zQ "a0!ld!s5!hl7!li2!kh8!lh2!lo5!lnc!lp9!ih5>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
  intros. apply bv_eq. unfold v_slliw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SLL (low32 a) (zext 32 s))
    with (low32 a ≪ bv_and (zext 32 s) (Z_to_bv 32 31)).
  rewrite bv_shiftl_unsigned, shamt5_mask, low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  rewrite !Z.shiftl_mul_pow2 by apply u5_range.
  rewrite !bv_wrap32_mod.
  apply Z.mul_mod_idemp_l. lia.
Qed.

Lemma w_srliw : ltac2:(zQ "a0!ld!s5!hl7!lj7!kh8!lh2!lo5!lnc!lq4!ih5>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
  intros. apply bv_eq. unfold v_srliw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRL (low32 a) (zext 32 s))
    with (low32 a ≫ bv_and (zext 32 s) (Z_to_bv 32 31)).
  rewrite bv_shiftr_unsigned, shamt5_mask, low32_unsigned.
  reflexivity.
Qed.

Lemma w_sraiw : ltac2:(zQ "a0!ld!s5!hl7!lkc!kh8!lh2!lo5!lnc!lqf!ih5>1a@1$1@1$0#k0>1s@1$1@1$0#5@3$2@1$1@1$0#k0@3$4@1$0#i0@1$0#k0@3$6$3@1$7^2@3$5@1$0#5@1$0#i0^1@2$8^2@2$9@1$0#5^1").
Proof.
  intros. apply bv_eq. unfold v_sraiw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRA (low32 a) (zext 32 s))
    with (bv_ashiftr (low32 a) (bv_and (zext 32 s) (Z_to_bv 32 31))).
  rewrite bv_ashiftr_unsigned, shamt5_mask, low32_signed.
  rewrite bv_swrap_wrap'. reflexivity.
Qed.

Lemma w_addw : ltac2:(zQ "80!ld!s5!lnc!hl7!kp1!kh8!lo5!lra>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. apply bv_eq. unfold v_addw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_ADD (low32 a) (low32 b)) with (low32 a + low32 b).
  rewrite bv_add_unsigned, !low32_unsigned.
  rewrite bv_swrap_wrap', bv_swrap_add_idemp_l, bv_swrap_add_idemp_r.
  reflexivity.
Qed.

Lemma w_subw : ltac2:(zQ "80!ld!s5!lnc!hl7!kq5!kh8!lo5!ls4>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. apply bv_eq. unfold v_subw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SUB (low32 a) (low32 b)) with (low32 a - low32 b).
  rewrite bv_sub_unsigned, !low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  rewrite !bv_wrap32_mod.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.

Lemma w_sllw : ltac2:(zQ "80!ld!s5!lnc!hl7!li2!kh8!lo5!lse>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. apply bv_eq. unfold v_sllw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SLL (low32 a) (low32 b))
    with (low32 a ≪ bv_and (low32 b) (Z_to_bv 32 31)).
  rewrite bv_shiftl_unsigned, regamt32_mask, low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  pose proof (Z.mod_pos_bound (bv_unsigned b) 32 ltac:(lia)).
  rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite !bv_wrap32_mod.
  apply Z.mul_mod_idemp_l. lia.
Qed.

Lemma w_srlw : ltac2:(zQ "80!ld!s5!lnc!hl7!lj7!kh8!lo5!lt8>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. apply bv_eq. unfold v_srlw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRL (low32 a) (low32 b))
    with (low32 a ≫ bv_and (low32 b) (Z_to_bv 32 31)).
  rewrite bv_shiftr_unsigned, regamt32_mask, low32_unsigned.
  reflexivity.
Qed.

Lemma w_sraw : ltac2:(zQ "80!ld!s5!lnc!hl7!lkc!kh8!lo5!lu2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@3$6$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. apply bv_eq. unfold v_sraw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_SRA (low32 a) (low32 b))
    with (bv_ashiftr (low32 a) (bv_and (low32 b) (Z_to_bv 32 31))).
  rewrite bv_ashiftr_unsigned, regamt32_mask, low32_signed.
  rewrite bv_swrap_wrap'. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_mul : ltac2:(zQ "60!ld!s5!hl7!luc!lv5!mg0>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma m_mulh : ltac2:(zQ "60!ld!s5!hl7!mg9!lv5!mh3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma m_mulhsu : ltac2:(zQ "60!ld!s5!hl7!mhd!lv5!mi9>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma m_mulhu : ltac2:(zQ "60!ld!s5!hl7!mj5!lv5!mk0>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma m_div : ltac2:(zQ "60!ld!s5!hl7!mkb!lv5!ml4>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma m_rem : ltac2:(zQ "60!ld!s5!hl7!mld!lv5!mm6>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^2^1@2$5^2^1").
Proof. reflexivity. Qed.

Lemma w_mulw : ltac2:(zQ "80!ld!s5!lnc!hl7!luc!kh8!lv5!mmf>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. apply bv_eq. unfold v_mulw.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  change (mul_div M_MUL (low32 a) (low32 b)) with (low32 a * low32 b).
  rewrite bv_mul_unsigned, !low32_unsigned.
  rewrite bv_swrap_wrap'.
  apply bv_swrap_congr.
  rewrite !bv_wrap32_mod.
  rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma div0_32 : ltac2:(zQ "80!ld!ir8!ih5!ua!hl7!lnc!s5!hp9>1b@1$6@1$0#k0@3$4$3@2$1@2$2@1$0#i0@1$5^1Z@2$1@2$7@1$0#i0@2$2@1$0#k0^1Z").
Proof. intro b. rewrite low32_unsigned. reflexivity. Qed.

Lemma w_divw : ltac2:(zQ "80!ld!s5!lnc!hl7!mkb!kh8!lv5!mn9>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. unfold mul_div, v_divw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
    rewrite bv_quots_unsigned, bv_swrap_wrap', !low32_signed.
    reflexivity.
Qed.

Lemma w_remw : ltac2:(zQ "80!ld!s5!lnc!hl7!mld!kh8!lv5!mo3>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. unfold mul_div, v_remw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned, low32_unsigned.
    rewrite bv_swrap_wrap'. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
    rewrite bv_rems_unsigned, bv_swrap_wrap', !low32_signed.
    reflexivity.
Qed.

Lemma w_divuw : ltac2:(zQ "80!ld!s5!lnc!hl7!mod!kh8!lv5!mp7>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. unfold mul_div, v_divuw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
    f_equal; rewrite ?bv_divu_unsigned, ?low32_unsigned; reflexivity.
Qed.

Lemma w_remuw : ltac2:(zQ "80!ld!s5!lnc!hl7!mq2!kh8!lv5!mqc>1a@1$1@1$0#k0>1b@1$1@1$0#k0@3$3@1$1@1$0#k0@3$5@1$0#i0@1$0#k0@4$6@1$0#i0$4@1$2^2@1$2^1@2$7^2^1").
Proof.
  intros. unfold mul_div, v_remuw.
  rewrite div0_32.
  destruct (bv_wrap 32 (bv_unsigned b) =? 0)%Z.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned, low32_unsigned.
    rewrite bv_swrap_wrap'. reflexivity.
  - apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
    f_equal; rewrite ?bv_modu_unsigned, ?low32_unsigned; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_swrap_hi : ltac2:(zQ "b0!hl7!ig5!hmc!mr7!ms4!kg6!hr4!hs8!ii3!msa!hva>1n$1>1z$2>0@1$4@3$0$1^2$5>0@2$6@1$9^3^2>0@2$7^3@1$3^4@3$0$2@2$a^5^4@2$8^4@1$3^5").
Proof.
  intros n z Hn Hlo Hhi. unfold bv_swrap, bv_wrap.
  pose proof (bv_half_modulus_twice n Hn) as Htw.
  pose proof (bv_modulus_pos n) as Hpos.
  replace (z + bv_half_modulus n)%Z
    with ((z + bv_half_modulus n - bv_modulus n) + 1 * bv_modulus n)%Z by lia.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small by lia.
  lia.
Qed.

Lemma b_lui : ltac2:(zQ "90!ld!s5!hl7!kh8!mtc!iqe!rb!mu5!ig9>3imm@1$1@1$0#h4@3$2@1$1@1$0#k0@3$3@1$0#i0@1$0#k0@5$7@1$0#i0@1$0#h4@1$0#c^1@2$6@1$0#cZ@1$4@2$5@2$8@1$0#h4^1+c").
Proof.
  intros imm. apply bv_eq. unfold v_lui.
  rewrite sext32_unsigned, Z_to_bv_unsigned. f_equal.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite (Z_to_bv_small 12 0) by (change (bv_modulus 12) with (2^12)%Z; lia).
  rewrite Z.lor_0_r.
  unfold bv_signed.
  pose proof (bv_unsigned_in_range _ imm) as Hr.
  change (bv_modulus 20) with (2^20)%Z in Hr.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (Z.of_N 12) with 12%Z.
  destruct (Z.lt_ge_cases (bv_unsigned imm) (2^19)) as [Hlt|Hge].
  - rewrite (bv_swrap_small 32)
      by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    rewrite (bv_swrap_small 20)
      by (change (bv_half_modulus 20) with (2^19)%Z; lia).
    reflexivity.
  - rewrite (bv_swrap_hi 32)
      by first [discriminate
               |change (bv_half_modulus 32) with (2^31)%Z;
                change (bv_modulus 32) with (2^32)%Z; lia].
    rewrite (bv_swrap_hi 20)
      by first [discriminate
               |change (bv_half_modulus 20) with (2^19)%Z;
                change (bv_modulus 20) with (2^20)%Z; lia].
    change (bv_modulus 32) with (2^32)%Z.
    change (bv_modulus 20) with (2^20)%Z.
    lia.
Qed.

Lemma b_auipc : ltac2:(zQ "a0!ld!s5!hl7!kh8!mv1!iqe!rb!kk6!mu5!ig9>1p@1$1@1$0#k0>3imm@1$1@1$0#h4@3$2@1$1@1$0#k0@3$7@1$0#k0^2@3$3@1$0#i0@1$0#k0@5$8@1$0#i0@1$0#h4@1$0#c^1@2$6@1$0#cZ@2$4^2@2$5@2$9@1$0#h4^1+c").
Proof.
  intros. rewrite b_lui. apply bv_eq. unfold v_lui, v_auipc.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_r. f_equal. lia.
Qed.

Lemma Z_land_m2_wrap : ltac2:(zQ "50!ld!hp9!hmc!ht9!hl7>1z$2@3$4$2@2$3@2$1@1$0#k0^1@2$1@1$0#k0-2@2$1@1$0#k0@2$3^1-2").
Proof.
  intro z. rewrite !bv_wrap64_mod.
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  destruct (Z.lt_ge_cases k 64) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite Z.land_spec. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia.
    apply andb_false_r.
Qed.

Lemma b_jalr : ltac2:(zQ "a0!ld!s5!hl7!kh8!mvc!rb!kk6!lh9!ng8!ig9>1a@1$1@1$0#k0>3imm@1$1@1$0#c@3$2@1$1@1$0#k0@3$7@1$0#k0@3$6@1$0#k0^2@3$3@1$0#c@1$0#k0^1@2$8@1$0#k0@2$5@1$0#k0+1@2$4^2@2$9@1$0#c^1").
Proof.
  intros. rewrite b_addsext. apply bv_eq.
  unfold jalr_tgt, jalr_tgtZ, v_addi.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z.
  change (Z.lnot 1) with (-2)%Z.
  apply Z_land_m2_wrap.
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac step_pipeline Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mkst];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Section FPX2. Context {fx : FPState}.
Lemma step_opimm_gen : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!nr4!nrd!hg9!kh8!kne!ns6!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$hf@1$0#5ZKv$f@2$i0@1$0#5Z^c@3$hd^c^6@3$hb^7@2$hc^c^5@3$ha@1$0#c@1$0#k0^4@2$he^b+4^a^9").
Proof.
  intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_shiftimm_gen : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!ntc!nrd!hg9!lh2!kne!ns6!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>0@3$3@1$2@1$1@1$0#i0@2$h2^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$hf@1$0#5ZKv$f@2$i0@1$0#5Z^c@3$hd^c^6@3$hb^7@2$hc^c^5@3$ha@1$0#6@1$0#k0^4@2$he^b+4^a^9").
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_op_gen : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!nu8!nrd!hg9!kne!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$h9>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h4^6$d>0@3$3@1$2@2$8$6$5@1$h7^7@2$7@2$8$6$5@4$f$6$5@4$h8^6^5^4^3+4@3$3@1$h5$9@2$h6^d@5$c?2fx^c^b^a^9@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^c@3$hc^c^6@3$hb^7@2$b^c^5@2$b^c^4@2$hd^b+4^a^9").
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_opimm32_gen : ltac2:(zQ "i21!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!kh8!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kp1!nue!hg9!lo5!lnc!ns6!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@3$h9^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$i0@1$0#5ZKv$h0@2$i1@1$0#5Z^b@3$he^b^6@3$b@1$0#i0@1$0#k0@3$hb$h8@1$hc@2$hd^b^5@3$b@1$0#c@1$0#i0^4@2$hf^a+4^9^8").
Proof.
  intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_shiftimm32_gen : ltac2:(zQ "i31!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!nv9!nrd!hg9!kh8!lh2!lo5!lnc!ns6!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$h8>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h2^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h3^6$c>0@3$3@1$2@2$8$6$5@1$h6^7@2$7@2$8$6$5@4$e$6$5@4$h7^6^5^4^3+4@3$3@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$i1@1$0#5ZKv$f@2$i2@1$0#5Z^c@3$hf^c^6@3$ha@1$0#i0@1$0#k0@3$hc^7@1$hd@2$he^c^5@3$hb@1$0#5@1$0#i0^4@2$i0^b+4^a^9").
Proof.
  intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_op32_gen : ltac2:(zQ "i21!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!lnc!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!og7!nrd!hg9!kh8!lo5!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$f$h2>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$ha>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h4^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h5^6$e>0@3$3@1$2@2$8$6$5@1$h8^7@2$7@2$8$6$5@4$h0$6$5@4$h9^6^5^4^3+4@3$3@1$h6$9@2$h7^d@5$d?2fx^c^b^a^9@2$h3$9@5$d?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$hb@1$0#5^6@3$i0@1$0#5ZKv$h1@2$i1@1$0#5Z^c@3$he^c^6@3$hc@1$0#i0@1$0#k0@3$hd^7@1$b@2$c^c^5@1$b@2$c^c^4@2$hf^b+4^a^9").
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_mul_gen : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!ogf!oh6!hg9!lv5!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$h9>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h4^6$d>0@3$3@1$2@2$8$6$5@1$h7^7@2$7@2$8$6$5@4$f$6$5@4$h8^6^5^4^3+4@3$3@1$h5$9@2$h6^d@5$c?2fx^c^b^a^9@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^c@3$hc^c^6@4$hb@1$0#k0^7@2$b^c^5@2$b^c^4@2$hd^b+4^a^9").
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

Lemma step_mul32_gen : ltac2:(zQ "i21!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!lnc!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!ohf!oh6!hg9!kh8!lv5!nsc!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$f$h2>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2op$ha>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h4^a^8@2$7@1$1@1$0#i0^5>0@3$3$4@1$h5^6$e>0@3$3@1$2@2$8$6$5@1$h8^7@2$7@2$8$6$5@4$h0$6$5@4$h9^6^5^4^3+4@3$3@1$h6$9@2$h7^d@5$d?2fx^c^b^a^9@2$h3$9@5$d?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$hb@1$0#5^6@3$i0@1$0#5ZKv$h1@2$i1@1$0#5Z^c@3$he^c^6@3$hc@1$0#i0@1$0#k0@4$hd@1$0#i0^7@1$b@2$c^c^5@1$b@2$c^c^4@2$hf^b+4^a^9").
Proof.
  intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rs2); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_branch_tk_gen : ltac2:(zQ "hd1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!nha!ni1!ns6!nj2!hra!iu2!nj8!hm5!ji7!njf!nkc!nla!nm6!nn8!nq6!oi8!oj2!sa!ok1!ol1!ig9&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>1c$h8>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h3^6$c>0@3$2@1$3@2$8$5$4@1$h6^7@2$6@2$8$5$4@4$e$5$4@4$h7^6^5^4^3+4>0@3$2$7@3$ha^7@2$a^c^6@2$a^c^5$f@3$2@1$h4$9@2$h5^e@5$b?2fx^d^c^b^a@2$h1$9@5$b?2fx^d@2$hb^c@2$hc@1$0#d^5^b^a").
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_addsext; reflexivity.
Qed.

Lemma step_branch_ft_gen : ltac2:(zQ "hb1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!hra!nha!ni1!ns6!nj2!iu2!nj8!ji7!njf!nkc!nla!nm6!nn8!nq6!oi8!oj2!sa!ok1!nt4&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>1c$h7>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^a^8@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$e$5$4@4$h6^6^5^4^3+4>0@3$2$7@3$h9^7@2$b^c^6@2$b^c^5$8@3$2@1$h3$a@2$h4^e@5$c?2fx^d^c^b^a@2$h0$a@5$c?2fx^d@2$ha^c+4^b^a").
Proof.
  intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_addi : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!nt4!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kp1!nr4!hg9!ns6!nsc!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$b?2fx^b^a^9^8@2$h2$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$hd@1$0#5ZKv$h0@2$he@1$0#5Z^b@3$hc^b^6@2$c@2$hb^b^5@2$hf@1$0#c^4@2$c^a+4^9^8").
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_addi. reflexivity.
Qed.

Lemma step_andi : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kt8!nr4!hg9!ns6!nsc!nt4!ol7!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#c^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_andi. reflexivity.
Qed.

Lemma step_ori : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kuc!nr4!hg9!ns6!nsc!nt4!olf!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#c^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_ori. reflexivity.
Qed.

Lemma step_xori : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kve!nr4!hg9!ns6!nsc!nt4!om6!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#c^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_xori. reflexivity.
Qed.

Lemma step_sltiu : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!ks2!nr4!hg9!ns6!nsc!nt4!ome!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#c^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_sltiu. reflexivity.
Qed.

Lemma step_slti : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kn3!nr4!hg9!ns6!nsc!nt4!on7!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#c^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_opimm_gen by eassumption.
  rewrite alu_slti. reflexivity.
Qed.

Lemma step_slli : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!li2!ntc!hg9!ns6!nsc!nt4!onf!hjf!hk4!ih5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#6^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_shiftimm_gen by eassumption.
  rewrite alu_slli. reflexivity.
Qed.

Lemma step_srli : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lj7!ntc!hg9!ns6!nsc!nt4!oo7!hjf!hk4!ih5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#6^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_shiftimm_gen by eassumption.
  rewrite alu_srli. reflexivity.
Qed.

Lemma step_srai : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lkc!ntc!hg9!ns6!nsc!nt4!oof!hjf!hk4!ih5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#6>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#6^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_shiftimm_gen by eassumption.
  rewrite alu_srai. reflexivity.
Qed.

Lemma step_add : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kp1!nu8!hg9!nsc!op7!nt4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hc@2$b^b^5@2$b^b^4@2$hd^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_add. reflexivity.
Qed.

Lemma step_sub : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kq5!nu8!hg9!nsc!nt4!ope!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sub. reflexivity.
Qed.

Lemma step_slt : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kn3!nu8!hg9!nsc!nt4!oq5!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_slt. reflexivity.
Qed.

Lemma step_sltu : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!ks2!nu8!hg9!nsc!nt4!oqc!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sltu. reflexivity.
Qed.

Lemma step_and : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kt8!nu8!hg9!nsc!nt4!or4!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_and. reflexivity.
Qed.

Lemma step_or : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kuc!nu8!hg9!nsc!nt4!orb!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_or. reflexivity.
Qed.

Lemma step_xor : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kve!nu8!hg9!nsc!nt4!os1!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_xor. reflexivity.
Qed.

Lemma step_sll : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!li2!nu8!hg9!nsc!nt4!os8!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sll. reflexivity.
Qed.

Lemma step_srl : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lj7!nu8!hg9!nsc!nt4!osf!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_srl. reflexivity.
Qed.

Lemma step_sra : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lkc!nu8!hg9!nsc!nt4!ot6!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op_gen by eassumption.
  rewrite alu_sra. reflexivity.
Qed.

Lemma step_addiw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!nue!hg9!ns6!nsc!nt4!otd!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@3$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^6@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^b@3$ha^b^6@2$hc@2$h9^b^5@2$hf@1$0#c^4@2$hb^a+4^9^8").
Proof.
  intros. erewrite step_opimm32_gen by eassumption.
  rewrite w_addiw. reflexivity.
Qed.

Lemma step_slliw : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!li2!nv9!hg9!ns6!nsc!nt4!ou6!hjf!hk4!ih5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#5^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_shiftimm32_gen by eassumption.
  rewrite w_slliw. reflexivity.
Qed.

Lemma step_srliw : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lj7!nv9!hg9!ns6!nsc!nt4!ouf!hjf!hk4!ih5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#5^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_shiftimm32_gen by eassumption.
  rewrite w_srliw. reflexivity.
Qed.

Lemma step_sraiw : ltac2:(zQ "i11!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lkc!nv9!hg9!ns6!nsc!nt4!ov8!hjf!hk4!ih5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2sh@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@4$h8$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h9@1$0#5^6@3$he@1$0#5ZKv$f@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$ha^b^5@2$i0@1$0#5^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_shiftimm32_gen by eassumption.
  rewrite w_sraiw. reflexivity.
Qed.

Lemma step_addw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kp1!og7!hg9!nsc!nt4!pg1!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_addw. reflexivity.
Qed.

Lemma step_subw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!kq5!og7!hg9!nsc!nt4!pg9!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_subw. reflexivity.
Qed.

Lemma step_sllw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!li2!og7!hg9!nsc!nt4!ph1!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_sllw. reflexivity.
Qed.

Lemma step_srlw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lj7!og7!hg9!nsc!nt4!ph9!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_srlw. reflexivity.
Qed.

Lemma step_sraw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!lkc!og7!hg9!nsc!nt4!pi1!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_op32_gen by eassumption.
  rewrite w_sraw. reflexivity.
Qed.

Lemma step_mul : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!luc!ogf!hg9!nsc!nt4!pi9!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mul. reflexivity.
Qed.

Lemma step_mulh : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mg9!ogf!hg9!nsc!nt4!pj0!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mulh. reflexivity.
Qed.

Lemma step_mulhsu : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mhd!ogf!hg9!nsc!nt4!pj8!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mulhsu. reflexivity.
Qed.

Lemma step_mulhu : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mj5!ogf!hg9!nsc!nt4!pk2!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_mulhu. reflexivity.
Qed.

Lemma step_div : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mkb!ogf!hg9!nsc!nt4!pkb!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_div. reflexivity.
Qed.

Lemma step_rem : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mld!ogf!hg9!nsc!nt4!pl2!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul_gen by eassumption.
  rewrite m_rem. reflexivity.
Qed.

Lemma step_mulw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!luc!ohf!hg9!nsc!nt4!pl9!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_mulw. reflexivity.
Qed.

Lemma step_divw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mkb!ohf!hg9!nsc!nt4!pm1!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_divw. reflexivity.
Qed.

Lemma step_divuw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mod!ohf!hg9!nsc!nt4!pm9!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_divuw. reflexivity.
Qed.

Lemma step_remw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mld!ohf!hg9!nsc!nt4!pn2!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_remw. reflexivity.
Qed.

Lemma step_remuw : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!ns6!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!mq2!ohf!hg9!nsc!nt4!pna!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$e$h1>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>0@3$3@1$2@1$1@1$0#i0@2$h3^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h4^5$d>0@3$3@1$2@2$8$6$5@1$h7^6@2$7@2$8$6$5@4$f$6$5@4$h9$h8^5^4^3+4@3$3@1$h5$9@2$h6^c@5$c?2fx^b^a^9^8@2$h2$9@5$c?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$ha@1$0#5^6@3$he@1$0#5ZKv$h0@2$hf@1$0#5Z^b@3$hb^b^6@2$hd@2$b^b^5@2$b^b^4@2$hc^a+4^9^8").
Proof.
  intros. erewrite step_mul32_gen by eassumption.
  rewrite w_remuw. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_beq_tk : ltac2:(zQ "hd1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!nha!ni1!ns6!nj2!hra!iu2!nj8!hm5!ji7!njf!nkc!nla!nm6!nn8!nq6!po3!oi8!sa!ol1!poc!ig9&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h3^5$c>0@3$2@1$3@2$8$5$4@1$h6^6@2$6@2$8$5$4@4$e$5$4@4$h8$h7^5^4^3+4>0@3$2$7@2$hb@2$a^b^6@2$a^b^5$f@3$2@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fx^c@2$ha^b@2$hc@1$0#d^5^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

Lemma step_beq_ft : ltac2:(zQ "hb1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!hra!nha!ni1!ns6!nj2!iu2!nj8!ji7!njf!nkc!nla!nm6!nn8!nq6!po3!oi8!sa!poc!nt4&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$e$5$4@4$h7$h6^5^4^3+4>0@3$2$7@2$h9@2$b^b^6@2$b^b^5$8@3$2@1$h3$a@2$h4^d@5$c?2fx^c^b^a^9@2$h0$a@5$c?2fx^c@2$ha^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

(* [comment removed for export] *)
Lemma step_bne_tk : ltac2:(zQ "hc1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!hra!nha!ni1!ns6!nj2!iu2!nj8!ji7!njf!nkc!nla!nm6!nn8!nq6!pp2!oi8!sa!ol1!poc!ig9&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$e$5$4@4$h7$h6^5^4^3+4>0@3$2$7@2$ha@2$b^b^6@2$b^b^5$8@3$2@1$h3$a@2$h4^d@5$c?2fx^c^b^a^9@2$h0$a@5$c?2fx^c@2$h9^b@2$hb@1$0#d^5^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

Lemma step_bne_ft : ltac2:(zQ "hc1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!nha!ni1!ns6!nj2!hra!iu2!nj8!hm5!ji7!njf!nkc!nla!nm6!nn8!nq6!pp2!oi8!sa!poc!nt4&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h3^5$c>0@3$2@1$3@2$8$5$4@1$h6^6@2$6@2$8$5$4@4$e$5$4@4$h8$h7^5^4^3+4>0@3$2$7@2$ha@2$a^b^6@2$a^b^5$f@3$2@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fx^c@2$hb^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_blt_tk : ltac2:(zQ "hd1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!nha!ni1!ns6!nj2!hra!iu2!nj8!hm5!ji7!njf!nkc!nla!nm6!nn8!nq6!ppb!oi8!sa!ol1!pq4!ig9&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h3^5$c>0@3$2@1$3@2$8$5$4@1$h6^6@2$6@2$8$5$4@4$e$5$4@4$h8$h7^5^4^3+4>0@3$2$7@2$hb@2$a^b^6@2$a^b^5$f@3$2@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fx^c@2$ha^b@2$hc@1$0#d^5^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

Lemma step_blt_ft : ltac2:(zQ "hb1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!hra!nha!ni1!ns6!nj2!iu2!nj8!ji7!njf!nkc!nla!nm6!nn8!nq6!ppb!oi8!sa!pq4!nt4&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$e$5$4@4$h7$h6^5^4^3+4>0@3$2$7@2$h9@2$b^b^6@2$b^b^5$8@3$2@1$h3$a@2$h4^d@5$c?2fx^c^b^a^9@2$h0$a@5$c?2fx^c@2$ha^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

(* [comment removed for export] *)
Lemma step_bge_tk : ltac2:(zQ "hc1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!hra!nha!ni1!ns6!nj2!iu2!nj8!ji7!njf!nkc!nla!nm6!nn8!nq6!pqb!oi8!sa!ol1!pq4!ig9&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$e$5$4@4$h7$h6^5^4^3+4>0@3$2$7@2$ha@2$b^b^6@2$b^b^5$8@3$2@1$h3$a@2$h4^d@5$c?2fx^c^b^a^9@2$h0$a@5$c?2fx^c@2$h9^b@2$hb@1$0#d^5^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_lts in Hc. rewrite Hc. reflexivity.
Qed.

Lemma step_bge_ft : ltac2:(zQ "hc1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!nha!ni1!ns6!nj2!hra!iu2!nj8!hm5!ji7!njf!nkc!nla!nm6!nn8!nq6!pqb!oi8!sa!pq4!nt4&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h3^5$c>0@3$2@1$3@2$8$5$4@1$h6^6@2$6@2$8$5$4@4$e$5$4@4$h8$h7^5^4^3+4>0@3$2$7@2$ha@2$a^b^6@2$a^b^5$f@3$2@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fx^c@2$hb^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_lts in Hc. rewrite Hc. reflexivity.
Qed.

Lemma step_bltu_tk : ltac2:(zQ "hd1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!nha!ni1!ns6!nj2!hra!iu2!nj8!hm5!ji7!njf!nkc!nla!nm6!nn8!nq6!pr4!oi8!sa!ol1!pre!ig9&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h3^5$c>0@3$2@1$3@2$8$5$4@1$h6^6@2$6@2$8$5$4@4$e$5$4@4$h8$h7^5^4^3+4>0@3$2$7@2$hb@2$a^b^6@2$a^b^5$f@3$2@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fx^c@2$ha^b@2$hc@1$0#d^5^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

Lemma step_bltu_ft : ltac2:(zQ "hb1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!hra!nha!ni1!ns6!nj2!iu2!nj8!ji7!njf!nkc!nla!nm6!nn8!nq6!pr4!oi8!sa!pre!nt4&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$e$5$4@4$h7$h6^5^4^3+4>0@3$2$7@2$h9@2$b^b^6@2$b^b^5$8@3$2@1$h3$a@2$h4^d@5$c?2fx^c^b^a^9@2$h0$a@5$c?2fx^c@2$ha^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hf He Hd).
  exact Hc.
Qed.

(* [comment removed for export] *)
Lemma step_bgeu_tk : ltac2:(zQ "hc1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!hra!nha!ni1!ns6!nj2!iu2!nj8!ji7!njf!nkc!nla!nm6!nn8!nq6!ps5!oi8!sa!ol1!pre!ig9&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h2^5$8>0@3$2@1$3@2$9$5$4@1$h5^6@2$6@2$9$5$4@4$e$5$4@4$h7$h6^5^4^3+4>0@3$2$7@2$ha@2$b^b^6@2$b^b^5$8@3$2@1$h3$a@2$h4^d@5$c?2fx^c^b^a^9@2$h0$a@5$c?2fx^c@2$h9^b@2$hb@1$0#d^5^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_tk_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_ltu in Hc. rewrite Hc. reflexivity.
Qed.

Lemma step_bgeu_ft : ltac2:(zQ "hc1!ld!s5!hl7!iu9!hmc!nh1!jj9!ua!nha!ni1!ns6!nj2!hra!iu2!nj8!hm5!ji7!njf!nkc!nla!nm6!nn8!nq6!ps5!oi8!sa!pre!nt4&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^9^7@2$6@1$1@1$0#i0^4>0@3$2$7@1$h3^5$c>0@3$2@1$3@2$8$5$4@1$h6^6@2$6@2$8$5$4@4$e$5$4@4$h8$h7^5^4^3+4>0@3$2$7@2$ha@2$a^b^6@2$a^b^5$f@3$2@1$h4$9@2$h5^d@5$b?2fx^c^b^a^9@2$h1$9@5$b?2fx^c@2$hb^b+4^a^9").
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_ltu in Hc. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_lui : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!psf!hg9!nsc!nt4!pt6!iqe!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h4>0@3$3@1$2@1$1@1$0#i0@2$h2^8^6@2$7@1$1@1$0#i0^3>0@3$3$4@1$h3^4$c>0@3$3@1$2@2$8$6$5@1$h6^5@2$7@2$8$6$5@4$e$6$5@2$h7^4^3+4@3$3@1$h4$9@2$h5^b@5$b?2fx^a^9^8^7@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^5@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^a@3$h9^a^5@1$hb@2$hc@2$hf@1$0#h4^4+c@2$ha^9+4^8^7").
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.

Lemma step_auipc : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!ptd!hg9!nsc!nt4!pu6!iqe!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3imm@1$1@1$0#h4>0@3$3@1$2@1$1@1$0#i0@2$h2^8^6@2$7@1$1@1$0#i0^3>0@3$3$4@1$h3^4$c>0@3$3@1$2@2$8$6$5@1$h6^5@2$7@2$8$6$5@4$e$6$5@2$h7^4^3+4@3$3@1$h4$9@2$h5^b@5$b?2fx^a^9^8^7@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^5@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^a@3$h9^a^5@2$hb^9@2$hc@2$hf@1$0#h4^4+c@2$ha^9+4^8^7").
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.

Lemma step_jal_x0 : ltac2:(zQ "hc1!ld!s5!iu9!hl7!hmc!nh1!jj9!nha!ni1!nj2!ua!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!puf!sa!ol1!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$c$f>4regs@2$h7@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>3imm@1$1@1$0#h5>0@3$3@1$2@1$1@1$0#i0@2$h1^7^5@2$6@1$1@1$0#i0^2>0@3$3$a@1$h2^3$b>0@3$3@1$2@2$7$5$4@1$h5^4@2$6@2$7$5$4@4$d$5$4@2$h6@3$h9@1$0#5ZKv$e@2$ha@1$0#5Z^3+4@3$3@1$h3$8@2$h4^a@5$9?2fx^9^8^7^6@2$h0$8@5$9?2fx^9@2$h8^8@2$hb@1$0#h5^4^7^6").
Proof.
  intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  rewrite is_x0_0; cbv beta iota.
  rewrite b_addsext. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr_gen : ltac2:(zQ "i01!ld!s5!iu9!hl7!ua!hmc!nh1!jj9!nha!ni1!sa!nj2!hra!iu2!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!pv6!hg9!ns6!pve!nsc!nt4!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$h0>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3imm@1$1@1$0#c>0@3$3@1$2@1$1@1$0#i0@2$h2^9^7@2$7@1$1@1$0#i0^4>0@3$3$4@1$h3^5$c>0@3$3@1$2@2$8$6$5@1$h6^6@2$7@2$8$6$5@4$e$6$5@3$h7^5^4^3+4@3$3@1$h4$9@2$h5^c@5$b?2fx^b^a^9^8@2$h1$9@5$b?2fxM4\0$4@2$a@1$0#5@1$1@1$0#k0@3$h8@1$0#5^6@3$hd@1$0#5ZKv$f@2$he@1$0#5Z^b@3$hb^b^6@2$hc^a+4@2$ha@2$h9^b^5@2$hf@1$0#c^4^9^8").
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  destruct (is_x0 rs1); cbv beta iota;
    destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.

Lemma step_ecall : ltac2:(zQ "h91!ld!s5!iu9!hl7!jj9!ni1!jj2!ua!iu2!hm5!hg5!ji7!qg8!njf!nkc!nla!nm6!nn8!sa!qi0!qi8!ns6!nj2!hjf!hk4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$8$b>4regs@2$h2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>0@3$3@1$2@1$1@1$0#i0@2$e^6^4@2$4@1$1@1$0#i0^1>0@3$3$7@1$f^2$9@3$3@1$h0$5@2$h1^8@5$h6?2fx^7^6^5^4@2$d$5@8$c^7@1$h4?2fx^6@2$4@1$1@1$0#k0@2$h5^7@3$h7@1$0#5+h1Kv$a@2$h8@1$0#5+h1@1$6@1$1@1$0#k0@1$h3?2fx^5^4").
Proof.
  intros segs regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses.
  cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.drop_access_report,
    RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_lbu : ltac2:(zQ "i51!ld!s5!iu9!hl7!jj9!ua!iu2!hmc!nh1!hra!nha!ni1!sa!nj2!nt4!jq4!jqb!nj8!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!qj1!qje!hg9!ns6!qk5!nsc!hjf!hk4!rb!ig9!ih5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$6$h3>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1b@1$1@1$0#8>0@3$3@1$2@1$1@1$0#i0@2$h5^a^8@2$4@1$1@1$0#i0^5>0@3$3$5@1$h6^6$9>0@3$3@1$2@2$a$8$7@1$h9^7@2$4@2$a$8$7@4$h1$8$7@5$ha$hb$9^6^5^4+4>0@3$3@1$2@1$6@1$1@1$0#8@4$he^d^a@2$e@2$hd^c^6@2$i3@1$0#c^5N1@2$4@1$6@1$1@1$0#8@3$f@1$1@1$0#8^4@1$h0@1$1@1$0#8@3$3@1$h7$b@2$h8^e@5$d?2fx^d^c^b^a@2$h4$b@5$d?2fxM5\0$5@2$c@1$0#5@1$1@1$0#k0@3$hc@1$0#5^8@3$i0@1$0#5ZKv$h2@2$i1@1$0#5Z^d@3$hf^d^8@2$i2@1$0#k0@2$i4@1$0#8^5@2$e^c+4^b^a").
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
  { rewrite le_word_1, b_extract8_id. apply bv_eq.
    unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
    pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_lb : ltac2:(zQ "i51!ld!s5!iu9!hl7!jj9!ua!iu2!hmc!nh1!nha!ni1!sa!nj2!nt4!jq4!hra!jqb!nj8!hm5!hg5!ji7!njf!nkc!nla!nm6!nn8!nq6!qj1!qje!hg9!ns6!qk5!nsc!qka!hjf!hk4!ig9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$6$h4>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>1b@1$1@1$0#8>0@3$3@1$2@1$1@1$0#i0@2$h6^a^8@2$4@1$1@1$0#i0^5>0@3$3$5@1$h7^6$f>0@3$3@1$2@2$9$8$7@1$ha^7@2$4@2$9$8$7@4$h1$8$7@5$hb$hc$h2^6^5^4+4>0@3$3@1$2@1$6@1$1@1$0#8@4$hf^d^a@2$d@2$he^c^6@2$i4@1$0#c^5N1@2$4@1$6@1$1@1$0#8@3$e@1$1@1$0#8^4@1$h0@1$1@1$0#8@3$3@1$h8$a@2$h9^e@5$c?2fx^d^c^b^a@2$h5$a@5$c?2fxM5\0$5@2$b@1$0#5@1$1@1$0#k0@3$hd@1$0#5^8@3$i2@1$0#5ZKv$h3@2$i3@1$0#5Z^d@3$i0^d^8@1$i1^5@2$d^c+4^b^a").
Proof.
  intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite b_lb_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_lh : ltac2:(zQ "i51!ld!s5!hl7!iu9!iu2!hmc!jj9!ua!nh1!nha!ni1!sa!nj2!nt4!hra!nj8!hm5!hg5!jv5!ji7!njf!nkc!nla!nm6!nn8!nq6!qj1!ql0!hg9!ns6!qk5!nsc!ql7!hjf!hk4!ig9!ih5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$4$h3>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>2bs@1$4@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h5^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h6^7$e>0@3$2@1$3@2$9$8$5@1$h9^8@2$6@2$9$8$5@4$f$8$5@5$ha$hb$h0^7^6^5+4>0@3$2@1$3@1$4@1$1@1$0#8@4$he^e^b@2$d@2$hd^d^7@2$i3@1$0#c^6N2@2$6@1$4@1$1@1$0#8^5>0@3$2$5@1$h2^6@2$i4@1$0#k0^5@3$2@1$h7$a@2$h8^h0@5$c?2fx^f^e^d^c@2$h4$a@5$c?2fxM7\0$7@2$b@1$0#5@1$1@1$0#k0@3$hc@1$0#5^a@3$i1@1$0#5ZKv$h1@2$i2@1$0#5Z^f@3$hf^f^a@1$i0^6@2$d^e+4^d^c").
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_lhu : ltac2:(zQ "i31!ld!s5!hl7!iu9!iu2!hmc!jj9!ua!nh1!hra!nha!ni1!sa!nj2!nt4!nj8!hg5!jv5!ji7!njf!nkc!nla!nm6!nn8!nq6!qj1!ql0!hg9!ns6!qk5!nsc!hjf!hk4!ig9!ih5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$4$h2>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>2bs@1$4@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h4^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h5^7$9>0@3$2@1$3@2$a$8$5@1$h8^8@2$6@2$a$8$5@4$f$8$5@5$h9$ha$9^7^6^5+4>0@3$2@1$3@1$4@1$1@1$0#8@4$hd^e^b@2$e@2$hc^d^7@2$i1@1$0#c^6N2@2$6@1$4@1$1@1$0#8^5>0@3$2$5@1$h1^6@2$i2@1$0#k0^5@3$2@1$h6$b@2$h7^h0@5$d?2fx^f^e^d^c@2$h3$b@5$d?2fxM7\0$7@2$c@1$0#5@1$1@1$0#k0@3$hb@1$0#5^a@3$hf@1$0#5ZKv$h0@2$i0@1$0#5Z^f@3$he^f^a^6@2$e^e+4^d^c").
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 16 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 16) with 65536%Z.
    change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_lw : ltac2:(zQ "i51!ld!s5!hl7!iu9!iu2!hmc!jj9!ua!nh1!nha!ni1!sa!nj2!nt4!hra!nj8!hm5!hg5!jv5!ji7!njf!nkc!nla!nm6!nn8!nq6!qj1!qld!hg9!ns6!qk5!nsc!qm4!hjf!hk4!ig9!ih5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$4$h3>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>2bs@1$4@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h5^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h6^7$e>0@3$2@1$3@2$9$8$5@1$h9^8@2$6@2$9$8$5@4$f$8$5@5$ha$hb$h0^7^6^5+4>0@3$2@1$3@1$4@1$1@1$0#8@4$he^e^b@2$d@2$hd^d^7@2$i3@1$0#c^6N4@2$6@1$4@1$1@1$0#8^5>0@3$2$5@1$h2^6@2$i4@1$0#k0^5@3$2@1$h7$a@2$h8^h0@5$c?2fx^f^e^d^c@2$h4$a@5$c?2fxM7\0$7@2$b@1$0#5@1$1@1$0#k0@3$hc@1$0#5^a@3$i1@1$0#5ZKv$h1@2$i2@1$0#5Z^f@3$hf^f^a@1$i0^6@2$d^e+4^d^c").
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_lwu : ltac2:(zQ "i31!ld!s5!hl7!iu9!iu2!hmc!jj9!ua!nh1!hra!nha!ni1!sa!nj2!nt4!nj8!hg5!jv5!ji7!njf!nkc!nla!nm6!nn8!nq6!qj1!qld!hg9!ns6!qk5!nsc!hjf!hk4!ig9!ih5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$4$h2>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>2bs@1$4@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h4^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h5^7$9>0@3$2@1$3@2$a$8$5@1$h8^8@2$6@2$a$8$5@4$f$8$5@5$h9$ha$9^7^6^5+4>0@3$2@1$3@1$4@1$1@1$0#8@4$hd^e^b@2$e@2$hc^d^7@2$i1@1$0#c^6N4@2$6@1$4@1$1@1$0#8^5>0@3$2$5@1$h1^6@2$i2@1$0#k0^5@3$2@1$h6$b@2$h7^h0@5$d?2fx^f^e^d^c@2$h3$b@5$d?2fxM7\0$7@2$c@1$0#5@1$1@1$0#k0@3$hb@1$0#5^a@3$hf@1$0#5ZKv$h0@2$i0@1$0#5Z^f@3$he^f^a^6@2$e^e+4^d^c").
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : zext 64 (bv_extract 0 32 v) = v).
  { pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as Hb.
    pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
    rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
    apply bv_eq. unfold zext.
    rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_small.
    change (bv_modulus 32) with 4294967296%Z.
    change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

Lemma step_ld : ltac2:(zQ "i41!ld!s5!hl7!iu9!iu2!hmc!jj9!ua!nh1!nha!ni1!sa!nj2!nt4!hra!nj8!hm5!hg5!jv5!ji7!njf!nkc!nla!nm6!nn8!nq6!qj1!qma!hg9!ns6!qk5!nsc!hjf!hk4!ig9!ih5&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$4$h3>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2rd@1$1@1$0#5>2rs@1$1@1$0#5>3imm@1$1@1$0#c>2bs@1$4@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h5^b^9@2$6@1$1@1$0#i0^6>0@3$2$7@1$h6^7$e>0@3$2@1$3@2$9$8$5@1$h9^8@2$6@2$9$8$5@4$f$8$5@5$ha$hb$h0^7^6^5+4>0@3$2@1$3@1$4@1$1@1$0#8@4$he^e^b@2$d@2$hd^d^7@2$i2@1$0#c^6N8@2$6@1$4@1$1@1$0#8^5>0@3$2$5@1$h2^6@2$i3@1$0#k0^5@3$2@1$h7$a@2$h8^h0@5$c?2fx^f^e^d^c@2$h4$a@5$c?2fxM7\0$7@2$b@1$0#5@1$1@1$0#k0@3$hc@1$0#5^a@3$i0@1$0#5ZKv$h1@2$i1@1$0#5Z^f@3$hf^f^a^6@2$d^e+4^d^c").
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_unsigned. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  destruct (is_x0 rd); cbv beta iota;
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_addi_0 : ltac2:(zQ "40!ld!s5!hl7!nt4>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3^1Z^1").
Proof.
  intro x. apply bv_eq. unfold v_addi.
  rewrite Z_to_bv_unsigned, Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_signed_small : ltac2:(zQ "80!ld!ih5!hl7!hmc!hs8!hp2!s5!ig9>1x@1$6@1$0#k0>0@2$4@2$1@1$0#k0^1@2$5+2+jf@3$2$3@2$7@1$0#k0^2@2$1@1$0#k0^2").
Proof.
  intros x Hx. unfold bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 64) with (2^63)%Z.
  pose proof (u64_range x). lia.
Qed.

Lemma bv_signed_hi : ltac2:(zQ "90!ld!hp2!ih5!hl7!hmc!hr4!ii3!s5!ig9>1x@1$7@1$0#k0>0@2$5@2$1+2+jf@2$2@1$0#k0^1@3$3$4@2$8@1$0#k0^2@2$6@2$2@1$0#k0^2@2$1+2+k0").
Proof.
  intros x Hx. unfold bv_signed.
  rewrite (bv_swrap_hi 64);
    [ change (bv_modulus 64) with (2^64)%Z; reflexivity
    | discriminate
    | change (bv_half_modulus 64) with (2^63)%Z; lia
    | change (bv_modulus 64) with (2^64)%Z; apply u64_range ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma c_eq_0_false : ltac2:(zQ "a0!ld!hl7!ua!hra!ms4!hmc!poc!rb!s5!ih5>1x@1$8@1$0#k0>0@1$4@3$1$5@2$9@1$0#k0^1Z@3$1$2@2$6^2@2$7@1$0#k0Z$3").
Proof.
  intros x Hnz. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact Hnz.
Qed.

(* [comment removed for export] *)

Lemma c_eq_neq : ltac2:(zQ "90!ld!hl7!s5!ih5!ua!hra!ms4!hmc!poc>1x@1$2@1$0#k0>1y@1$2@1$0#k0>0@1$6@3$1$7@2$3@1$0#k0^2@2$3@1$0#k0^1@3$1$4@2$8^3^2$5").
Proof. intros x y Hne. unfold c_eq, bv_eqb. apply Z.eqb_neq. exact Hne. Qed.

Lemma c_eq_refl : ltac2:(zQ "60!ua!hm5!hl7!ld!poc!s5>1x@1$5@1$3#k0@3$2$0@2$4^1^1$1").
Proof. intro x. apply bv_eqb_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_same : ltac2:(zQ "a0!ld!s5!hl7!hg5!ms4!sa!ns6!nsc!hjf!hk4>4regs@2$5@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0>0@1$4@3$2@1$1@1$0#5^2@3$8@1$0#5ZKv$3@2$9@1$0#5Z@3$2@1$1@1$0#k0@2$6@3$7^4^3^2^3^2").
Proof.
  intros regs r v H. unfold getr, regupd, reg_get.
  rewrite (bv_eqb_neq r 0 H), bvmap_get_set_same. reflexivity.
Qed.

Lemma getr_other : ltac2:(zQ "70!ld!s5!hl7!ns6!ms4!sa!nsc>4regs@2$5@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0>2r'@1$1@1$0#5>0@1$4@3$2@1$1@1$0#5^1^3@3$2@1$1@1$0#k0@2$3@3$6^5^4^3^2@2$3^5^2").
Proof.
  intros regs r v r' H. unfold getr, regupd, reg_get.
  destruct (bv_eqb r' 0); [reflexivity|].
  rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.

Lemma getr_nz : ltac2:(zQ "a0!ld!s5!hl7!hg5!ms4!sa!hj4!ns6!hjf!hk4>4regs@2$5@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@1$4@3$2@1$1@1$0#5^1@3$8@1$0#5ZKv$3@2$9@1$0#5Z@3$2@1$1@1$0#k0@2$7^3^2@2$6^3^2").
Proof.
  intros regs r H. unfold getr. rewrite (bv_eqb_neq r 0 H). reflexivity.
Qed.

Lemma regupd_other : ltac2:(zQ "70!ld!s5!hl7!hj4!ms4!sa!nsc>4regs@2$5@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0>2r'@1$1@1$0#5>0@1$4@3$2@1$1@1$0#5^1^3@3$2@1$1@1$0#k0@2$3@3$6^5^4^3^2@2$3^5^2").
Proof.
  intros regs r v r' H. unfold regupd, reg_get.
  rewrite bvmap_get_set_other by congruence. reflexivity.
Qed.

Lemma regupd_same : ltac2:(zQ "60!ld!s5!hl7!sa!hj4!nsc>4regs@2$3@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>1v@1$1@1$0#k0@3$2@1$1@1$0#k0@2$4@3$5^3^2^1^2^1").
Proof.
  intros. unfold regupd, reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX3. Context {fx : FPState}.
Lemma bytes_le_single : ltac2:(zQ "80!ld!s5!jq4!jqb!hl7!hmc!jv5!ih5>1b@1$1@1$0#8@3$4$5@1$6@3$2@1$1@1$0#8^1@1$3@1$1@1$0#8@2$7@1$0#8^1").
Proof. intro b. cbn. apply Z.lor_0_r. Qed.

Lemma bv_wrap8_mod : ltac2:(zQ "60!hmc!hl7!ld!ho8!hp2!hp9>1z$0@3$1$0@2$5@1$2#8^1@2$3^1@2$4+2+8").
Proof. reflexivity. Qed.

Lemma bytes_le_Z_to_le : ltac2:(zQ "a0!hmc!jo6!hl7!qn1!jv5!hr4!ho8!iia!hqa!hp2>1k$1>1z$0>0@2$5Z^1@3$2$0@1$4@2$3^3^2@2$6^2@2$9+2@2$7+8@1$8^3").
Proof.
  induction k as [|k IH]; intros z Hz.
  - cbn. change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.mod_1_r. reflexivity.
  - cbn [Z_to_le_bytes bytes_le_to_Z].
    rewrite IH by (apply Z.shiftr_nonneg; lia).
    rewrite Z_to_bv_unsigned, bv_wrap8_mod.
    replace (8 * Z.of_nat (S k))%Z with (8 * Z.of_nat k + 8)%Z by lia.
    pose proof (Nat2Z.is_nonneg k).
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + rewrite (Z.mod_pow2_bits_low z 8 i) by lia.
      rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
      rewrite (Z.testbit_neg_r _ (i - 8)) by lia.
      apply orb_false_r.
    + rewrite (Z.mod_pow2_bits_high z 8 i) by lia.
      rewrite orb_false_l.
      destruct (Z.lt_ge_cases i (8 * Z.of_nat k + 8)) as [Hik|Hik].
      * rewrite (Z.mod_pow2_bits_low _ (8 * Z.of_nat k) (i - 8)) by lia.
        rewrite Z.shiftr_spec by lia.
        rewrite (Z.mod_pow2_bits_low z (8 * Z.of_nat k + 8) i) by lia.
        f_equal. lia.
      * rewrite (Z.mod_pow2_bits_high _ (8 * Z.of_nat k) (i - 8)) by lia.
        rewrite (Z.mod_pow2_bits_high z (8 * Z.of_nat k + 8) i) by lia.
        reflexivity.
Qed.

Lemma bytes_le_N : ltac2:(zQ "c0!ld!jo6!hl7!hmc!jv5!qo2!ho8!iia!hqa!hp2!s5!ih5>1k$1>1v@1$a@1$0#k0@3$2$3@1$4@2$5^2^1@2$6@2$b@1$0#k0^1@2$9+2@2$7+8@1$8^2").
Proof.
  intros k v. unfold word_to_le_bytes.
  apply bytes_le_Z_to_le. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma n_to_le_8_spec : ltac2:(zQ "60!ld!s5!iu2!hl7!qp7!qo2>1v@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@1$4^1@2$5N8^1").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_error_skipn_cons : forall {A} (bs : list A) d, (d < length bs)%nat ->
  exists b, nth_error bs d = Some b /\ skipn d bs = b :: skipn (S d) bs.
Proof.
  intros A bs. induction bs as [|x bs IH]; intros d Hd; [cbn in Hd; lia|].
  destruct d as [|d'].
  - exists x. split; reflexivity.
  - cbn [length] in Hd. destruct (IH d' ltac:(lia)) as [b [H1 H2]].
    exists b. split; [exact H1|]. cbn [skipn]. exact H2.
Qed.

Lemma u_add1 : ltac2:(zQ "c0!ld!ih5!hq3!hg5!hl7!hmc!hs8!hp2!hjf!hk4!s5!kk6>1a@1$a@1$0#k0>0@2$6@2$2@2$1@1$0#k0^1+1@2$7+2+k0@3$4$5@2$1@1$0#k0@3$b@1$0#k0^2@3$8@1$0#k0+1Kv$3@2$9@1$0#k0+1@2$2@2$1@1$0#k0^2+1").
Proof.
  intros a Ha. rewrite bv_add_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite bv_wrap64_mod. apply Z.mod_small.
  pose proof (u64_range a). lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_stack : ltac2:(zQ "h70!ld!s5!ih5!iu2!kj7!ii3!qq3!jj9!jo6!iu9!hl7!qrf!qta!qv7!rg1!ji7!rje!qk5!hq3!hr4!hs8!hqa!hp2>4segs@1$3$f>2sp@1$1@1$0#k0>5bytes@1$3@1$1@1$0#8>1k$8>4addr@1$1@1$0#k0>0@2$h3@2$2@1$0#k0^4@2$2@1$0#k0^1>0@2$c@2$b@1$6@2$5@2$2@1$0#k0^2@2$2@1$0#k0^5^3@2$4@1$1@1$0#8^4>0@2$h4@2$h2@2$2@1$0#k0^6@1$h5@2$4@1$1@1$0#8^5@2$h6+2+k0@3$a@1$9@1$3@1$1@1$0#8@4$h1^8@2$h0^7^6^4^5@2$7@1$3@1$1@1$0#8@3$d@1$1@1$0#8^5@3$e@1$1@1$0#8@1$6@2$5@2$2@1$0#k0^4@2$2@1$0#k0^7^6").
Proof.
  intros segs sp bytes k. induction k as [|k IH]; intros addr Hsp Hlen Hnw.
  - cbn. reflexivity.
  - cbn [rdn].
    destruct (nth_error_skipn_cons bytes (Z.to_nat (bv_unsigned addr - bv_unsigned sp)) ltac:(lia)) as [b [Hnth Hskip]].
    unfold stack_to_mem.
    assert (Hle : Z.leb (bv_unsigned sp) (bv_unsigned addr) = true) by (apply Z.leb_le; lia).
    rewrite Hle.
    assert (Hlt : Z.ltb (bv_unsigned addr - bv_unsigned sp) (Z.of_nat (length bytes)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hlt. rewrite Hnth.
    assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z) by (apply u_add1; lia).
    rewrite IH by lia.
    rewrite Hskip.
    replace (Z.to_nat (bv_unsigned (addr + 1) - bv_unsigned sp))
      with (S (Z.to_nat (bv_unsigned addr - bv_unsigned sp))) by lia.
    reflexivity.
Qed.

Lemma rdn_ext : ltac2:(zQ "f1!ld!s5!ih5!iu9!iu2!hl7!qk5!hq3!hr4!hqa!jo6!hs2!ji7!hs8!hp2&>1x@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$4$c>1k$a>2m1~0>2m2~0>1a@1$1@1$0#k0>0@2$8@2$7@2$2@1$0#k0^1@1$9^4@2$e+2+k0>0>1x@1$1@1$0#k0>0@2$b@2$8@2$2@1$0#k0^3@2$2@1$0#k0^1@2$d@2$2@1$0#k0^1@2$7@2$2@1$0#k0^3@1$9^6@3$5@1$3@1$1@1$0#8@1^6^2@1^5^2@3$5@1$3@1$4@1$1@1$0#8@4$6^7^5^3^6@4$6^7^4^3^6").
Proof.
  intros segs k. induction k as [|k IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
  cbn [rdn].
  rewrite (Hext a ltac:(pose proof (u64_range a); lia)).
  destruct k as [|k'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH m1 m2 (a+1) ltac:(lia)
              ltac:(intros x Hx; apply Hext; lia)).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_n_to_le_8 : ltac2:(zQ "60!ld!s5!kj7!jo6!hl7!qp7>1v@1$1@1$0#k0@3$4$3@2$2@1$1@1$0#8@1$5^1N8").
Proof. reflexivity. Qed.

Lemma length_flat_map_le8 : ltac2:(zQ "90!ld!s5!kj7!iu2!jo6!hl7!rke!qp7!rm8>1l@1$3@1$1@1$0#k0@3$5$4@2$2@1$1@1$0#8@4$8@1$1@1$0#k0@1$1@1$0#8$7^1@2$6N8@2$2@1$1@1$0#k0^1").
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [flat_map length]. rewrite length_app, IH, length_n_to_le_8. lia.
Qed.

(* [comment removed for export] *)
Definition total_arg_bytes_nat : ltac2:(zQ "40!iu2!jo6!ld!s5>4args@1$0@1$0@1$3@1$2#8$1") := ltac2:(zQ "70!iu2!ld!s5!jo6!qrf!kj7!rn4\4args@1$0@1$0@1$2@1$1#8@5$6$3@1$0@1$2@1$1#8\1a@1$0@1$2@1$1#8\3acc$3@2$4@2$4@2$5@1$2@1$1#8^2N1^1N0^1").

Lemma total_arg_bytes_Z : ltac2:(zQ "80!iu2!hl7!ld!hmc!rqe!sg1!hqa!s5>1l@1$0@1$0@1$7@1$2#8@3$1$3@1$4^1@1$6@1$5^1").
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbv [total_arg_bytes total_arg_bytes_nat] in *. cbn [fold_right].
  rewrite IH. lia.
Qed.

Lemma length_flatten_strings : ltac2:(zQ "80!iu2!ld!s5!kj7!jo6!hl7!sh9!sg1>1l@1$0@1$0@1$2@1$1#8@3$5$4@2$3@1$2@1$1#8@1$6^1@1$7^1").
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbv [flatten_strings total_arg_bytes_nat] in *. cbn [flat_map fold_right].
  rewrite length_app, IH. rewrite length_app. cbn [length]. lia.
Qed.

Lemma len_word_nat : forall {A} (l : list A), len_word l = nat_to_word (length l).
Proof. reflexivity. Qed.

Lemma word1_nat : ltac2:(zQ "70!ld!s5!hg5!hl7!sic!hjf!hk4@3$3@1$1@1$0#k0Kd@3$5@1$0#k0+1Kv$2@2$6@1$0#k0+1@1$1@1$0#k0@1$4N1").
Proof. apply bv_eq. reflexivity. Qed.

Lemma word_add_0 : ltac2:(zQ "50!ld!s5!hl7!sic!kk6>1a@1$1@1$0#k0@3$2@1$1@1$0#k0@3$4@1$0#k0^1@1$3N0^1").
Proof.
  intro a. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 (Z.of_nat 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma nat_to_word_merge : ltac2:(zQ "70!sic!jo6!ld!hl7!qrf!s5!kk6>1m$1>1k$1@3$3@1$5@1$2#k0@3$6@1$2#k0@1$0^2@1$0^1@1$0@2$4^2^1").
Proof.
  intros m k. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r.
  f_equal. lia.
Qed.

Lemma nat_to_word_add_merge : ltac2:(zQ "70!ld!sic!kk6!jo6!s5!hl7!qrf>1a@1$4@1$0#k0>1m$3>1k$3@3$5@1$4@1$0#k0@3$2@1$0#k0@3$2@1$0#k0^3@1$1^2@1$1^1@3$2@1$0#k0^3@1$1@2$6^2^1").
Proof.
  intros a m k.
  rewrite <- (assoc_L bv_add).
  rewrite nat_to_word_merge. reflexivity.
Qed.

Lemma string_addrs_fst_structure : ltac2:(zQ "d0!ld!s5!iu2!sjb!sk1!kk6!jq4!jqb!hg5!hl7!sl1!hjf!hk4>4strs@1$2@1$2@1$1@1$0#8>4base@1$1@1$0#k0@3$9@1$2@1$1@1$0#k0@3$3@1$2@1$1@1$0#k0@1$1@1$0#k0@2$4^1^2M2\4strs@1$2@1$2@1$1@1$0#8@1$2@1$1@1$0#k0^2@1$7@1$1@1$0#k0\1s@1$2@1$1@1$0#8\4rest@1$2@1$2@1$1@1$0#8@3$6@1$1@1$0#k0^3@3$3@1$2@1$1@1$0#k0@1$1@1$0#k0@2$4@3$5@1$0#k0@3$5@1$0#k0^3@2$a@1$1@1$0#8^2@3$b@1$0#k0+1Kv$8@2$c@1$0#k0+1^1").
Proof.
  intros strs base. destruct strs as [|s rest]; [reflexivity|].
  cbn [string_addrs].
  destruct (string_addrs (base + len_word s + 1) rest) as [ptrs fin] eqn:E.
  reflexivity.
Qed.

Lemma string_addrs_pair : ltac2:(zQ "b0!ld!s5!iu2!sk1!sjb!nj8!nha!hl7!sic!sg1!kk6>4strs@1$2@1$2@1$1@1$0#8>4base@1$1@1$0#k0@3$7@2$6@1$2@1$1@1$0#k0@1$1@1$0#k0@2$3^1^2@4$5@1$2@1$1@1$0#k0@1$1@1$0#k0@3$4@1$2@1$1@1$0#k0@1$1@1$0#k0@2$3^1^2@3$a@1$0#k0^1@1$8@1$9^2").
Proof.
  induction strs as [|s rest IH]; intro base.
  - cbn. rewrite word_add_0. reflexivity.
  - cbn [string_addrs].
    rewrite (IH (base + len_word s + 1)).
    cbn [fst]. f_equal.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    cbv [total_arg_bytes_nat]. cbn [fold_right]. f_equal. f_equal. lia.
Qed.

Lemma length_string_addrs_fst : ltac2:(zQ "80!ld!s5!iu2!kj7!sjb!jo6!hl7!sk1>4strs@1$2@1$2@1$1@1$0#8>4base@1$1@1$0#k0@3$6$5@2$3@1$1@1$0#k0@3$4@1$2@1$1@1$0#k0@1$1@1$0#k0@2$7^1^2@2$3@1$2@1$1@1$0#8^2").
Proof.
  induction strs as [|s rest IH]; intro base; [reflexivity|].
  rewrite string_addrs_fst_structure. cbn [length]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma build_stack_bytes_within_span : ltac2:(zQ "a0!ld!s5!iu2!kj7!sld!sm9!sne!sob!hr4!hqa>2ph$4>2sp@1$1@1$0#k0>1a@1$2@1$2@1$1@1$0#8>1e@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$6@2$8@1$9@2$3@1$1@1$0#8@7$7^7^6^5^4^3^2^1@2$5^5^4").
Proof.
  intros ph sp a e uid hw rnd.
  unfold entry_stack_span, build_stack_bytes. cbv zeta.
  rewrite (string_addrs_pair a). cbv beta iota.
  rewrite (string_addrs_pair e). cbv beta iota.
  rewrite !length_app, repeat_length, !length_flat_map_le8,
    !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
    !length_flatten_strings, length_at_random_bytes.
  rewrite !total_arg_bytes_Z.
  match goal with
  | |- context [Z.to_nat ?pd] =>
      assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia)
  end.
  unfold auxv_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bsb_argc_prefix : ltac2:(zQ "b0!ld!s5!iu2!kk0!hl7!sq1!sl1!qp7!sld!sne!sob>2ph$8>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$9@2$5@1$2@1$1@1$0#8\2tl@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@7$a^8^7^6^5^4^3^2@3$3@1$1@1$0#8@1$7@2$6@1$2@1$1@1$0#8^6^1").
Proof.
  intros ph sp argv envp uid hw rnd. unfold build_stack_bytes.
  rewrite (string_addrs_pair argv). cbv beta iota.
  rewrite (string_addrs_pair envp). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma read_at_offset : ltac2:(zQ "h30!ld!s5!iu2!kj7!hl7!kk0!jo6!jj9!iu9!sic!ji7!rje!qk5!hq3!hs8!hqa!hp2!kk6!ih5>4segs@1$2$a>2sp@1$1@1$0#k0>5bytes@1$2@1$1@1$0#8>3pre@1$2@1$1@1$0#8>3mid@1$2@1$1@1$0#8>4post@1$2@1$1@1$0#8>1k$6>0@3$4@1$2@1$1@1$0#8^5@3$5@1$1@1$0#8^4@3$5@1$1@1$0#8^3^2>0@3$4$6@2$3@1$1@1$0#8^4^2>0@2$e@2$d@2$h2@1$0#k0^8@1$f@2$3@1$1@1$0#8^7@2$h0+2+k0@3$4@1$8@1$2@1$1@1$0#8@4$c^a@2$b^9^8@3$h1@1$0#k0^9@1$9@2$3@1$1@1$0#8^7^4@2$7@1$2@1$1@1$0#8^6").
Proof.
  intros segs sp bytes pre mid post k Hb Hk Hnw.
  pose proof (u64_range sp) as Hsp64.
  assert (Hlenpre : (length pre <= length bytes)%nat)
    by (rewrite Hb, !length_app; lia).
  assert (Hu : bv_unsigned (sp + nat_to_word (length pre)) = (bv_unsigned sp + Z.of_nat (length pre))%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
    apply Z.mod_small. lia. }
  assert (Hsp : (bv_unsigned sp <= bv_unsigned (sp + nat_to_word (length pre)))%Z) by lia.
  assert (Hlen : (Z.to_nat (bv_unsigned (sp + nat_to_word (length pre)) - bv_unsigned sp) + k <= length bytes)%nat)
    by (rewrite Hu, Hb, !length_app; lia).
  rewrite (rdn_stack segs sp bytes k _ Hsp Hlen Hnw).
  rewrite Hu.
  replace (Z.to_nat (bv_unsigned sp + Z.of_nat (length pre) - bv_unsigned sp)) with (length pre) by lia.
  rewrite Hb, skipn_app, skipn_all, Nat.sub_diag.
  cbn [app]. rewrite skipn_O.
  rewrite firstn_app, <- Hk, firstn_all, Nat.sub_diag.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_image_in_block : ltac2:(zQ "h30!ld!s5!iu2!sob!rje!qk5!hq3!hr4!hqa!ih5!jo6!iu9!hl7!sld!ji7!sq6!sr9!sne!hp2>4segs@1$2$e>2ph$d>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>5hwcap@1$1@1$0#k0>4draw$h1>1a@1$1@1$0#k0>1n$a>0@2$7@2$6@2$9@1$0#k0^2@1$8^1@2$f^8@7$3^9^8^7^6^5^4^3>0@2$7@2$6@2$9@1$0#k0^3@1$8^2@2$h2+2+k0@3$c@1$b@1$2@1$1@1$0#8@4$5^c@2$4^a@7$h0^b^a^9^8^7^6^5^4^3@4$5^c@2$4^a@7$3^b^a^9^8^7^6^5^4^3").
Proof.
  intros segs ph sp argv envp uid hwcap draw a n Hin Hnw.
  apply rdn_ext; [exact Hnw|].
  intros x Hx. apply stack_to_mem_image_in_block. lia.
Qed.

(* [comment removed for export] *)
Lemma read_at_offset_image : ltac2:(zQ "h70!ld!s5!iu2!kj7!hl7!kk0!jo6!sob!jj9!iu9!sic!sld!ji7!sr9!sne!rje!qk5!hq3!hs8!hqa!hp2!kk6!ih5>4segs@1$2$c>2ph$b>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>5hwcap@1$1@1$0#k0>4draw$e>3pre@1$2@1$1@1$0#8>3mid@1$2@1$1@1$0#8>4post@1$2@1$1@1$0#8>1k$6>0@3$4@1$2@1$1@1$0#8@7$7^b^a^9^8^7^6^5@3$5@1$1@1$0#8^4@3$5@1$1@1$0#8^3^2>0@3$4$6@2$3@1$1@1$0#8^4^2>0@2$h2@2$h1@2$h6@1$0#k0^c@1$h3@2$3@1$1@1$0#8@7$7^d^c^b^a^9^8^7@2$h4+2+k0@3$4@1$9@1$2@1$1@1$0#8@4$h0^f@2$f^d@7$d^e^d^c^b^a^9^8@3$h5@1$0#k0^d@1$a@2$3@1$1@1$0#8^7^4@2$8@1$2@1$1@1$0#8^6").
Proof.
  intros segs ph sp argv envp uid hwcap draw pre mid post k Hb Hk Hnw.
  pose proof (u64_range sp) as Hsp64.
  assert (Hlen : (length pre + length mid <= length (build_stack_bytes ph sp argv envp uid hwcap draw))%nat)
    by (rewrite Hb, !length_app; lia).
  assert (Hu : bv_unsigned (sp + nat_to_word (length pre))
               = (bv_unsigned sp + Z.of_nat (length pre))%Z).
  { unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    rewrite bv_wrap_add_idemp_r, bv_wrap64_mod. apply Z.mod_small. lia. }
  rewrite rdn_image_in_block
    by (unfold entry_block_top; rewrite Hu; lia).
  exact (read_at_offset segs sp _ pre mid post k Hb Hk Hnw).
Qed.

Lemma read_argc : ltac2:(zQ "h50!ld!s5!iu2!jj9!kj7!iu9!hl7!sl1!qp7!sld!ji7!sr9!sne!sob!rje!qk5!hq3!hs8!hqa!hp2!ih5>2ph$9>4segs@1$2$a>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$c>0@2$h1@2$h0@2$h4@1$0#k0^6@1$h2@2$4@1$1@1$0#8@7$d^8^6^5^4^3^2^1@2$h3+2+k0@3$6@1$5@1$2@1$1@1$0#8@4$f^8@2$e^7@7$b^9^7^6^5^4^3^2^7N8@2$3@1$2@1$1@1$0#8@1$8@2$7@1$2@1$1@1$0#8^6").
Proof.
  intros ph segs sp argv envp uid hw rnd Hnw.
  destruct (bsb_argc_prefix ph sp argv envp uid hw rnd) as [tl E].
  pose proof (read_at_offset_image segs ph sp argv envp uid hw rnd [] (word_le8 (len_word argv)) tl 8%nat) as H.
  cbn [length] in H.
  rewrite word_add_0 in H.
  apply H; [rewrite E; reflexivity|reflexivity|exact Hnw].
Qed.

(* [comment removed for export] *)
Lemma read_byte_at_image : ltac2:(zQ "hd0!ld!s5!iu2!kj7!kk0!hl7!sob!jj9!jq4!jo6!jqb!iu9!qrf!ssf!st5!sic!sld!ji7!sr9!sne!rje!qk5!hq3!hs8!hqa!hp2!rb!kk6!ih5>4segs@1$2$h1>2ph$h0>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>5hwcap@1$1@1$0#k0>4draw$h3>3pre@1$2@1$1@1$0#8>1s@1$2@1$1@1$0#8>4post@1$2@1$1@1$0#8>1j$9>0@3$5@1$2@1$1@1$0#8@7$6^b^a^9^8^7^6^5@3$4@1$1@1$0#8^4@3$4@1$1@1$0#8^3^2>0@2$d^2@2$3@1$1@1$0#8^4>0@2$h7@2$h6@2$hc@1$0#k0^c@1$h8@2$3@1$1@1$0#8@7$6^d^c^b^a^9^8^7@2$h9+2+k0@3$5@1$b@1$2@1$1@1$0#8@4$h5^f@2$h4^d@7$h2^e^d^c^b^a^9^8@3$hb@1$0#k0^d@1$f@2$c@2$3@1$1@1$0#8^7^4N1@2$7@1$2@1$1@1$0#8@3$8@1$1@1$0#8@4$e@1$1@1$0#8^4^6@2$ha@1$0#8Z@1$a@1$1@1$0#8").
Proof.
  intros segs ph sp argv envp uid hwcap draw pre s post j Hb Hj Hnw.
  destruct (nth_error_skipn_cons s j Hj) as [b [Hnth Hskip]].
  assert (Hsj : s = firstn j s ++ b :: skipn (S j) s)
    by (rewrite <- Hskip; symmetry; apply firstn_skipn).
  pose proof (read_at_offset_image segs ph sp argv envp uid hwcap draw
                (pre ++ firstn j s) [b] (skipn (S j) s ++ post) 1%nat) as H.
  rewrite length_app in H.
  rewrite firstn_length_le in H by lia.
  replace (nth j s (Z_to_bv 8 0)) with b by (symmetry; apply (nth_error_nth _ _ _ Hnth)).
  apply H; [|reflexivity|exact Hnw].
  rewrite Hb. rewrite Hsj at 1. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition wrap_mem : ltac2:(zQ "60!ld!s5!iu2!iu9!sld!sne>2ph$4>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$5>0@1$1@1$0#k0@1$3@1$1@1$0#8") := ltac2:(zQ "h20!ld!s5!iu2!iu9!ih5!jj9!ua!jj2!stc!sld!sr9!sne!rje!th1!ti3!ip5!ii3!rb\2ph$9\2sp@1$1@1$0#k0\4argv@1$2@1$2@1$1@1$0#8\4envp@1$2@1$2@1$1@1$0#8\3uid@1$1@1$0#k0\2hw@1$1@1$0#k0\3rnd$b\4addr@1$1@1$0#k0M3\1x@1$3@1$1@1$0#8@1$3@1$1@1$0#8@3$c^7@7$a^8^7^6^5^4^3^2^1\1b@1$1@1$0#8@2$5@1$1@1$0#8^1M6\0$6@1$3@1$1@1$0#8@2$8@2$e@2$h0@2$4@1$0#k0^7$d@2$4@1$0#k0^1@2$f@2$4@1$0#k0^1@2$4@1$0#k0^7@2$5@1$1@1$0#8@2$h1@1$0#8Z@1$7@1$1@1$0#8").

Lemma init_mkst : ltac2:(zQ "h50!ld!s5!iu2!hg5!nsc!hjf!hk4!rb!hl7!ig5!sld!ji7!ni1!tia!sne!oa!tk1!tkd!nj2!tl2!tlb>4segs@1$2$b>2pc$9>2ph$a>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$e@3$8$c@9$d^9^8^7^6^1^5^4^3^2@5$h2$h1@3$4@3$4@2$f@1$0#5@1$1@1$0#k0@3$5@1$0#5+aKv$3@2$6@1$0#5+a@2$7@1$0#k0Z@3$5@1$0#5+2Kv$3@2$6@1$0#5+2^6@2$7@1$0#k0@1$h4^8@7$h0^7^6^5^4^3^2^1@1$h3^9").
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wrap_above_sp : ltac2:(zQ "c0!ld!s5!iu2!ih5!iu9!hl7!sld!sr9!sne!rje!tk1!hr4>2ph$6>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>1x@1$1@1$0#k0>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$8>0@2$b@2$3@1$0#k0^7@2$3@1$0#k0^4@3$5@1$4@1$1@1$0#8@8$a^9^8^7^6^4^3^2^5@3$9^8@7$7^9^8^7^6^4^3^2^5").
Proof.
  intros ph sp argv envp x uid hw rnd Hx. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|] eqn:E; [reflexivity|].
  assert (Hltf : Z.ltb (bv_unsigned x) (bv_unsigned sp) = false) by (apply Z.ltb_ge; lia).
  rewrite Hltf, andb_false_r. reflexivity.
Qed.

Lemma rdn_wrap_stack_above : ltac2:(zQ "h20!ld!s5!iu2!ih5!qk5!hr4!jo6!iu9!hl7!sld!ji7!sr9!sne!rje!tk1!hq3!hqa!hp2>4segs@1$2$a>2ph$9>2sp@1$1@1$0#k0>4argv@1$2@1$2@1$1@1$0#8>4envp@1$2@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1n$6>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$c>0@2$5@2$3@1$0#k0^8@2$3@1$0#k0^5>0@2$5@2$f@2$3@1$0#k0^6@1$h0^5@2$h1+2+k0@3$8@1$7@1$2@1$1@1$0#8@4$4^c@7$e^b^a^9^8^5^4^3^7^6@4$4^c@2$d^a@7$b^b^a^9^8^5^4^3^7^6").
Proof.
  intros segs ph sp argv envp a n uid hw rnd Hsp Hnw.
  apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wrap_above_sp. lia.
Qed.
End FPX3.
(* [comment removed for export] *)
