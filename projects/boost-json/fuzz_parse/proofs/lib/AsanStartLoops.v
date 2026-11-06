(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos01Z37Corelib4Init5Logici23andi22eq46Stdlib6ZArith6BinInt1Zk12lek12ltk13pow35stdpp9bitvectorbdefinitionsm97Z_to_bvm9bbv_unsigned69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~pe6v_addik13addm92bvpe4btgt37Corelib4Init9Datatypesv44boolpe4c_eqk13eqbi21Im92BVm94BvWfm99bv_signed3h5LinuxProcessSemantics5Riscv7Preludehjc5bvmappe4getri22or69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~hn7aregs_agreek13mulk16of_natv43natpe4mksti22ex37Corelib4Init3Nathte3add79OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanStartLoops7EnvLoop~~~~~~hv78env_post69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~ikc6mstepsv46option69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~ip89mem_grows79OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanStartLoops6PnLoop~~~~~~itf7cellrel3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjj2h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~jne6wbytesv44listv44Somev44consv46lengthv43nil37Corelib4Init5Peanoju62lejne7byte_atpe3rdnv44truejj28store_ok37Corelib5Lists7ListDefki45skipnitf7pn_post3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekkf7Segmentjj2afetch_wordv45falsejj28is_ecall3h5LinuxProcessSemantics5Riscv5Instrkr15instrv44prodv44pair3h5LinuxProcessSemantics5Riscv7DecodeCkucadecode_anykr1|41L1o1a1dkr13SZ8kr17ALU_ADDkr15OpImmkr15BC_NEkr16Branchi23notju62ltk13subkr15Storekr13SZ1kr15BC_EQ36Stdlib5Lists4Listlo62In" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma u_lit : ltac2:(zQ "90!h9!hf!j6!jc!l9!le!m3!o6!p0>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : ltac2:(zQ "b0!h9!hf!o6!j6!jc!t9!u2!l9!le!m3!u8>1a$1>1k$1>0@2$3@2$7Z^2@2$8^2@2$9+2+k0@3$4@1$a@1$0#k0@2$5@2$2@1$0#k0^3^2@2$2@1$0#k0@2$6^3^2").
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : ltac2:(zQ "b0!h9!hf!o6!j6!jc!ud!u2!l9!le!m3!u8>1a$1>1k$1>0@2$3@2$7Z^2@2$8^2@2$9+2+k0@3$4@1$a@1$0#k0@2$5@2$2@1$0#k0^3^2@2$2@1$0#k0@2$6^3^2").
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

Lemma c_eq_lit : ltac2:(zQ "b1!j6!h9!hf!l9!le!m3!o6!hgc!jc!hh3!hha&@2$0@2$3Z^2@2$4^2@2$5+2+k0>1a$2>1b$2>0~0>0~0@3$8$7@2$9@2$6@1$1#k0^4@2$6@1$1#k0^3@2$a^4^3").
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.

End FPX1.

(* [comment removed for export] *)
Ltac rif :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?u else ?v] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let c := eval vm_compute in (bv_eqb a b) in
              lazymatch c with
              | true => change (if bv_eqb a b then u else v) with u
              | false => change (if bv_eqb a b then u else v) with v
              end
          end
      end
  end.

(* [comment removed for export] *)
Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma signed12_0 : ltac2:(zQ "80!h9!hi0!jc!hf!hi4!hi9!u8!hj0@3$2$3@2$7@1$0#cKd@3$4@1$0#cZKv$1@2$5@1$0#cZ@1$6@1$0#cZ"). Proof. reflexivity. Qed.
Lemma signed12_1 : ltac2:(zQ "80!h9!hi0!jc!hf!hi4!hi9!u8!hj0@3$2$3@2$7@1$0#cKd@3$4@1$0#c+1Kv$1@2$5@1$0#c+1@1$6@1$0#c+1"). Proof. reflexivity. Qed.
Lemma signed12_8 : ltac2:(zQ "80!h9!hi0!jc!hf!hi4!hi9!u8!hj0@3$2$3@2$7@1$0#cKd@3$4@1$0#c+8Kv$1@2$5@1$0#c+8@1$6@1$0#c+8"). Proof. reflexivity. Qed.
Lemma signed12_m1 : ltac2:(zQ "80!h9!hi0!jc!hf!hi4!hi9!u8!hj0@3$2$3@2$7@1$0#cKd@3$4@1$0#c+vvfKv$1@2$5@1$0#c+vvf@1$6@1$0#c-1"). Proof. reflexivity. Qed.
Lemma signed13_m8 : ltac2:(zQ "80!h9!hi0!jc!hf!hi4!hi9!u8!hj0@3$2$3@2$7@1$0#dKd@3$4@1$0#d+hvv8Kv$1@2$5@1$0#d+hvv8@1$6@1$0#d-8"). Proof. reflexivity. Qed.
Lemma signed13_m12 : ltac2:(zQ "80!h9!hi0!jc!hf!hi4!hi9!u8!hj0@3$2$3@2$7@1$0#dKd@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4@1$6@1$0#d-c"). Proof. reflexivity. Qed.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EnvLoop.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable SEGS : ltac2:(zQ "20!js2!ko4@1$0$1").
  Variable x : Z.
  Variables w1 w2 w3 : bv 32.
  Hypothesis Hx : ltac2:(zQ "50!j6!u2!l9!le!m3@2$0@2$2Z?1x@2$3@2$1?1x+c@2$4+2+k0").
  Hypothesis F1 : ltac2:(zQ "70!h9!u8!js9!iof!jc!kof!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$6@1$0#k0?1x@2$2@1$1@1$0#i0?2w1").
  Hypothesis F2 : ltac2:(zQ "80!h9!u8!js9!iof!jc!kof!u2!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$7@1$0#k0@2$6?1x+4@2$2@1$1@1$0#i0?2w2").
  Hypothesis F3 : ltac2:(zQ "80!h9!u8!js9!iof!jc!kof!u2!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$7@1$0#k0@2$6?1x+8@2$2@1$1@1$0#i0?2w3").
  Hypothesis E1 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w1$1").
  Hypothesis E2 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w2$1").
  Hypothesis E3 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w3$1").
  Hypothesis D1 : ltac2:(zQ "f0!h9!hi0!hf!kt5!hi4!hi9!kte!js9!iof!ku5!kh1!jc!lh2!li0!lid@3$b@1$8@2$6$3$2@1$c?2w1@2$7@2$6$3$2@4$9$3$2@5$d$e$a@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
  Hypothesis D2 : ltac2:(zQ "e1!h9!hi0!hf!kt5!hi4!hi9!kte!js9!iof!ku5!jc!lh2!lj4!ljf&@3$4@1$0#5+9Kv$1@2$5@1$0#5+9@3$a@1$8@2$6$3$2@1$b?2w2@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+8Kv$1@2$5@1$0#c+8+4").
  Hypothesis D3 : ltac2:(zQ "e0!h9!hi0!hf!kt5!hi4!hi9!kte!js9!iof!ku5!jc!lh2!lk8!ll1@3$a@1$8@2$6$3$2@1$b?2w3@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv8Kv$1@2$5@1$0#d+hvv8+4").

  Variable M : ltac2:(zQ "30!h9!u8!iof>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable rom : ltac2:(zQ "30!h9!u8!iof>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  (* [comment removed for export] *)
  Variable e : Z.
  Variable envc : nat.
  Variable ptr : ltac2:(zQ "30!hsc!h9!u8>0$0@1$2@1$1#k0").
  Hypothesis He : ltac2:(zQ "70!u2!j6!l9!le!hrd!hs3!m3@2$1@2$2Z?1e@2$3@2$0@2$0?1e@2$4+8@1$5?4envc+h0@2$6+2+k0").
  Hypothesis Rk : ltac2:(zQ "h20!h9!js2!jc!u8!js9!hsc!iof!j6!llb!lm1!hf!jm9!kgb!u2!hrd!hs3!o6!p0>1k$5>0@2$9^1?4envc@2$7@3$2@1$6@1$1@1$3@1$0#8@4$c?4SEGS?1M@2$h0@1$0#k0@2$d?1e@2$e+8@1$f^2N8@2$4@1$1@1$3@1$0#8@2$bN8@1?3ptr^2@1$8@3$2$a@2$h1@1$0#k0@1?3ptr^2Z").
  Hypothesis Rn : ltac2:(zQ "c0!h9!js2!o6!u8!js9!iof!jc!jm9!kgb!u2!hrd!hs3@3$6@1$5@1$1@1$3@1$0#8@4$8?4SEGS?1M@2$2@1$0#k0@2$9?1e@2$a+8@1$b?4envcN8@2$4@1$1@1$3@1$0#8@2$7N8@2$2@1$0#k0Z").

  Definition env_post : ltac2:(zQ "30!h9!hm2!u8>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "f2!h9!u8!hi0!jc!hi4!hi9!j6!hm2!hmb!u2!o6!hn2!hqf!hrd!hs3&@3$4@1$0#5+9Kv$2@2$5@1$0#5+9&@3$4@1$0#5+aKv$2@2$5@1$0#5+a\4regs@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$6@3$3@1$1@1$0#k0@2$8^1~0@2$a@1$0#k0@2$9@2$9?1e@2$d+8@1$e?4envc+8@2$6@3$3@1$1@1$0#k0@2$8^1~1@2$a@1$0#k0Z@3$c\1r@1$1@1$0#5@2$b@3$3@1$1@1$0#5^1~0@3$3@1$1@1$0#5^1~1^2^1").

  Lemma env_loop : ltac2:(zQ "h30!h9!u8!hsc!hm2!o6!jc!ht2!u2!hi0!j6!ht9!hv0!ik0!io5!hmb!hrd!hs3!hi4!hi9>1n$2>1k$2>4regs@2$3@1$0#5@1$1@1$0#k0>0@3$5$2@2$b^2^3?4envc>0@3$5@1$1@1$0#k0@2$e^2@3$h1@1$0#5+9Kv$8@2$h2@1$0#5+9@2$4@1$0#k0@2$7?1e@2$f+8@1$h0^3@2$a@2$3@1$0#5@1$1@1$0#k0\5regs'@2$3@1$0#5@1$1@1$0#k0@2$9@3$d?4SEGS@5$6?2fx^4@2$4@1$0#k0?1x?1M?3rom@5$6?2fx^1@2$4@1$0#k0@2$7?1x+c?1M?3rom@2$c^4^1").
  Proof.
    induction n as [|n IH]; intros k regs Hkn H9.
    - (* [comment removed for export] *)
      assert (k = envc) by lia. subst k.
      eexists. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (Z_to_bv 64 0) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rn.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_same by reg_neq_tac. reflexivity.
        * rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity.
        * intros r Hr. rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
    - assert (Hk : (k < envc)%nat) by lia.
      destruct (Rk k Hk) as [Rd Hnz].
      destruct (IH (S k) (regupd (regupd regs 10 (ptr k)) 9 (Z_to_bv 64 (e + 8 * Z.of_nat (S k)))) ltac:(lia)) as [regs' [Hms Hpost]].
      { rewrite getr_same by reg_neq_tac. reflexivity. }
      exists regs'. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (ptr k) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rd.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_tk SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. apply c_eq_0_false. exact Hnz. }
        rewrite signed13_m8, btgt_lit by lia. pc_is x.
        replace (e + 8 * Z.of_nat k + 8) with (e + 8 * Z.of_nat (S k)) by lia.
        exact Hms.
      + ndestruct Hpost as (P9 & P10 & Pag). split; [exact P9|]. split; [exact P10|].
        intros r Hr. rewrite (Pag r Hr). rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End EnvLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PnLoop.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable SEGS : ltac2:(zQ "20!js2!ko4@1$0$1").
  Variable x : Z.            (* [comment removed for export] *)
  Variables w0 w1 w2 w3 w4 : bv 32.
  Hypothesis Hx : ltac2:(zQ "50!j6!u2!l9!le!m3@2$0@2$2+8?1x@2$3@2$1?1x+c@2$4+2+k0").
  Hypothesis F0 : ltac2:(zQ "80!h9!u8!js9!iof!jc!kof!lm7!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$7@1$0#k0@2$6?1x+8@2$2@1$1@1$0#i0?2w0").
  Hypothesis F1 : ltac2:(zQ "80!h9!u8!js9!iof!jc!kof!lm7!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$7@1$0#k0@2$6?1x+4@2$2@1$1@1$0#i0?2w1").
  Hypothesis F2 : ltac2:(zQ "70!h9!u8!js9!iof!jc!kof!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$6@1$0#k0?1x@2$2@1$1@1$0#i0?2w2").
  Hypothesis F3 : ltac2:(zQ "80!h9!u8!js9!iof!jc!kof!u2!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$7@1$0#k0@2$6?1x+4@2$2@1$1@1$0#i0?2w3").
  Hypothesis F4 : ltac2:(zQ "80!h9!u8!js9!iof!jc!kof!u2!o6@3$4@1$3@1$1@1$0#i0@2$5?4SEGS@2$7@1$0#k0@2$6?1x+8@2$2@1$1@1$0#i0?2w4").
  Hypothesis E0 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w0$1").
  Hypothesis E1 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w1$1").
  Hypothesis E2 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w2$1").
  Hypothesis E3 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w3$1").
  Hypothesis E4 : ltac2:(zQ "40!hgc!kpd!jc!kq5@3$2$0@1$3?2w4$1").
  Hypothesis D0 : ltac2:(zQ "e0!h9!hi0!hf!kt5!hi4!hi9!kte!js9!iof!ku5!jc!lh2!lid!lmd@3$a@1$8@2$6$3$2@1$b?2w0@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+aKv$1@2$5@1$0#5+a@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#cZKv$1@2$5@1$0#cZ+4").
  Hypothesis D1 : ltac2:(zQ "e1!h9!hi0!hf!kt5!hi4!hi9!kte!js9!iof!ku5!jc!lh2!lj4!ljf&@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$a@1$8@2$6$3$2@1$b?2w1@2$7@2$6$3$2@4$9$3$2@4$d$c~0~0@3$4@1$0#c+1Kv$1@2$5@1$0#c+1+4").
  Hypothesis D2 : ltac2:(zQ "f0!h9!hi0!hf!kt5!hi4!hi9!kte!js9!kpd!iof!ku5!jc!lh2!li0!ln6@3$b@1$9@2$6$3$2@1$c?2w2@2$7@2$6$3$2@4$a$3$2@5$d$e$8@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+bKv$1@2$5@1$0#5+b@3$4@1$0#c+vvfKv$1@2$5@1$0#c+vvf+4").
  Hypothesis D3 : ltac2:(zQ "e0!h9!hi0!hf!kt5!hi4!hi9!kte!js9!iof!ku5!jc!lh2!lnd!ll1@3$a@1$8@2$6$3$2@1$b?2w3@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5+cKv$1@2$5@1$0#5+c@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").
  Hypothesis D4 : ltac2:(zQ "e0!h9!hi0!hf!kt5!hi4!hi9!kte!js9!iof!ku5!jc!lh2!lk8!ll1@3$a@1$8@2$6$3$2@1$b?2w4@2$7@2$6$3$2@4$9$3$2@4$d$c@3$4@1$0#5+dKv$1@2$5@1$0#5+d@3$4@1$0#5ZKv$1@2$5@1$0#5Z@3$4@1$0#d+hvv4Kv$1@2$5@1$0#d+hvv4+4").

  Variable M0 : ltac2:(zQ "30!h9!u8!iof>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable rom : ltac2:(zQ "30!h9!u8!iof>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  (* [comment removed for export] *)
  Variable p pn : Z.
  Variable s : ltac2:(zQ "30!js2!h9!u8@1$0@1$2@1$1#8").
  Hypothesis Hp : ltac2:(zQ "40!l9!j6!u2!m3@2$1@2$0Z?1p@2$0@2$2?1p+8@2$3+2+k0").
  Hypothesis Hpn : ltac2:(zQ "90!u2!jt7!j6!h9!l9!le!hs3!m3!u8@2$2@2$4Z?2pn@2$5@2$0@2$0?2pn@1$6@2$1@1$8@1$3#8?1s+2@2$7+2+k0").
  Hypothesis Hapart : ltac2:(zQ "70!u2!l9!jt7!hn2!h9!hs3!u8@2$3@2$1@2$0?1p+8?2pn@2$1@2$0@2$0?2pn@1$5@2$2@1$6@1$4#8?1s+1?1p").
  Hypothesis Hnz : ltac2:(zQ "50!h9!llb!lp9!o6!u8@1$1@3$2@1$4@1$0#8@2$3@1$0#8Z?1s").
  Hypothesis Hrd : ltac2:(zQ "h00!h9!u8!js2!js9!jt0!jt7!hsc!ju0!iof!jc!jva!kg0!kgb!u2!hs3!o6>1j$6>0@2$a^1@2$5@1$1@1$0#8?1s@3$9@1$8@1$2@1$1@1$0#8@4$c?4SEGS?2M0@2$f@1$0#k0@2$d?2pn@1$e^2N1@2$3@1$2@1$1@1$0#8@3$4@1$1@1$0#8@2$b?1s^2@1$7@1$1@1$0#8").
  Hypothesis Hst : ltac2:(zQ "60!hgc!kh1!jc!h9!kh8!o6@3$2$0@4$4?4SEGS?2M0@2$5@1$3#k0?1pN8$1").

  (* [comment removed for export] *)
  Definition cellrel : ltac2:(zQ "30!h9!u8!iof>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "b0!h9!u8!iof!p0!j6!jc!hn2!it2!u2!l9!le\1M>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$4>1a@1$1@1$0#k0>0@2$6@2$a@2$3@1$0#k0^1?1p@2$9@2$8?1p+8@2$3@1$0#k0^1@3$5@1$2@1$1@1$0#8@1^3^2@1?2M0^2@2$7?2M0^1").

  Lemma cellrel_refl : ltac2:(zQ "10!ji7@1$0?2M0").
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma cellrel_wbytes : ltac2:(zQ "70!h9!u8!ji7!iof!jm9!jr8!o6>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8>1v@1$1@1$0#k0>0@1$2^2@1$2@3$5^3@2$6@1$0#k0?1p@2$4N8^2").
  Proof.
    intros M v [H1 H2]. split.
    - intros a Ha. rewrite <- (H1 a Ha).
      destruct Ha as [Ha|Ha].
      + apply wbytes_below; rewrite ?length_N_to_le_bytes, u_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
      + apply wbytes_above. rewrite length_N_to_le_bytes, u_lit by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact H2 | apply wbytes_grows].
  Qed.

  Lemma cellrel_rd : ltac2:(zQ "h10!h9!u8!js2!iof!js9!jt0!jt7!hsc!ju0!jc!jva!ji7!kg0!kgb!u2!hs3!o6>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8>1j$7>0@1$b^2>0@2$a^2@2$6@1$1@1$0#8?1s@3$9@1$3@1$2@1$1@1$0#8@4$d?4SEGS^4@2$h0@1$0#k0@2$e?2pn@1$f^3N1@2$4@1$2@1$1@1$0#8@3$5@1$1@1$0#8@2$c?1s^3@1$8@1$1@1$0#8").
  Proof.
    intros M j [H1 _] Hj. rewrite <- (Hrd j Hj). apply rdn_ext.
    - rewrite u_lit by lia. change (Z.of_nat 1) with 1. lia.
    - intros y Hy. rewrite u_lit in Hy by lia. change (Z.of_nat 1) with 1 in Hy. apply H1. lia.
  Qed.

  Lemma cellrel_st : ltac2:(zQ "90!h9!u8!hgc!iof!kh1!jc!kh8!ji7!o6>1M>0@1$1@1$0#k0@1$3@1$1@1$0#8>0@1$7^1@3$5$2@4$6?4SEGS^2@2$8@1$0#k0?1pN8$4").
  Proof. intros M [_ H2]. eapply store_ok_mono; [exact H2 | exact Hst]. Qed.

  Definition pn_post : ltac2:(zQ "30!h9!hm2!u8>4regs@2$1@1$0#5@1$2@1$0#k0>5regs'@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "f2!h9!u8!hi0!jc!hi4!hi9!j6!hm2!hmb!u2!o6!jt7!hn2!hqf!hs3&@3$4@1$0#5+bKv$2@2$5@1$0#5+b&@3$4@1$0#5+dKv$2@2$5@1$0#5+d\4regs@2$7@1$0#5@1$1@1$0#k0\5regs'@2$7@1$0#5@1$1@1$0#k0@2$6@3$3@1$1@1$0#k0@2$8^1~0@2$a@1$0#k0@2$9@2$9?2pn@1$e@2$b@1$1@1$0#8?1s+1@2$6@3$3@1$1@1$0#k0@2$8^1~1@2$a@1$0#k0Z@3$d\1r@1$1@1$0#5@2$c@3$3@1$1@1$0#5^1~0@3$3@1$1@1$0#5^1~1^2^1").

  Lemma byte_u : ltac2:(zQ "60!h9!p0!j6!l9!le!u8>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
  Proof. intros b. pose proof (u8_range b). lia. Qed.

  Lemma pn_loop : ltac2:(zQ "h71!h9!u8!o6!jc!iof!hi0!hm2!hmb!u2!hi4!hi9!js2!j6!ht9!ji7!ht2!jt7!hsc!jva!kjb!kk4!io5!hs3&>0@1$1@1$0#k0@1$4@1$1@1$0#8>2l2@1$b@1$1@1$0#8>1j$h1>4regs@2$6@1$0#5@1$1@1$0#k0>1M~0>0@3$3@1$b@1$1@1$0#8@3$h3@1$1@1$0#8^3?1s^4>0@2$h2^4@2$h0@1$1@1$0#8?1s>0@3$3@1$1@1$0#k0@2$7^4@3$9@1$0#5+aKv$5@2$a@1$0#5+a@2$2@1$0#k0?1p>0@3$3@1$1@1$0#k0@2$7^5@3$9@1$0#5+bKv$5@2$a@1$0#5+b@2$2@1$0#k0@2$8@2$8?2pn@1$h6^6+1>0@3$3@1$1@1$0#k0@2$7^6@3$9@1$0#5+cKv$5@2$a@1$0#5+c@2$2@1$0#k0+if>0@1$e^6@2$d@2$6@1$0#5@1$1@1$0#k0\5regs'@2$6@1$0#5@1$1@1$0#k0@2$d~0\2M'~0@2$c@3$h5?4SEGS@5$f?2fx^a@2$2@1$0#k0?1x^9?3rom@5$f?2fx^2@2$2@1$0#k0@2$8?1x+c^1?3rom@2$c@2$h4^a^2@1$e^1").
  Proof.
    induction l2 as [|b l2 IH]; intros j regs M Hskip Hj H10 H11 H12 HM.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      subst j.
      exists (regupd regs 13 (Z_to_bv 64 (bv_unsigned (byte_at s (length s))))), M. split; [|split; [|exact HM]].
      + eapply mst_step; [reflexivity| |].
        { eapply (step_lbu SEGS regs _ M rom w2 13 11 4095 (byte_at s (length s)) F2 E2 D2).
          rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat (length s) + 1 + -1) with (pn + Z.of_nat (length s)) by lia.
          apply cellrel_rd; [exact HM | lia]. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        rewrite byte_at_len. change (bv_unsigned (Z_to_bv 8 0)) with 0.
        eapply mst_step; [reflexivity| |].
        { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
          rewrite getr_same by reg_neq_tac. rewrite getr_other by reg_neq_tac.
          rewrite H12. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 8).
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
          rewrite getr_same by reg_neq_tac. rewrite getr_zero. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_other by reg_neq_tac. exact H11.
        * rewrite getr_same by reg_neq_tac. rewrite byte_at_len. reflexivity.
        * intros r Hr. rewrite getr_other; [reflexivity|]. intros ->. apply Hr. auto.
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : byte_at s j = b).
      { unfold byte_at. rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : bv_unsigned b <> 0).
      { intros Hb0. apply Hnz. rewrite <- Hb in Hb0. rewrite nth_lt_byte_at in Hb0 by lia.
        replace (Z_to_bv 8 0) with (nth j s (Z_to_bv 8 0)); [apply nth_In; lia|].
        apply bv_eq. rewrite Hb0. reflexivity. }
      assert (Hskip' : skipn (S j) s = l2).
      { replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
      pose proof (byte_u b) as Hbu.
      (* [comment removed for export] *)
      set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
      assert (S1 : RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 x) M rom) = MachineOk (mkst regs1 (Z_to_bv 64 (x + 4)) M rom)).
      { erewrite (step_lbu SEGS regs _ M rom w2 13 11 4095 b F2 E2 D2).
        - rif. rewrite v_addi_lit by lia. reflexivity.
        - rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat j + 1 + -1) with (pn + Z.of_nat j) by lia. rewrite <- Hb.
          apply cellrel_rd; [exact HM | lia]. }
      assert (G13 : getr regs1 13 = Z_to_bv 64 (bv_unsigned b)) by (unfold regs1; rewrite getr_same by reg_neq_tac; reflexivity).
      assert (G10 : getr regs1 10 = Z_to_bv 64 p) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H10).
      assert (G11 : getr regs1 11 = Z_to_bv 64 (pn + Z.of_nat j + 1)) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H11).
      assert (G12 : getr regs1 12 = Z_to_bv 64 47) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H12).
      destruct (Z.eqb (bv_unsigned b) 47) eqn:Eb.
      + (* [comment removed for export] *)
        set (M1 := wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (pn + Z.of_nat j + 1)))).
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        assert (HM1 : cellrel M1) by (unfold M1; apply cellrel_wbytes; exact HM).
        ndestruct (IH (S j) regs2 M1 Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM1. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_tk SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_sd_at SEGS regs1 _ M rom w0 10 11 0 (Z_to_bv 64 p) _ F0 E0 D0).
            - rewrite G10, signed12_0, v_addi_lit by lia. f_equal. lia.
            - exact G11.
            - apply cellrel_st. exact HM. }
          fold M1. rewrite v_addi_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M1 rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * ndestruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
      + (* [comment removed for export] *)
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        ndestruct (IH (S j) regs2 M Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite v_addi_lit by lia. pc_is (x + 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_bne_tk SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
            rewrite G13, getr_zero. apply c_eq_0_false. rewrite u_lit by lia. exact Hbnz. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * ndestruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End PnLoop.
(* [comment removed for export] *)
