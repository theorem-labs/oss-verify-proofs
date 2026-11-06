(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec SeqExec StepTac WalkTac LibAtomic StartupTac.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq37Corelib4Init9Datatypesla4boolla6option01Zla4listhfbbv_unsignedla4Some3h5LinuxProcessSemantics5Riscv5Instrq15instrla4prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticst4dmachine_state3h5LinuxProcessSemantics5Riscv7Preludehhb5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hka4getrhka4mkstla5falsela4pairla4truek11I3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehqfdbytes_le_to_Z3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehuf7Segmentt49MachineOkt4afetch_wordt48is_ecallt4emachine_resultt44stept48store_okt4h0word_to_le_bytes3h5LinuxProcessSemantics5Riscv7DecodeCioaadecode_anyq17AMO_ADDq12AWq13Amohhb6bv_eqb69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~itd6wbyteshka3rdnhka6regupdhka6v_addihka4v_lw46Stdlib6ZArith6BinInt1Zjk43addjk46modulohf2BVhf4BvWfhf7Z_to_bv" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma step_amoadd_w_at : ltac2:(zQ "ib1!h9!jc!l5!n2!n9!o2!o5!oc!pa!s5!sd!hgb!hk1!ho5!hod!hp5!hpd!hq4!hqb!hte!ii4!iif!ijb!ik8!il3!im4!imb!in6!ir0!ire!is8!isd!it3!jh7!ji1!ji8!jj2!jjc!jlc!jm3!jmd!jn2!jn9&>0@1$1@1$0#k0@1$4@1$1@1$0#8>4segs@1$6$h4>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2aq$3>2rl$3>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1a@1$1@1$0#k0>2bs@1$6@1$1@1$0#8>1v@1$1@1$0#k0>1s@1$1@1$0#k0>1r@1$1@1$0#k0>0@3$2@1$4@1$1@1$0#i0@2$h6^h0^e@2$8@1$1@1$0#i0^b>0@3$2$3@1$h7^c$f>0@3$2@1$4@2$a$9$5@1$hc^d@2$8@2$a$9$5@4$h0$9$5@7$hf$hd$he^c^b^a^9^8+4>0@3$2@1$1@1$0#k0@2$d^h2^a^8>0@3$2@1$1@1$0#k0@2$d^h3^a^6>0@3$2@1$1@1$0#k0@2$ia@1$0#k0@2$i6@2$7@1$0#k0^8@2$7@1$0#k0^7^6>0@3$2$5@2$i7@2$7@1$0#k0^b+4Z>0@3$2@1$4@1$6@1$1@1$0#8@4$i2^h7^h4^cN4@2$8@1$6@1$1@1$0#8^b>0@3$2$5@1$h3^c@2$7@1$0#k0^b>0@3$2$3@4$ha^h9^h6^eN4$h1@3$2@1$h8$b@2$h9^ha@5$e?2fx^h9^h8^h7^h6@2$h5$b@5$e?2fxM3\0$3@2$c@1$0#5@1$1@1$0#k0@3$i0@1$0#5^h2@3$i8@1$0#5ZKv$h2@2$i9@1$0#5Z^h9@3$i3^h9^h2@1$i5^d@2$i4^h8+4@3$i1^h7^f@2$hbN4^b^h6").
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 a bs v s r Hfetch Hecall Hdecode Ha Hs Hr Hal Hread Hv Hok.
  subst a s r.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite Hok. cbv beta iota. rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4, write_to_mem_wbytes.
  assert (HA : Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 v) (low32 (getr regs rs2))))
               = word_to_le_bytes 4 (Z_to_bv 64 (bv_unsigned v + bv_unsigned (getr regs rs2)))).
  { unfold amo_val, low32, word_to_le_bytes. rewrite bv_add_unsigned, !bv_extract_unsigned, !Z.shiftr_0_r, Z_to_bv_unsigned.
    rewrite <- (Z_to_le_bytes_wrap 4 32 (bv_wrap 64 _)) by (cbn; lia).
    f_equal. rewrite bv_wrap_bv_wrap by (cbn; lia). rewrite bv_wrap_add_idemp. reflexivity. }
  rewrite HA. unfold regupd. destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.
End FPX1.

(* [comment removed for export] *)
Ltac amo_step F D aa bsv vv ss rr rdtac valtac oktac :=
  chain_step;
  [ reflexivity
  | eapply step_amoadd_w_at with (a := aa) (bs := bsv) (v := vv) (s := ss) (r := rr);
    [ exact F | reflexivity | exact D | vclose | vclose | vclose
    | lazymatch goal with |- ?g => first [ check_closed_term g; vm_compute; reflexivity | idtac ] end
    | addr_norm; rdtac | valtac | oktac ]
  | step_simpl; push_store ]; vnorm; pin.
