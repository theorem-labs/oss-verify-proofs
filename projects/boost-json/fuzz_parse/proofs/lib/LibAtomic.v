(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec SeqExec StepTac.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm2dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeq95bvmapk14Nonek14Somem2h3Build_machine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~vc6fp_csrvc7fp_regs37Corelib4Init5Logichka2eqk14bool01Zk14list3h5LinuxProcessSemantics5Riscv5Instrhn55instrvc4getrk14prodhfbbv_unsignedk15falsek14pairhka1I3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseht2dbytes_le_to_Z3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeih27Segmentm29MachineOkm2afetch_wordm28is_ecallm2emachine_resultm24step3h5LinuxProcessSemantics5Riscv7DecodeCioeadecode_anyhn52AWhn52Lrq96bv_eqb69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibAtomic~~~~~~it76mkst_rvc4mkstvc3rdnvc6regupdvc6v_addivc4v_lw46Stdlib6ZArith6BinInt1Zjk36modulohf2BVhf4BvWfhn52ADk14truem28store_okm2h0word_to_le_byteshn52Sc69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~jq36wbyteshf7Z_to_bvhn56Branchhn5bbranch_cond3h5LinuxProcessSemantics5Riscv3Semkgacbranch_takenhn55BC_NEvc4c_eq" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition mkst_r : ltac2:(zQ "51!h9!jc!l9!p9!sf&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$4@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1r@1$1@1$0#k0$3") := ltac2:(zQ "91!h9!jc!l9!t7!te!u5!sf!hj7!hk0&>0@1$1@1$0#k0@1$2@1$1@1$0#8\4regs@2$6@1$0#5@1$1@1$0#k0\2pc@1$1@1$0#k0\3mem~0\3rom~0\1r@1$1@1$0#k0@8$5^5@1$8?2fx^4@1$3@1$1@1$0#k0@2$4@1$1@1$0#k0^1@1$7?2fx^3^2").

End FPX1.

Ltac atomic_pipeline Hfetch Hecall Hdecode :=
  unfold mkst_r;
  step_pipeline Hfetch Hecall Hdecode;
  cbv beta iota zeta delta [amo_aligned amo_bytes ms_fregs ms_fcsr];
  rewrite ?bv_eqb0_is_x0.

(* [comment removed for export] *)
Ltac norm_pc_r :=
  try lazymatch goal with
      | |- CatSim.msteps _ (mkst_r _ ?p _ _ _) _ => wlit p
      end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma step_lr_w : ltac2:(zQ "i51!h9!jc!hle!hm4!l9!hmb!hme!te!hp9!hq2!hq9!p9!sf!hr0!hre!hs6!hsd!ig1!ik7!il2!ile!imb!in6!io7!ir4!is2!is8!ise!jh3!jhd!ji4!jia!jj3!jjc!jlb!jm5!jma&>0@1$1@1$0#k0@1$4@1$1@1$0#8>4segs@1$6$h2>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2aq$3>2rl$3>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2bs@1$6@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2@1$4@1$1@1$0#i0@2$h4^c^a@2$7@1$1@1$0#i0^7>0@3$2$3@1$h5^8$e>0@3$2@1$4@2$a$8$5@1$h8^9@2$7@2$a$8$5@4$f$8$5@5$ha$h9^8^7^6^5+4>0@3$2$5@2$i2@2$d@1$0#k0@2$9^e^6+4Z>0@3$2@1$4@1$6@1$1@1$0#8@4$he^h0^d@2$9^f^7N4@2$7@1$6@1$1@1$0#8^6>0@3$2$5@1$h1^7@2$d@1$0#k0^6@3$2@1$h6$b@2$h7^h2@5$hd?2fx^h1^h0^f^e@2$h3$b@6$hc?2fxM3\0$3@2$c@1$0#5@1$1@1$0#k0@3$hb@1$0#5^a@3$i3@1$0#5ZKv$h0@2$i4@1$0#5Z^h1@3$hf^h1^a@1$i1^7@2$i0^h0+4^f^e@2$9^h1^9").
Proof.
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma step_lr_d : ltac2:(zQ "i41!h9!jc!hle!hm4!l9!hmb!hme!te!hp9!hq2!hq9!p9!sf!hr0!hre!hs6!hsd!ig1!ik7!il2!ile!imb!in6!io7!ir4!jn1!is8!ise!jh3!jhd!ji4!jia!jj3!jlb!jm5!jma&>0@1$1@1$0#k0@1$4@1$1@1$0#8>4segs@1$6$h2>4regs@2$c@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2aq$3>2rl$3>2rd@1$1@1$0#5>2rs@1$1@1$0#5>2bs@1$6@1$1@1$0#8>1v@1$1@1$0#k0>0@3$2@1$4@1$1@1$0#i0@2$h4^c^a@2$7@1$1@1$0#i0^7>0@3$2$3@1$h5^8$e>0@3$2@1$4@2$a$8$5@1$h8^9@2$7@2$a$8$5@4$f$8$5@5$ha$h9^8^7^6^5+4>0@3$2$5@2$i1@2$d@1$0#k0@2$9^e^6+8Z>0@3$2@1$4@1$6@1$1@1$0#8@4$he^h0^d@2$9^f^7N8@2$7@1$6@1$1@1$0#8^6>0@3$2$5@1$h1^7@2$d@1$0#k0^6@3$2@1$h6$b@2$h7^h2@5$hd?2fx^h1^h0^f^e@2$h3$b@6$hc?2fxM3\0$3@2$c@1$0#5@1$1@1$0#k0@3$hb@1$0#5^a@3$i2@1$0#5ZKv$h0@2$i3@1$0#5Z^h1@3$hf^h1^a^7@2$i0^h0+4^f^e@2$9^h1^9").
Proof.
  intros segs regs pc mem rom w aq rl rd rs bs v Hfetch Hecall Hdecode Hal Hread Hv.
  assert (Hz : bv_extract 0 64 v = v).
  { apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_unsigned. }
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs then Z_to_bv 64 0 else reg_get regs rs) with (getr regs rs).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  rewrite ov_rdn, Hread. cbv beta iota.
  rewrite (le_word_v _ _ Hv), Hz, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sc_w_ok : ltac2:(zQ "i71!h9!jc!hle!hm4!hq2!l9!hmb!hp9!te!hq9!p9!sf!hre!hme!hs6!jn7!hsd!ik7!il2!ile!imb!in6!io7!jne!jo9!ir4!is2!jpd!ise!jtd!jh3!jhd!jia!jj3!jlb!jm5!jma!ju7!hr0&>0@1$1@1$0#k0@1$5@1$1@1$0#8>4segs@1$d$h1>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2aq$3>2rl$3>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1r@1$1@1$0#k0>0@3$2@1$5@1$1@1$0#i0@2$h3^c^a@2$8@1$1@1$0#i0^7>0@3$2$3@1$h4^8$c>0@3$2@1$5@2$9$7$6@1$h9^9@2$8@2$9$7$6@4$e$7$6@6$hb$ha^8^7^6^5^4+4>0@3$2$6@2$i2@2$i6@1$0#k0@2$4^e^6+4Z>0@3$2@1$1@1$0#k0^5@2$4^f^7>0@3$2$3@4$h7^h1^e@2$4^h0^8N4$f@3$2@1$h5$a@2$h6^h2@6$he?2fx^h1^h0^f^e^7@2$h2$a@5$hf?2fxM3\0$3@2$b@1$0#5@1$1@1$0#k0@3$hc@1$0#5^a@3$i3@1$0#5ZKv$h0@2$i4@1$0#5Z^h1@3$i0^h1^a@2$i5@1$0#k0Z@2$i1^h0+4@3$hd^f@2$4^h1^9@2$h8N4@2$4^h1^8^e").
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  subst r. rewrite Z.eqb_refl. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  unfold regupd.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sc_d_ok : ltac2:(zQ "i71!h9!jc!hle!hm4!hq2!l9!hmb!hp9!te!hq9!p9!sf!hre!hme!hs6!jn7!hsd!ik7!il2!ile!imb!in6!io7!jne!jo9!ir4!jn1!jpd!ise!jtd!jh3!jhd!jia!jj3!jlb!jm5!jma!ju7!hr0&>0@1$1@1$0#k0@1$5@1$1@1$0#8>4segs@1$d$h1>4regs@2$b@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>2aq$3>2rl$3>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1r@1$1@1$0#k0>0@3$2@1$5@1$1@1$0#i0@2$h3^c^a@2$8@1$1@1$0#i0^7>0@3$2$3@1$h4^8$c>0@3$2@1$5@2$9$7$6@1$h9^9@2$8@2$9$7$6@4$e$7$6@6$hb$ha^8^7^6^5^4+4>0@3$2$6@2$i2@2$i6@1$0#k0@2$4^e^6+8Z>0@3$2@1$1@1$0#k0^5@2$4^f^7>0@3$2$3@4$h7^h1^e@2$4^h0^8N8$f@3$2@1$h5$a@2$h6^h2@6$he?2fx^h1^h0^f^e^7@2$h2$a@5$hf?2fxM3\0$3@2$b@1$0#5@1$1@1$0#k0@3$hc@1$0#5^a@3$i3@1$0#5ZKv$h0@2$i4@1$0#5Z^h1@3$i0^h1^a@2$i5@1$0#k0Z@2$i1^h0+4@3$hd^f@2$4^h1^9@2$h8N8@2$4^h1^8^e").
Proof.
  intros segs regs pc mem rom w aq rl rd rs1 rs2 r Hfetch Hecall Hdecode Hal Hr Hok.
  atomic_pipeline Hfetch Hecall Hdecode.
  change (if is_x0 rs1 then Z_to_bv 64 0 else reg_get regs rs1) with (getr regs rs1).
  change (if is_x0 rs2 then Z_to_bv 64 0 else reg_get regs rs2) with (getr regs rs2).
  rewrite Hal. change (negb (0 =? 0)%Z) with false. cbv beta iota.
  subst r. rewrite Z.eqb_refl. cbv beta iota.
  rewrite Hok. cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  unfold regupd, word_to_le_bytes.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma step_branch_ft_r : ltac2:(zQ "hb1!h9!jc!hle!l9!hmb!hp9!te!hm4!hre!hq9!p9!jh3!hq2!hme!hs6!ik7!il2!ile!imb!in6!io7!ir4!jv1!jvb!sf!kic!jj3&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$f>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1r@1$1@1$0#k0>1w@1$1@1$0#i0>1c$h7>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h1^b^9@2$6@1$1@1$0#i0^5>0@3$2$7@1$h2^6$8>0@3$2@1$3@2$9$5$4@1$h5^7@2$6@2$9$5$4@4$e$5$4@4$h6^6^5^4^3+4>0@3$2$7@3$h9^7@2$c^d^6@2$c^d^5$8@3$2@1$h3$a@2$h4^f@6$b?2fx^e^d^c^b^a@2$h0$a@6$b?2fx^e@2$ha^d+4^c^b^a").
Proof.
  intros segs regs pc mem rom r w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
  atomic_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
  destruct (is_x0 rs1); destruct (is_x0 rs2);
    cbv beta iota; rewrite Hc; cbv beta iota;
    rewrite b_npc4; reflexivity.
Qed.

Lemma step_bne_ft_r : ltac2:(zQ "hc1!h9!jc!hle!l9!hmb!hp9!te!hm4!hq9!p9!jh3!hq2!hre!hme!hs6!jn7!ik7!il2!ile!imb!in6!io7!ir4!kjc!jv1!sf!kk5!jj3&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$d$h0>4regs@2$h9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1r@1$1@1$0#k0>1w@1$1@1$0#i0>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>3imm@1$1@1$0#d>0@3$2@1$3@1$1@1$0#i0@2$h2^a^8@2$6@1$1@1$0#i0^4>0@3$2$7@1$h3^5$c>0@3$2@1$3@2$8$5$4@1$h6^6@2$6@2$8$5$4@4$e$5$4@4$h8$h7^5^4^3+4>0@3$2$7@2$ha@2$b^c^6@2$b^c^5$f@3$2@1$h4$9@2$h5^e@6$a?2fx^d^c^b^a^9@2$h1$9@6$a?2fx^d@2$hb^c+4^b^a^9").
Proof.
  intros segs regs pc mem rom r w rs1 rs2 imm Hf He Hd Hc.
  apply (step_branch_ft_r segs regs pc mem rom r w BC_NE rs1 rs2 imm Hf He Hd).
  cbn [branch_taken]. unfold c_eq in Hc. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX2.
(* [comment removed for export] *)
