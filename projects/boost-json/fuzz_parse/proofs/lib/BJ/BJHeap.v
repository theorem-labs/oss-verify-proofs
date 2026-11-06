(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run06config79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~j45hs_SR37Corelib7Numbers7BinNumsne4Npos35stdpp9bitvectorbdefinitionspe2bv37Corelib4Init5Logics02eq37Corelib4Init9Datatypest94prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsv8dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statehjf5Modelt94Nonet94listt93nilt96options03and09cfg_model06cfg_ms05mkCfghjf8m_haltedhjf9m_vm_lazy79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~hsc3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~ige5rsegsj47hs_KREL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ild6PStatej48hs_MPRESj48hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~ir9h0RHEAP_frame_stmtir9h6RHEAP_block_range_stmtir9haRHEAP_blocks_disjoint_stmtir9h7RHEAP_blocks_nodup_stmtj4bhs_rauxv_okir9h3rauxv_ok_frame_stmtj4elb_remove_lawsj4dopdel_mf_stmtj4dopnew_mf_stmtj48eh_STACK46Stdlib6ZArith6BinInt1Zjt02lej4h3eh_static_range_lawj4h2eh_chain_frame_lawj4h1eh_idle_frame_lawj4h0eh_slo_range_lawj4h1eh_chain_cons_lawj4h1eh_chain_base_lawj4ceh_X_pad_lawj4eeh_X_nopad_lawj4h2exc_live_frame_lawj4deh_resume_lawj4ceh_catch_lawir95block69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ksc5hceilir98blk_addrir98blk_sizeir93mem36Stdlib5Lists4Listlif2Injt03addj43hmfj43ehkj4cheap_mf_hyps" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section HH.
  Variable H : ltac2:(zQ "10!lkf$0").
  Variable E : ltac2:(zQ "10!ll5$0").
  Hypothesis HH : ltac2:(zQ "10!llb@3$0?5HCEIL?1H?1E").

  Local Ltac hh := pose proof HH as (Lsr & Lkrel & Lmpres & Lrf & Lbr & Lbd & Lnd & Lperm & Laux & Llbr
                                     & Lmalloc & Lfree & Lopdel & Lopdel2 & Lopnew
                                     & Lstk & Lsta & Lchf & Lidf & Lsvf & Lslo & Lcons & Lbase & Lpad & Lnopad & Lxperm & Lexcf & Lres & Lcatch).

  Lemma hh_done : ltac2:(zQ "20!ic!n6>1Q>0$0P>1c$0>0@1^2^1@3$1?1H^3^2").
  Proof. hh. exact (proj1 Lsr). Qed.
  Lemma hh_mono : ltac2:(zQ "20!ic!n6>1Q>0$0P>2Q'>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@1^5^2@3$1?1H^4^3").
  Proof. hh. exact (proj1 (proj2 Lsr)). Qed.
  Lemma hh_seq : ltac2:(zQ "20!ic!n6>2Q1>0$0P>2Q2>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@3$1?1H^5^2@3$1?1H^4^3").
  Proof. hh. exact (proj1 (proj2 (proj2 Lsr))). Qed.
  Lemma hh_lift : ltac2:(zQ "h41!p7!rb!t4!v1!hif!hmd!hn6!hnd!ho4!hoa!hp3!hp9!hq4!ic!hqc!hr3!hrf!n6!ig7!ika&@2$3@1$1@1$0#k0@1$1@1$0#k0>1P>0$4P>2ms$4>2mo$5>0@3$2@1$9@1$1@1$0#k0@1$f^1@1$6@1$1@1$0#k0>0@3$2@1$7~0@1$h0^2@1$8~0>0@3$h2$h3^5^4@3$h1?1H\1c$d@2$a@1^7@1$c^1@3$2$5@1$b^1^5@2$e^5^4").
  Proof. hh. exact (proj2 (proj2 (proj2 Lsr))). Qed.
  Lemma hh_krel : ltac2:(zQ "e1!p7!rb!v1!t4!hn6!hnd!ho4!hoa!hp3!hmd!hr3!hrf!il3!ip9&@2$2@1$1@1$0#k0@1$1@1$0#k0>1s$d>2mo$9>0@3$c?1H^2^1@2$8@3$3@1$7@1$1@1$0#k0@1$a^2@1$4@1$1@1$0#k0@3$3@1$5~0@1$b^2@1$6~0").
  Proof. hh. exact Lkrel. Qed.
  Lemma hh_mpres_refl : ltac2:(zQ "20!hmd!iq3>2mo$0@3$1?1H^1^1").
  Proof. hh. exact (proj1 Lmpres). Qed.
  Lemma hh_mpres_trans : ltac2:(zQ "20!hmd!iq3>3mo1$0>3mo2$0>3mo3$0>0@3$1?1H^3^2>0@3$1?1H^3^2@3$1?1H^5^3").
  Proof. hh. exact (proj2 Lmpres). Qed.
  Lemma hh_RHEAP_frame : ltac2:(zQ "20!iqe!jg3@2$1?5HCEIL@1$0?1H").
  Proof. hh. exact Lrf. Qed.
  Lemma hh_blocks : ltac2:(zQ "20!iqe!jh8@2$1?5HCEIL@1$0?1H").
  Proof. hh. exact Lbr. Qed.
  Lemma hh_disj : ltac2:(zQ "20!iqe!jj3@1$1@1$0?1H").
  Proof. hh. exact Lbd. Qed.
  Lemma hh_nodup : ltac2:(zQ "20!iqe!jl2@1$1@1$0?1H").
  Proof. hh. exact Lnd. Qed.
  Lemma hh_perm : RHEAP_perm H.
  Proof. hh. exact Lperm. Qed.
  Lemma hh_rauxv_frame : ltac2:(zQ "20!jme!jnc@1$1@1$0?1H").
  Proof. hh. exact Laux. Qed.
  Lemma hh_lb_remove : ltac2:(zQ "10!jp4@1$0?1H").
  Proof. hh. exact Llbr. Qed.
  Lemma hh_opdel : ltac2:(zQ "10!jq5@2$0?5HCEIL?1H").
  Proof. hh. exact Lopdel. Qed.
  Lemma hh_opnew : ltac2:(zQ "10!jr5@3$0?5HCEIL?1H?1E").
  Proof. hh. exact Lopnew. Qed.
  Lemma hh_eh_stack : ltac2:(zQ "20!js5!ju8@2$1Z@1$0?1E").
  Proof. hh. exact Lstk. Qed.
  Lemma hh_static_range : ltac2:(zQ "10!jue@1$0?1E").
  Proof. hh. exact Lsta. Qed.
  Lemma hh_chain_frame : ltac2:(zQ "10!kg5@1$0?1E").
  Proof. hh. exact Lchf. Qed.
  Lemma hh_idle_frame : ltac2:(zQ "10!khb@1$0?1E").
  Proof. hh. exact Lidf. Qed.
  Lemma hh_slo_range : ltac2:(zQ "10!kj0@1$0?1E").
  Proof. hh. exact Lslo. Qed.
  Lemma hh_chain_cons : ltac2:(zQ "10!kk4@1$0?1E").
  Proof. hh. exact Lcons. Qed.
  Lemma hh_chain_base : ltac2:(zQ "10!kl9@1$0?1E").
  Proof. hh. exact Lbase. Qed.
  Lemma hh_pad : ltac2:(zQ "10!kme@2$0?1H?1E").
  Proof. hh. exact Lpad. Qed.
  Lemma hh_nopad : ltac2:(zQ "10!knd@1$0?1E").
  Proof. hh. exact Lnopad. Qed.
  Lemma hh_exc_frame : ltac2:(zQ "10!koe@1$0?1E").
  Proof. hh. exact Lexcf. Qed.
  Lemma hh_resume : ltac2:(zQ "10!kq4@3$0?5HCEIL?1H?1E").
  Proof. hh. exact Lres. Qed.
  Lemma hh_catch : ltac2:(zQ "10!kr4@3$0?5HCEIL?1H?1E").
  Proof. hh. exact Lcatch. Qed.

  (* [comment removed for export] *)
  Lemma hh_blocks_below : ltac2:(zQ "b0!ks3!hnd!iqe!lg7!lh0!lhc!li8!ip9!lk2!lk8!ju8>1s$7>2LB@1$1$0>1m$6>0@4$2?1H^3^2^1>1b$0>0@3$8$0^1^4@2$a@2$9@1$4^2@1$5^2@1$3?5HCEIL").
  Proof. intros s LB m HP b Hb. destruct (hh_blocks _ _ _ b HP Hb) as (_ & _ & _ & H4 & _). exact H4. Qed.

  (* [comment removed for export] *)
  Lemma hh_evt : ltac2:(zQ "90!hif!hqc!ic!hmd!il3!n6!ig7!ika!ip9>1P>0$0P>1Q>0$2P>2ms$0>2mo$3>1s$8>0@3$4?1H^1^2>0@3$6$7^6^4>0>3ms'$0>0@1^8^1@1^8@2$1^2^6@3$5?1H^7@2$1^6^5").
  Proof.
    intros P Q ms mo s K EV W. destruct (hh_krel _ _ K) as [K1 K2].
    eapply hh_mono; [eapply hh_lift; [exact K1| exact K2| exact EV]|].
    intros [ms' mo'] [HP E']. cbn in HP, E'. subst mo'. apply W. exact HP.
  Qed.

  (* [comment removed for export] *)
  Lemma hh_evt_then : ltac2:(zQ "90!hif!hqc!n6!ic!hmd!il3!ig7!ika!ip9>1P>0$0P>1Q>0$3P>2ms$0>2mo$4>1s$8>0@3$5?1H^1^2>0@3$6$7^6^4>0>3ms'$0>0@1^8^1@3$2?1H^8@2$1^2^6@3$2?1H^7@2$1^6^5").
  Proof.
    intros P Q ms mo s K EV W. destruct (hh_krel _ _ K) as [K1 K2].
    eapply hh_seq; [eapply hh_lift; [exact K1| exact K2| exact EV]|].
    intros [ms' mo'] [HP E']. cbn in HP, E'. subst mo'. apply W. exact HP.
  Qed.
End HH.
End HCW.
(* [comment removed for export] *)
