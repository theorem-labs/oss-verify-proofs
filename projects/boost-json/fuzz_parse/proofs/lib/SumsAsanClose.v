(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsImages.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec StoreOk Hoare AgentLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanPopFree AsanPlanSoundSums SumsAsanSpecs AsanIStrncpy AsanPopFreeAsan AsPlanImages.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos36Stdlib5Lists4Listhf2In35stdpp9bitvectorbdefinitionsj72bv37Corelib4Init9Datatypesl93nat69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanIStrncpy~~~~~~n7distrncpy_clob79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~s6ccaller_saved79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hh34ridx69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~hlc6ASAN_H69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~hq15ASEGSs6ax_istrncpys68x_sealed79OSSVerify6Proofsaboost_jsonafuzz_parse3libh1AsanPlanSoundSums4APSX~~~~~~ig1distrncpy_specs69x_popfree69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanPopFree~~~~~~im8cpopfree_specs68XIMemset79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~is16x_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jgfdhunspell_scfgs67XMemsets68XIMemcpys67XMemcpys6aXMemIsZeros69XIStrncpys68XPopFreel94booll94lists63acs01Zs64hulll94Nonel96options6cfill_in_winss6csummary_fills69x_imemsets68x_memsetis1cfz_item_stmthh34exprhh36kentryhh35two64hh33envl94true37Corelib4Init5Logickj62eqs64CEIL46Stdlib6ZArith6BinInt1Zkl72lej7bbv_unsigneds6be_sp0_earlys6cexpr_vars_lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AxSymRun3~~~~~~kq09env_agree3h5LinuxProcessSemanticsfLinuxProcessSem2Fsku92Fs" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma istrncpy_clob_sub : ltac2:(zQ "70!h9!j2!l4!n1!r6!hg4!hl4>1r@1$2@1$0#5>0@3$1@1$2@1$0#5^1$4@3$1$3@1$6^2$5").
Proof.
  intros r H. unfold istrncpy_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma asan_istrncpy_spec : ltac2:(zQ "50!hp7!hu0!hu9!hv6!ikb@4$4?2fx$1@1$2$0@1$3$0").
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  ndestruct (asan_istrncpy_sealed mem0 dst (seg_rom ASEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (AP.x_istrncpy ASAN_H)) with asan_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma asan_popfree_spec' : ltac2:(zQ "40!hp7!hu0!ilc!iq6@3$3?2fx$1@1$2$0").
Proof. exact asan_popfree_spec. Qed.
End FPX1.

(* [comment removed for export] *)

Section AsanNodes.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : ltac2:(zQ "40!h9!l4!jrf!ki8>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
Variable argH : ltac2:(zQ "40!jpa!h9!ki8!l4>0$2>0@1$3@1$1#k0$0").
Hypothesis argH_high : ltac2:(zQ "90!h9!jpa!kif!kka!kl0!ki8!kmf!l4!kn5>1E$5>1a@1$7@1$0#k0>0@3$3$1@2?4argH^2^1$2@2$6$4@2$8@1$0#k0^2").
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (AX2.edenot E AP.e_sp0_early) <= bv_unsigned a.  (* [comment removed for export] *)
Hypothesis E_SP0 : ltac2:(zQ "50!jpa!kif!kka!ko3!kp1@3$2$0@2$4?3nx0$3$1").                                                                    (* [comment removed for export] *)
Hypothesis argH_agree : ltac2:(zQ "60!ki8!jpa!kka!h9!ktc!l4>1E$0>2E'$0>1a@1$5@1$3#k0>0@3$4?3nx0^3^2@3$2$1@2?4argH^4^2@2?4argH^3^2").
Hypothesis SINV_frame : ltac2:(zQ "71!h9!l4!jrf!kka!jpa!kif!ki8&>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1E$6>1M~0>2M'~0>0>1a@1$1@1$0#k0>0@3$3$4@2?4argH^4^1$5@3$3@1$2@1$1@1$0#8@1^3^2@1^4^2>0@2?4SINV^4^3@2?4SINV^5^3").
Hypothesis SINV_agree : ltac2:(zQ "50!h9!ki8!l4!jrf!ktc>1E$1>2E'$1>1M>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@3$4?3nx0^3^2>0@2?4SINV^4^2@2?4SINV^4^3").
Variable FS0 : ltac2:(zQ "10!lh4$0").

#[local] Notation XSTMT := (APS.x_stmt ASEGS ASAN_H nx0 LIMIT SINV argH FS0).

Theorem asan_node_x_sound_XIMemset : ltac2:(zQ "50!hp7!hu0!ir6!jg5!jk6@a$3?2fx$1$4$0?3nx0?5LIMIT?4SINV?4argH?3FS0$2").
Proof. eapply APSX.node_x_sound_XIMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_imemset. Qed.
Theorem asan_node_x_sound_XMemset : ltac2:(zQ "50!hp7!hu0!jl7!jg5!jk6@a$3?2fx$1$4$0?3nx0?5LIMIT?4SINV?4argH?3FS0$2").
Proof. eapply APSX.node_x_sound_XMemset; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_fill_spec_memset. Qed.
Theorem asan_node_x_sound_XIMemcpy : ltac2:(zQ "50!hp7!hu0!jm1!jg5!jk6@a$3?2fx$1$4$0?3nx0?5LIMIT?4SINV?4argH?3FS0$2").
Proof. eapply APSX.node_x_sound_XIMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_imemcpy. Qed.
Theorem asan_node_x_sound_XMemcpy : ltac2:(zQ "50!hp7!hu0!jmc!jg5!jk6@a$3?2fx$1$4$0?3nx0?5LIMIT?4SINV?4argH?3FS0$2").
Proof. eapply APSX.node_x_sound_XMemcpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_copy_spec_memcpy. Qed.
Theorem asan_node_x_sound_XMemIsZero : ltac2:(zQ "50!hp7!hu0!jn6!jg5!jk6@a$3?2fx$1$4$0?3nx0?5LIMIT?4SINV?4argH?3FS0$2").
Proof. eapply APSX.node_x_sound_XMemIsZero; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_miz_spec. Qed.
Theorem asan_node_x_sound_XIStrncpy : ltac2:(zQ "50!hp7!hu0!jo3!jg5!jk6@a$3?2fx$1$4$0?3nx0?5LIMIT?4SINV?4argH?3FS0$2").
Proof. eapply APSX.node_x_sound_XIStrncpy; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_istrncpy_spec. Qed.
Theorem asan_node_x_sound_XPopFree : ltac2:(zQ "50!hp7!hu0!jof!jg5!jk6@a$3?2fx$1$4$0?3nx0?5LIMIT?4SINV?4argH?3FS0$2").
Proof. eapply APSX.node_x_sound_XPopFree; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok. apply asan_popfree_spec'. Qed.
(* [comment removed for export] *)
Theorem asan_node_fillfz_sound : ltac2:(zQ "h30!jpa!jq1!hp7!jq8!jqe!jr1!jr8!n1!jrf!hu0!js8!jt7!ju6!jv2!jvd!kgd!kh5!khf!jk6>2hs@1$1$5>2ws@1$1$5>4cold@1$1$f>2fz@1$1$h0>2n0$7>1i$0@f$e?2fx$9$h2$2?3nx0?5LIMIT?4SINV?4argH?3FS0^6^5^4^3^2\2cs$3M0\0$0@1$8$3@3$a^7^6^1@5$b$2?3nx0^1M0\1i$0$4^2@1$c$2@1$d$2M0\1i$0$4^2+hg0$h1@1$6$3").
Proof. eapply APSX.node_fillfz_sound_of; try eassumption; try apply asan_segs_wr; try apply asan_wx; try apply asan_in_hull;
       try apply asan_res_len; try apply asan_hull_ok; [apply asan_fill_spec_imemset | apply asan_fill_spec_memset]. Qed.
End AsanNodes.
(* [comment removed for export] *)
