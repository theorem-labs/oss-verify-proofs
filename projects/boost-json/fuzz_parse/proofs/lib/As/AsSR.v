(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Exec MState.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run06config37Corelib4Init5Logicj43and09cfg_model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~l95asegs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~pc4lzok3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticstcdmachine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~hi38restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~hme6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hr1dhunspell_scfg89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As4AsSR7Generic~~~~~~hv92SR05mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Stateik85Modelhv95AKRELhv93VIS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~iof3evtj42eq37Corelib7Numbers7BinNumsit64Npos35stdpp9bitvectorbdefinitionsiv72bv37Corelib4Init9Datatypesjha4Nonejha6optionik88m_halted3h5LinuxProcessSemantics5Riscv7Preludejl05bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jnf2MSj42ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~js78realizesjs74TSethi3h5same_but_materialized" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Generic.
  (* [comment removed for export] *)
  Variable St : Type.
  Variables aL aS aZr : St -> list (word * word).
  (* [comment removed for export] *)
  Variable K : ltac2:(zQ "10!in6>0?2St>0$0P").
  Variable MPRES : ltac2:(zQ "10!in6>0$0>0$0P").

  (* [comment removed for export] *)
  Hypothesis K_mat : ltac2:(zQ "20!in6!kh6>1s?2St>2mo$0>3mo'$0>0@2?1K^3^2>0@2$1^3^2@2?1K^5^3").
  Hypothesis MPRES_mat : ltac2:(zQ "20!in6!kh6>2mo$0>3mo'$0>0@2$1^2^1@2?5MPRES^3^2").

  Definition AKREL : ltac2:(zQ "10!ic>1s?2St>1c$0P") := ltac2:(zQ "50!k8!ke!ic!p4!t5\1s?2St\1c$2@2$0@5$4$3@1?2aL^2@1?2aS^2@1?3aZr^2^1@2?1K^2@1$1^1").

  Definition VIS : ltac2:(zQ "10!hh3>1s?2St>3msF$0$0") := ltac2:(zQ "20!hh3!hm2\1s?2St\3msF$0@3$1@1?2aL^2@1?2aS^2^1").

  Definition SR : ltac2:(zQ "10!ic>0>0$0P>0$0P") := ltac2:(zQ "30!p4!hq7!hu8@2$1$0$2").

  (* [comment removed for export] *)
  Lemma ASR_done : ltac2:(zQ "20!ic!ijb>1Q>0$0P>1c$0>0@1^2^1@2$1^3^2").
  Proof. intros Q c H. apply sreach_done. exact H. Qed.

  Lemma ASR_mono : ltac2:(zQ "20!ic!ijb>1Q>0$0P>2Q'>0$0P>1c$0>0@2$1^3^1>0>2c'$0>0@1^5^1@1^5^2@2$1^4^3").
  Proof. intros Q Q' c H HQ. eapply sreach_mono; eassumption. Qed.

  Lemma ASR_seq : ltac2:(zQ "20!ic!ijb>2Q1>0$0P>2Q2>0$0P>1c$0>0@2$1^3^1>0>2c'$0>0@1^5^1@2$1^5^2@2$1^4^3").
  Proof. intros Q1 Q2 c H K'. eapply sreach_seq; eassumption. Qed.

  (* [comment removed for export] *)
  Theorem ASR_lift : ltac2:(zQ "90!ik1!hh3!in6!inf!ijb!io8!ic!p4!isa>1P>0$1P>1Q>0$6P>1s?2St>3msF$1>2mo$2>0@2$3^3@2$0^2^1>0@3$8$7^6@2$5^4^3>0>4msF'$1>3mo'$2>0@2$3^7@2$0^2^1>0@2?5MPRES^6^2>0@1^b@2$5^9^4@2$4^b@2$0^5^4@2$4^7@2$0^5^4").
  Proof.
    intros P Q s msF mo [Hok HK] Hevt Hk. unfold SR, VIS in *.
    eapply (evt_sreach_lazy_k asegs (aL s) (aS s) (aZr s) P msF mo Q Hok Hevt).
    intros msF' mo' Hok' Hsame _ HP. apply Hk; [| apply MPRES_mat; exact Hsame | exact HP].
    split; [exact Hok' |]. cbn. eapply K_mat; [exact HK | exact Hsame].
  Qed.

  (* [comment removed for export] *)
  Corollary ASR_lift_at : ltac2:(zQ "a0!hh3!ik1!in6!inf!ijb!io8!it1!ic!p4!isa>1P>0$0P>1Q>0$7P>1s?2St>3msF$0>2ms$0>2mo$2>0@2$3^4@2$1^3^1>0@3$6$0@2$5^5^4^3>0@3$9$8^8^4>0>4msF'$0>3mo'$2>0@2$3^9@2$1^2^1>0@2?5MPRES^7^2>0@1^d@2$5^b^4@2$4^d@2$1^5^4@2$4^9@2$1^7^5").
  Proof. intros P Q s msF ms mo HA <- He Hk. eapply ASR_lift; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma AKREL_halted : ltac2:(zQ "90!iuf!jh4!jj2!jja!it1!ke!ic!jk4!inf>1s?2St>1c$6>0@2$8^2^1@3$4@1$3@1$1@1$0#k0@1$7@1$5^2@1$2@1$1@1$0#k0").
  Proof. intros s c [Hok _]. exact (lzok_halted Hok). Qed.

  (* [comment removed for export] *)
  Lemma VIS_MS : ltac2:(zQ "91!iuf!jh4!jja!jn6!jrc!it1!js2!hh3!io8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1s?2St>1R@2$3@1$0#5@1$1@1$0#k0>1F@2$3@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0@2$6~0\2m'~0@3$5$7@2$8^9@7$4^8^7^6^5^4^3^2@7$4^8^7^6^5^4^1^2").
  Proof. intros. exists (restrict_mem (aL s) (aS s) m). apply restrict_MS. Qed.

  (* [comment removed for export] *)
  Theorem ASR_SR_laws : ltac2:(zQ "b0!ic!ijb!hh3!ik1!k8!in6!inf!io8!it1!p4!isa@2$4>1Q>0$0P>1c$0>0@1^2^1@2$1^3^2@2$4>1Q>0$0P>2Q'>0$0P>1c$0>0@2$1^3^1>0>2c'$0>0@1^5^1@1^5^2@2$1^4^3@2$4>2Q1>0$0P>2Q2>0$0P>1c$0>0@2$1^3^1>0>2c'$0>0@1^5^1@2$1^5^2@2$1^4^3>1P>0$2P>1Q>0$0P>1s?2St>3msF$2>2ms$2>2mo$5>0@2$6^4@2$3^3^1>0@3$8$2@2$7^5^4^3>0@3$a$9^8^4>0>4msF'$2>3mo'$5>0@2$6^9@2$3^2^1>0@2?5MPRES^7^2>0@1^d@2$7^b^4@2$1^d@2$3^5^4@2$1^9@2$3^7^5").
  Proof.
    split; [exact ASR_done|]. split; [exact ASR_mono|]. split; [exact ASR_seq|]. exact ASR_lift_at.
  Qed.

  Theorem ASR_AKREL_laws : ltac2:(zQ "f1!iuf!jh4!jja!it1!jn6!jrc!jj2!k8!js2!hh3!ke!ic!jk4!inf!io8&>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$7>1s?2St>1c$b>0@2$d^2^1@3$3@1$2@1$1@1$0#k0@1$c@1$a^2@1$6@1$1@1$0#k0>1s?2St>1R@2$4@1$0#5@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0@2$8~0\2m'~0@3$3$9@2$e^9@7$5^8^7^6^5^4^3^2@7$5^8^7^6^5^4^1^2").
  Proof. split; [exact AKREL_halted | exact VIS_MS]. Qed.

  (* [comment removed for export] *)
  Lemma ASR_realizes : ltac2:(zQ "60!ic!p4!hu8!kg2!ijb!kge>1Q>0$0P>1c$0>1T$5>0@2$4^3^2>0>2c'$0>0@1^5^1@4$3$1$2^2^4@4$3$1$2^4^3").
  Proof. intros Q c T H Hk. eapply sreach_realizes; eassumption. Qed.
End Generic.
(* [comment removed for export] *)
