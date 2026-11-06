(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec SymExec2 SymExec2Sound SymRun SymDrive LibKnowFrame
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AsLazyRun AsPrintfFirst.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~he6kentry04bool37Corelib7Numbers7BinNumsmc4Nposhe8sidecond35stdpp9bitvectorbdefinitionsp72bv04prod06option04pair79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~sd7know_ok37Corelib4Init5Logichhc2eq3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehj67Segment89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsCarryKeep4FPX1~~~~~~hn6acarry_keephe3envhe6sentrysd8log_flatsd9mem_denotsd9scs_denot3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshvcdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runik45mkCfghe7scriptshe9sym_state03nilhe5s_log03natmc1Z3h5LinuxProcessSemanticsfLinuxProcessSem5Stateiq55Model3h5LinuxProcessSemantics5Riscv7Preludeitc5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~jgb8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~jl64lzok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jp74mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jtadhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ki28realizessd7regs_okp77Z_to_bv04truejgbh5same_but_materializedjl68hid_sameki24TSethe2SShe4exprhe4s_pche6s_regshe8sym_exec" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2. Import SX2S.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Fixpoint carry_keep (keep : kentry -> bool) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry_keep keep older kn hints in
      let '(kn2, scs2, hs2) := prune kn1 a w kn1 hs1 in
      ((if keep (KWord a w v) then KWord a w v :: kn2 else kn2), scs1 ++ scs2, hs2)
  end.

Lemma carry_keep_sound : ltac2:(zQ "h21!h8!ld!m6!o5!oc!r4!r9!rf!s7!hh2!hj0!hmb!hrc!hsa!ht0!ht9!hu4!hv0&>0@1$5@1$3#k0@1$7@1$5@1$3#8>4segs@1$0$b>4keep>0$1$2>1E$d>7anybase~0>4base~0>3log@1$0$e>2kn@1$0$1>5hints@1$0$2>3kn'@1$0$1>3scs@1$0$4>3hs'@1$0$2>0@3$a@2$6@2$6@1$0$1@1$0$4@1$0$2@4$c^a^6^5^4@4$8@2$6@1$0$1@1$0$4@1$0$2@4$8@1$0$1@1$0$4^3^2^1>0@2$f^a^7>0@4$9^d^b^9^7>0@4$h1^e^b^c^5@4$9^f^d@3$h0^d^b^a^7").
Proof.
  intros segs keep E anyb base log. induction log as [|[a w v] older IH]; intros kn hints kn' scs hs' Hc Hlf Hkn Hscs.
  - cbn in Hc. injection Hc as <- <- <-. exact Hkn.
  - cbn [carry_keep] in Hc. cbn [log_flat] in Hlf. ndestruct Hlf as (Hw8 & Hfa & Hlf').
    destruct (carry_keep keep older kn hints) as [[kn1 scs1] hs1] eqn:Hco.
    destruct (prune kn1 a w kn1 hs1) as [[kn2 scs2] hs2] eqn:Hpr.
    injection Hc as <- <- <-.
    apply scs_denot_app in Hscs as [Hs1 Hs2].
    cbn [mem_denot].
    assert (HP : know_ok segs E (wbytes (mem_denot E base older) (adenot E a) (word_to_le_bytes w (edenot E v))) kn2)
      by (eapply prune_sound; eauto).
    destruct (keep (KWord a w v)); [| exact HP].
    constructor; [| exact HP].
    cbn [kentry_ok]. split; [exact Hw8|]. split; [exact Hfa|].
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes w (edenot E v)) (mem_denot E base older) (adenot E a)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite (flat_u E _ _ Hfa).
    ndestruct Hfa as (?&?&?&?). lia.
Qed.

(* [comment removed for export] *)
Theorem rz_run_lf_lazy_keep : ltac2:(zQ "ic3!h8!o5!r4!r9!oc!ld!m6!hj0!rf!s7!ij3!in0!in9!io3!iof!ip4!ipc!iq1!it3!jg2!jka!jof!jt2!kh1!kld!hh2!km9!hv0!kn3!knd!hmb!hrc!ko3!kpd!kq9!kr1!hsa!kr6!krd!ks4!ht0!ksd!ht9!hu4&@2$3@1$2@1$1#k0@1$2@1$1#k0&@1$0~0&>0@1$2@1$1#k0@1$8@1$2@1$1#8>4keep>0$5$6>4segs@1$0$he>1L~1>1S~1>2Zr~1>4fuel$h0>5stops@1$0$h1>3scr$c>2pc$h1>2sr@1$0$i5>2kn@1$0$5>2nx$h0>3ss'$d>3scs@1$0$4>4scr'$c>3kn'@1$0$5>4scs2@1$0$4>3hs2@1$0$6>1E$i4>1M~2>3rom~2>1R@2$h3@1$1#5@1$2@1$1#k0>3msF$a>2mo$h2>1T$i2>0@3$7@2$3@2$3$d@1$0$4$c@7$i9^h8^h4$hd^h3^h2@5$i3^h1^h0@1$e$i8^f^e@1$e$4@4$9@2$3$d@1$0$4$c@4$9$d@1$0$4^d^c^b>0@3$7@2$3@2$3@1$0$5@1$0$4@1$0$6@4$hf^ha@1$f^e^h0@1$e$6@4$9@2$3@1$0$5@1$0$4@1$0$6@4$9@1$0$5@1$0$4^b^a^9>0@3$ha^9^h2^6>0@4$h9^hb^a^9^h2>0@4$hb^hc^a^b^h0>0@4$hb^hd^b^c^e>0@5$h5^he^hd^hc^hb@2$b^9^8>0@3$7$a@3$h4^he^hd^a@5$h6?2fx^b@2$hc@1$1#k0^h8^d^c>0>2R'@2$h3@1$1#5@1$2@1$1#k0>2M'~2>4msF'$a>3mo'$h2>0@3$ha^h3@1$i7^h9^4>0@4$h9^i5^h4^4^h7>0@3$7~2^5@3$ib^h5^h4@1$f^hb>0@2$ia^h6@1$f^hc>0@5$h5^i8^i7^i6^i5@2$b^6^5>0@2$i0^h3^6>0@4$i1^i9^i8^h5^8>0@3$7$a@3$h4^ia^i9^9@5$h6?2fx^b@2$hc@1$1#k0@1$i6^i0^a^h8@4$h8^ic$h7@2$b^a^9^h5@4$h8^i1$h7@2$b^c^b^a").
Proof.
  intros keep segs L S Zr fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R msF mo T
         Hex Hc HR HK Hsc Hsc2 Hok Hr Hcont.
  ndestruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply (rz_msteps_lazy_mkst segs L S Zr); [exact Hok | exact Hr | exact Hms |].
  intros msF' mo' Hok' Hsb Hhs Hr'.
  apply (Hcont R' (mem_denot E M (s_log ss')) msF' mo' HR'); [| reflexivity | exact Hlf | exact Hok' | exact Hsb | exact Hhs | exact Hr'].
  eapply carry_keep_sound; eassumption.
Qed.
End FPX1.
