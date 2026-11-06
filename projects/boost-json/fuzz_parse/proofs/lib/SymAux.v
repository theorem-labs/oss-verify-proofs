(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Frame SymExec SymExec2 SymExec2Sound SymRun RefMemcpyLib AgentLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04prod37Corelib7Numbers7BinNumshe1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~jb5saddrhe4Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux4FPX1~~~~~~o97sregionjb3env35stdpp9bitvectorbdefinitionst72bv03fst04pair03snd79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~hg96estartt77Z_to_bv04listhg94flat36Stdlib5Lists4Listhn02In46Stdlib6ZArith6BinInt1Zho96of_natt7bbv_unsigned04bool03nat04true37Corelib4Init5Logichsa3andhsa2eqhsa3not37Corelib5Lists7ListDefhv23map69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~ih07outsideo9dentry_coveredo96rdenoto9cregions_flatho93addho92leho92lt06option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsip6h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~iu26wbytesih09frame_modjb6adenoto9blog_coveredjb6sentryhg98log_flathg99mem_denotjb4expr3h5LinuxProcessSemantics5Riscv7Preludejn35bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jq24getrjb6sr_gethg97regs_oko99same_regs69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefMemcpyLib~~~~~~kg5ccallee_savedkg58keeps_cs" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition sregion : ltac2:(zQ "00T") := ltac2:(zQ "30!h8!j7!na@2$0$2$1").

Definition rdenot : ltac2:(zQ "60!h8!o2!j7!s7!t1!v4>1E$4>1r$3@2$0@1$5@1$1#k0$2") := ltac2:(zQ "b0!j7!o2!na!v9!ve!hg4!s7!t1!hke!hl8!v4\1E$7\1r$6@4$4@1$a@1$1#k0$0@2$9@1$1#k0@2$8^2@3$3$2$0^1@3$5$2$0^1").

(* [comment removed for export] *)
Fixpoint entry_covered (rs : list sregion) (a : saddr) (w : nat) : bool :=
  match rs with
  | [] => false
  | (SA rb rk, n) :: rest =>
      (expr_eqb (a_base a) rb && Z.leb rk (a_off a) && Z.leb (a_off a + Z.of_nat w) (rk + n))%bool
      || entry_covered rest a w
  end.

Fixpoint log_covered (rs : list sregion) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a w _ :: rest => entry_covered rs a w && log_covered rs rest
  end.

Definition regions_flat : ltac2:(zQ "30!hm2!s7!t1>1E$2>2rs@1$0$1P") := ltac2:(zQ "90!s7!j7!na!v9!hm2!hg4!t1!hm8!ho3\1E$6\2rs@1$4$0>1r$0>0@3$8$0^1^2@3$7^4@3$3$2$1^2@3$5$2$1^2").

Lemma entry_covered_in : ltac2:(zQ "ha0!o2!s7!hke!hq1!v4!hqb!hr9!hm2!hrf!h8!hs4!hte!hu5!hub!ig9!j7!ik8!il3!im3!imc!t1!na!hm8!inb!io2!io8>1E$h4>2rs@1$7$1>1a$h5>1w$8>1x@1$4@1$0#k0>0@3$c$6@3$h1^4^3^2$a>0@2$h3^6^5>0@3$h6^7^5@1$3^4>0@2$b@2$h8@2$2^8^6@2$5@1$0#k0^4@2$h9@2$5@1$0#k0^4@2$h7@2$2^8^6@1$3^5@1$d@2$h0^5@4$e$1@2$9@1$4@1$0#k0$f@1$h2^9^8").
Proof.
  intros E rs a w x. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered map outside]; intros Hc Hrf Hfa Hx.
  - discriminate.
  - apply orb_prop in Hc as [Hc|Hc].
    + apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
      apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
      intros [Hno _]. apply Hno. unfold in_rng, rdenot. cbn [fst snd].
      pose proof (Hrf _ (or_introl eq_refl)) as Hfr. cbn [fst snd] in Hfr.
      unfold flat, estart in *. cbn [a_base a_off] in *. rewrite <- H1 in *.
      rewrite u64_lit by lia. lia.
    + intros [_ Hout]. apply (IH Hc); [| exact Hfa | exact Hx | exact Hout].
      intros r Hr. apply Hrf. right. exact Hr.
Qed.

Lemma frame_layer : ltac2:(zQ "h70!o2!v4!s7!hr9!hm2!hrf!ioe!h8!hs4!hu5!ig9!j7!isd!jhc!ji6!il3!im3!imc!jj3!t1!na!hm8!hq1>1E$h3>2rs@1$4$2>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1a$h4>1w$5>1v@1$1@1$0#k0>0@3$9$3@3$f^5^3^2$8>0@2$h1^7^6>0@3$h5^8^5@1$h6^4@3$e^7@3$d^7@2$h2^9^6@2$c^5^4@4$a$2@2$7@1$1@1$0#k0$b@1$h0^9^8").
Proof.
  intros E rs m a w v Hc Hrf Hfa.
  pose proof (flat_u E a _ Hfa) as Hu.
  eapply frame_mod_weaken.
  2:{ apply frame_mod_wbytes. rewrite length_N_to_le_bytes, Hu. ndestruct Hfa as (?&?&?&?). lia. }
  intros x Hout. cbn [outside]. split; [|exact I].
  intros Hin. unfold in_rng in Hin. rewrite length_N_to_le_bytes, Hu in Hin.
  exact (entry_covered_in E rs a w x Hc Hrf Hfa Hin Hout).
Qed.

Theorem log_covered_frame : ltac2:(zQ "h30!o2!v4!hm2!s7!hr9!ioe!h8!hs4!hu5!ig9!j7!ji6!jjc!im3!imc!t1!jka!jl3!jlf>1E$f>4base>0@1$1@1$0#k0@1$5@1$1@1$0#8>2rs@1$2$3>3log@1$2$h0>0@3$8$4@2$c^2^1$7>0@2$e^5^3>0@2$h1^6^3@3$b^6@3$h2^7^6^4@4$9$3@2$6@1$1@1$0#k0$a@1$d^7^5").
Proof.
  intros E base rs log. induction log as [|[a w v] rest IH]; cbn [log_covered mem_denot log_flat]; intros Hc Hrf Hlf.
  - apply frame_mod_refl.
  - apply andb_prop in Hc as [H1 H2]. ndestruct Hlf as (Hw & Hfa & Hlf').
    eapply frame_mod_trans_same; [apply IH; assumption|].
    apply frame_layer; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma regs_ok_same : ltac2:(zQ "a0!o2!v4!jmc!hm2!hu5!jp9!jtd!ju5!jue!t1>1E$9>2sr@1$3$2>3sr'@1$3$2>1R@2$5@1$0#5@1$1@1$0#k0>2R'@2$5@1$0#5@1$1@1$0#k0>1r@1$1@1$0#5>0@3$8^6^5^3>0@3$8^7^5^3>0@3$4$2@2$7^6^3@2$7^7^3@3$4@1$1@1$0#k0@2$6^5^4@2$6^6^4").
Proof. intros E sr sr' R R' r HR HR' Hs. rewrite (HR r), (HR' r), Hs. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint same_regs (sr sr' : list expr) (rs : list reg) : bool :=
  match rs with
  | [] => true
  | r :: rest => expr_eqb (sr_get sr' r) (sr_get sr r) && same_regs sr sr' rest
  end.

Lemma same_regs_sound : ltac2:(zQ "d0!o2!v4!hm2!hu5!jp9!jtd!jmc!jue!hr9!hs4!jv9!t1!ho3>1E$b>2sr@1$2$6>3sr'@1$2$6>1R@2$4@1$0#5@1$1@1$0#k0>2R'@2$4@1$0#5@1$1@1$0#k0>2rs@1$2@1$1@1$0#5>0@3$3$8@3$a^5^4^1$9>0@3$7^7^6^4>0@3$7^8^6^4>1r@1$1@1$0#5>0@3$c@1$1@1$0#5^1^5@3$3@1$1@1$0#k0@2$5^7^2@2$5^8^2").
Proof.
  intros E sr sr' R R' rs. induction rs as [|r0 rest IH]; cbn [same_regs]; intros Hs HR HR' r Hin.
  - destruct Hin.
  - apply andb_prop in Hs as [H1 H2]. destruct Hin as [<-|Hin].
    + apply (regs_ok_same E sr sr' R R' r0 HR HR'). apply expr_eqb_eq. exact H1.
    + apply IH; assumption.
Qed.

Lemma keeps_cs_of_same : ltac2:(zQ "d0!o2!hm2!jp9!jmc!jue!v4!hr9!hs4!hu5!kk4!kl4!jv9!t1>1E$c>2sr@1$1$3>3sr'@1$1$3>1R@2$2@1$0#5@1$5@1$0#k0>2R'@2$2@1$0#5@1$5@1$0#k0>0@3$8$6@3$b^4^3$9$7>0@3$4^6^5^3>0@3$4^7^5^3@2$a^5^4").
Proof. intros E sr sr' R R' Hs HR HR' r Hin. eapply same_regs_sound; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End FPX1.
(* [comment removed for export] *)
