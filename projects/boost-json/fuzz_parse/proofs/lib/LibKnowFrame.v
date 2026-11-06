(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec StoreOk AllocSim MmapSim MemSplit SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hc4expr37Corelib4Init9Datatypesm24boolm24listhc6kentry46Stdlib6ZArith6BinInt1Zp13addp13lebm23orbhc8expr_eqbhccranges_aparthc2SA79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ta6estart04Nposp12le35stdpp9bitvectorbdefinitionshj32bvm26optionm24true37Corelib4Init5Logichm62eqhm62or3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeho67Segment79OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibKnowFrame4FPX1~~~~~~hs67apart_bhc3envta7know_okm23nilm23nathc5saddrm24consm24andbp13ltb3h5LinuxProcessSemantics5Riscv5Instrikd5aluopikd5mulophc4ELitp13powp13subhc5KZerop13maxm23appp13minp16of_naths69kn_frame136Stdlib5Lists4Listis68flat_maphc6edenothj3bbv_unsignedhs68kn_frame69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~jg99mem_growsta4flatp12lt" s.   (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition apart_b : ltac2:(zQ "50!h9!lb!na!o1!o8>5allkn@1$3$4>2ub$1>2uk$0>2un$0>1b$1>1k$0>1n$0$2") := ltac2:(zQ "a0!h9!na!lb!q9!qf!o1!r5!rb!o8!s6\5allkn@1$5$8\2ub$2\2uk$0\2un$0\1b$2\1k$0\1n$0M1\0$1$1@2$7^3^6@2$6@2$4@2$3^2^1^5@2$4@2$3^5^4^2@7$9^7^6^5^4^3^2^1").

Lemma apart_b_sound : ltac2:(zQ "h30!h9!t5!hhf!o1!hi8!lb!q9!hie!hl0!na!hl6!hlf!hna!ho0!hrb!iga!ih5!o8!ihb>4segs@1$3$e>1E$h0>1M>0@1$8@1$4#k0@1$a@1$8@1$4#8>5allkn@1$3$h1>2ub$5>2uk$0>2un$0>1b$5>1k$0>1n$0>0@4$h2^a^9^8^7>0@3$c$9@7$f^8^7^6^5^4^3^2$b@2$d@2$7@2$6@2$2^b@2$1^8^7^6@2$2^b@2$1^5^4@2$7@2$6@2$2^b@2$1^5^4^3@2$2^b@2$1^8^7").
Proof.
  intros segs E M allkn ub uk un b k n HK H. unfold apart_b in H.
  destruct (expr_eqb b ub) eqn:Heq.
  - apply expr_eqb_eq in Heq. subst b. unfold estart. cbn [a_base a_off].
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - eapply ranges_apart_sound; [exact HK | exact H].
Qed.

(* [comment removed for export] *)
Definition kn_frame1 : ltac2:(zQ "40!o8!o1!h9!lb>5allkn@1$1$0>2ub$3>2uk$2>2un$2>1K$0@1$1$0") := ltac2:(zQ "ha4!o8!ii5!lb!na!h9!o1!iib!ij1!ij9!ik0!q9!ik7!in1!ina!iga!qf!io3!ioa!ip0!ip6!t5!ipe!iq4!rb!iqa!ir0&@2$9@2$fZ^1@2$b^1@2$h1+2+k0&\2op$c\2a0$2\2b0$2@1$1$0&\2op$d\2a0$2\2b0$2@1$1$0&\2sx$3\2lo$6\2n0$6\1e$2@1$1$0\5allkn@1$5$0\2ub$2\2uk$4\2un$4\1K$0M0\1K$0@1$5$0^1\1a$7\1w$6\1v$2M7\1a$7@1$5$0^3\1b$2\1k$4M3\0$3@1$5$0@7$e^a^9^8^7^2^1@1$h9^4@3$8$0^6@1$1$0@1$1$0\1a$7\1n$2M7\1a$7@1$5$0^2\1b$2\1k$4M2\1n$2@1$5$0^3\1l$4M3\0$3@1$5$0~0M3\0$3@1$5$0@7$e^a^9^8^7^3^2^1@3$8$0^6@1$1$0M3\0$3@1$5$0@2$h7^3^9@3$h6$0M3\0$3@1$5$0@2$b^2^8@3$8$0@2$h3@2$h4^3^2@1$h0@2$h8^1@2$h2^8^2@1$1$0@1$1$0M3\0$3@1$5$0@2$b@2$a^8^7@2$a^2^1@3$8$0@2$h3@2$h4^3@2$h5^2@2$a^8^7@1$h0@2$h2@2$a^2^1@2$h5^2@2$a^8^7@1$1$0@1$1$0@1$1$0@1$1$0\2n0$6@1$1$0~1~1~2~2~3\2sx$3\2k0$6\1i$4\2n0$6@1$1$0\1a$7\1n$2\2k0$6M7\1a$7@1$5$0^3\1b$2\1k$4M2\1n$2@1$5$0^4\1l$4M3\0$3@1$5$0@2$9~0@7$e^b^a^9^8^3^2^1@3$8$0^7@1$1$0@1$1$0\2n0$6@1$1$0~1~1~2~2~3\2sx$3\2k1$6\1i$4\2n0$6@1$1$0\2lo$4\2hi$4M3\0$3@1$5$0@2$9@2$9@2$9@2$fZ^2@2$b^2^1@2$f^1@2$h1+2+k0@7$e^7^6^5^4@1$h0Z^2@2$h2^1^2@3$8$0^3@1$1$0@1$1$0\1e$2\1m$4@3$8$0^3@1$1$0\1e$2\2lo$4\2hi$4@3$8$0^4@1$1$0\1a$7\1n$4@3$8$0^3@1$1$0\2a1$7\2n1$4\2a2$7\2n2$4@3$8$0^5@1$1$0").

Definition kn_frame : ltac2:(zQ "40!o1!h9!o8!lb>2kn@1$0$2>2ub$3>2uk$1>2un$1@1$0$2") := ltac2:(zQ "60!o8!h9!o1!ir9!lb!it9\2kn@1$2$0\2ub$4\2uk$1\2un$1@4$5$0$0@4$3^4^3^2^1^4").

Lemma edenot_lit0 : ltac2:(zQ "70!hna!hi8!h9!io3!iu5!ih5!iue>1E$5@3$0$2@2$6@1$1#k0@2$4^1@1$3ZZ").
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma know_ok_frame : ltac2:(zQ "h50!hi8!hl0!hl6!t5!o1!h9!hhf!ihb!iue!hna!ho0!hrb!ivd!jk3!ih5!lb!o8!jl0!q9!hie!jl7>4segs@1$4$b>1E$e>1M>0@1$1@1$0#k0@1$2@1$1@1$0#8>2M'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>2kn@1$4$h0>2ub$f>2uk$5>2un$5>0@4$7^8^7^6^4>0@3$h1^8@2$3^4^3^2>0>1x@1$1@1$0#k0>0@2$a@2$h4@2$8@1$0#k0^1@2$6^a@2$3^6^5@2$h3@2$h2@2$6^a@2$3^6^5^4@2$8@1$0#k0^1@3$9@1$2@1$1@1$0#8@1^9^2@1^a^2>0@2$d^9^8@4$7^c^b^9@4$c^8^7^6^5").
Proof.
  intros segs E M M' kn ub uk un HK Hfl OUT GR.
  pose proof (flat_u E _ _ Hfl) as Hu. ndestruct Hfl as (F1 & F2 & F3 & F4).
  unfold know_ok, kn_frame. apply Forall_forall. intros K' HinF.
  apply in_flat_map in HinF as (K & Hin & Hb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (APART : forall b k n, apart_b kn ub uk un b k n = true ->
            ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
  { intros b k n H. eapply apart_b_sound; [exact HK | exact H]. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kn_frame1] in Hb.
  - (* [comment removed for export] *)
    destruct (apart_b kn ub uk un b k (Z.of_nat w)) eqn:Hap; [|destruct Hb].
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    ndestruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hf) as Hub. ndestruct Hf as (G1 & G2 & G3 & G4).
    apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hap); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool eqn:Hl; [|destruct Hb].
    apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK. destruct HKK as (Hf & Hz).
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. pose proof Hf as Hf0. ndestruct Hf as (G1 & G2 & G3 & G4).
    destruct (apart_b kn ub uk un b k l) eqn:Hap.
    + destruct Hb as [<-|[]]. cbn [kentry_ok]. rewrite El. split; [exact Hf0|].
      intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
      rewrite u_small by lia. destruct (APART b k l Hap); lia.
    + destruct (expr_eqb b ub) eqn:Heq; [|destruct Hb].
      apply expr_eqb_eq in Heq. subst b.
      unfold estart in G1, G2, G4, OUT, Hz |- *. cbn [a_base a_off] in G1, G2, G4, OUT, Hz |- *.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * destruct (Z.ltb k uk) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [exact G1 | split; [exact G2 | split; lia]]|].
        intros i Hi. rewrite OUT; [apply Hz; lia|]. rewrite u_small by lia. lia.
      * destruct (Z.ltb (uk + un) (k + l)) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [lia | split; [lia | split; lia]]|].
        intros i Hi. rewrite OUT; [|rewrite u_small by lia; lia].
        replace (bv_unsigned (edenot E ub) + Z.max k (uk + un) + i)%Z
          with (bv_unsigned (edenot E ub) + k + (Z.max k (uk + un) - k + i))%Z by lia.
        apply Hz. lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b kn ub uk un b k l)%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK |- *. ndestruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. ndestruct Hf as (G1 & G2 & G3 & G4).
    intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
    rewrite u_small by lia. destruct (APART b k l Hap); lia.
  - (* [comment removed for export] *)
    destruct (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b kn ub uk un (ELit 0) lo (hi - lo))%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
    cbn [kentry_ok] in HKK |- *. ndestruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite OUT; [apply Hnone; exact Hi|].
    pose proof (APART (ELit 0) lo (hi - lo)%Z Hap) as AP. unfold estart in AP |- *. cbn [a_base a_off] in AP |- *.
    rewrite edenot_lit0 in AP. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *)
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    intros d m Hd Hm. eapply store_ok_mono; [exact GR | apply Hst; assumption].
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
