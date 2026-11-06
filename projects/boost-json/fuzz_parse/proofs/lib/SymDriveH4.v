(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemSplit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11Ik12eq3h5LinuxProcessSemantics5Riscv7Preludele4sext3h5LinuxProcessSemantics5Riscv3Semob5low32hf2BVhf4BvWfhf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~sb6edenot3h5LinuxProcessSemantics5Riscv5Instrhh37ALU_ADDsb5EAluwsb4ELitsb3envsb4expr46Stdlib6ZArith6BinInt1Zhle2lthle3powhfbbv_unsigned37Corelib4Init9Datatypeshp14truesb4EExt01Zhp14boolhp13nathle3lebhp14andbhp15falsehle3addhh35aluophh35mulophp13orb46Stdlib5Arith8PeanoNat3Natig23eqbhle3eqbhle3opphle2lek13andsb2evk13not79OSSVerify6Proofsaboost_jsonafuzz_parse3libaSymDriveH44FPX2~~~~~~ik96win_okik99win_out_bsb6sentrysb5saddrhle6of_nathp14listik9bentry_out_b36Stdlib5Lists4Listit47forallbhp16optionik99log_out_b79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~jg99mem_denot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jlb3rdn3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejpd7Segmentsb6kentryhle3ltbik9ckentry_out_bit46filterjg95elenZjg99kentry_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~khd9mem_growsjg97know_okik96kn_cuthp16length69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ko36wbytes" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma low32_zero_sext : ltac2:(zQ "90!h9!jc!l5!l9!o4!qd!r5!ra!s1@3$3@1$1@1$0#i0@1$5@2$8@1$0#k0Z@3$4@1$0#c@1$0#i0Kd@3$6@1$0#cZKv$2@2$7@1$0#cZ@1$1@1$0#c").
Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma edenot_addw0_r : ltac2:(zQ "c0!hga!h9!l9!hj7!hk2!hka!hl1!hl7!hn6!hnc!jc!ho3>1E$6>1a$7>0@2$8@2$b@1$1#k0@2$0^2^1@2$9+2+hf@3$2@1$a@1$1#k0@2$0^3@3$4$3^2@1$5Z@2$0^3^2").
Proof.
  intros E a Ha. cbn [edenot]. rewrite low32_zero_sext, w_addiw.
  change (bv_signed (0 : bv 12)) with 0%Z. apply v_addiw_id. exact Ha.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma edenot_exts4 : ltac2:(zQ "b0!hga!h9!hq9!l9!hr1!hl1!hl7!hn6!hnc!jc!ho3>1E$5>1a$6>0@2$7@2$a@1$1#k0@2$0^2^1@2$8+2+hf@3$3@1$9@1$1#k0@2$0^3@4$4$2N0N4^2@2$0^3^2").
Proof.
  intros E a Ha. cbn [edenot]. apply ext_val_sx_id; [lia|].
  change (2 ^ (8 * Z.of_nat 4 - 1))%Z with (2 ^ 31)%Z. exact Ha.
Qed.

(* [comment removed for export] *)
End FPX1.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition win_out_b : ltac2:(zQ "40!hr8!hrb!hs3!hl7>3spi$2>2lo$0>2hi$0>3ihi$0>1b$3>1k$0>1n$0$1") := ltac2:(zQ "f0!hl7!hsa!ht1!hr8!ht9!hs3!hrb!hu2!hu9!hv2!hnc!hvb!ihd!ii4!iib\3spi$5\2lo$3\2hi$3\3ihi$3\1b$0\1k$3\1n$3M0\1b$0$6^3\1z$3@2$2@2$2@2$2@2$d^1Z@2$1Z^3@2$1Z^2@2$1@2$7^3^2^5\1i$5@2$2@2$2@2$2@2$2@2$c^1^8@2$b@2$1@2$7^3^2^7@2$1^6^3@2$1@1$e@2$a+2+i8^3@2$1@2$7^3^2@2$a+2+i8@2$1Z^2\2op$8\1a$0\2b0$0$4\2op$8\1a$0\2b0$0$4\2op$9\1a$0\2b0$0$4\2op$9\1a$0\2b0$0$4\2sx$6\3lo0$5\2n0$5\1e$0$4\2sx$6\2k0$5\1i$3\2n0$5$4").

(* [comment removed for export] *)
Definition win_ok : ltac2:(zQ "30!hr8!hs3!hl1>1E$2>3spi$1>2lo$0>2hi$0>3ihi$0P") := ltac2:(zQ "b0!ij2!ij8!hnc!h9!hr8!ije!ho3!hu2!hs3!hl1!iib\1E$9\3spi$8\2lo$4\2hi$4\3ihi$4@2$1@2$0@2$2+2+i9@2$6@1$3#k0@2$5^5^4@2$1@2$0@2$7@2$6@1$3#k0@2$5^5^4@2$2+2+i9@2$2+2+k0@2$1@2$0^3^2@2$1@2$0@1$a@2$2+2+i8^3@2$1@2$0^2@2$2+2+i8@2$1@2$0Z^1@2$0^1@2$7@2$6@1$3#k0@2$5^5^4^3").

Lemma win_out_sound : ltac2:(zQ "h42!h9!ho3!hu2!ij8!hr8!hga!ij2!hn6!ije!hnc!hrb!hs3!hq9!l9!ik3!iob!ip5!hl1!hl7!jc&@2$2@2$1@1$0#k0@2$5^a^5^4&@2$2@2$1@1$0#k0@2$5^b^6^5>1E$h1>3spi$b>2lo$4>2hi$4>3ihi$4>1b$h2>1k$4>1n$4>0@3$d$a@7$h0^7^6^5^4^3^2^1$c>0@5$f^9^8^7^6^5@2$3@2$6Z~0@2$3@2$3@2$7~0@2$9+2+k0@2$6@2$2~0^3@2$9+2+k0@2$3@2$6Z^3>1x@1$h3@1$0#k0>0@2$3@2$6~1@2$1@1$0#k0^1@2$7@2$1@1$0#k0^1@2$2~1^4@1$e@2$3@2$6@2$2@2$1@1$0#k0@2$8^c^b^a@2$1@1$0#k0^2@2$7@2$1@1$0#k0^2@2$2@2$1@1$0#k0@2$8^c^b^9").
Proof.
  (intros E spi lo hi ihi b k n Hb nd_i1; ndestruct nd_i1 as (W1 & W2 & W3 & W4 & W5 & W6 & W7)).
  destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Z.eqb_eq in Hb. subst z.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
    cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat split; try lia.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Nat.eqb_eq in Hb. subst i.
    repeat match goal with
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : (_ || _)%bool = true |- _ => apply orb_prop in H
           end.
    cbn [edenot]. repeat split; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition entry_out_b : ltac2:(zQ "40!hr8!hrb!hs3!iq2>3spi$2>2lo$0>2hi$0>3ihi$0>1e$3$1") := ltac2:(zQ "80!hr8!iqb!iq2!hrb!hs3!hl7!ip5!ir3\3spi$4\2lo$0\2hi$0\3ihi$0\1e$2M2\1e$2$3^1\6e_addr$1\1w$4\5e_val$5M1\6e_addr$1$3^3\1b$5\1k$0@7$6^a^9^8^7^2^1@1$7^4").

Definition log_out_b : ltac2:(zQ "50!hr8!hrb!ird!hs3!iq2>3spi$3>2lo$0>2hi$0>3ihi$0>3log@1$2$4$1") := ltac2:(zQ "60!hr8!iq2!ird!hs3!is5!iu7\3spi$3\2lo$0\2hi$0\3ihi$0\3log@1$2$1@3$5$1@4$4^5^4^3^2^1").

Lemma mem_denot_out : ltac2:(zQ "h40!h9!jc!ho3!hr8!iv2!l9!ije!hu2!hrb!ird!hs3!hq9!ij8!ivc!iob!hl1!iq2!jke!ij2!hn6>1E$f>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>3log@1$9$h0>3spi$a>2lo$3>2hi$3>3ihi$3>1x@1$1@1$0#k0>0@3$5$8@5$d^5^4^3^2^6$b>0@5$e^9^6^5^4^3>0@2$c@2$h2@2$7@2$2@1$0#k0@2$6^a^7^6@2$2@1$0#k0^3@2$h3@2$2@1$0#k0^3@2$7@2$2@1$0#k0@2$6^a^7^5@3$5@1$4@1$1@1$0#8@4$h1^b^a^9^4@1^a^4").
Proof.
  intros E M log spi lo hi ihi x Hb Hw Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_out_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_out_b] in He.
  ndestruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) He Hw) as (A & B & C & D).
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
    pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
    exfalso. apply (D x); lia.
Qed.

Lemma rdn_mem_denot_out : ltac2:(zQ "h50!h9!jc!ho3!ird!hr8!hu2!hs3!iv2!l9!jp6!ije!ij2!hrb!hq9!jt2!ivc!iob!hl1!iq2!jke!ir3>4segs@1$3$e>1E$h1>1M>0@1$1@1$0#k0@1$7@1$1@1$0#8>3log@1$3$h2>3spi$6>2lo$4>2hi$4>3ihi$4>1a@1$1@1$0#k0>1n$6>0@3$8$c@5$f^6^5^4^3^7$d>0@5$h0^a^7^6^5^4>0@2$b@2$5@2$2@1$0#k0@2$a^b^8^7@2$2@1$0#k0^4>0@2$b@2$5@2$2@1$0#k0^5@1$h4^4@2$5@2$2@1$0#k0@2$a^c^9^7@3$8@1$7@1$3@1$1@1$0#8@4$9^e@3$h3^d^c^b^6^5@4$9^e^c^6^5").
Proof.
  intros segs E M log spi lo hi ihi a n Hb Hw H1 H2.
  ndestruct Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  apply rdn_agree. intros j Hj. pose proof (u64_range a).
  apply (mem_denot_out E M log spi lo hi ihi); [exact Hb | repeat split; assumption |].
  rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_out_b : ltac2:(zQ "40!hr8!hrb!hs3!jtd>3spi$2>2lo$0>2hi$0>3ihi$0>1K$3$1") := ltac2:(zQ "h01!hl7!hr8!ht9!hs3!iqb!hrb!hq9!hu9!hv2!ip5!jtd!ht1!ju6!hnc!hsa!ir3&\2sx$5\3lo0$3\1n$3\1e$0$2\3spi$3\2lo$1\2hi$1\3ihi$1\1K$aMa\1K$a$5^1\1a$4\1w$3\1v$0M4\1a$4$5^3\1b$0\1k$1@7$9^a^9^8^7^2^1@1$f^4\1a$4\2n0$0M4\1a$4$5^2\1b$0\1k$1M0\2n0$0$5^3\1n$1@2$b@2$c^1@2$d+2+k0@7$9^a^9^8^7^3^2^1\1n$3$2\2op$7\2a0$0\2b0$0$2\2op$7\2a0$0\2b0$0$2\2op$8\2a0$0\2b0$0$2\2op$8\2a0$0\2b0$0$2~0\2sx$5\2k0$3\1i$1\1n$3$2\1a$4\2n0$0\2k0$3M4\1a$4$5^3\1b$0\1k$1M0\2n0$0$5^4\1n$1@2$b@2$c^1@2$d+2+k0@7$9^b^a^9^8^3^2^1\1n$3$2\2op$7\2a0$0\2b0$0$2\2op$7\2a0$0\2b0$0$2\2op$8\2a0$0\2b0$0$2\2op$8\2a0$0\2b0$0$2~0\2sx$5\2k1$3\1i$1\1n$3$2\1l$1\1h$1@2$e^1^4\1e$0\1m$1$6\1e$0\3lo0$1\3hi0$1$6\1a$4\1n$1$6\2a1$4\2n1$1\2a2$4\2n2$1$6").

Definition kn_cut : ltac2:(zQ "40!hr8!ird!jtd!hs3>3spi$3>2lo$0>2hi$0>3ihi$0>2kn@1$1$2@1$1$2") := ltac2:(zQ "60!hr8!jtd!ird!hs3!jud!jvd\3spi$3\2lo$0\2hi$0\3ihi$0\2kn@1$2$1@3$5$1@4$4^5^4^3^2^1").

Lemma elenZ_lit_small : ltac2:(zQ "90!hr8!ij8!l9!hka!hl1!kg7!ij2!hn6!hnc>1E$4>1n$0>0@2$1@2$6Z^1@2$7^1@2$8+2+k0@3$2$0@2$5^3@1$3^2^2").
Proof. intros E n Hn. unfold elenZ. cbn [edenot]. apply u_small. lia. Qed.

Lemma kentry_cut_sound : ltac2:(zQ "h71!h9!jc!ho3!iv2!hr8!l9!ije!kh0!hu2!hrb!ird!hs3!hq9!ij8!ik3!jt2!kl7!jud!iob!hl1!jtd!ij2!hn6&>1x@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$a$f>1E$h3>1M~0>2M'~0>3spi$b>2lo$4>2hi$4>3ihi$4>1K$h4>0@5$h2^8^5^4^3^2>0>1x@1$1@1$0#k0>0@1$e@2$d@2$h5@2$8@2$2@1$0#k0@2$6^a^7^6@2$2@1$0#k0^1@2$h6@2$2@1$0#k0^1@2$8@2$2@1$0#k0@2$6^a^7^5@3$5@1$3@1$1@1$0#8@1^9^2@1^a^2>0@2$h0^9^8>0@4$7^c^b^a^4>0@3$5$9@5$h1^9^8^7^6^5$c@4$7^e^d^b^6").
Proof.
  intros segs E M M' spi lo hi ihi K Hw Hag Hg HK Hb.
  pose proof Hw as Hw'. ndestruct Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2]; cbn [kentry_out_b] in Hb;
    cbn [kentry_ok] in HK |- *; try exact HK.
  - (* [comment removed for export] *)
    ndestruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
    ndestruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) Hb Hw) as (A & B & C & D).
    rewrite <- Hr. apply rdn_agree. intros j Hj. apply Hag. 
    pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
    rewrite Hu. apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz).
    assert (Hn0 : (0 <= n)%Z).
    { destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
        repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    ndestruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    ndestruct HK as (Hfl & Hlen & Hz).
    assert (Hn0 : (0 <= n)%Z).
    { destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
        repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
    rewrite elenZ_lit_small in Hfl, Hlen, Hz |- * by lia.
    split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    ndestruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    apply Z.leb_le in Hb. ndestruct HK as (H0 & H64 & Hnone).
    split; [exact H0|]. split; [exact H64|]. intros i Hi.
    rewrite Hag; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
Qed.

Theorem know_cut_sound : ltac2:(zQ "h51!h9!jc!ho3!iv2!hr8!ird!ije!km4!hu2!hs3!ij8!l9!ik3!jt2!kl7!kmf!iob!hl1!jtd!ij2!hn6&>1x@1$1@1$0#k0@1$3@1$1@1$0#8>4segs@1$5$d>1E$h1>1M~0>2M'~0>3spi$9>2lo$4>2hi$4>3ihi$4>2kn@1$5$h2>0@5$h0^8^5^4^3^2>0>1x@1$1@1$0#k0>0@1$c@2$a@2$h3@2$8@2$2@1$0#k0@2$6^a^7^6@2$2@1$0#k0^1@2$h4@2$2@1$0#k0^1@2$8@2$2@1$0#k0@2$6^a^7^5@3$b@1$3@1$1@1$0#8@1^9^2@1^a^2>0@2$e^9^8>0@4$7^c^b^a^4@4$7^d^c^a@5$f^9^8^7^6^5").
Proof.
  intros segs E M M' spi lo hi ihi kn Hw Hag Hg HK. unfold know_ok in *.
  induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HK2].
  change (kn_cut spi lo hi ihi (K :: rest))
    with (if kentry_out_b spi lo hi ihi K then K :: kn_cut spi lo hi ihi rest else kn_cut spi lo hi ihi rest).
  destruct (kentry_out_b spi lo hi ihi K) eqn:Hb.
  - constructor; [|apply IH; exact HK2]. eapply kentry_cut_sound; eauto.
  - apply IH. exact HK2.
Qed.

(* [comment removed for export] *)
Lemma wbytes_agree_out : ltac2:(zQ "h30!h9!ho3!jc!hu2!ije!ij2!iv2!hr8!kn9!ird!hs3!ij8!l9!ik3!krd!hl1!hn6!ir3!hnc>1M>0@1$2@1$0#k0@1$6@1$2@1$0#8>1a@1$2@1$0#k0>2bs@1$9@1$2@1$0#8>1E$f>3spi$a>2lo$7>2hi$7>0@2$5@2$3@2$1@1$0#k0@2$4^4^3^2@2$1@1$0#k0^6>0@2$5@2$3@2$1@1$0#k0^7@1$h1@2$8@1$2@1$0#8^6@2$3@2$1@1$0#k0@2$4^5^4^2>0@2$5@2$3@2$1@1$0#k0@2$4^6^5^3@2$h2+2+k0>1x@1$2@1$0#k0>0@1$d@2$b@2$5@2$3@2$1@1$0#k0@2$4^8^7^6@2$1@1$0#k0^1@2$h0@2$1@1$0#k0^1@2$3@2$1@1$0#k0@2$4^8^7^5@3$c@1$6@1$2@1$0#8@4$e^c^b^a^2@1^c^2").
Proof.
  intros M a bs E spi lo hi H1 H2 H3 x Hx. pose proof (u64_range x).
  apply wbytes_outside; [lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [L|G]; [left; exact L | right].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [L2|G2]; [|exact G2].
  exfalso. apply Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
