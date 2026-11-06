(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec StoreOk AgentLib Frame SymExec2 SymExec2Sound SymRun SymDrive MemSplit LibTail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import LibDiagKn MainDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame Image.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option37Corelib4Init5Logicm92eq3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeo27Segment79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~s17seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hga7seg_romk13nats13rdnhga3rdn3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshm3cwrite_to_mem69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~hqa6wbytes01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hv12wahf7Z_to_bvk14prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ik23ivlk13fsthfbbv_unsignedk14pairk13snd37Corelib5Lists7ListDefiq63map46Stdlib6ZArith6BinInt1Zis43add69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~iu37outsideik27outside89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U7MainMem4FPX1~~~~~~jj14ivlsiu39frame_modik25munchik25wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~jp95rsegs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~jtf9mem_grows69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~ki6floaded_segmentsis42ltis46of_natk14Nonek14boolk14truem93andm93nothm38store_okhm35wviewis42leis43powik23stk69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~ks96stk_okis43subhv15wr_atis43lebk14Somek14andbhm3cfind_segment59OSSVerifyaboost_jsonafuzz_parse6images5Ubsan~~~~~~lk1h1Ubsan_segment_000lk1h1Ubsan_segment_001lk1h1Ubsan_segment_002lk1h1Ubsan_segment_003hv17ro_addrk15falsem92orhv17mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs~~~~~~lv07ro_noneiq66Forallk16length79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~mkbcrblock_range36Stdlib5Lists4Listmq62In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~mrf8cells_okmrf9cell_wf_bmq67forallbmrfadiag_cellsmrf9pf1_cellsm92exk11Sk14consm91Ihv13mrdhf2BVhf4BvWfhf6bv_addhv18bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~nn84cellk13nilnn82C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ns88rw_cells" s.   (* [comment removed for export] *)
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
(* [comment removed for export] *)
Lemma seg_rom_same : ltac2:(zQ "80!h9!jc!l9!m0!nd!r7!hg0!hk5@3$4>4segs@1$2$5>0@1$1@1$0#k0@1$3@1$1@1$0#8$6$7").
Proof. reflexivity. Qed.
Lemma rdn_same : ltac2:(zQ "90!h9!jc!l9!m0!hl0!nd!r7!hl6!hlc@3$5>4segs@1$2$6>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1n$4@1$3@1$2@1$1@1$0#8$7$8").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wbytes_eq : ltac2:(zQ "71!h9!jc!m0!l9!nd!hpa!hu4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2bs@1$3@1$1@1$0#8>1m~0>1a@1$1@1$0#k0@3$4~0@3$6^2^1^3@3$5^2^1^3").
Proof. induction bs as [|b bs IH]; intros m a; cbn; [reflexivity | apply IH]. Qed.

Lemma wa_eq : ltac2:(zQ "60!h9!nd!hue!iib!ij1!jc>1z$2@3$1@1$5@1$0#k0@1$3^1@2$4@1$0#k0^1"). Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ivls : ltac2:(zQ "60!l9!ijb!h9!hue!ine!jc>2rs@1$0@2$1@1$5@1$2#k0$3@1$0$4") := ltac2:(zQ "b1!hue!h9!jc!ijb!io5!iob!l9!ip9!iq0!ird!itc&@2$5@1$1#k0@3$4@1$2@1$1#k0$0^1\2rs@1$6@2$3@1$2@1$1#k0$0@4$9@2$3@1$2@1$1#k0$0@2$3$0$0\1r@2$3@1$2@1$1#k0$0@4$7$0$0~0@2$a~0@3$8@1$2@1$1#k0$0^1^1").

Lemma outside_ivls : ltac2:(zQ "90!h9!jc!l9!ijb!hue!jhb!ji6!jn2!iob>2rs@1$2@2$3@1$1@1$0#k0$4>1x@1$1@1$0#k0>0@2$6@1$7^2@2$8@1$0#k0^1@2$5^2^3").
Proof.
  induction rs as [|[b n] rs IH]; intros x H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [|apply IH; exact H2]. unfold in_rng. lia.
Qed.

Lemma frame_mod_munch : ltac2:(zQ "91!h9!jc!m0!l9!ijb!hue!jna!jo7!jn2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>2rs@1$3@2$4@1$1@1$0#k0$5>0@3$6^3^2^1@3$7@1$8^2^4^3").
Proof. intros m m' rs [H _] x Hx. apply H. apply outside_ivls. exact Hx. Qed.

Lemma mem_grows_wmono : ltac2:(zQ "61!h9!jc!m0!jp0!jt6!kh9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>0@2$5^2^1@3$3$4^3^2").
Proof.
  intros m m' Hg x Hw. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - assert (m' x <> None) as H' by (apply Hg; congruence). destruct (m' x); [discriminate|contradiction].
  - destruct (m' x); [discriminate|]. exact Hw.
Qed.

Lemma frame_mod_wmono : ltac2:(zQ "91!h9!jc!m0!l9!ijb!hue!jna!jp0!jt6&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>2rs@1$3@2$4@1$1@1$0#k0$5>0@3$6^3^2^1@3$7$8^4^3").
Proof. intros m m' rs [_ Hg]. apply mem_grows_wmono. exact Hg. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma store_ok_of_wview : ltac2:(zQ "h50!h9!jc!m0!nd!klc!itc!kmf!kn5!iob!knf!ko6!hl0!kod!kp4!kpa!hue!kq0!kqc!kr5!krb!ij1>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1n$b>1a@1$1@1$0#k0>0@2$6@2$5@2$8@1$0#k0^1@1$7^2@2$h3+2+k0>0>1i$f>0@2$d@2$h2Z^1@2$6^1@1$7^4@1$e@3$3@1$2@1$1@1$0#8@3$h1$4^6@2$h4@1$0#k0@2$5@2$8@1$0#k0^4^2@1$9@1$1@1$0#8@3$3$a@4$h0$4^5^3^4$c").
Proof.
  intros m n. induction n as [|n IH]; intros a Hn Hw; [reflexivity|].
  cbn [store_ok]. pose proof (u64_range a) as Ha.
  assert (W0 : wview RSEGS m a <> None).
  { pose proof (Hw 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. exact H0. }
  destruct (wview RSEGS m a); [|contradiction].
  apply IH; [rewrite u_add1 by lia; lia|]. intros i Hi. rewrite u_add1 by lia.
  replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hw. lia.
Qed.

Lemma stk_stk_ok : ltac2:(zQ "d0!h9!hue!kr5!jc!iob!m0!ks2!jt6!lg2!klc!kmf!krb!lgc>1m>0@1$3@1$0#k0@1$5@1$3@1$0#8>2lo$1>2hi$1>2sp@1$3@1$0#k0>1K$1>0@4$6$7^5^4^3>0@2$2^5@2$c@2$4@1$0#k0^3^2>0@2$2@2$4@1$0#k0^4^5>0@2$2Z^4>0@2$a^7@2$b+2+k0@4$8$9^a^7^6").
Proof.
  (intros m lo hi sp K nd_i1 Hlo Hhi HK Hhi2 a n Ha Hn; ndestruct nd_i1 as (H1 & H2 & H)). pose proof (u64_range a).
  apply store_ok_of_wview; [lia|]. intros i Hi. rewrite <- wa_eq. apply (H (bv_unsigned a + i)). lia.
Qed.

Lemma wr_at_store_ok : ltac2:(zQ "h20!h9!hue!itc!kr5!jc!ko6!hl0!m0!kod!nd!kq0!lh3!jt6!klc!kmf!kn5!krb!ij1>1m>0@1$4@1$0#k0@1$7@1$4@1$0#8>1A$1>1n$1>1k$1>1j$6>0@4$b$c^5^4^3>0@2$3Z^3>0@2$3@2$2^4@1$f^3^5>0@2$e@2$2^7^6@2$h0+2+k0@3$9$5@4$a$d^9@2$h1@1$0#k0@2$2^8^6^5$8").
Proof.
  (intros m A n k j nd_i2 Hk Hj HAn; ndestruct nd_i2 as (H1 & H2 & H)). apply store_ok_of_wview; [rewrite u_small by lia; lia|].
  intros i Hi. rewrite u_small by lia. rewrite <- wa_eq. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma find_segment_rsegs : ltac2:(zQ "h00!r7!ko6!lhc!m0!li3!lia!itc!knf!nd!hue!lj1!jt6!ln5!lob!lq1!lr7>1x$9@3$8@1$3$0@3$a$b^1+1M1\0$1@1$3$0@2$5@2$2+hggg0^1@2$2@2$6^1+1+kmgg0@2$4$0$cM1\0$1@1$3$0@2$5@2$2+kmgg0^1@2$2@2$6^1+1+vkgg0@2$4$0$dM1\0$1@1$3$0@2$5@2$2+vkgg0^1@2$2@2$6^1+1+vsgg0@2$4$0$eM1\0$1@1$3$0@2$5@2$2+vsgg0^1@2$2@2$6^1+1+hjhgg0@2$4$0$f@1$7$0").
Proof. intros x. reflexivity. Qed.

Lemma ro_addr_true : ltac2:(zQ "b0!h9!iob!ko6!kod!kp4!nd!lsd!jt6!kr5!kmf!jc>1a@1$a@1$0#k0>0@2$4@2$8+hggg0@2$1@1$0#k0^1@2$9@2$1@1$0#k0^1+vkgg0@3$5$2@2$6$7^2$3").
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_rsegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x46000); cbn [andb]; [reflexivity| | lia | lia].
  destruct (Z.leb_spec 0x46000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0xf4000); cbn [andb]; [reflexivity| lia | lia | lia].
Qed.

Lemma ro_addr_false : ltac2:(zQ "b0!h9!iob!ko6!lt8!nd!lu0!lsd!jt6!kr5!kmf!jc>1a@1$a@1$0#k0>0@2$5@2$9@2$1@1$0#k0^1+hggg0@2$8+vkgg0@2$1@1$0#k0^1@3$4$2@2$6$7^2$3").
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_rsegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x46000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x46000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0xf4000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0xf4000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0xfc000); cbn [andb]; try lia; try reflexivity;
  destruct (Z.leb_spec 0xfc000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x131000); cbn [andb]; try lia; reflexivity.
Qed.

Lemma mem_inv_ro_none : ltac2:(zQ "60!h9!jc!m0!lu5!jt6!mid>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0@2$3$4^1@1$5^2").
Proof.
  intros m Hinv i Hi. destruct (m (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (Hinv _ _ E) as Hro. rewrite ro_addr_true in Hro; [discriminate|]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mem_inv_frame : ltac2:(zQ "h23!h9!jc!hue!io5!ijb!kr5!iob!m0!iq0!lu5!jt6!itc!l9!kp4!lu0!mj8!jna!krb&>0@1$1@1$0#k0@1$7@1$1@1$0#8&@2$6@1$0#k0@3$3@1$1@1$0#k0$2^1&@2$b~1@3$8@1$1@1$0#k0$2^1>1m~0>2m'~0>2rs@1$c@2$4@1$1@1$0#k0$2>0@2$9$a^3>0@3$h0^4^3^2>0@3$f@2$4@1$1@1$0#k0$2\1r@2$4@1$1@1$0#k0$2@2$d@2$5~2@2$h1+2+k0@2$e@2$5~2+hggg0@2$5+vkgg0~1^3@2$9$a^5").
Proof.
  intros m m' rs Hinv [Hout Hg] Hrs a b Hab.
  destruct (ro_addr rsegs a) eqn:Ero; [|reflexivity]. exfalso.
  assert (Hcase : OSSVerify.Proofs.boost_json.fuzz_parse.lib.Frame.outside a rs \/ (bv_unsigned a < 0x10000 \/ 0xf4000 <= bv_unsigned a)).
  { clear Hab Ero Hout Hg Hinv. induction rs as [|[r n] rs IH]; [left; exact I|].
    inversion Hrs as [|x l [Hnw Hr] Hl]; subst. cbn [fst snd] in Hnw, Hr.
    destruct (IH Hl) as [Ho|Hx]; [|right; exact Hx].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r)) as [Hlt|Hge]; [left; cbn; split; [unfold in_rng; lia|exact Ho]|].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r + n)) as [Hin|Hout']; [|left; cbn; split; [unfold in_rng; lia|exact Ho]].
    right. lia. }
  destruct Hcase as [Ho|Hx].
  - rewrite (Hout a Ho) in Hab. pose proof (Hinv a b Hab). congruence.
  - rewrite ro_addr_false in Ero by exact Hx. discriminate.
Qed.
End FPX1.

(* [comment removed for export] *)
Section HCW.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {HCEIL : HeapCeil}.
Lemma mem_inv_wbytes_block : ltac2:(zQ "e0!h9!jc!hue!lu5!jt6!itc!kr5!mk2!l9!m0!hu4!mp6!kn5!ij1>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$2>1n$2>1k$2>2bs@1$8@1$1@1$0#8>0@2$3$4^5>0@3$b?5HCEIL^5^4>0@2$6Z^4>0@2$6@2$5^5@1$c@2$7@1$1@1$0#8^4^6@2$3$4@3$a^9@2$d@1$0#k0@2$5^8^6^5").
Proof.
  (intros m A n k bs Hinv nd_i3 Hk Hl a b Hab; ndestruct nd_i3 as (R1 & R2 & R3 & R4 & R5)). clear R2.
  pose proof (u64_range a) as Ha. hcb.
  destruct (Z_lt_le_dec (bv_unsigned a) (A + k)) as [Hlt|Hge].
  - rewrite wbytes_below in Hab by (rewrite ?u_small by lia; lia). exact (Hinv a b Hab).
  - destruct (Z_lt_le_dec (bv_unsigned a) (A + k + Z.of_nat (length bs))) as [Hin|Hout].
    + apply ro_addr_false. lia.
    + rewrite wbytes_above in Hab by (rewrite u_small by lia; lia). exact (Hinv a b Hab).
Qed.
End HCW.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma outside_of_disjoint : ltac2:(zQ "e1!h9!jc!hue!iob!ijb!io5!l9!iq0!lu0!jhb!mr9!itc!kr5!kmf&@2$3@1$0#k0@3$5@1$1@1$0#k0$2^2>1x@1$1@1$0#k0>2rs@1$6@2$4@1$1@1$0#k0$2>0>1r@2$4@1$1@1$0#k0$2>0@3$a@2$4@1$1@1$0#k0$2^1^2@2$8@2$d@2$3@1$0#k0^4~0@2$c@2$b~0@3$7@1$1@1$0#k0$2^2@2$3@1$0#k0^4@2$9^3^2").
Proof.
  intros x rs H. induction rs as [|[r n] rs IH]; [exact I|]. cbn. split.
  - pose proof (H (r, n) (or_introl eq_refl)) as H1. cbn [fst snd] in H1. unfold in_rng. lia.
  - apply IH. intros r' Hr'. apply H. right. exact Hr'.
Qed.

Lemma cells_ok_frame : ltac2:(zQ "h72!hue!ijb!h9!jc!hl0!io5!l9!m0!mvd!itc!kr5!iob!ko6!iq0!kod!nd!lu0!mj8!jna!ng9!mr9!nh6!kn5&>0@1$3@1$2#k0@1$7@1$3@1$2#8&@2$b@1$2#k0@3$5@1$3@1$2#k0$0^2>1m~0>2m'~0>2rs@1$6@2$1@1$3@1$2#k0$0>2cs@1$6@2$1@2$1$0$4$0>0@3$f$c@3$h5@2$1@2$1$0$4$0$h3^1$e>0@2$8^5^2>0@3$h2^6^5^4>0@3$h1@2$1@2$1$0$4$0\1c@2$1@2$1$0$4$0M1\1c@2$1@2$1$0$4$0P^1\1y@2$1$0$4\2y0$0M1\1y@2$1$0$4P^2\1a$0\1w$4>1r@2$1@1$3@1$2#k0$0>0@3$h4@2$1@1$3@1$2#k0$0^1^b@2$h0@2$a@2$9^4@1$h6^3~1@2$a@2$9~1@3$d@1$3@1$2#k0$0^2^4^4@2$8^7^5").
Proof.
  intros m m' rs cs Hwf Hc [Hout _] Hd. eapply cells_ok_agree; [exact Hwf| |exact Hc].
  clear Hc. induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  intros i Hi. apply Hout. apply outside_of_disjoint. intros r0 Hr0.
  pose proof (Hx r0 Hr0) as D. rewrite u_small by lia. lia.
Qed.

Lemma rdn_frame : ltac2:(zQ "h52!h9!jc!l9!hue!iob!m0!ijb!itc!kr5!li3!io5!nd!hlc!klc!kn5!hl0!iq0!lu0!jna!mr9!krb&>0@1$1@1$0#k0@1$5@1$1@1$0#8&@2$4@1$0#k0@3$a@1$1@1$0#k0$3^2>1m~0>2m'~0>2rs@1$2@2$6@1$1@1$0#k0$3>1a@1$1@1$0#k0>1n$f>2bs@1$2@1$1@1$0#8>0@3$h2^6^5^4>0@3$b@1$5@1$2@1$1@1$0#8@4$c$d^7^4^3@2$9@1$2@1$1@1$0#8^2>0@2$8@2$7@2$4@1$0#k0^5@1$e^4@2$h4+2+k0>0>1r@2$6@1$1@1$0#k0$3>0@3$h3@2$6@1$1@1$0#k0$3^1^8@2$h1@2$8@2$7@2$4@1$0#k0^8@1$e^7~1@2$8@2$7~1@3$h0@1$1@1$0#k0$3^2@2$4@1$0#k0^8@3$b@1$5@1$2@1$1@1$0#8@4$c$d^9^7^6@2$9@1$2@1$1@1$0#8^5").
Proof.
  intros m m' rs a n bs [Hout _] Hr Hnw Hd. rewrite (rdn_ext RSEGS n m' m a); [exact Hr | exact Hnw |].
  intros x Hx. apply Hout. apply outside_of_disjoint. intros r0 Hr0. pose proof (Hd r0 Hr0). lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_out : ltac2:(zQ "h10!h9!jc!l9!iob!itc!kr5!kn5!m0!li3!mk2!nd!hlc!klc!krb!hl0!lu0!hu4>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>3wad@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>1a@1$1@1$0#k0>1n$e>1v@1$2@1$1@1$0#8>0@3$a@1$7@1$2@1$1@1$0#8@4$b$c^6^3^2@2$8@1$2@1$1@1$0#8^1>0@2$5@2$4@2$3@1$0#k0^6@1$6@2$9@1$1@1$0#8^5@2$d+2+k0>0@2$5@2$4@2$3@1$0#k0^5@1$6^4@2$d+2+k0>0@2$f@2$5@2$4@2$3@1$0#k0^6@1$6^5@2$3@1$0#k0^8@2$5@2$4@2$3@1$0#k0^8@1$6@2$9@1$1@1$0#8^7@2$3@1$0#k0^6@3$a@1$7@1$2@1$1@1$0#8@4$b$c@3$h0^a^9^8^7^6@2$8@1$2@1$1@1$0#8^5").
Proof.
  intros m wad bs a n v Hr H1 H2 Hd. rewrite (rdn_ext RSEGS n (wbytes m wad bs) m a); [exact Hr | exact H2 |].
  intros x Hx. apply wbytes_outside; lia.
Qed.

Lemma cells_ok_wbytes_out : ltac2:(zQ "h60!ijb!hue!h9!hl0!jc!itc!kr5!kn5!iob!mk2!l9!mvd!ko6!m0!kod!nd!lu0!mj8!hu4!ng9!nh6!krb>1m>0@1$4@1$2#k0@1$d@1$4@1$2#8>3wad@1$4@1$2#k0>2bs@1$a@1$4@1$2#8>2cs@1$a@2$0@2$0$1$3$1>0@3$f$c@3$h4@2$0@2$0$1$3$1$h3^1$e>0@2$b^5^2>0@2$6@2$5@2$8@1$2#k0^5@1$7@2$9@1$4@1$2#8^4@2$h5+2+k0>0@3$h1@2$0@2$0$1$3$1\1c@2$0@2$0$1$3$1M0\1c@2$0@2$0$1$3$1P^1\1y@2$0$1$3\2y0$1M0\1y@2$0$1$3P^2\1a$1\1w$3@2$h0@2$6@2$5^2@1$7^1@2$8@1$2#k0^b@2$6@2$5@2$8@1$2#k0^b@1$7@2$9@1$4@1$2#8^a^2^4@2$b@3$h2^8^7^6^5").
Proof.
  intros m wad bs cs Hwf Hc Hnw Hd. eapply cells_ok_agree; [exact Hwf| |exact Hc].
  clear Hc. induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  intros i Hi. apply wbytes_outside; rewrite ?u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma diag_cells_range : ltac2:(zQ "90!ijb!hue!hl0!kr5!kp4!mj8!ni1!itc!kn5@3$5@2$0@2$0$1$2$1\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1P^1\1y@2$0$1$2\2y0$1M0\1y@2$0$1$2P^2\1a$1\1w$2@2$4@2$3+vkmr8^2@2$3@2$7^2@1$8^1+hivjt8$6").
Proof. unfold diag_cells. repeat constructor; cbn; lia. Qed.
Lemma pf1_cells_range : ltac2:(zQ "90!ijb!hue!hl0!kr5!kp4!mj8!nif!itc!kn5@3$5@2$0@2$0$1$2$1\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1P^1\1y@2$0$1$2\2y0$1M0\1y@2$0$1$2P^2\1a$1\1w$2@2$4@2$3+vkmr8^2@2$3@2$7^2@1$8^1+hivjt8$6").
Proof. unfold pf1_cells. repeat constructor; cbn; lia. Qed.
Lemma pf1_cells_wf : ltac2:(zQ "90!ijb!hue!ko6!hl0!kod!nd!ng9!nif!nh6@3$5$2@3$8@2$0@2$0$1$3$1$6$7$4").
Proof. vm_compute. reflexivity. Qed.

Lemma Forall_cells_weaken : ltac2:(zQ "60!hue!ijb!hl0!ip9!mj8!l9>1P>0@2$1@2$1$0$2$0P>1Q>0@2$1@2$1$0$2$0P>2cs@1$5@2$1@2$1$0$2$0>0>1a$0>1w$2>1v$0>0@1^6@4$3@2$1$0$2$0@4$3$0$2^3^2^1@1^6@4$3@2$1$0$2$0@4$3$0$2^4^3^2>0@3$4@2$1@2$1$0$2$0^4^2@3$4@2$1@2$1$0$2$0^4^3").
Proof. intros P Q cs H HP. eapply Forall_impl; [|exact HP]. intros [[a w] v]. apply H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_S : ltac2:(zQ "h30!h9!jc!l9!m0!nd!li3!kp4!njc!hlc!klc!nk1!nk5!hl0!nkc!nl0!jt6!nl7!nlc!nm3>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1n$c>2bs@1$2@1$1@1$0#8>0@3$4@1$3@1$2@1$1@1$0#8@4$8$9^4^3@1$a^2@2$5@1$2@1$1@1$0#8^1@2$7@1$1@1$0#8\1b@1$1@1$0#8@2$7@1$2@1$1@1$0#8\1r@1$2@1$1@1$0#8@2$6@3$4@1$2@1$1@1$0#8^4@3$b@1$1@1$0#8^2^1@2$6@3$4@1$3@1$1@1$0#8@3$e$f^7^6@2$5@1$1@1$0#8^2@3$4@1$3@1$2@1$1@1$0#8@4$8$9^7@3$h2@1$0#k0^6@3$h0@1$0#k0+1Kv$d@2$h1@1$0#k0+1^5@2$5@1$2@1$1@1$0#8^1").
Proof.
  intros m a n bs H. change (rdn RSEGS) with (OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.PropExec.rdn rsegs) in H |- *.
  rewrite rdn_unfold in H. destruct (mrd rsegs m a) as [b|]; [|discriminate].
  destruct (OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.PropExec.rdn rsegs m (a + 1)%bv n) as [r|]; [|discriminate].
  injection H as <-. exists b, r. auto.
Qed.

Lemma rdn_bytes_at : ltac2:(zQ "h10!h9!jc!l9!mk2!m0!kr5!li3!nd!hue!nmc!hlc!jt6!klc!itc!kn5!krb!ij1>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a$8>0@3$7@1$4@1$2@1$1@1$0#8@4$a$c^2@2$h0@1$0#k0^1@2$3@1$1@1$0#8^3@2$6@1$2@1$1@1$0#8^3>0@2$5Z^2>0@2$5@2$d^3@1$e@2$3@1$1@1$0#8^5@2$f+2+k0@4$9$b^5^4^6").
Proof.
  induction bs as [|b bs IH]; intros m a H Ha Hn.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [length] in H, Hn. destruct (rdn_S m _ _ _ H) as (b' & r & E & Hm & Hr). injection E as <- <-.
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. rewrite wa_eq. exact Hm.
    + cbn [nth_error]. destruct (Z.eq_dec (a + 1) (2 ^ 64)) as [Heq|Hne].
      { cbn [length] in Hi. lia. }
      assert (IHr := IH m (a + 1)).
      assert (Ea : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
      { apply bv_eq. rewrite u_add1 by (rewrite u_small by lia; lia). rewrite !u_small by lia. reflexivity. }
      rewrite Ea in Hr. specialize (IHr Hr ltac:(lia) ltac:(cbn [length] in Hi |- *; lia)).
      ndestruct IHr as (_ & _ & IH3). rewrite <- (IH3 i) by (cbn [length] in Hi; lia). f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma errno_rw_any : ltac2:(zQ "b0!h9!jc!nr4!nk5!nrc!m0!njc!ns2!og3!jt6!lgc>1m>0@1$1@1$0#k0@1$5@1$1@1$0#8@2$6@1$1@1$0#k0\1e@1$1@1$0#k0@4$8$9^2@2$a+hgurv8+q4@3$3$2@1$7^1@1$4$2").
Proof.
  intros m.
  assert (RD : forall i, 0 <= i < 4 -> exists b, mrd rsegs m (wa (0x10eb54 + i)) = Some b).
  { intros i Hi. unfold mrd. destruct (m (wa (0x10eb54 + i))) as [b|]; [exists b; reflexivity|].
    rewrite seg_rom_same. change rsegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; eexists; reflexivity. }
  destruct (RD 0 ltac:(lia)) as [b0 H0]. destruct (RD 1 ltac:(lia)) as [b1 H1].
  destruct (RD 2 ltac:(lia)) as [b2 H2]. destruct (RD 3 ltac:(lia)) as [b3 H3].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  split.
  - split; [cbn; repeat split; exact I|]. cbn [cells_bytes cbytes app].
    change (le4 ?v) with (word_to_le_bytes 4 v). rewrite word_to_le_bytes_of_lez by (reflexivity || (cbn; lia)).
    rewrite app_nil_r. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; [ | | | | lia].
    + rewrite Z.add_0_r in H0. exact H0. + exact H1. + exact H2. + exact H3.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    replace (0x10ebf8 - 164 + i)%Z with (0x10eb54 + i)%Z by lia.
    unfold wview. destruct (m (wa (0x10eb54 + i))) as [b|]; [discriminate|].
    change rsegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; discriminate.
Qed.
End FPX2.
(* [comment removed for export] *)
