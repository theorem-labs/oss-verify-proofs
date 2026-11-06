(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocWalkKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AW_LargeAlloc1 AW_PoisonRemap1 SecLazy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~03mem37Corelib4Init9Datatypesk34list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~m23ivl37Corelib7Numbers7BinNumsq44Npos35stdpp9bitvectorbdefinitionss42bvk34Nonek36option37Corelib4Init5Logicv62eqv63not3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh55wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hl55asegsm27outsides4bbv_unsigned89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8SecLazy23HCW~~~~~~hr19wmono_outm25wmonom25munchq41Zk34prodk34consk33nilk34pair69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~iif6unfill46Stdlib6ZArith6BinInt1Zin33addv63andin32lein32ltm2ddisjoint_fromin33sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~irb5wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ive8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jk54celljk5acells_sizein36of_natm23stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jq75u8arrk36lengthjq76u64arrin33mul79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAW_LargeAlloc1~~~~~~kg44SENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAW_PoisonRemap1~~~~~~kl04RENVk34boolk35falsek33snd69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~kr22hikr22lokr23remkr25zcovb3h5LinuxProcessSemanticsfLinuxProcessSem5Statelgbdmaps_subtractkr2eentries_nowrapk33app69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~lm2ain_rangesb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~lqf2wzin33powk34Somehh5afetch_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7SecLazy~~~~~~mgc6ECALLWs47Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Definition wmono_out : ltac2:(zQ "30!je!lb!pe>1X@1$1$2>1m$0>2m'$0P") := ltac2:(zQ "d0!rd!u1!u6!ud!hga!hgf!hkc!hp0!je!lb!pe!hp9!hq3\1X@1$9$a\1m$8\2m'$8>1x@1$1@1$0#k0>0@2$b^4@2$c@1$0#k0^1>0@1$5@3$4@1$3@1$1@1$0#8@3$6$7^4^2@1$2@1$1@1$0#8@1$5@3$4@1$3@1$1@1$0#8@3$6$7^4^3@1$2@1$1@1$0#8").

Lemma wmono_out_of_wmono : ltac2:(zQ "81!rd!u1!ud!lb!hp0!hv3!pe!ig0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1X@1$3$6>1m~0>2m'~0>0@3$7$4^2^1@3$5^4^3^2").
Proof. intros X m m' WM x _ Hx. exact (WM x Hx). Qed.

Lemma wmono_out_trans : ltac2:(zQ "40!je!hv3!lb!pe>1X@1$2$3>2m1$0>2m2$0>2m3$0>0@3$1^4^3^2>0@3$1^5^3^2@3$1^6^5^3").
Proof. intros X m1 m2 m3 A B x Ho Hx. exact (B x Ho (A x Ho Hx)). Qed.

Lemma wmono_out_wmono_l : ltac2:(zQ "91!rd!u1!ud!hv3!lb!hp0!je!pe!ig0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1X@1$4$7>2m1~0>2m2~0>2m3$6>0@3$8$5^3^2>0@3$3^5^3^2@3$3^6^5^3").
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [apply wmono_out_of_wmono; exact A| exact B]. Qed.

Lemma wmono_out_wmono_r : ltac2:(zQ "90!rd!je!hv3!u1!lb!ud!hp0!pe!ig0>1X@1$4$7>2m1$1>2m2$1>2m3>0@1$3@1$0#k0@1$5@1$3@1$0#8>0@3$2^4^3^2>0@3$8$6^3^2@3$2^6^5^3").
Proof. intros X m1 m2 m3 A B. eapply wmono_out_trans; [exact A| apply wmono_out_of_wmono; exact B]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wview_pointwise : ltac2:(zQ "70!rd!u1!ud!hga!hkc!hp0!je>1m$6>2m'$6>1x@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#8@1^2^1@1^3^1@3$3@1$2@1$1@1$0#8@3$4$5^3^2@3$4$5^4^2").
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma munch_wmono_out : ltac2:(zQ "71!rd!u1!ud!lb!hv3!pe!ig8&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$3$5>1m~0>2m'~0>0@3$6^3^2^1@3$4^4^3^2").
Proof. intros W m m' MU x Ho Hx. rewrite (wview_pointwise m m' x (MU x Ho)). exact Hx. Qed.

Lemma unfill_wmono_out : ltac2:(zQ "c0!ih0!rd!hq3!ih4!u1!ihb!ii2!ii8!je!hv3!im9!iob>1a@1$4@1$1#k0>1n@1$4@1$1#k0>1m$8@3$9@3$5@2$3$0$0@4$7$0$0@2$2@1$1#k0^3@2$b@2$2@1$1#k0^3@2$2@1$1#k0^2@1$6@2$3$0$0^1@3$a^3^2^1").
Proof. intros a n m. apply munch_wmono_out. apply unfill_munch. Qed.

(* [comment removed for export] *)
Lemma unfill_none : ltac2:(zQ "c0!rd!u1!hq3!u6!ud!ip2!hga!je!im9!iob!ip8!ipe>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m$7>1x@1$1@1$0#k0>0@2$5@2$a@2$2@1$0#k0^4@2$2@1$0#k0^1@2$b@2$2@1$0#k0^1@2$9@2$2@1$0#k0^4@2$2@1$0#k0^3@3$6@1$4@1$1@1$0#8@4$8^5^4^3^2@1$3@1$1@1$0#8").
Proof.
  intros a n m x Hx. unfold unfill.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb];
    try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma none_range_munch : ltac2:(zQ "h00!rd!u1!hq3!u6!ud!ip2!hga!ih0!je!ip8!ipe!lb!iq4!pe!ig8!ir4>1W@1$b$d>1m$8>2m'$8>2lo$7>2hi$7>0>1x@1$1@1$0#k0>0@2$5@2$9^3@2$2@1$0#k0^1@2$a@2$2@1$0#k0^1^2@3$6@1$4@1$1@1$0#8@1^6^2@1$3@1$1@1$0#8>0@3$e^6^5^4>0@3$c^7^4@2$f^3^4>1x@1$1@1$0#k0>0@2$5@2$9^6@2$2@1$0#k0^1@2$a@2$2@1$0#k0^1^5@3$6@1$4@1$1@1$0#8@1^8^2@1$3@1$1@1$0#8").
Proof.
  intros W m m' lo hi N MU D x Hx. rewrite (MU x); [exact (N x Hx)|].
  eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MuTransport.
  Variables (W : list ivl) (m m' : mem).
  Hypothesis MU : ltac2:(zQ "10!ig8@3$0?1W?1m?2m'").

  Lemma wr_at_transport_mu : ltac2:(zQ "40!ih0!hp0!iv5!iq4>1A$0>1n$0>0@4$2$1?1m^2^1>0@3$3?1W^3^2@4$2$1?2m'^4^3").
  Proof.
    (intros A n nd_i1 D; ndestruct nd_i1 as (Ha & Hn & H)). split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    rewrite (wview_pointwise m m'); [exact (H i Hi)|]. apply MU. eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma rw_cells_transport_mu : ltac2:(zQ "80!hp0!jj9!lb!ih0!jo1!jo9!iq4!jp7>1A$3>2cs@1$2$4>0@4$1$0?1m^2^1>0@3$6?1W^3@1$7@1$5^2@4$1$0?2m'^4^3").
  Proof.
    intros A cs [[Hwf Hb] Hw] D. split; [split; [exact Hwf|]|].
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite cells_bytes_length by assumption. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.

  Lemma stk_transport_mu : ltac2:(zQ "50!ih0!hp0!jq1!iq4!ir4>2lo$0>2hi$0>0@4$2$1?1m^2^1>0@3$3?1W^3@2$4^2^3@4$2$1?2m'^4^3").
  Proof.
    (intros lo hi nd_i2 D; ndestruct nd_i2 as (H1 & H2 & H)). split; [exact H1|]. split; [exact H2|]. intros a Ha.
    assert (E : m' (wa a) = m (wa a)) by (apply MU; eapply disjoint_outside; [exact D|]; rewrite wa_unsigned by lia; lia).
    destruct (H a Ha) as [Hw (b & Hb)]. split.
    - rewrite (wview_pointwise m m' (wa a) E). exact Hw.
    - exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma u8arr_transport_mu : ltac2:(zQ "90!rd!hp0!ju1!u1!jua!lb!ih0!iq4!jp7>1A$6>2bs@1$5@1$3@1$0#8>0@4$2$1?1m^2^1>0@3$7?1W^3@1$8@2$4@1$3@1$0#8^2@4$2$1?2m'^4^3").
  Proof.
    intros A bs [Hb Hw] D. split; [eapply bytes_at_transport; [exact Hb| exact MU| exact D]| eapply wr_at_transport_mu; [exact Hw| exact D]].
  Qed.

  Lemma u64arr_transport_mu : ltac2:(zQ "a0!rd!hp0!jv3!u1!jua!lb!ih0!iq4!jvd!jp7>1A$6>2ws@1$5@1$3@1$0#k0>0@4$2$1?1m^2^1>0@3$7?1W^3@2$8+8@1$9@2$4@1$3@1$0#k0^2@4$2$1?2m'^4^3").
  Proof.
    intros A ws [Hb Hw] D. split.
    - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite u64s_length, Nat2Z.inj_mul. exact D.
    - eapply wr_at_transport_mu; [exact Hw| exact D].
  Qed.

  Lemma senv_transport_mu : ltac2:(zQ "70!iq4!ih0!rd!kk8!iob!u1!hq3>2tp@1$5@1$2#k0>3TSD$1>3CTX$1>2TH$1>0@5$3^4^3^2^1?1m>0@3$0?1W+hrvqq0+8>0@3$0?1W@2$4@2$6@1$2#k0^6-l8+8>0@3$0?1W^6+8>0@3$0?1W@2$4^6+p8+8>0@3$0?1W+hrvqpc+1>0@3$0?1W+hrlln8+n8>0@3$0?1W+hsgij8+8>0@3$0?1W+hsgvi0+h8>0@3$0?1W+ilhtu0+8>0@3$0?1W+ilhtv8+8>0@3$0?1W+ilhumc+1>0@3$0?1W+hrnlq0+8>0@3$0?1W+ikvsu0+8>0@3$0?1W+hrnlt8+8@5$3^h3^h2^h1^h0?2m'").
  Proof.
    intros tp TSD CTX TH E; intros; destruct E; constructor;
      (eapply rw_cells_transport_mu; [eassumption | ]);
      unfold AGOT_VALS; cbn [cells_size csize length map Nat.add Nat.mul]; assumption.
  Qed.

  Lemma renv_transport_mu : ltac2:(zQ "40!iq4!rd!kp5!u1>1g@1$3@1$1#k0>1b@1$3@1$1#8>0@3$2^2^1?1m>0@3$0?1W+hrlln8+n8>0@3$0?1W+hsgij8+8>0@3$0?1W+hsgvi0+h8>0@3$0?1W+ilhtu0+8>0@3$0?1W+ilhtv8+8>0@3$0?1W+ilhuk3+1>0@3$0?1W+ilhulc+1>0@3$0?1W+hrnlq0+8>0@3$0?1W+ikvsu0+8>0@3$0?1W+nhkmp8+8>0@3$0?1W+hrmji8+8>0@3$0?1W+nhkkh8+8@3$2^f^e?2m'").
  Proof.
    intros g b E; intros; destruct E; constructor;
      (eapply rw_cells_transport_mu; [eassumption | ]);
      unfold AGOT_VALS; cbn [cells_size csize length map Nat.add Nat.mul]; assumption.
  Qed.
End MuTransport.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rem_uncovered : ltac2:(zQ "h11!rd!u1!ih4!hga!ih0!kpd!kq4!lb!kqc!ip2!kuf!kv5!kvb!lg2!ip8!ipe!hq3&@2$2@1$1@1$0#k0@1$1@1$0#k0>1e~0>1C@1$7~0>0>1x$4>0@2$9@2$e@1$b^3^1@2$f^1@1$a^3@3$3$5@2$d^3^2$6@3$3$4@2$c^3^2@2$h0@1$0#k0@3$8@1$1@1$0#k0@1$1@1$0#k0^3").
Proof.
  intros e C H. unfold rem. rewrite <- hi_minus_lo. apply zmeasure_all; [apply lo_hi|].
  intros x Hx. rewrite (H x Hx). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zcovb_maps_subtract_false : ltac2:(zQ "c0!ih0!kpd!kq4!hga!rd!lg2!ip8!u1!lb!ih4!lj9!lka>1C@1$8@2$9@1$7@1$4#k0@1$7@1$4#k0>1l$0>1h$0>1x$0>0@1$b^4>0@2$6Z^4>0@2$6^5^4>0@3$3$1@2$5^7^4$2@3$3$1@2$5@3$a^8^7^6^5$2").
Proof. intros C l h x NW Hl Hlh H. rewrite (zcovb_maps_subtract C l h x NW Hl Hlh), H. reflexivity. Qed.

Lemma zcovb_app_false : ltac2:(zQ "a2!rd!u1!kpd!kq4!ih4!hga!lg2!lb!llc!ih0&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$7~0>2C1~1>2C2~1>1x$9>0@3$5$2@2$6^3^1$3>0@3$5$2@2$6^3^2$3@3$5$2@2$6@3$8~0^5^4^3$3").
Proof. intros C1 C2 x H1 H2. rewrite zcovb_app, H1, H2. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_rangesb_false_zcovb : ltac2:(zQ "f0!kpd!kq4!hga!rd!u1!lb!ih4!ip2!ih0!lg2!lq1!lua!ip8!ipe!lv0>1C@1$5@2$6@1$4@1$3#k0@1$4@1$3#k0>1x$8>0@2$7@2$cZ^1@2$d^1@2$e+2+k0>0@3$2$0@2$a@1$b^2^3$1@3$2$0@2$9^4^3$1").
Proof. intros C x Hx H. rewrite in_rangesb_zcovb in H. unfold wz in H. rewrite unsigned_lit in H by lia. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ecall_a2ab4 : ltac2:(zQ "90!rd!u1!lv7!ud!hga!lve!hp0!mk9!ml3@3$4@1$3@1$1@1$0#i0@2$5$6@2$8@1$0#k0+qiqq4@2$2@1$1@1$0#i0$7").
Proof. vm_compute. reflexivity. Qed.

End HCW.

(* [comment removed for export] *)
