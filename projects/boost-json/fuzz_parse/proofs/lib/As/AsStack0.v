(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsIface AsCXXHeap CXXRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~hc3mem37Corelib4Init5Logiclf3and46Stdlib6ZArith6BinInt1Zn92len93sublf2eqlf2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~q67AAPP_HIq65aceilq6baddressablen96modulo37Corelib4Init9Datatypeshgd4prodhgd3fsthgd3sndlf2orq66AHI_LOq62sh89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsStack03HCW~~~~~~hke6stack004Npos35stdpp9bitvectorbdefinitionshq02bvhgd4listhgd4Somehgd4conshgd3nilhgd6option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshucdov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ij45asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~in82wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ir82b8n93addn96shiftrhq07Z_to_bvq6aaccessibleq6ain_app_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jid3stkq65shvis37Corelib5Lists7ListDefjn86Forallq63nshhke9stack0_okjidddisjoint_fromjid3ivljid5munchjid5wmonohgd4pairq64aapphc5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6CXXRep~~~~~~jud5xpreshc3asr" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition stack0 : ltac2:(zQ "20!h9!l9>1m$1>2lo$0>2hi$0P") := ltac2:(zQ "b0!n3!h9!p1!p6!pc!q1!l9!u4!ue!v6!hg4\1m$6\2lo$1\2hi$1@2$5$1\1g$1@2$0@2$0@2$2@1$8?5HCEIL^1@2$2^1^3@2$0@2$0@2$2^3^2@2$2^2$7@2$0@3$4$1@2$a@2$3^2^1+8Z@3$9^4^1@2$3^2^1").

(* [comment removed for export] *)
Definition stack0_ok : ltac2:(zQ "20!h9!hi5>2iv@2$1$0$0P") := ltac2:(zQ "90!h9!p1!hid!hi5!hj4!hjb!hk0!ue!hk9\2iv@2$3$0$0@2$5@2$1$6@3$2$0$0^1@2$1@3$4$0$0^1@1$8@1$7?5HCEIL").

Lemma stack0_bounds : ltac2:(zQ "70!p1!n3!h9!l9!u4!ue!hp0>1m$3>2lo$2>2hi$2>0@3$6^3^2^1@2$1@2$0@1$5?5HCEIL^3@2$1@2$0^3^2@2$0^2$4").
Proof. (intros m lo hi nd_i1; ndestruct nd_i1 as (g & H1 & H2 & _)). lia. Qed.

Lemma stack0_sub : ltac2:(zQ "70!h9!p1!hp0!n3!pc!l9!hg4>1m$5>2lo$0>2hi$0>3lo'$0>3hi'$0>0@3$2^5^4^3>0@2$1^5^3>0@2$3@2$1^4^3@2$1^3^5>0@3$4$0@2$6^4+8Z@3$2^9^6^5").
Proof.
  (intros m lo hi lo' hi' nd_i2 Hlo Hhi H8; ndestruct nd_i2 as (g & H1 & H2 & H3 & AD)). exists g.
  pose proof AD as [_ SH]. pose proof (SHAD_aligned _ _ _ SH) as [G0 G8].
  split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; nia|].
  destruct (addressable_split8 m g (hi - g) (hi' - g) AD H3 ltac:(Z.div_mod_to_equations; nia) ltac:(lia)) as [A1 _]. exact A1.
Qed.

(* [comment removed for export] *)
Lemma stack0_read0 : ltac2:(zQ "h20!hpa!hrd!h9!p1!hs3!pc!hsb!ht3!htb!hu2!ii3!imf!l9!hk9!hp0!ir2!iv3!iv9>1m$c>2lo$2>2hi$2>1a$2>1w$2>1x@1$1@1$0#k0>0@3$e^6^5^4>0@2$3^6^4>0@2$3+1^4>0@2$3@2$h1^6^5^7>0@3$5@1$1@1$0#k0^5@1$f@1$d^7@3$5@1$9@1$4@1$1@1$0#8@4$a$b^b^6N1@2$6@1$4@1$1@1$0#8@3$7@1$1@1$0#8@1$h0Z@1$8@1$1@1$0#8").
Proof.
  (intros m lo hi a w x nd_i3 Hlo Hw Hhi ->; ndestruct nd_i3 as (g & H1 & H2 & H3 & AD)).
  eapply (addressable_read0_w m g (hi - g) a w); [exact AD| lia| lia| | reflexivity].
  replace (8 * ((hi - g) / 8)) with (hi - g) by (Z.div_mod_to_equations; nia). lia.
Qed.

(* [comment removed for export] *)
Lemma stack0_read0_sr : ltac2:(zQ "h20!hpa!h9!hrd!p1!hs3!iv9!hsb!ht3!htb!hu2!pc!ii3!imf!l9!hp0!iv3!ivf!jg8>1m$d>2lo$1>2hi$1>1a$1>1w$1>0@3$e^5^4^3>0@2$3^5^3>0@2$3+1^3>0@2$3@2$5^5^4^6@3$a@1$9@1$4@1$2@1$0#8@4$b$c^9@2$h1@1$0#k0@2$5@2$h0^6+3+nvvvogg0N1@2$6@1$4@1$2@1$0#8@3$7@1$2@1$0#8@1$fZ@1$8@1$2@1$0#8").
Proof.
  intros m lo hi a w ST Hlo Hw Hhi. pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. acb.
  eapply stack0_read0; [exact ST| exact Hlo| exact Hw| exact Hhi|].
  unfold wa. rewrite <- sh_shiftr by lia. rewrite ASHADOW_BASE_val. reflexivity.
Qed.

Lemma stack0_accessible : ltac2:(zQ "60!h9!p1!l9!jh3!hp0!iv9>1m$2>2lo$0>2hi$0>1a$0>1n$0>0@3$4^5^4^3>0@2$1^5^3>0@2$1Z^3>0@2$1@2$5^5^4^6@3$3^9^6^5").
Proof.
  intros m lo hi a n (g & H1 & H2 & H3 & AD) ? ? ?. eapply addressable_accessible; [exact AD| lia| lia| lia].
Qed.

Lemma stack0_in_app_mem : ltac2:(zQ "60!h9!p1!l9!ji0!hp0!iv9>1m$2>2lo$0>2hi$0>1a$0>1b$0>0@3$4^5^4^3>0@2$1^5^3>0@2$1@2$5^3+8^5@2$3^5^4").
Proof. intros m lo hi a b (g & H1 & H2 & _) ? ?. right. acb; unfold AHI_LO in *. lia. Qed.

(* [comment removed for export] *)
Lemma stack0_stk : ltac2:(zQ "c0!h9!n3!hk9!p1!pc!q1!imf!l9!ue!hp0!jm9!hg4>1m$7>2lo$0>2hi$0>0@3$9^3^2^1@2$5$0\1g$0@2$1@2$1@2$3@1$8?5HCEIL^1@2$3^1^4@2$1@3$4$0@2$b^1+8Z@4$a$6^5@1$2^1@1$2^3").
Proof.
  (intros m lo hi nd_i4; ndestruct nd_i4 as (g & H1 & H2 & H3 & [Hn SH])). exists g. pose proof (SHAD_aligned _ _ _ SH) as [G0 G8].
  split; [lia|]. split; [exact G8|].
  pose proof (stk_of_rw_cells asegs m _ _ (SHAD_rw_cells _ _ _ SH)) as K. cbn [cells_size csize Nat.add] in K.
  rewrite Nat.add_0_r, shadow_of_length in K by lia.
  replace (sh g + nsh (hi - g)) with (sh hi) in K; [exact K|].
  unfold nsh. rewrite (sh_rel g hi G8) by lia. Z.div_mod_to_equations. nia.
Qed.

Lemma stack0_shvis : ltac2:(zQ "60!h9!p1!iv9!l9!jn0!hp0>1m$3>2lo$0>2hi$0>1a$0>1b$0>0@3$5^5^4^3>0@2$1@2$2^5+k0^3>0@2$1^4^3>0@2$1@2$2^4+k0^6@3$4^9^6^5").
Proof.
  intros m lo hi a b ST Ha Hab Hb. pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. acb.
  destruct (stack0_stk _ _ _ ST) as (g & G1 & G8 & K). unfold shvis.
  npose (hull_lo_le a ltac:(lia)) as (L1 & L2 & L3). npose (hull_hi_ge b ltac:(lia)) as (R1 & R2 & R3).
  ndestruct K as (K0 & K1 & K). split; [pose proof (sh_mono g (hull_lo a) ltac:(lia)); lia|].
  split; [pose proof (sh_mono (hull_hi b) hi ltac:(lia)); lia|].
  intros x Hx. apply K. pose proof (sh_mono g (hull_lo a) ltac:(lia)). pose proof (sh_mono (hull_hi b) hi ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma stack0_ok_disjoint : ltac2:(zQ "c0!h9!p1!hi5!hs3!jof!u4!ue!jp9!hk9!jpf!jqc!iv9>1W@1$3@2$2$0$0>1g$0>1n$0>0@3$4@2$2$0$0$9^3>0@2$1@1$6?5HCEIL^3>0@2$1Z^3>0@2$1@2$b^5^4$5@3$a^7@1$8^6@1$7^5").
Proof.
  induction W as [|[l h] W IH]; intros g n HW Hg Hn Hhi; cbn; [exact I|].
  pose proof (Forall_inv HW) as H1. cbn in H1. unfold stack0_ok in H1. cbn in H1.
  pose proof (sh_nsh_high g n ltac:(acb; lia) Hn Hhi) as T.
  pose proof (sh_mono aceil g Hg) as U.
  split; [lia| apply IH; [exact (Forall_inv_tail HW)| lia| lia| lia]].
Qed.

Lemma stack0_transport : ltac2:(zQ "e0!h9!hpa!hp0!hrd!hs3!hu2!hi5!jof!imf!l9!jpf!jrd!js4!jsd>1W@1$4$b>1m$9>2m'>0@1$3@1$1#k0@1$5@1$3@1$1#8>2lo$0>2hi$0>0@3$2^4^2^1>0@3$c^6^5^4>0@3$d$8^6^5>0@3$7@2$6$0$0$a^8@3$2^7^6^5").
Proof.
  (intros W m m' lo hi nd_i5 MU WM HW; ndestruct nd_i5 as (g & H1 & H2 & H3 & AD)). exists g. split; [lia|]. split; [lia|]. split; [exact H3|].
  eapply addressable_transport; [exact AD| exact MU| exact WM|]. apply stack0_ok_disjoint; [exact HW| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma stack0_ok_app : ltac2:(zQ "50!h9!jt6!hk0!jpf!p1>1l$0>1h$0>0@2$4$2^2@1$3@4$1$0$0^3^2").
Proof. intros l h H. left. exact H. Qed.

(* [comment removed for export] *)
Lemma stack0_ok_aapp : ltac2:(zQ "60!h9!p1!jt6!jte!jpf!iv9>1A$0>1n$0>1l$0>1h$0>0@3$3?5HCEIL^4^3>0@2$1^5^3>0@2$1^3@2$5^6^5@1$4@4$2$0$0^5^4").
Proof.
  intros A n l h AP Hl Hh. destruct AP as [[P1 P2]|[P1 P2]]; [right| left]; cbn; [| lia].
  acb. unfold sh, ALOWSH_LO in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section X.
  Variable H : ltac2:(zQ "10!kj2$0").

  Lemma stack0_xpres : ltac2:(zQ "90!h9!hs3!hi5!l9!hp0!jof!ju5!jpf!ki9>2LB@1$1$6>2SP$0>1X@1$1@2$2$0$0>1m$3>2m'$3>2lo$0>2hi$0>0@7$8?5HCEIL?1H^7^6^5^4^3>0@3$4^5^3^2>0@3$5@2$2$0$0$7^7@3$4^6^5^4").
  Proof.
    (intros LB SP X m m' lo hi XP nd_i6 HX; ndestruct nd_i6 as (g & H1 & H2 & H3 & [Hn (G0 & G8 & [UB UW])])).
    assert (CL : xclient_range H LB SP X (sh g) (nsh (hi - g))).
    { split.
      - right; right; right; right; right; right. pose proof (sh_mono aceil g (proj1 H1)).
        pose proof (sh_nsh_high g (hi - g) G0 ltac:(lia) ltac:(lia)). lia.
      - eapply Forall_impl; [| exact HX]. intros [l h] K. cbn. unfold stack0_ok in K. cbn in K.
        pose proof (sh_mono aceil g (proj1 H1)). pose proof (sh_nsh_high g (hi - g) G0 ltac:(lia) ltac:(lia)). lia. }
    exists g. split; [lia|]. split; [lia|]. split; [exact H3|]. split; [exact Hn|]. split; [exact G0|]. split; [exact G8|].
    rewrite <- (shadow_of_length (hi - g)) in CL by lia. split.
    - eapply xpres_bytes_at; [exact XP| exact UB| exact CL].
    - eapply xpres_wr_at; [exact XP| exact UW| exact CL].
  Qed.
End X.

End HCW.

(* [comment removed for export] *)
