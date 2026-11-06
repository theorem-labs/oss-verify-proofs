(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU6BJKitW~~~~~~hc9gcap_from46Stdlib6ZArith6BinInt1Zm52lem52ltm53mul37Corelib4Init9Datatypesod3nat37Corelib4Init5Logicqb3andqb2eqqb2orm56of_natm53powhc8grow_cap04Nposm53add35stdpp9bitvectorbdefinitionsv57Z_to_bvm53oppm56shiftrv52bvv59bv_signedv5bbv_unsignedm56shiftlod4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hla4cellod4conshla2C8od3nilhla2C1hla2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hrd2b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~hve3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~il08rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ip75rsegshla2C4qb2ex99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU6BJKitW3HCW1W~~~~~~iu8ebj_statics_raw79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU5BJRep~~~~~~jjdabj_staticshve5blockhvearheap_presod4prodod3fstod6optionod3snd37Corelib5Lists7ListDefjra6Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jtb3ivljtb5munchjtb5wmonohlaacells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~kje7eh_preskjeh3eh_static_range_lawhvedrclient_rangekje7eh_idlekjeh1eh_idle_frame_law79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kt72waod4Noneqb3not3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsli45wviewkjebeh_chain_okkje8chain_spkjeh2eh_chain_frame_lawkje5frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame~~~~~~lpf7rin_ivslpf5xpreskjebsaves_clearkje8eh_fsizekje5fr_fnkje5fr_sp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~mhf4bptrod4pair36Stdlib5Lists4Listmma2In69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mo35hceilkje8hs_RHEAPmhf6PStatejtb3stkkje6EH_IVSkje8exc_livekje3hmfkje3ehkkjecheap_mf_hyps" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint gcap_from (fuel : nat) (c need : Z) : Z :=
  match fuel with O => c | S f => if c <? need then gcap_from f (2 * c) need else c end.
Definition grow_cap : ltac2:(zQ "10!h9>4need$0$0") := ltac2:(zQ "20!h9!l9\4need$0@3$1Ni4+h0^1").

Lemma gcap_from_ge : ltac2:(zQ "b0!h9!l9!nd!o2!o7!q5!rf!s5!sa!sf!t8>4fuel$5>1c$0>4need$0>0@2$3Z^2>0@2$2^2@2$4^3@2$a+2@1$9^4@2$6@2$2^3@3$1^5^4^3@2$8@3$7$0@3$1^5^4^3^4@2$3@3$1^5^4^3@2$4+2^3").
Proof.
  induction fuel as [|fuel IH]; intros c need Hc Hn; cbn [gcap_from].
  - cbn in Hn. lia.
  - destruct (Z.ltb_spec c need).
    + destruct (IH (2*c) need ltac:(lia)) as [A B].
      { rewrite Nat2Z.inj_succ in Hn. rewrite Z.pow_succ_r in Hn by lia. lia. }
      split; [exact A|]. right. destruct B; lia.
    + lia.
Qed.

Lemma gcap_from_lower : ltac2:(zQ "40!h9!nd!q5!l9>4fuel$2>1c$0>4need$0>0@2$1Z^2@2$1^3@3$3^4^3^2").
Proof.
  induction fuel as [|fuel IH]; intros c need Hc; cbn [gcap_from]; [lia|].
  destruct (c <? need); [|lia]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma grow_cap_bounds : ltac2:(zQ "90!te!nd!rf!h9!s5!sa!o2!o7!t8>4need$3>0@2$2@2$1Z^1@2$1^1@2$8+2+i8@2$2@2$1^2@1$0^2@2$2@2$1+h0@1$0^2@2$5@3$4$3@1$0^2+h0@2$6@1$0^2@2$7+2^2").
Proof.
  intros need Hn. unfold grow_cap.
  destruct (gcap_from_ge 36 16 need ltac:(lia) ltac:(cbn; lia)) as [A B].
  pose proof (gcap_from_lower 36 16 need ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma cap_calc : ltac2:(zQ "f0!u9!uf!hh2!h9!o7!rf!s5!nd!o2!hhc!t8!hi2!hib!hj0!hjc>1B$3>3cap$3>0@2$5@2$7Z^1@2$8^1@2$a+2+i8@3$6@1$c@1$0#k0@2$2@1$0#k0@2$1@2$4@2$e@1$0#k0@2$2@1$0#k0@2$b@2$d@1$0#k0@2$2@1$0#k0@2$1@2$1^3@2$4+h8^2@1$9^3+3+qqqqqqqqqqqqqqqb+1@2$2@1$0#k0@2$1^2+1").
Proof.
  intros B cap Hc. replace (B + 24 * cap + - B) with (24 * cap) by lia.
  rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N N.sub Z.pow_pos Pos.iter Z.mul Pos.mul]. change (2 ^ 64 / 2) with (2^63). rewrite (Z.mod_small) by lia.
  replace (24 * cap + 2 ^ 63 - 2 ^ 63) with (24 * cap) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (24 * cap / 2 ^ 3) with (3 * cap) by (change (2^3) with 8; rewrite <- (Z.div_mul (3*cap) 8) by lia; f_equal; lia).
  rewrite unsigned_lit by lia.
  rewrite <- Z_to_bv_mod64. f_equal.
  replace (3 * cap * 12297829382473034411 + 1) with ((cap + 1) + (2 * cap) * 2^64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes24 : ltac2:(zQ "d0!u9!h9!hka!rf!s5!uf!nd!o2!o7!hhc!t8!hh2!hjc>1g$1>0@2$3@2$6Z^1@2$7^1@2$a+2+i8@3$4$1@2$5@2$2^2+5@1$9@2$c@1$0#k0@2$b@1$0#k0@2$2^2+3@2$8+h8^2").
Proof. intros g Hg. rewrite !Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by (cbn; lia). cbn. lia. Qed.


Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : ltac2:(zQ "10!mva$0").
  Variable E : ltac2:(zQ "10!ng1$0").
  Hypothesis HH : ltac2:(zQ "10!ng8@3$0?5HCEIL?1H?1E").

  (* [comment removed for export] *)
  Definition vs_hdr_raw : ltac2:(zQ "50!h9!hl3!u9!hp6!hib>4temp$0>1B$0>3top$0>4eend$0>5chars$0>2j7@1$1@1$4@1$2#8@1$1$3") := ltac2:(zQ "c0!hp6!hpe!u9!hq5!hh2!h9!hl3!hqb!hr1!hr7!hv8!hib\4temp$5\1B$5\3top$5\4eend$5\5chars$5\2j7@1$6@1$b@1$2#8@3$1$0@1$3@2$4@1$2#k0Z@3$1$0@1$3@2$4@1$2#k0^6@3$1$0@1$3@2$4@1$2#k0^5@3$1$0@1$3@2$4@1$2#k0^4@3$1$0@1$3@2$4@1$2#k0^3@3$1$0@1$3@2$4@1$2#k0^2@3$1$0@1$8@1$a+1@3$1$0@2$9N7^1@3$1$0@1$3@2$4@1$2#k0Z@1$7$0").


  Definition bj_statics_raw : ltac2:(zQ "30!u9!ik9!hib>1m$1>4salt@1$2@1$0#k0P") := ltac2:(zQ "c0!hp6!hpe!u9!hh2!hq5!hqb!iob!it4!rf!itd!ik9!hib\1m$a\4salt@1$b@1$2#k0@2$8@4$6$7^2+vstn0@3$1$0@1$4@2$3@1$2#k0+vkos8@1$5$0@2$8@4$6$7^2+vkos8@3$1$0@1$4@2$3@1$2#k0+lqkr0@3$1$0@1$4@2$3@1$2#k0+lqkr4@3$1$0@1$4@2$3@1$2#k0+lqkrc@3$1$0@1$4@2$3@1$2#k0+lqks4@3$1$0@1$4@2$3@1$2#k0+lqksc@1$5$0@2$8@4$6$7^2+hgthr0@3$1$0@1$9@2$3@1$2#k0Z@3$1$0@1$9@2$3@1$2#k0Z@1$5$0@2$8@4$6$7^2+hgthr8@3$1$0@1$9@2$3@1$2#k0Z@3$1$0@1$9@2$3@1$2#k0Z@3$1$0@1$4^1@1$5$0@2$8@4$6$7^2+vstg0@3$1$0@1$4@2$3@1$2#k0+vkng0@3$1$0@1$4@2$3@1$2#k0+rpqprppiihnnsnn2@1$5$0@4$6$7^2+vknj0@3$1$0@1$4@2$3@1$2#k0+lqsl4@1$5$0").

  Lemma bj_statics_raw_of : ltac2:(zQ "60!u9!hib!iu3!jib!jn9!ik9>1m$5>0@1$4^1@2$2@1$1@1$0#k0\4salt@1$1@1$0#k0@2$3^3^1").
  Proof. intros m BS. bj_statics_open BS. exists salt. cbv beta delta [wz] in BS1, BS2, BS3, BS4, BS5, BS6. repeat (split; [assumption|]). assumption. Qed.
  Lemma bj_statics_of_raw : ltac2:(zQ "50!u9!jib!jn9!ik9!hib>1m$3>4salt@1$4@1$0#k0>0@2$1^2^1@1$2^3").
  Proof. (intros m salt nd_i1; ndestruct nd_i1 as (B1 & B2 & B3 & B4 & B5 & B6)). eapply bj_statics_fold; cbv beta delta [wz]; eassumption. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma statics_raw_rheap : ltac2:(zQ "80!jib!ik9!hl3!u9!h9!jo7!jp0!hib>1m$1>2m'$1>4salt@1$7@1$3#k0>2LB@1$2$5>2SP$4>0@2$0^5^3>0@4$6^3^2^6^5@2$0^6^5").
  Proof.
    (intros m m' salt LB SP nd_i2 HP; ndestruct nd_i2 as (B1 & B2 & B3 & B4 & B5 & B6)).
    unfold bj_statics_raw.
    repeat match goal with |- _ /\ _ => split end;
      (eapply rheap_pres_rw_cells; [exact HP | eassumption |
         right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn [cells_size csize Nat.add Z.of_nat]; lia]).
  Qed.

  Lemma statics_raw_munch : ltac2:(zQ "h10!h9!u9!hib!jpe!jib!nd!jq5!hl3!jqb!jr4!sa!jt1!kh7!khe!ki7!ik9!it4>1m$f>2m'>0@1$2@1$1#k0@1$8@1$2@1$1#8>4salt@1$2@1$1#k0>1W@1$7$c>0@2$4^4^2>0@3$d^2^5^4>0@3$e$h0^6^5>0@3$b@2$3$0$0\2iv@2$3$0$0@2$a@2$5+hjhgg0@3$6$0$0^1@2$5@3$9$0$0^1+vkgg0^4@2$4^7^6").
  Proof.
    (intros m m' salt W nd_i3 MU WM FW; ndestruct nd_i3 as (B1 & B2 & B3 & B4 & B5 & B6)).
    assert (DJ : forall A n, 0xf4000 <= A -> A + n <= 0x131000 -> disjoint_from W A n).
    { intros A n HA Hn. clear -FW HA Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|].
      pose proof (Forall_inv FW) as F1. cbn in F1. split; [lia| apply IH; exact (Forall_inv_tail FW)]. }
    unfold bj_statics_raw.
    repeat match goal with |- _ /\ _ => split end;
      (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply DJ; cbn; lia]).
  Qed.

  Lemma eh_pres_rw_cells : ltac2:(zQ "f0!nd!kj0!sf!hl3!sa!h9!iob!ik9!it4!uf!hp6!ko2!kod!jo7!kq5>2LB@1$3$d>2SP$5>1m$7>2m'$7>1A$5>2cs@1$3$a>0@1$c?1E>0@5$b?1E^7^6^5^4>0@4$6$8^6^4^3>0@4$e^9^8^5@1$2@1$1^4>0@2$4@2$0@2$9^6@1$2@1$1^5+hgths8@2$0+hgtjv0^6>0@2$4@2$0@2$9^7@1$2@1$1^6+hguri0@2$0+hguri7^7@4$6$8^9^8^7").
  Proof.
    intros LB SP m m' A cs RL HP [[Hwf HB] HW] HR D1 D2.
    assert (PW : forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None)).
    { intros a Ha. npose HB as (H0 & H1 & _). rewrite cells_bytes_length in H1 by exact Hwf.
      apply HP; [lia | eapply rclient_range_addr; [exact HR| lia] |].
      intros ES. destruct (RL a ES); lia. }
    split; [split; [exact Hwf|]|].
    - ndestruct HB as (H0 & H1 & HBB). split; [exact H0|]. split; [exact H1|]. intros i Hi.
      rewrite <- (HBB i Hi). unfold mrd. rewrite cells_bytes_length in Hi by exact Hwf.
      destruct (PW (A + Z.of_nat i) ltac:(lia)) as [-> _]. reflexivity.
    - ndestruct HW as (H0 & H1 & HWW). split; [exact H0|]. split; [exact H1|]. intros i Hi.
      destruct (PW (A + i) ltac:(lia)) as [_ Wv]. apply Wv. apply HWW. exact Hi.
  Qed.

  Lemma statics_raw_ehpres : ltac2:(zQ "90!jib!ik9!hl3!u9!h9!ko2!kod!jo7!hib>1m$1>2m'$1>4salt@1$8@1$3#k0>2LB@1$2$7>2SP$4>0@1$6?1E>0@2$0^6^4>0@5$5?1E^4^3^7^6@2$0^7^6").
  Proof.
    (intros m m' salt LB SP RL nd_i4 HP; ndestruct nd_i4 as (B1 & B2 & B3 & B4 & B5 & B6)).
    unfold bj_statics_raw.
    repeat match goal with |- _ /\ _ => split end;
      (eapply eh_pres_rw_cells; [exact RL | exact HP | eassumption |
         right; left; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; cbn [cells_size csize Nat.add Z.of_nat]; lia
       | cbn [cells_size csize Nat.add Z.of_nat]; lia | cbn [cells_size csize Nat.add Z.of_nat]; lia ]).
  Qed.

  Lemma idle_rheap : ltac2:(zQ "80!kr6!ik9!hl3!h9!ks1!kod!jo7!jp0>1m$1>2m'$1>2LB@1$2$6>2SP$3>0@1$5?1E>0@1$4?1E>0@2$0?1E^6>0@4$7^5^4^7^6@2$0?1E^7").
  Proof.
    intros m m' LB SP RL IFL ID HP. eapply IFL; [exact ID|].
    intros a Ha ES. destruct (HP a Ha) as [E0 _]; [|exact E0].
    right. left. destruct (RL a ES); unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia.
  Qed.

  Lemma idle_munch : ltac2:(zQ "h10!h9!jpe!u9!kr6!nd!hib!jq5!hl3!jqb!jr4!sa!jt1!kh7!khe!ks1!kod!ik9>1m$h0>2m'>0@1$5@1$2#k0@1$8@1$5@1$2#8>1W@1$7$c>0@1$f?1E>0@1$e?1E>0@2$3?1E^5>0@3$d^4^6^5>0@3$b@2$1$0$0\2iv@2$1$0$0@2$a@2$4+hjhgg0@3$6$0$0^1@2$4@3$9$0$0^1+vkgg0^5@2$3?1E^7").
  Proof.
    intros m m' W RL IFL ID MU FW. eapply IFL; [exact ID|].
    intros a Ha ES. unfold wa. apply MU. try rewrite unsigned_lit by lia.
    assert (R : 0xf4000 <= a < 0x131000) by (destruct (RL a ES); lia).
    clear -FW R. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    pose proof (Forall_inv FW) as F1. cbn in F1. split; [lia| apply IH; exact (Forall_inv_tail FW)].
  Qed.

  (* [comment removed for export] *)
  Lemma wview_of_eq : ltac2:(zQ "b0!u9!hib!lh1!jqb!s5!lh7!lhe!llb!ik9!it4!h9>1m$8>2m'$8>1a$a>0@3$4@1$3@1$1@1$0#8@1^2@1$2^1@1^3@1$2^1>0@1$6@3$4@1$3@1$1@1$0#8@3$7$9^4@1$2^2@1$5@1$1@1$0#8@1$6@3$4@1$3@1$1@1$0#8@3$7$9^4@1$2^3@1$5@1$1@1$0#8").
  Proof. intros m m' a EQ W. unfold wview in *. rewrite EQ. exact W. Qed.

  Lemma chain_eq_above : ltac2:(zQ "h00!u9!hib!jqb!lh1!lm4!hl3!rf!s5!h9!ln3!lnf!lp6!ik9!nd!o2!t8>1G@1$5$b>1m$c>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@1$a?1E>0@3$4?1E^4^3>0>1a$8>0@2$6@2$d@1$9^6^1@2$e^1@2$f+2+k0@3$7@1$2@1$1@1$0#8@1^5@1$3^2@1^6@1$3^2@3$4?1E^6^4").
  Proof.
    intros G m m' CFL CH EQ. eapply CFL; [exact CH| |].
    - intros a Ha _. apply EQ. exact Ha.
    - intros a Ha W. eapply wview_of_eq; [apply EQ; exact Ha| exact W].
  Qed.

  Lemma chain_munch : ltac2:(zQ "h00!h9!hl3!jpe!u9!ln3!lm4!nd!hib!jqb!jr4!jt1!kh7!khe!lnf!lp6!ik9>1G@1$1$e>1m$f>2m'>0@1$7@1$3#k0@1$8@1$7@1$3#8>1W@1$1$b>0@1$d?1E>0@3$5?1E^5^4>0@3$c^3^5^4>0@2$6Z@1$4^7>0@3$a@2$2$0$0\2iv@2$2$0$0@2$6@3$9$0$0^1@1$4^9^5@3$5?1E^9^7").
  Proof.
    intros G m m' W CFL CH MU POS FW. eapply chain_eq_above; [exact CFL| exact CH|].
    intros a Ha. unfold wa. apply MU. try rewrite unsigned_lit by lia.
    clear -FW Ha. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    pose proof (Forall_inv FW) as F1. cbn in F1. split; [lia| apply IH; exact (Forall_inv_tail FW)].
  Qed.

  Lemma chain_rheap : ltac2:(zQ "b0!hl3!lm4!ik9!nd!rf!h9!ln3!lnf!lp6!jo7!jp0>1G@1$0$8>1m$2>2m'$2>2LB@1$0$9>2SP$5>0@1$7?1E>0@3$1?1E^6^5>0@4$a^4^3^6^5>0@2$4@2$3Z^4@2$3^4@1$6^8@3$1?1E^9^7").
  Proof.
    intros G m m' LB SP CFL CH HP LE. eapply chain_eq_above; [exact CFL| exact CH|].
    intros a Ha. destruct (HP a ltac:(lia)) as [E0 _]; [left; lia| exact E0].
  Qed.

  (* [comment removed for export] *)
  Lemma chain_xpres : ltac2:(zQ "h90!h9!hl3!nd!rf!u9!ln3!lm4!ik9!hib!lh7!jqb!jpe!s5!lhe!llb!lh1!lte!lu9!lnf!lp6!lv2!jo7!it4!o2!t8>1G@1$1$h3>1m$7>2m'$7>2LB@1$1$h5>2SP$0>1X@1$1@2$b$0$0>0@1$h2?1E>0@3$6?1E^7^6>0@5$h1^5^4^3^7^6>0@2$3@2$2Z^5@2$2^5@1$5^9>0@3$h4?1E^a^5>0>1a$0>0@2$3@2$2@1$5^c^1@2$h7^1@2$h8+2+k0>0@2$h0^8^2@1$d@3$c@1$a@1$8@1$4#8@3$e$h6^c@1$f^3@1$9@1$8@1$4#8@3$6?1E^c^a").
  Proof.
    intros G m m' LB SP X CFL CH HP LE SC WX. eapply CFL; [exact CH| |].
    - (intros a Ha nd_i5; ndestruct nd_i5 as (f & Hf & Hr)). destruct (HP a ltac:(lia)) as [E0 _]; [| exact E0].
      split; [left; lia|]. exact (SC f a Hf Hr).
    - intros a Ha W.
      assert (DEC : rin_ivs X a \/ ~ rin_ivs X a).
      { clear. induction X as [|[lo hi] X IH]; cbn; [right; tauto|]. destruct (Z_le_dec lo a); destruct (Z_lt_dec a hi); tauto || (destruct IH; [left; right; assumption| right; intros [K|K]; [lia| tauto]]). }
      destruct DEC as [IN|OUT]; [apply WX; [exact Ha| exact IN]|].
      destruct (HP a ltac:(lia)) as [_ WM]; [split; [left; lia| exact OUT]|]. apply WM. exact W.
  Qed.

  (* [comment removed for export] *)
  Lemma saves_clear_cons : ltac2:(zQ "d0!h9!jpe!lp6!hl3!lv2!hpe!jq5!jt1!mg1!mgd!mh6!uf!nd>1f$2>1G@1$3$2>1X@1$3@2$1$0$0>0@3$4?1E^2^1>0@3$7@2$1$0$0\2iv@2$1$0$0@2$c@2$b@1$a^5@2$8?1E@1$9^5@3$6$0$0^1^2@3$4?1E@3$5$2^5^4^3").
  Proof.
    intros f G X SC FX f' a [<-|Hin] Hr.
    - pose proof (hh_slo_range H E HH (fr_fn f)) as SR0.
      clear SC. induction X as [|[lo hi] X IH]; cbn; [tauto|].
      pose proof (Forall_inv FX) as F1. cbn in F1. intros [K|K]; [lia| exact (IH (Forall_inv_tail FX) K)].
    - exact (SC f' a Hin Hr).
  Qed.


  (* [comment removed for export] *)
  Lemma xpres_fresh_block : ltac2:(zQ "h61!h9!jpe!mlb!u9!hib!hl3!mm3!nd!hpe!jqb!mnd!hqb!rf!mre!khe!ki7!lu9!ms7!ik9!it4!mt3!uf&>0@1$4@1$3#k0@1$9@1$4@1$3#8>1s$h4>2LB@1$5@2$1@2$1$2$0$0>2m0$h2>1p$2>1A$0>1n$0>4REST@1$5@2$1@2$1$2$0$0>2SP$0>1X@1$5@2$1$0$0>1m~0>2m'~0>1k$0>0@4$h1?1H^c@3$8@2$1@2$1$2$0$0@4$6@2$1$2$0$0@4$6$2$0^9^8^7^b^a>0>1b@2$1@2$1$2$0$0>0@3$a@2$1@2$1$2$0$0^1^8@3$a@2$1@2$1$2$0$0^2^e>0@3$e@3$8@2$1$0$0@4$6$0$0^a@2$h5^a^3@1$b@2$1$0$0^5^4>0@3$f$h3^6^5>0@2$c@2$7Z^5@2$7^5^b>0@2$7@1$d?5HCEIL^a@5$h0^c^b^a^9^8").
  Proof.
    intros s LB m0 p A n REST SP X m m' k HP SUB MU WM HK HS a Ha [HC _].
    pose proof (hh_blocks H E HH _ _ _ (p, A, n) HP (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5). cbn in R1, R2, R3, R4, R5. hcb.
    assert (OUT : outside [(A, A + k)] a).
    { cbn. split; [| exact I].
      destruct HC as [H1|[[H1 H2]|(b & Hb & Hr)]]; [lia| lia|].
      pose proof (hh_nodup H E HH _ _ _ HP) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [NI _].
      assert (NE : blk_id (p, A, n) <> blk_id b).
      { cbn. intros EQ. apply NI. apply in_map_iff. exists b. split; [symmetry; exact EQ| apply SUB; exact Hb]. }
      destruct (hh_disj H E HH _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror (SUB _ Hb)) NE) as [D|D]; cbn in D; lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.


  (* [comment removed for export] *)
  Lemma xpres_of_munch_blk : ltac2:(zQ "hc1!h9!jpe!mlb!nd!hl3!u9!hib!jq5!jr4!rf!jqb!mm3!sa!mre!mnd!hpe!jt1!kh7!khe!ki7!lte!lu9!ms7!ik9!it4!mt3!uf!o2&>0@1$6@1$5#k0@1$a@1$6@1$5#8>1s$h9>2LB@1$4@2$1@2$1$2$0$0>2m0$h7>1p$2>1A$0>1n$0>4REST@1$4@2$1@2$1$2$0$0>2SP$0>1X@1$4@2$1$0$0>1W@1$4$h1>1m~0>2m'~0>0@4$h6?1H^c@3$f@2$1@2$1$2$0$0@4$b@2$1$2$0$0@4$b$2$0^9^8^7^b^a>0>1b@2$1@2$1$2$0$0>0@3$e@2$1@2$1$2$0$0^1^8@3$e@2$1@2$1$2$0$0^2^e>0@3$h2^5^4^3>0@3$h3$h8^5^4>0@2$3@1$d?5HCEIL^9>0@3$h0@2$1$0$0\2iv@2$1$0$0@2$c@2$9@2$3@1$d?5HCEIL@3$7$0$0^1@2$3@3$8$0$0^1^b@2$c>1a$0>0@2$9@2$3@3$7$0$0^2^1@2$hb^1@3$8$0$0^2@2$h4^c^2@2$9@2$3^e@3$7$0$0^1@2$3@3$8$0$0^1@2$ha^e^d^8@5$h5^c^b^a^8^7").
  Proof.
    intros s LB m0 p A n REST SP X W m m' HP SUB MU WM HS FW a Ha [HC HX].
    pose proof (hh_blocks H E HH _ _ _ (p, A, n) HP (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5). cbn in R1, R2, R3, R4, R5. hcb.
    assert (HBL : forall b, In b LB -> blk_addr b + blk_size b <= hceil).
    { intros b Hb. eapply (hh_blocks_below H E HH); [exact HP| right; exact Hb]. }
    assert (NB : forall b, In b REST -> blk_addr b <= a < blk_addr b + blk_size b -> ~ (A <= a < A + n)).
    { intros b Hb Hr.
      pose proof (hh_nodup H E HH _ _ _ HP) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [NI _].
      assert (NE : blk_id (p, A, n) <> blk_id b).
      { cbn. intros EQ. apply NI. apply in_map_iff. exists b. split; [symmetry; exact EQ| apply SUB; exact Hb]. }
      destruct (hh_disj H E HH _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror (SUB _ Hb)) NE) as [D|D]; cbn in D; lia. }
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[H1|[H1 H2]]].
      - destruct HC as [Hc|[[Hc _]|(b & Hb & Hr)]]; [lia| hcb; lia|]. pose proof (HBL b (SUB b Hb)). lia.
      - intros R. apply HX. apply H1. exact R.
      - destruct HC as [Hc|[[Hc Hc2]|(b & Hb & Hr)]]; [lia| hcb; lia|]. pose proof (NB b Hb Hr). lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma stk_frame : ltac2:(zQ "d0!h9!u9!it4!hib!hl3!jqb!s5!hp6!kj0!mtd!iob!uf!sf>1m>0@1$3@1$1#k0@1$5@1$3@1$1#8>1A$0>2cs@1$4$7>1n$0>0@4$a$2^4^3^2>0@3$6$0@1$c@1$8^3^2@4$9$2^6^5@2$b^5^3").
  Proof. intros m A cs n R <-. apply stk_of_rw_cells. exact R. Qed.

  (* [comment removed for export] *)
  Lemma xpres_of_ehpres : ltac2:(zQ "c0!h9!jo7!hl3!lte!ik9!mnd!jpe!lu9!mu4!ko2!kod!nd>2LB@1$2$1>3LB'@1$2$1>2SP$0>3SP'$0>1X@1$2@2$6$0$0>1m$4>2m'$4>0@1$a?1E>0@5$9?1E^8^6^3^2>0@2$b^7^6>0>1b$1>0@3$5$1^1^a@3$5$1^2^c>0>1a$0>0@2$3$8^1@2$3^9^2@5$7^b^9^8^7^6").
  Proof.
    intros LB LB' SP SP' X m m' RL HP LE SUB HX a Ha [HC HXa]. apply HP; [exact Ha| |].
    - destruct HC as [H1|[H1|(b & Hb & Hr)]]; [left; lia| right; left; exact H1| right; right].
      exists b. split; [apply SUB; exact Hb| exact Hr].
    - intros ES. apply HXa. apply HX. destruct (RL a ES); unfold EH_IVS; cbn [rin_ivs app fst snd]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exc_live_rheap : ltac2:(zQ "a0!jo7!hl3!mue!ik9!mnd!u9!h9!lp6!jp0!hib>1G@1$1$7>3tok@1$9@1$5#k0>3LBX@1$1$0>2LB@1$1$0>2SP$6>1m$3>2m'$3>0@5$2?1E^7^6^5^2>0@4$8^5^4^3^2>0>1b$0>0@3$4$0^1^8@3$4$0^2^8@5$2?1E^a^9^8^4").
  Proof.
    intros G tok LBX LB SP m m' EX HP SUB. eapply (hh_exc_frame H E HH); [exact EX|].
    intros a Ha [ES|IB].
    - destruct (HP a Ha) as [E0 _]; [|exact E0]. right. left.
      destruct (hh_static_range H E HH a ES); unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK; lia.
    - destruct (HP a Ha) as [E0 _]; [|exact E0]. right. right.
      ndestruct IB as (b & Hb & Hr). exists b. split; [apply SUB; exact Hb| exact Hr].
  Qed.

  (* [comment removed for export] *)

End W.
End HCW.
(* [comment removed for export] *)
