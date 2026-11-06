(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJArithU BJRep BJHeap BJIface BJIfaceObj BJKitVS BJKitW BJKitDtor BJKitObj BJHeapFloor
     W_dtor_value W_dtor_value2 W_dtor_helpers W_octor W_digest W_octorL.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44list3h5LinuxProcessSemanticsfLinuxProcessSem3Runm36config3h5LinuxProcessSemanticsfLinuxProcessSem5Statep85Model3h5LinuxProcessSemantics5Riscv7Preludese5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~vc5blockvc3mem37Corelib4Init5Logichl52exhl53andk46optionm39cfg_model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hob6PStatek44Nonehl52eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshtedmachine_statem36cfg_ms79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU7BJIface~~~~~~iifh0bj_env_post_core79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~io23mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~is52MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jg87seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~jl27hs_KRELjl28hs_MPRESjl28hs_RHEAPvcarheap_pres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~js65rsegshf7Z_to_bvhfbbv_unsigned46Stdlib6ZArith6BinInt1Zki43add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU5BJRep~~~~~~kk37jheightki42lek43app37Corelib4Init5Peanokp62lem35mkCfgiifbRDTOR_STACKiifbbj_env_corekk38blocks_vkk32jvkk36val_at89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU9L_octorLD3HCW~~~~~~kv2cdestroy_post69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lk65hceiljl25hs_SRvcdrclient_rangeki42ltki43powjl23hmfjl23ehkjl2cheap_mf_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUbBJHeapFloor~~~~~~lseaheap_floor" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!lr0$0").
  Variable E : ltac2:(zQ "10!lr7$0").
  Hypothesis HH : ltac2:(zQ "10!lre@3$0?5HCEIL?1H?1E").
  Hypothesis HFL : ltac2:(zQ "10!mh0@1$0?1H").

  (* [comment removed for export] *)
  Let DSTR := dtor_str_spec H E HH.
  Let DARR := dtor_arr_spec H E HH HFL.
  Let DOBJ := dtor_obj_spec H E HH HFL.

  Definition destroy_post : ltac2:(zQ "90!h9!jc!k1!lc!of!s6!v4!hk7!hkf>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>4REST@1$3$7>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "hd1!h9!jc!hm9!hmf!hn6!k1!hnf!hs7!ht1!lc!ht8!ih5!ii6!of!s6!v4!imd!ire!jg2!jk7!jp6!jq1!jqd!hk7!hkf!jr9!kg3!kgc!kh6&>0@1$1@1$0#k0@1$4@1$1@1$0#8\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$f@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\4REST@1$9$h7\2lo$5\1B$5\1m$h8\2mo$e\1c$d@2$2@1$1@1$0#k0\2ra@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$7\2s'$7@2$3@3$a$b@1$c^h3@7$h2@hf$h1^h2^i9^i8^i7^h1^h0^f^i6^i5^e^d^c^b^a^9^8^7^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^6^5^4^3^ha@2$hb@1$0#k0+krpi0^h9@1$8@1$1@1$0#k0^2@1$h3$ha@2$3@3$h4?1H^1@1$6^h3@2$3@3$h5?1H^h4@1$6^h3@2$3@4$h6?1H^1^h8^2@2$3@6$h0?1H^2^i9^i7^h7^h6@4$h9^h8@2$hc@1$0#k0^i9^h5^2").

  Lemma ol_destroy : ltac2:(zQ "i30!h9!jc!kh6!kjc!k1!knf!hk7!koa!ht1!kp0!lc!kqa!kr0!s6!v4!kr8!ks7!kt6!ku2!ku8!lj6!lo1!ire!jg2!jk7!jp6!jqd!loa!hkf!lp3!kg3!hs7!lq3!lq9!kgc>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$e@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$hc>1s$hf>4REST@1$a$6>1v$h2>2lo$4>1B$4>4errv@1$1@1$0#k0>2mo$d>0@4$ha?1H^7@3$9$6@1$h1^5^6^8>0@3$h9?1H^8^2>0@a$h0?5HCEIL?1H^a^ia^i8^6^5@1$f@1$5^7^4^b>0@4$h3?5HCEIL^b@2$2@1$0#k0^h8^8>0@2$b@1$5^9Ni0>0@4$hd^b@2$2@1$0#k0^id@2$2@1$0#k0^ha+h8>0@2$7@2$3@2$2@1$0#k0^hb+h8@1$h5?5HCEIL>0@2$7@2$3@2$2@1$0#k0^if+h0^a>0@2$i0@2$3@2$2@1$0#k0^j0+h0@2$i1+2+k0@3$hb?1H@h6$h4^j1^j0^if^ib^ia^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h3^h2^f^d^c^h1^a@2$c@7$h7@hf$h6^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3@2$i2@1$0#k0+kron4^h2@1$8@1$1@1$0#k0^h1@1$h8$he^a").
  Proof.
    intros until mo. intros HP KR ENV VA H32 RC SJH SPB16 SP64.
    npose ENV as (AUX & SPB & ST & CEIL & LO & ERR & MI & TP & BS).
    pose proof (bv_unsigned_in_range _ s5) as RS5. unfold bv_modulus in RS5; cbn in RS5.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP; cbn in RSP. hcb.
    set (Sj := bv_unsigned s5) in *.
    assert (ES5 : s5 = Z_to_bv 64 Sj) by (subst Sj; symmetry; apply Z_to_bv_bv_unsigned).
    ndestruct VA as (hb & LEN & RB & VH & VD).
    (* [comment removed for export] *)
    pose proof (rclient_range_loc H E HH _ _ _ _ _ _ HP (rclient_range_LB_mono _ _ _ _ _ RC ltac:(intros b Hb; apply in_or_app; right; exact Hb)) ltac:(lia)) as LOC.
    assert (SJ0 : 0 < Sj).
    { pose proof LO as LOq. unfold RDTOR_STACK, ROPDEL_STACK, RFREE_STACK in LOq. destruct RC as [R1|[R1|(b & Hb & R1 & R2)]]; [lia| lia|].
      pose proof (hh_blocks H E HH _ _ _ b HP ltac:(apply in_or_app; right; exact Hb)) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    (* [comment removed for export] *)
    assert (RET : forall (pc : Z) (c : config),
      (pc = 0x4b914 \/ pc = 0x4b95c) ->
      dtor_value_post H (Z_to_bv 64 pc) sp gp tp s0 (s1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc REST lo B m mo c ->
      hs_SR H (destroy_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc REST lo B m mo) c).
    { (intros pc [ms' mo'] PC nd_i1; ndestruct nd_i1 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & s' & EMS & KR' & MP' & HP' & ENV' & PRES')).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'. subst ms'.
      replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc) by (symmetry; apply ret_pc_even; [destruct PC; subst pc; cbn; lia| destruct PC; subst pc; reflexivity]).
      ndestruct ENV' as (AUX' & ST' & ERR' & MI' & BS').
      assert (RB' : rw_cells rsegs m' Sj [CB 24 hb]) by (eapply rheap_pres_rw_cells; [exact PRES'| exact RB| exact RC]).
      destruct (vhdr_word0 _ _ VH LEN) as (hr & EHB & LHR).
      assert (RB0 : rw_cells rsegs m' Sj (C8 (wz 0) :: [CB 16 hr])).
      { apply rw_cells_of_CB with (n := 24%nat); [| cbn; repeat split; auto; exact I| cbn; reflexivity]. rewrite EHB in RB'. cbn [cells_bytes cbytes app]. rewrite ?app_nil_r. exact RB'. }
      eapply (hh_evt H E HH); [exact KR'| eapply (oL_U2_ret pc); [exact MI'| exact PC| exact ES5| exact SJ0| subst Sj; lia| exact RB0]|].
      (intros ms2 nd_i2; ndestruct nd_i2 as (xa0 & xa1 & ->)). unfold destroy_post. cbn [cfg_ms cfg_model].
      neexists 18. split; [reflexivity|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact HP'|].
      split; [split; [exact AUX'| split; [exact ST'| split; [exact ERR'| split; [exact MI'| exact BS']]]]| exact PRES']. }
    destruct v as [k| n| [[p T'] sz] n| t cap es| t cap ss].
    - (* [comment removed for export] *)
      cbn [vhdr] in VH. ndestruct VH as (K04 & junk7 & pay & L7 & L8 & EHB).
      assert (RBs : rw_cells rsegs m Sj [C8 (wz 0); C1 (b8 k); CB 7 junk7; CB 8 pay]).
      { apply rw_cells_of_CB with (n := 24%nat); [rewrite <- EHB; exact RB| cbn; repeat split; auto; exact I| cbn; reflexivity]. }
      eapply (hh_evt H E HH); [exact KR| eapply oL_U2_sca; [exact MI| exact ES5| exact SJ0| subst Sj; lia| exact RBs| exact K04]|].
      (intros ms2 nd_i3; ndestruct nd_i3 as (xa0 & xa1 & ->)). unfold destroy_post. cbn [cfg_ms cfg_model blocks_v app] in HP |- *.
      neexists 18. split; [reflexivity|]. split; [exact KR|]. split; [apply (hh_mpres_refl H E HH)|]. split; [exact HP|].
      split; [split; [exact AUX| split; [exact ST| split; [exists errv; exact ERR| split; [exact MI| exact BS]]]]| apply rheap_pres_refl].
    - (* [comment removed for export] *)
      cbn [vhdr] in VH. ndestruct VH as (N14 & bs & L14 & EHB).
      assert (RBs : rw_cells rsegs m Sj [C8 (wz 0); C1 (b8 KIND_SSTR); CB 15 (bs ++ [b8 (14 - n)])]).
      { apply rw_cells_of_CB with (n := 24%nat); [| cbn; rewrite length_app, L14; cbn; repeat split; auto; exact I| cbn; reflexivity].
        rewrite EHB in RB. cbn [cells_bytes cbytes app] in RB |- *. rewrite ?app_nil_r, <- ?app_assoc in RB. rewrite ?app_nil_r, <- ?app_assoc. exact RB. }
      eapply (hh_evt_then H E HH); [exact KR| eapply oL_U2_str; [exact MI| exact ES5| exact SJ0| subst Sj; lia| exact RBs| right; reflexivity]|].
      intros ms2 (xa1 & ->).
      eapply (hh_mono H E HH).
      { eapply (DSTR _ sp gp tp) with (v := Jsstr n) (REST := REST); [exact I| exact HP| exact KR| exact ENV| rewrite unsigned_lit by lia; exists hb; split; [exact LEN| split; [exact RB| split; [cbn; split; [exact N14| exists bs; split; [exact L14| exact EHB]]| exact VD]]]| cbn; lia| rewrite unsigned_lit by lia; exact RC| exact SPB16| exact SP64]. }
      (intros [ms' mo'] nd_i4; ndestruct nd_i4 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & s' & EMS & KR' & MP' & HP' & ENV' & PRES')).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'. subst ms'. unfold destroy_post. cbn [cfg_ms cfg_model].
      replace (ret_pc (Z_to_bv 64 0x4b920)) with (Z_to_bv 64 0x4b920) by (symmetry; apply ret_pc_even; [cbn; lia| reflexivity]).
      neexists 18. split; [reflexivity|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact HP'|]. split; [exact ENV'| exact PRES'].
    - (* [comment removed for export] *)
      cbn [vhdr] in VH. ndestruct VH as (junk7 & L7 & EHB).
      assert (RBs : rw_cells rsegs m Sj [C8 (wz 0); C1 (b8 KIND_STRING); CB 15 (junk7 ++ le8 (wz T'))]).
      { apply rw_cells_of_CB with (n := 24%nat); [| cbn; rewrite length_app, L7, length_le8; cbn; repeat split; auto; exact I| cbn; reflexivity].
        rewrite EHB in RB. unfold val_hdr in RB. cbn [cells_bytes cbytes app] in RB |- *. rewrite ?app_nil_r, <- ?app_assoc in RB. rewrite ?app_nil_r, <- ?app_assoc. exact RB. }
      eapply (hh_evt_then H E HH); [exact KR| eapply oL_U2_str; [exact MI| exact ES5| exact SJ0| subst Sj; lia| exact RBs| left; reflexivity]|].
      intros ms2 (xa1 & ->).
      eapply (hh_mono H E HH).
      { eapply (DSTR _ sp gp tp) with (v := Jlstr (p, T', sz) n) (REST := REST); [exact I| exact HP| exact KR| exact ENV| rewrite unsigned_lit by lia; exists hb; split; [exact LEN| split; [exact RB| split; [cbn; exists junk7; split; [exact L7| exact EHB]| exact VD]]]| cbn; lia| rewrite unsigned_lit by lia; exact RC| exact SPB16| exact SP64]. }
      (intros [ms' mo'] nd_i5; ndestruct nd_i5 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m' & s' & EMS & KR' & MP' & HP' & ENV' & PRES')).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'. subst ms'. unfold destroy_post. cbn [cfg_ms cfg_model].
      replace (ret_pc (Z_to_bv 64 0x4b920)) with (Z_to_bv 64 0x4b920) by (symmetry; apply ret_pc_even; [cbn; lia| reflexivity]).
      neexists 18. split; [reflexivity|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact HP'|]. split; [exact ENV'| exact PRES'].
    - (* [comment removed for export] *)
      assert (HB6 : exists r15, length r15 = 15%nat /\ hb = cells_bytes [C8 (wz 0); C1 (b8 KIND_ARRAY); CB 15 r15]).
      { cbn [vhdr] in VH. destruct t as [[[p T'] sz]|].
        - ndestruct VH as (junk7 & L7 & ->). exists (junk7 ++ le8 (wz T')). split; [rewrite length_app, L7, length_le8; reflexivity|]. unfold val_hdr. cbn [cells_bytes cbytes app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
        - ndestruct VH as (C0 & E0 & junk7 & L7 & ->). exists (junk7 ++ le8 (wz BJ_ARR_EMPTY)). split; [rewrite length_app, L7, length_le8; reflexivity|]. unfold val_hdr. cbn [cells_bytes cbytes app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      ndestruct HB6 as (r15 & L15 & EHB).
      assert (RBs : rw_cells rsegs m Sj [C8 (wz 0); C1 (b8 KIND_ARRAY); CB 15 r15]).
      { apply rw_cells_of_CB with (n := 24%nat); [rewrite <- EHB; exact RB| cbn; repeat split; auto; exact I| cbn; reflexivity]. }
      eapply (hh_evt_then H E HH); [exact KR| eapply oL_U2_arr; [exact MI| exact ES5| exact SJ0| subst Sj; lia| exact RBs]|].
      intros ms2 (xa1 & ->).
      eapply (hh_seq H E HH).
      { eapply (DARR _ sp gp tp) with (v := Jarr t cap es) (REST := REST); [exact I| exact HP| exact KR| exact ENV| rewrite unsigned_lit by lia; exists hb; split; [exact LEN| split; [exact RB| split; [exact VH| exact VD]]]| lia| rewrite unsigned_lit by lia; exact RC| exact SPB16| exact SP64]. }
      intros c' PD. eapply RET; [right; reflexivity| exact PD].
    - (* [comment removed for export] *)
      destruct t as [[[p T'] sz]|].
      + (* [comment removed for export] *)
        cbn [vhdr] in VH. ndestruct VH as (junk7 & L7 & EHB).
        assert (RBs : rw_cells rsegs m Sj (val_hdr KIND_OBJECT junk7 (wz T'))).
        { apply rw_cells_of_CB with (n := 24%nat); [rewrite <- EHB; exact RB| cbn; repeat split; auto; exact I| cbn; reflexivity]. }
        pose proof VD as VD'. cbn [vdeep] in VD'. ndestruct VD' as (tsalt & sbs & junk & jbk & SZ & NES & CAP & TR & TB & _ & _ & _).
        eapply (hh_evt_then H E HH); [exact KR| eapply oL_U2_objS; [exact MI| exact ES5| exact SJ0| subst Sj; lia| exact RBs| exact TB| exact TR| lia| lia]|].
        (intros ms2 nd_i6; ndestruct nd_i6 as (xa1 & xa2 & ->)).
        eapply (hh_seq H E HH).
        { eapply (DOBJ _ sp gp tp) with (v := Jobj (Some (p, T', sz)) cap ss) (REST := REST); [exact I| exact HP| exact KR| exact ENV| rewrite unsigned_lit by lia; exists hb; split; [exact LEN| split; [exact RB| split; [cbn; exists junk7; split; [exact L7| exact EHB]| exact VD]]]| cbn [jheight] in H32 |- *; lia| rewrite unsigned_lit by lia; exact RC| exact SPB16| exact SP64]. }
        intros c' PD. eapply RET; [left; reflexivity| exact PD].
      + (* [comment removed for export] *)
        cbn [vhdr] in VH. ndestruct VH as (C0 & SS0 & junk7 & L7 & EHB).
        assert (RBs : rw_cells rsegs m Sj (val_hdr KIND_OBJECT junk7 (wz BJ_OBJ_EMPTY))).
        { apply rw_cells_of_CB with (n := 24%nat); [rewrite <- EHB; exact RB| cbn; repeat split; auto; exact I| cbn; reflexivity]. }
        destruct (bj_statics_raw_of m BS) as [salt BSR].
        eapply (hh_evt H E HH); [exact KR| eapply oL_U2_obj0; [exact MI| exact BSR| exact ES5| exact SJ0| subst Sj; lia| exact RBs]|].
        (intros ms2 nd_i7; ndestruct nd_i7 as (xa0 & xa1 & xa2 & ->)). unfold destroy_post. subst ss. cbn [cfg_ms cfg_model blocks_v blocks_kvs app] in HP |- *.
        neexists 18. split; [reflexivity|]. split; [exact KR|]. split; [apply (hh_mpres_refl H E HH)|]. split; [exact HP|].
        split; [split; [exact AUX| split; [exact ST| split; [exists errv; exact ERR| split; [exact MI| exact BS]]]]| apply rheap_pres_refl].
  Qed.
End HCW.
