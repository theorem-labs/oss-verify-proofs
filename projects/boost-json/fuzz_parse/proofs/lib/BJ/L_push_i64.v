(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJEhTabs BJKitVS BJKitW W_maybe_grow W_push_i64.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhfbbv_unsigned46Stdlib6ZArith6BinInt1Zkf2lekf3add37Corelib4Init9Datatypesn24cons37Corelib4Init5Logicp12eqp12or01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~r25frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~vc4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hjf5blockp13and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~hp85rsegsn24Nonen24listn23nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ5BJRep~~~~~~hv17vs_tempvc2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ijc8rw_cellskf2ltkf3pown23appn26optionp13not3h5LinuxProcessSemanticsfLinuxProcessSem3Runiq36configiq35mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Stateiu25Model3h5LinuxProcessSemantics5Riscv7Preludejh95bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJIface~~~~~~jk8cRVS_PUSH_I64jk8eRVS_PUSH_STACKjk86bj_envjk88chain_atjk8emaybe_grow_unwjk8dpush_sca_posthv19blocks_vshv15vs_athv16vs_bufhv18vs_charshv14vs_nhv16vstackr23csrr27fr_liver27hs_KRELr28hs_RHEAPr25hs_SRr25mkCSR69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~kl35hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kp73mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~kta2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~lhd7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~lm72wzhjf3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~lqf6PStatehf7Z_to_bvjk8dpush_i64_stmtr23hmfr23ehkr2cheap_mf_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8BJEhTabs~~~~~~mib9bj_ehtabs" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!mh0$0").
  Variable E : ltac2:(zQ "10!mh6$0").
  Hypothesis HH : ltac2:(zQ "10!mhc@3$0?5HCEIL?1H?1E").
  Hypothesis TABS : ltac2:(zQ "10!mm9@1$0?1E").

  Lemma push_i64_stmt_some : ltac2:(zQ "j70!h9!jc!k1!m7!mc!oa!q5!qa!qf!v4!hj8!ho9!hp2!ht4!htd!hu4!hub!iic!ij7!in7!io3!io8!ioe!ip4!ipd!isf!it9!jh0!jjf!jo5!jp5!jq7!jr1!jrd!jsf!ju0!jud!jv6!kg0!kgc!kh4!khe!ki4!kie!kj8!kk3!kkb!koe!kt3!lh7!llc!lq2!lq8!lub!lv5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hc@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j4>1s$j5>4REST@1$f$b>2st$i8>2lo$8>1B$8>4errv@1$1@1$0#k0>2mo$hb>1g$9>1G@1$f$9>7payload@1$1@1$0#k0>0@1$h8@3$6@1$h7$b@1$i5^8@1$e$b>0@4$ic?1H^b@3$h6$b@1$i3^9^a^c>0@3$ib?1H^c^6>0@b$hf?5HCEIL?1H?1E^e^ie^ic^a^9@1$he?1E^8^f>0@4$i4?5HCEIL^f@2$2@1$0#k0^i7^c>0@3$6$8@1$i6^dZ>0@2$h4@2$4@1$i7^e+1@2$h5+2+ha>0@2$c@2$3@2$2@1$0#k0^j2@2$2@1$0#k0^ia@2$3@2$4@2$2@1$0#k0^ia+k0^d>0@2$c@2$3@1$if?5HCEIL@1$h1^h0@2$h4@1$h1^h0@2$h5+2+k0>0@4$h3$d^h4@2$2@1$0#k0^ib@3$5$a@1$h2^a@1$h0$a>0@2$3@2$2@1$0#k0^j5@2$2@1$0#k0^ic>0@2$7@2$3@2$4@2$2@1$0#k0^id+8@2$2@1$0#k0^ie@2$3@2$4@2$2@1$0#k0^ie+k0@2$2@1$0#k0^id>0@4$h3$d^h7@2$2@1$0#k0^id@3$5$a@1$h2@2$j6@1$0#k0Z@1$h0$a>0@2$7@3$6$8@2$2@1$0#k0^ie@2$4@2$2@1$0#k0^j0+j8@2$c@2$3@2$2@1$0#k0^j8@2$2@1$0#k0^ie@2$7@2$3@2$4@2$2@1$0#k0^ie+8@2$2@1$0#k0^j0@2$3@2$4@2$2@1$0#k0^j0+k0@2$2@1$0#k0^ie>0@5$i0?1E@3$5$9^h1^h0^h9^j9^ja>0@3$6$i9@1$ia^h2@d$ie^ja^j4^j3^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1@3$id?1H\1c$h9@2$7@he$i2?5HCEIL?1H?1E^jd^jc^jb^ja^j6^j5^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^he^hd^ha@2$2@1$0#k0^j4^h9+2^h8^h7^hc^h5^1@e$i1?5HCEIL?1H?1E^jc@3$5$9^h4^h3^ha@2$2@1$0#k0^j4^h9^h8^h7^hd^hc^h5^1@2$ha@7$j1@hf$j0^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd@1$j3$hd^hc@1$e@1$1@1$0#k0^hb@1$j2$d^h4").
  Proof.
    intros until G. intros payload SOME HP KR ENV VS CH0 NB [ABOVE A0B] TEMP PAY PAYSP PAYLOC SPW SPWLOC CH LIVE.
    destruct st as [buf cap items chars temp]. destruct buf as [[[p Bb] sz]|]; [| exfalso; apply SOME; reflexivity].
    cbv [vs_chars vs_temp vs_n vs_items blocks_vs vs_buf] in CH0, NB, TEMP, HP |- *. subst chars.
    destruct (vs_at_some_elim _ _ _ _ _ _ _ _ _ VS) as (SZ & _ & (junk7 & HDR) & CAP16 & NLE & CAP32 & BR & BT & ITEMS & _ & (junk & JK)).
    subst sz. clear VS.
    apply items_at_raw in ITEMS. ndestruct ITEMS as (bs & LEN & RB & IH & ID).
    pose proof ENV as ENV'. ndestruct ENV' as (AUX & SPB & ST & CEIL & LO & _).
    pose proof (hh_eh_stack H E HH) as EHS. unfold RVS_PUSH_STACK, ROPNEW_STACK, RMALLOC_STACK in LO.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0. hcb.
    npose BR as (Q1 & Q2 & Q3 & Q4 & Q5).
    set (n := Z.of_nat (length items)) in *.
    assert (BUF : rw_cells rsegs m Bb [CB (Z.to_nat (24 * n)) bs; CB (Z.to_nat (24 * (cap - n))) junk]).
    { apply (proj2 (rw_cells_app _ _ _ [CB (Z.to_nat (24 * n)) bs] _)). cbn [cells_size csize Nat.add].
      replace (Z.to_nat (24 * n) + 0)%nat with (24 * length items)%nat by lia.
      split. { replace (Z.to_nat (24 * n)) with (24 * length items)%nat by lia. exact RB. }
      replace (Bb + Z.of_nat (24 * length items)) with (Bb + 24 * n) by lia. exact JK. }
    assert (BB : forall b, In b (blocks_items items ++ REST) -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (hh_blocks H E HH); [exact HP| right; exact Hb]. }
    eapply (hh_mono H E HH).
    { eapply (push_i64_raw H E HH TABS
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s (blocks_items items ++ REST)
                temp Bb n cap 0 junk7 bs junk payload p lo B errv mo g G);
        [exact HP| exact KR| exact ENV| unfold vs_hdr_raw; unfold wz in HDR; exact HDR| exact BUF| exact BR| lia| lia| lia| lia| exact TEMP| exact ABOVE| lia
        | exact PAY| exact PAYSP| exact PAYLOC| exact SPW| exact SPWLOC| exact CH| exact LIVE]. }
    intros [ms' mo'] [OK|UNW].
    - left. ndestruct OK as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & s' & B' & cap' & p' & junk' & j7'
                         & EMS & KR' & MP' & HP' & HDR' & ITEMS' & SLOT' & JK' & BR' & LT & C16 & CAPM & SAME & ENVP & XP).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'.
      unfold push_sca_post. nexists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
      exists (mkVS (Some (p', B', 24 * cap')) cap' (items ++ [VSval (Jsca 2)]) 0 temp), F.
      cbv [vs_buf vs_cap vs_items vs_chars vs_temp vs_n blocks_vs].
      split; [exact EMS|]. split; [exact KR'|]. split; [exact MP'|].
      split. { rewrite blocks_items_app. cbn [blocks_items blocks_item blocks_v]. rewrite app_nil_r. exact HP'. }
      npose BR' as (R1 & R2 & R3 & R4 & R5).
      split.
      { destruct (sca_hdr_of_cells8 _ _ _ _ _ SLOT' ltac:(lia)) as (hb & HB & VH).
        eapply vs_at_some_intro with (junk7 := junk7) (junk := junk'); rewrite ?length_app; cbn [length]; try lia.
        - unfold vs_hdr_raw in HDR'. unfold wz. replace (Z.of_nat (length items + 1)) with (n + 1) by lia. exact HDR'.
        - exact BR'.
        - eapply (items_at_snoc m' B' items bs (VSval (Jsca 2)) hb).
          + replace (24 * length items)%nat with (Z.to_nat (24 * n)) by lia. exact ITEMS'.
          + exact IH.
          + eapply (ideeps_xpres (blocks_items items ++ REST) (bv_unsigned sp) (vs_X (bv_unsigned a0)) m m');
              [exact XP| | exact BB| exact ID| intros b Hb; apply in_or_app; left; exact Hb].
            unfold X_above_hceil, vs_X. constructor; [|constructor]. cbn [fst snd]. left. lia.
          + fold n. exact HB.
          + cbn [item_hdr]. exact VH.
          + cbn. exact I.
        - replace (Z.of_nat (length items + 1)) with (n + 1) by lia.
          replace (24 * (cap' - (n + 1))) with (24 * (cap' - n - 1)) by lia. exact JK'. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact ENVP|].
      eapply xpres_weaken; [exact XP| lia| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
    - right. ndestruct UNW as (s' & X & MP' & HDR' & BUF' & BS' & _ & XP). cbn [cfg_ms cfg_model] in X, MP'.
      unfold maybe_grow_unw. exists s'. cbv [blocks_vs vs_buf vs_items].
      split; [exact X|]. split; [exact MP'|].
      apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat (24 * n)) bs] _)) in BUF'. cbn [cells_size csize Nat.add] in BUF'.
      destruct BUF' as [RB' JK'].
      split.
      { eapply vs_at_some_intro with (junk7 := junk7) (junk := junk); try lia.
        - unfold vs_hdr_raw in HDR'. unfold wz. fold n. exact HDR'.
        - exact BR.
        - eapply (items_at_relocate (blocks_items items ++ REST) (bv_unsigned sp) (vs_X (bv_unsigned a0) ++ EH_IVS) m _ Bb Bb items bs);
            [exact RB| exact IH| exact ID| | exact XP| | exact BB| intros b Hb; apply in_or_app; left; exact Hb].
          + replace (24 * length items)%nat with (Z.to_nat (24 * n)) by lia. exact RB'.
          + unfold X_above_hceil, vs_X, EH_IVS. constructor; [cbn [fst snd]; left; lia|]. constructor; [cbn [fst snd]; right; lia|].
            constructor; [cbn [fst snd]; right; lia| constructor].
        - fold n. replace (Z.to_nat (24 * n) + 0)%nat with (Z.to_nat (24 * n)) in JK' by lia.
          rewrite Z2Nat.id in JK' by lia. exact JK'. }
      split; [exact BS'|].
      eapply xpres_weaken; [exact XP| lia| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma push_i64_stmt_none : ltac2:(zQ "j60!h9!jc!k1!m7!mc!oa!q5!qa!qf!v4!hj8!ho9!hp2!ht4!htd!hu4!hub!iic!ij7!in7!io3!io8!ioe!ip4!isf!it9!jh0!jjf!jo5!jp5!jq7!jr1!jrd!jsf!ju0!jud!jv6!kg0!kgc!kh4!khe!ki4!kie!kj8!kk3!kkb!koe!kt3!lh7!llc!lq2!lq8!lub!lv5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hb@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j3>1s$j4>4REST@1$f$b>2st$i7>2lo$8>1B$8>4errv@1$1@1$0#k0>2mo$ha>1g$9>1G@1$f$9>7payload@1$1@1$0#k0>0@3$6@1$h7$b@1$i4^8@1$e$b>0@4$ib?1H^b@3$h6$b@1$i2^9^a^c>0@3$ia?1H^c^6>0@b$he?5HCEIL?1H?1E^e^ie^ic^a^9@1$hd?1E^8^f>0@4$i3?5HCEIL^f@2$2@1$0#k0^i7^c>0@3$6$8@1$i5^dZ>0@2$h4@2$4@1$i6^e+1@2$h5+2+ha>0@2$c@2$3@2$2@1$0#k0^j2@2$2@1$0#k0^ia@2$3@2$4@2$2@1$0#k0^ia+k0^d>0@2$c@2$3@1$ie?5HCEIL@1$h1^h0@2$h4@1$h1^h0@2$h5+2+k0>0@4$h3$d^h4@2$2@1$0#k0^ib@3$5$a@1$h2^a@1$h0$a>0@2$3@2$2@1$0#k0^j5@2$2@1$0#k0^ic>0@2$7@2$3@2$4@2$2@1$0#k0^id+8@2$2@1$0#k0^ie@2$3@2$4@2$2@1$0#k0^ie+k0@2$2@1$0#k0^id>0@4$h3$d^h7@2$2@1$0#k0^id@3$5$a@1$h2@2$j5@1$0#k0Z@1$h0$a>0@2$7@3$6$8@2$2@1$0#k0^ie@2$4@2$2@1$0#k0^j0+j8@2$c@2$3@2$2@1$0#k0^j8@2$2@1$0#k0^ie@2$7@2$3@2$4@2$2@1$0#k0^ie+8@2$2@1$0#k0^j0@2$3@2$4@2$2@1$0#k0^j0+k0@2$2@1$0#k0^ie>0@5$hf?1E@3$5$9^h1^h0^h9^j9^ja>0@3$6$i8@1$i9^h2@d$id^ja^j4^j3^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1@3$ic?1H\1c$h8@2$7@he$i1?5HCEIL?1H?1E^jd^jc^jb^ja^j6^j5^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^he^hd^ha@2$2@1$0#k0^j4^h9+2^h8^h7^hc^h5^1@e$i0?5HCEIL?1H?1E^jc@3$5$9^h4^h3^ha@2$2@1$0#k0^j4^h9^h8^h7^hd^hc^h5^1@2$h9@7$j0@hf$if^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd@1$j2$hc^hc@1$e@1$1@1$0#k0^hb@1$j1$d^h4").
  Proof.
    intros until G. intros payload NONE HP KR ENV VS CH0 NB [ABOVE A0B] TEMP PAY PAYSP PAYLOC SPW SPWLOC CH LIVE.
    destruct st as [buf cap items chars temp]. cbv [vs_buf] in NONE. subst buf.
    cbv [vs_chars vs_temp vs_n vs_items blocks_vs vs_buf] in CH0, NB, TEMP, HP |- *. cbn [app] in HP.
    ndestruct VS as (_ & (junk7 & HDR) & (CAP0 & ITEMS0 & _)). cbv [vs_cap vs_items vs_chars] in CAP0, ITEMS0. subst cap items chars.
    unfold vs_hdr, vs_top, vs_end, vs_begin, vs_n in HDR. cbv [vs_buf vs_cap vs_items vs_chars vs_temp] in HDR. cbn [length Z.of_nat Z.mul Z.add] in HDR.
    pose proof ENV as ENV'. ndestruct ENV' as (AUX & SPB & ST & CEIL & LO & _).
    pose proof (hh_eh_stack H E HH) as EHS. unfold RVS_PUSH_STACK, ROPNEW_STACK, RMALLOC_STACK in LO.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0. hcb.
    assert (BB : forall b, In b REST -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (hh_blocks H E HH); [exact HP| exact Hb]. }
    eapply (hh_mono H E HH).
    { eapply (push_i64_raw0 H E HH TABS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s REST temp 0 junk7 payload lo B errv mo g G);
        [exact HP| exact KR| exact ENV| unfold vs_hdr_raw; unfold wz in HDR; exact HDR| exact TEMP| exact ABOVE| lia
        | exact PAY| exact PAYSP| exact PAYLOC| exact SPW| exact SPWLOC| exact CH| exact LIVE]. }
    intros [ms' mo'] [OK|UNW].
    - left. ndestruct OK as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & s' & B' & p' & junk' & j7'
                         & EMS & KR' & MP' & HP' & HDR' & SLOT' & JK' & BR' & ENVP & XP).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'.
      unfold push_sca_post. nexists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
      exists (mkVS (Some (p', B', 24 * 16)) 16 [VSval (Jsca 2)] 0 temp), F.
      cbv [vs_buf vs_cap vs_items vs_chars vs_temp vs_n blocks_vs]. cbn [app blocks_items blocks_item blocks_v length Z.of_nat].
      split; [exact EMS|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact HP'|].
      npose BR' as (R1 & R2 & R3 & R4 & R5).
      split.
      { destruct (sca_hdr_of_cells8 _ _ _ _ _ SLOT' ltac:(lia)) as (hb & HB & VH).
        eapply vs_at_some_intro with (junk7 := junk7) (junk := junk'); try (cbn [length Z.of_nat]; lia).
        - unfold vs_hdr_raw in HDR'. unfold wz. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add]. exact HDR'.
        - exact BR'.
        - destruct (rw_cells_CB_split _ _ _ _ 0%nat _ HB ltac:(lia)) as [E0 _]. cbn [firstn] in E0.
          eapply (items_at_snoc m' B' [] [] (VSval (Jsca 2)) hb); [cbn [length Nat.mul]; exact E0| reflexivity| exact I| | cbn [item_hdr]; exact VH| cbn; exact I].
          cbn [length Z.of_nat Z.mul]. rewrite Z.add_0_r. exact HB.
        - cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add Z.sub Z.to_nat Pos.to_nat]. exact JK'. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact ENVP|].
      exact XP.
    - right. ndestruct UNW as (s' & X & MP' & HDR' & BS' & XP). cbn [cfg_ms cfg_model] in X, MP'.
      unfold maybe_grow_unw. exists s'. cbv [blocks_vs vs_buf vs_items]. cbn [app blocks_items].
      split; [exact X|]. split; [exact MP'|].
      split.
      { split; [cbv [vs_chars]; lia|]. split.
        { exists junk7. unfold vs_hdr, vs_top, vs_end, vs_begin, vs_n. cbv [vs_buf vs_cap vs_items vs_chars vs_temp].
          cbn [length Z.of_nat Z.mul Z.add]. unfold wz. unfold vs_hdr_raw in HDR'. exact HDR'. }
        cbv [vs_buf vs_cap vs_items vs_chars]. split; [reflexivity|]. split; reflexivity. }
      split; [exact BS'|]. exact XP.
  Qed.

  (* [comment removed for export] *)
  Lemma push_i64_spec : ltac2:(zQ "10!lvf@3$0?5HCEIL?1H?1E").
  Proof.
    unfold push_i64_stmt, push_sca_stmt_at. intros until pcell. intros HP KR ENV VS CH0 AB TEMP PC SPW' SPWLOC' NB CH LIVE.
    ndestruct (PC ltac:(lia)) as (POK & PAY & PAYSP & PAYLOC). pose proof (SPW' ltac:(lia)) as SPW. pose proof (SPWLOC' ltac:(lia)) as SPWLOC. unfold wz in SPW.
    destruct pcell as [payload| | | |]; cbn in POK; try (exfalso; lia).
    destruct (vs_buf st) eqn:EB.
    - eapply push_i64_stmt_some; try eassumption. rewrite EB. discriminate.
    - eapply push_i64_stmt_none; try eassumption.
  Qed.
End W.
