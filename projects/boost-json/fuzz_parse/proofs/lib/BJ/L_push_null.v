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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJEhTabs BJKitVS BJKitW W_maybe_grow W_push_null.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~kf5frame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~p95block37Corelib4Init5Logicub2eq01Z46Stdlib6ZArith6BinInt1Zhg72le37Corelib4Init9Datatypeshi54Nonehi54conshi54listub3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ5BJRep~~~~~~hlb7vs_temphg73addhg72lthg73powhi53apphi56optionub3notub2or3h5LinuxProcessSemanticsfLinuxProcessSem3Runht16confight15mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Stateih05Model3h5LinuxProcessSemantics5Riscv7Preludeik75bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJIface~~~~~~in6dRVS_PUSH_NULLin6eRVS_PUSH_STACKin66bj_envin68chain_atin6emaybe_grow_unwin6dpush_sca_posthlb9blocks_vshlb5vs_athlb6vs_bufhlb8vs_charshlb4vs_nhlb6vstackkf3csrkf7fr_livekf7hs_KRELkf8hs_RHEAPkf5hs_SRkf5mkCSR69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~jo25hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~js63mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~kg92MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kkc7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kp62wzp93mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~ktd5rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~li26PStatein6epush_null_stmtkf3hmfkf3ehkkfcheap_mf_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8BJEhTabs~~~~~~lp59bj_ehtabs" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!lna$0").
  Variable E : ltac2:(zQ "10!lo0$0").
  Hypothesis HH : ltac2:(zQ "10!lo6@3$0?5HCEIL?1H?1E").
  Hypothesis TABS : ltac2:(zQ "10!lt3@1$0?1E").

  Lemma push_null_stmt_some : ltac2:(zQ "j20!h9!jc!k1!p1!u3!vf!hg4!hhf!hjd!hk5!hkd!hl5!hp6!hq1!hq8!hqe!hr5!hrc!hs6!hsc!hvd!ig7!ije!imd!ir3!is4!it6!iu0!iuc!ive!jgf!jhc!ji5!jif!jjb!jk3!jkd!jl3!jld!jm7!jn2!jna!jrd!kg2!kk6!kob!kt1!kt7!lh9!lle>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$if>1s$j1>4REST@1$a$4>2st$i3>2lo$6>1B$6>4errv@1$1@1$0#k0>2mo$h6>1g$3>1G@1$a$3>0@1$h2@3$5@1$h1$4@1$i0^7@1$8$4>0@4$i7?1H^a@3$h0$4@1$he^8^9^b>0@3$i6?1H^b^5>0@b$ha?5HCEIL?1H?1E^d^id^ib^9^8@1$h9?1E^7^e>0@4$hf?5HCEIL^e@2$2@1$0#k0^i6^b>0@3$5$6@1$i1^cZ>0@2$e@2$d@1$i2^d+1@2$f+2+ha>0@2$b@2$7@2$2@1$0#k0^j1@2$2@1$0#k0^i9@2$7@2$d@2$2@1$0#k0^i9+k0^c>0@2$b@2$7@1$ia?5HCEIL@1$c^f@2$e@1$c^f@2$f+2+k0>0@5$hb?1E@3$9$3^b^a^h3^j3^j4>0@3$5$i4@1$i5^c@d$i9^j4^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb@3$i8?1H\1c$h4@2$h3@he$hd?5HCEIL?1H?1E^j7^j6^j5^j4^j0^if^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^h8^h7^h4@2$2@1$0#k0^ie^h3Z^h2^h1^h6^f^1@e$hc?5HCEIL?1H?1E^j6@3$9$3^e^d^h4@2$2@1$0#k0^ie^h3^h2^h1^h7^h6^f^1@2$h5@7$ic@hf$ib^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7@1$ie$h8^h6@1$8@1$1@1$0#k0^h5@1$id$j0^e").
  Proof.
    intros until G. intros SOME HP KR ENV VS CH0 NB [ABOVE A0B] TEMP CH LIVE.
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
    { eapply (push_null_raw H E HH TABS
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s (blocks_items items ++ REST)
                temp Bb n cap 0 junk7 bs junk p lo B errv mo g G);
        [exact HP| exact KR| exact ENV| unfold vs_hdr_raw; unfold wz in HDR; exact HDR| exact BUF| exact BR| lia| lia| lia| lia| exact TEMP| exact ABOVE| lia
        | exact CH| exact LIVE]. }
    intros [ms' mo'] [OK|UNW].
    - left. ndestruct OK as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & s' & B' & cap' & p' & junk' & j15
                         & EMS & KR' & MP' & HP' & HDR' & ITEMS' & SLOT' & JK' & BR' & LT & C16 & CAPM & SAME & ENVP & XP).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'.
      unfold push_sca_post. nexists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
      exists (mkVS (Some (p', B', 24 * cap')) cap' (items ++ [VSval (Jsca 0)]) 0 temp), F.
      cbv [vs_buf vs_cap vs_items vs_chars vs_temp vs_n blocks_vs].
      split; [exact EMS|]. split; [exact KR'|]. split; [exact MP'|].
      split. { rewrite blocks_items_app. cbn [blocks_items blocks_item blocks_v]. rewrite app_nil_r. exact HP'. }
      npose BR' as (R1 & R2 & R3 & R4 & R5).
      split.
      { destruct (sca_hdr_of_cells _ _ _ _ SLOT' ltac:(lia)) as (hb & HB & VH).
        eapply vs_at_some_intro with (junk7 := junk7) (junk := junk'); rewrite ?length_app; cbn [length]; try lia.
        - unfold vs_hdr_raw in HDR'. unfold wz. replace (Z.of_nat (length items + 1)) with (n + 1) by lia. exact HDR'.
        - exact BR'.
        - eapply (items_at_snoc m' B' items bs (VSval (Jsca 0)) hb).
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
  Lemma push_null_stmt_none : ltac2:(zQ "j10!h9!jc!k1!p1!u3!vf!hg4!hhf!hjd!hk5!hkd!hl5!hp6!hq1!hq8!hqe!hr5!hrc!hsc!hvd!ig7!ije!imd!ir3!is4!it6!iu0!iuc!ive!jgf!jhc!ji5!jif!jjb!jk3!jkd!jl3!jld!jm7!jn2!jna!jrd!kg2!kk6!kob!kt1!kt7!lh9!lle>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$ie>1s$j0>4REST@1$a$4>2st$i2>2lo$6>1B$6>4errv@1$1@1$0#k0>2mo$h5>1g$3>1G@1$a$3>0@3$5@1$h1$4@1$hf^7@1$8$4>0@4$i6?1H^a@3$h0$4@1$hd^8^9^b>0@3$i5?1H^b^5>0@b$h9?5HCEIL?1H?1E^d^id^ib^9^8@1$h8?1E^7^e>0@4$he?5HCEIL^e@2$2@1$0#k0^i6^b>0@3$5$6@1$i0^cZ>0@2$e@2$d@1$i1^d+1@2$f+2+ha>0@2$b@2$7@2$2@1$0#k0^j1@2$2@1$0#k0^i9@2$7@2$d@2$2@1$0#k0^i9+k0^c>0@2$b@2$7@1$i9?5HCEIL@1$c^f@2$e@1$c^f@2$f+2+k0>0@5$ha?1E@3$9$3^b^a^h3^j3^j4>0@3$5$i3@1$i4^c@d$i8^j4^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb@3$i7?1H\1c$h3@2$h2@he$hc?5HCEIL?1H?1E^j7^j6^j5^j4^j0^if^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^h8^h7^h4@2$2@1$0#k0^ie^h3Z^h2^h1^h6^f^1@e$hb?5HCEIL?1H?1E^j6@3$9$3^e^d^h4@2$2@1$0#k0^ie^h3^h2^h1^h7^h6^f^1@2$h4@7$ib@hf$ia^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7@1$id$h7^h6@1$8@1$1@1$0#k0^h5@1$ic$if^e").
  Proof.
    intros until G. intros NONE HP KR ENV VS CH0 NB [ABOVE A0B] TEMP CH LIVE.
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
    { eapply (push_null_raw0 H E HH TABS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s REST temp 0 junk7 lo B errv mo g G);
        [exact HP| exact KR| exact ENV| unfold vs_hdr_raw; unfold wz in HDR; exact HDR| exact TEMP| exact ABOVE| lia| exact CH| exact LIVE]. }
    intros [ms' mo'] [OK|UNW].
    - left. ndestruct OK as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & s' & B' & p' & junk' & j15
                         & EMS & KR' & MP' & HP' & HDR' & SLOT' & JK' & BR' & ENVP & XP).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'.
      unfold push_sca_post. nexists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
      exists (mkVS (Some (p', B', 24 * 16)) 16 [VSval (Jsca 0)] 0 temp), F.
      cbv [vs_buf vs_cap vs_items vs_chars vs_temp vs_n blocks_vs]. cbn [app blocks_items blocks_item blocks_v length Z.of_nat].
      split; [exact EMS|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact HP'|].
      npose BR' as (R1 & R2 & R3 & R4 & R5).
      split.
      { destruct (sca_hdr_of_cells _ _ _ _ SLOT' ltac:(lia)) as (hb & HB & VH).
        eapply vs_at_some_intro with (junk7 := junk7) (junk := junk'); try (cbn [length Z.of_nat]; lia).
        - unfold vs_hdr_raw in HDR'. unfold wz. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul Z.add]. exact HDR'.
        - exact BR'.
        - destruct (rw_cells_CB_split _ _ _ _ 0%nat _ HB ltac:(lia)) as [E0 _]. cbn [firstn] in E0.
          eapply (items_at_snoc m' B' [] [] (VSval (Jsca 0)) hb); [cbn [length Nat.mul]; exact E0| reflexivity| exact I| | cbn [item_hdr]; exact VH| cbn; exact I].
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
  Lemma push_null_spec : ltac2:(zQ "10!lm8@3$0?5HCEIL?1H?1E").
  Proof.
    unfold push_null_stmt, push_sca_stmt_at. intros until pcell. intros HP KR ENV VS CH0 AB TEMP _ _ _ NB CH LIVE.
    destruct (vs_buf st) eqn:EB.
    - eapply push_null_stmt_some; try eassumption. rewrite EB. discriminate.
    - eapply push_null_stmt_none; try eassumption.
  Qed.
End W.
