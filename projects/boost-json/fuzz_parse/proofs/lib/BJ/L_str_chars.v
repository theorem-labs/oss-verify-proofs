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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJEhTabs BJKitVS BJKitW BJKitStr BJIfaceStr W_maybe_grow W_str_chars.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhfbbv_unsigned46Stdlib6ZArith6BinInt1Zkf2le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~mc5blockkf3add37Corelib4Init5Logics43ands42eq01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~u65frame37Corelib4Init9Datatypeshj04lists42orhj04Nonehj04cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ5BJRep~~~~~~hm57vs_temp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hqb2wzmc8blk_addr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~hv75rsegskf3powhj03apphj06lengthhj06options42exs43not3h5LinuxProcessSemanticsfLinuxProcessSem3Runim86configim85mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Stateiq75Model3h5LinuxProcessSemantics5Riscv7Preludeite5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJIface~~~~~~jgdeRVS_PUSH_CHARSjgdeRVS_PUSH_STACKjgd6bj_envjgd8chain_atjgdemaybe_grow_unw79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJaBJIfaceStr~~~~~~jp6fpush_chars_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8BJKitStr~~~~~~ju9achars_needhm59blocks_vshm55vs_athm56vs_bufhm58vs_charshm54vs_nhm56vstacku63csru67fr_liveu67hs_KRELu68hs_RHEAPu65hs_SRu65mkCSR69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~kq85hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kuc3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lif2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ln28bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~lr87seg_rommc8blk_sizemc3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~mh36PState36Stdlib5Lists4Listml92Inkf2ltkf6of_natjp6fpush_chars_stmtu63hmfu63ehku6cheap_mf_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ8BJEhTabs~~~~~~mqe9bj_ehtabs" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!mp3$0").
  Variable E : ltac2:(zQ "10!mp9$0").
  Hypothesis HH : ltac2:(zQ "10!mpf@3$0?5HCEIL?1H?1E").
  Hypothesis TABS : ltac2:(zQ "10!muc@1$0?1E").

  Lemma push_chars_stmt_some : ltac2:(zQ "ja0!h9!jc!k1!m7!r6!re!t8!te!u3!hi8!hk8!hl0!hl5!hld!hq0!hu6!huc!ij3!ijc!ik2!ik9!il3!ild!im2!ip4!ipe!it5!jg4!jka!jlc!jme!jn8!jo4!jt6!ki7!kj5!kk2!kkb!kl5!km1!km9!kn3!kn9!ko3!kod!kp8!kq0!ku3!li8!lmc!lqc!lv7!mg2!mgd!mkf!mmc!mn2!mn7>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$hb@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j5>1s$j6>4REST@1$a$4>2st$i8>2lo$8>1B$8>4errv@1$1@1$0#k0>2mo$ha>1g$9>1G@1$a$9>3src@1$a@1$1@1$0#8>1n$8>0@1$h7@3$7@1$h5$4@1$i5^9@1$c$4>0@4$ic?1H^c@3$h3$4@1$i3^a^b^d>0@3$ib?1H^d^7>0@b$he?5HCEIL?1H?1E^f^if^id^b^a@1$hd?1E^9^h0>0@4$i4?5HCEIL^h0@2$2@1$0#k0^i8^d>0@2$3@3$i2@1$i7^e@1$i6^e^6@2$h2+2+ha>0@2$6@2$3@2$2@1$0#k0^j2@2$2@1$0#k0^ia@2$3@2$5@2$2@1$0#k0^ia+k0^d>0@2$6@2$3@1$if?5HCEIL@1$e^h0@2$j8@1$e^h0@2$h2+2+k0>0@3$7@1$1@1$0#k0^ia@1$f^9>0@2$3Z^a>0@4$j2$h1^h6@2$2@1$0#k0^id^c>0@3$7$8@1$j9@2$h4@1$1@1$0#8^d^c>0@2$b@2$3@2$2@1$0#k0^j8@2$2@1$0#k0^if@2$h6$4\1b$4@2$6@3$j7$4^1^h7@2$6@2$3@1$h0^1@2$2@1$0#k0^j0@2$3@2$5@2$2@1$0#k0^j0^e@2$5@1$h0^1@1$j4^1>0@2$b@2$3@2$5@2$2@1$0#k0^j0^e@2$2@1$0#k0^j1@2$3@2$5@2$2@1$0#k0^j1+k0@2$2@1$0#k0^j0>0@5$hf?1E@3$d$9^h2^h1^ha^ja^jb>0@3$7$i9@1$ia^h3@d$ie^jb^j5^j4^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2@3$id?1H\1c$h8@2$b@he$i1?5HCEIL?1H?1E^je^jd^jc^jb^j7^j6^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^hf^he^hb@2$2@1$0#k0^j5^ha^h2^h9^h8^hd^h6^1@e$i0?5HCEIL?1H?1E^jd@3$d$9^h5^h4^hb@2$2@1$0#k0^j5^ha^h9^h8^he^hd^h6^1@2$h9@7$j1@hf$j0^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he@1$f$hc^hd@1$c@1$1@1$0#k0^hc@1$j3$h1^h5").
  Proof.
    intros until n. intros SOME HP KR ENV VS NB [ABOVE A0B] TEMP EA2 N0 SRC SLEN SRCLOC SRCVS CH LIVE.
    destruct st as [buf cap items chars temp]. destruct buf as [[[p Bb] sz]|]; [| exfalso; apply SOME; reflexivity].
    cbv [vs_chars vs_temp vs_n vs_items blocks_vs vs_buf] in NB, TEMP, HP |- *.
    destruct (vs_at_some_elim _ _ _ _ _ _ _ _ _ VS) as (SZ & CH0 & (junk7 & HDR) & CAP16 & NLE & CAP32 & BR & BT & ITEMS & ROOMI & (junk & JK)).
    subst sz. clear VS.
    apply items_at_raw in ITEMS. ndestruct ITEMS as (bs & LEN & RB & IH & ID).
    pose proof ENV as ENV'. ndestruct ENV' as (AUX & SPB & ST & CEIL & LO & _).
    pose proof (hh_eh_stack H E HH) as EHS. unfold RVS_PUSH_STACK, ROPNEW_STACK, RMALLOC_STACK in LO.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0. hcb.
    npose BR as (Q1 & Q2 & Q3 & Q4 & Q5).
    set (k := Z.of_nat (length items)) in *.
    assert (BUF : rw_cells rsegs m Bb [CB (Z.to_nat (24 * k)) bs; CB (Z.to_nat (24 * (cap - k))) junk]).
    { apply (proj2 (rw_cells_app _ _ _ [CB (Z.to_nat (24 * k)) bs] _)). cbn [cells_size csize Nat.add].
      replace (Z.to_nat (24 * k) + 0)%nat with (24 * length items)%nat by lia.
      split. { replace (Z.to_nat (24 * k)) with (24 * length items)%nat by lia. exact RB. }
      replace (Bb + Z.of_nat (24 * length items)) with (Bb + 24 * k) by lia. exact JK. }
    assert (BB : forall b, In b (blocks_items items ++ REST) -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (hh_blocks H E HH); [exact HP| right; exact Hb]. }
    (* [comment removed for export] *)
    assert (SRCB : bv_unsigned a1 + n <= Bb \/ Bb + 24 * cap <= bv_unsigned a1).
    { destruct SRCLOC as [Hs|(b & Hb & Hb1 & Hb2)]; [right; lia|].
      pose proof (hh_nodup H E HH _ _ _ HP) as ND. cbn [map app] in ND. apply List.NoDup_cons_iff in ND as [NI _].
      assert (NE : blk_id (p, Bb, 24 * cap) <> blk_id b).
      { intros EQ. apply NI. rewrite map_app. apply in_or_app. right. apply in_map_iff. exists b. split; [symmetry; exact EQ| exact Hb]. }
      destruct (hh_disj H E HH _ _ _ (p, Bb, 24 * cap) b HP (or_introl eq_refl) (or_intror (in_or_app _ _ _ (or_intror Hb))) NE) as [D|D];
        cbn [blk_addr blk_size fst snd] in D; [right| left]; lia. }
    eapply (hh_mono H E HH).
    { eapply (push_chars_raw H E HH TABS
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s (blocks_items items ++ REST)
                temp Bb k cap chars n junk7 bs junk src p lo B errv mo g G);
        [exact HP| exact KR| exact ENV| unfold vs_hdr_raw; unfold wz in HDR; exact HDR| exact BUF| exact BR| lia| lia| lia| exact CH0| exact ROOMI| lia| exact NB
        | exact TEMP| exact ABOVE| lia| exact EA2| exact SRC| lia| | exact SRCVS| exact SRCB| exact CH| exact LIVE].
      destruct SRCLOC as [Hs|(b & Hb & Hb1 & Hb2)]; [left; exact Hs| right]. exists b. split; [apply in_or_app; right; exact Hb| lia]. }
    intros [ms' mo'] [OK|UNW].
    - left. ndestruct OK as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & s' & B' & cap' & p' & junk'
                         & EMS & KR' & MP' & HP' & HDR' & BUF' & BR' & RM' & C16 & CAPM & SAME & ENVP & XP).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'.
      unfold push_chars_post. nexists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
      exists (mkVS (Some (p', B', 24 * cap')) cap' items (chars + n) temp).
      cbv [vs_buf vs_cap vs_items vs_chars vs_temp vs_n blocks_vs].
      split; [exact EMS|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact HP'|].
      npose BR' as (R1 & R2 & R3 & R4 & R5).
      apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat (24 * k)) bs] _)) in BUF'. cbn [cells_size csize Nat.add] in BUF'.
      destruct BUF' as [RB' JK'].
      split.
      { eapply vs_at_some_intro with (junk7 := junk7) (junk := junk').
        - lia.
        - unfold vs_hdr_raw in HDR'. unfold wz. fold k. exact HDR'.
        - lia.
        - lia.
        - unfold chars_need in NB, CAPM. lia.
        - exact BR'.
        - lia.
        - eapply (items_at_relocate (blocks_items items ++ REST) (bv_unsigned sp) (vs_X (bv_unsigned a0)) m m' Bb B' items bs);
            [exact RB| exact IH| exact ID| | exact XP| | exact BB| intros b Hb; apply in_or_app; left; exact Hb].
          + replace (24 * length items)%nat with (Z.to_nat (24 * k)) by lia. exact RB'.
          + unfold X_above_hceil, vs_X. constructor; [|constructor]. cbn [fst snd]. left. lia.
        - lia.
        - fold k. replace (Z.to_nat (24 * k) + 0)%nat with (Z.to_nat (24 * k)) in JK' by lia. rewrite Z2Nat.id in JK' by lia. exact JK'. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact ENVP|].
      eapply xpres_weaken; [exact XP| lia| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
    - right. ndestruct UNW as (s' & X & MP' & HDR' & BUF' & BS' & XP). cbn [cfg_ms cfg_model] in X, MP'.
      unfold maybe_grow_unw. exists s'. cbv [blocks_vs vs_buf vs_items].
      split; [exact X|]. split; [exact MP'|].
      apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat (24 * k)) bs] _)) in BUF'. cbn [cells_size csize Nat.add] in BUF'.
      destruct BUF' as [RB' JK'].
      split.
      { eapply vs_at_some_intro with (junk7 := junk7) (junk := junk).
        - lia.
        - unfold vs_hdr_raw in HDR'. unfold wz. fold k. exact HDR'.
        - lia.
        - lia.
        - lia.
        - exact BR.
        - lia.
        - eapply (items_at_relocate (blocks_items items ++ REST) (bv_unsigned sp) (vs_X (bv_unsigned a0) ++ EH_IVS) m _ Bb Bb items bs);
            [exact RB| exact IH| exact ID| | exact XP| | exact BB| intros b Hb; apply in_or_app; left; exact Hb].
          + replace (24 * length items)%nat with (Z.to_nat (24 * k)) by lia. exact RB'.
          + unfold X_above_hceil, vs_X, EH_IVS. constructor; [cbn [fst snd]; left; lia|]. constructor; [cbn [fst snd]; right; lia|].
            constructor; [cbn [fst snd]; right; lia| constructor].
        - exact ROOMI.
        - fold k. replace (Z.to_nat (24 * k) + 0)%nat with (Z.to_nat (24 * k)) in JK' by lia.
          rewrite Z2Nat.id in JK' by lia. exact JK'. }
      split; [exact BS'|].
      eapply xpres_weaken; [exact XP| lia| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma push_chars_stmt_none : ltac2:(zQ "j90!h9!jc!k1!m7!r6!re!t8!te!u3!hi8!hk8!hl0!hl5!hld!hq0!hu6!huc!ij3!ijc!ik2!ik9!il3!ild!ip4!ipe!it5!jg4!jka!jlc!jme!jn8!jo4!jt6!ki7!kj5!kk2!kkb!kl5!km1!km9!kn3!kn9!ko3!kod!kp8!kq0!ku3!li8!lmc!lqc!lv7!mg2!mgd!mkf!mmc!mn2!mn7>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$ha@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j4>1s$j5>4REST@1$a$4>2st$i7>2lo$8>1B$8>4errv@1$1@1$0#k0>2mo$h9>1g$9>1G@1$a$9>3src@1$a@1$1@1$0#8>1n$8>0@3$7@1$h5$4@1$i4^9@1$c$4>0@4$ib?1H^c@3$h3$4@1$i2^a^b^d>0@3$ia?1H^d^7>0@b$hd?5HCEIL?1H?1E^f^if^id^b^a@1$hc?1E^9^h0>0@4$i3?5HCEIL^h0@2$2@1$0#k0^i8^d>0@2$3@3$i1@1$i6^e@1$i5^e^6@2$h2+2+ha>0@2$6@2$3@2$2@1$0#k0^j2@2$2@1$0#k0^ia@2$3@2$5@2$2@1$0#k0^ia+k0^d>0@2$6@2$3@1$ie?5HCEIL@1$e^h0@2$j7@1$e^h0@2$h2+2+k0>0@3$7@1$1@1$0#k0^ia@1$f^9>0@2$3Z^a>0@4$j1$h1^h6@2$2@1$0#k0^id^c>0@3$7$8@1$j8@2$h4@1$1@1$0#8^d^c>0@2$b@2$3@2$2@1$0#k0^j8@2$2@1$0#k0^if@2$h6$4\1b$4@2$6@3$j6$4^1^h7@2$6@2$3@1$h0^1@2$2@1$0#k0^j0@2$3@2$5@2$2@1$0#k0^j0^e@2$5@1$h0^1@1$j3^1>0@2$b@2$3@2$5@2$2@1$0#k0^j0^e@2$2@1$0#k0^j1@2$3@2$5@2$2@1$0#k0^j1+k0@2$2@1$0#k0^j0>0@5$he?1E@3$d$9^h2^h1^ha^ja^jb>0@3$7$i8@1$i9^h3@d$id^jb^j5^j4^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2@3$ic?1H\1c$h7@2$b@he$i0?5HCEIL?1H?1E^je^jd^jc^jb^j7^j6^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^hf^he^hb@2$2@1$0#k0^j5^ha^h2^h9^h8^hd^h6^1@e$hf?5HCEIL?1H?1E^jd@3$d$9^h5^h4^hb@2$2@1$0#k0^j5^ha^h9^h8^he^hd^h6^1@2$h8@7$j0@hf$if^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he@1$f$hb^hd@1$c@1$1@1$0#k0^hc@1$j2$h1^h5").
  Proof.
    intros until n. intros NONE HP KR ENV VS NB [ABOVE A0B] TEMP EA2 N0 SRC SLEN SRCLOC SRCVS CH LIVE.
    destruct st as [buf cap items chars temp]. cbv [vs_buf] in NONE. subst buf.
    cbv [vs_chars vs_temp vs_n vs_items blocks_vs vs_buf] in NB, TEMP, HP |- *. cbn [app] in HP.
    ndestruct VS as (_ & (junk7 & HDR) & (CAP0 & ITEMS0 & CHARS0)). cbv [vs_cap vs_items vs_chars] in CAP0, ITEMS0, CHARS0. subst cap items chars.
    unfold vs_hdr, vs_top, vs_end, vs_begin, vs_n in HDR. cbv [vs_buf vs_cap vs_items vs_chars vs_temp] in HDR. cbn [length Z.of_nat Z.mul Z.add] in HDR.
    cbn [length Z.of_nat] in NB.
    pose proof ENV as ENV'. ndestruct ENV' as (AUX & SPB & ST & CEIL & LO & _).
    pose proof (hh_eh_stack H E HH) as EHS. unfold RVS_PUSH_STACK, ROPNEW_STACK, RMALLOC_STACK in LO.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0. hcb.
    assert (BB : forall b, In b REST -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (hh_blocks H E HH); [exact HP| exact Hb]. }
    eapply (hh_mono H E HH).
    { eapply (push_chars_raw0 H E HH TABS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s REST temp n junk7 src lo B errv mo g G);
        [exact HP| exact KR| exact ENV| unfold vs_hdr_raw; unfold wz in HDR; exact HDR| exact N0| exact NB| exact TEMP| exact ABOVE| lia
        | exact EA2| exact SRC| lia| exact SRCLOC| exact SRCVS| exact CH| exact LIVE]. }
    intros [ms' mo'] [OK|UNW].
    - left. ndestruct OK as (u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & s' & B' & cap' & p' & junk'
                         & EMS & KR' & MP' & HP' & HDR' & JK' & BR' & RM' & C16 & CAPM & ENVP & XP).
      cbn [cfg_ms cfg_model] in EMS, KR', MP'.
      unfold push_chars_post. nexists u0, u1, u2, w0, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m', s'.
      exists (mkVS (Some (p', B', 24 * cap')) cap' [] n temp).
      cbv [vs_buf vs_cap vs_items vs_chars vs_temp vs_n blocks_vs]. cbn [app blocks_items length Z.of_nat].
      split; [exact EMS|]. split; [exact KR'|]. split; [exact MP'|]. split; [exact HP'|].
      npose BR' as (R1 & R2 & R3 & R4 & R5).
      split.
      { eapply vs_at_some_intro with (junk7 := junk7) (junk := junk'); cbn [length Z.of_nat].
        - lia.
        - unfold vs_hdr_raw in HDR'. unfold wz. rewrite Z.mul_0_r, Z.add_0_r. exact HDR'.
        - lia.
        - lia.
        - unfold chars_need in NB, CAPM. pose proof (Z.le_max_l 16 (2 * ((0 + n + 23) / 24 + 0 + 1))). lia.
        - exact BR'.
        - lia.
        - exists []. split; [| split; [reflexivity| exact I]]. cbn [length Nat.mul].
          destruct (rw_cells_CB_split _ _ _ _ 0%nat _ JK' ltac:(lia)) as [E0 _]. cbn [firstn] in E0. exact E0.
        - lia.
        - rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r. exact JK'. }
      split; [reflexivity|]. split; [cbn; lia|]. split; [reflexivity|]. split; [exact ENVP|].
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
  Lemma push_chars_spec : ltac2:(zQ "10!mo0@3$0?5HCEIL?1H?1E").
  Proof.
    unfold push_chars_stmt. intros until n. intros HP KR ENV VS NB AB TEMP EA2 N0 SRC SLEN SRCLOC SRCVS CH LIVE.
    destruct (vs_buf st) eqn:EB.
    - eapply push_chars_stmt_some; try eassumption. rewrite EB. discriminate.
    - eapply push_chars_stmt_none; try eassumption.
  Qed.
End W.
