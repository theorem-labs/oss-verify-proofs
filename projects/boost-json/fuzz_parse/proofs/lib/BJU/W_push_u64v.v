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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJU Require Import BJRep BJHeap BJIface BJEhTabs BJKitVS BJKitW W_grow_one L_grow_one.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsk4dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeob5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~r93mem37Corelib4Init5Logichga2exi27Z_to_bvhga3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hj55rsegsi2bbv_unsigned37Corelib4Init9Datatypesho94cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hq94cell46Stdlib6ZArith6BinInt1Zhud3addhq92C8ho94Noneho94listho93nilho96optionho94prodhga2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ik13mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~io42MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~is77seg_romho94pairhga2or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUaW_grow_one~~~~~~jhfcRVS_GROW_ONEhq92CBik15munchik13stkik15wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jof7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jt48rw_cellshud2lehud2lthud3pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJU6BJKitW~~~~~~kieavs_hdr_raw99OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUbW_push_u64v3HCW1W~~~~~~kn98pvE_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJUbW_push_u64v~~~~~~ksddRVS_PUSH_U64V69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~li05hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~lm43evthq92C1io46ret_pckn98pvW_posthud6modulo" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Definition RVS_PUSH_U64V : Z := 0x6062c.

Section HCW.
  Context {HCEIL : HeapCeil}.
Section W.
  Variable H : hmf.
  Variable E : ehk.
  Hypothesis HH : heap_mf_hyps H E.
  Hypothesis TABS : bj_ehtabs E.

  (* [comment removed for export] *)
  Definition pvE_post : ltac2:(zQ "60!hc!jf!h9!nb!r1!hg4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1T$2>2EE$2>2lo$2>1m$5>0$3P") := ltac2:(zQ "i32!hc!jf!hhe!h9!hi4!hie!hn2!hnb!hq1!hu5!ig5!nb!igc!ih2!iha!ii2!ii9!ij3!ijb!ind!is1!jg6!jh1!jh9!r1!jm0!jn0!jn6!jnf!jo6!js9!kgf!hg4!khb!ki1&>0@1$1@1$0#k0@1$h0@1$1@1$0#8&@2$4@1$0#k0@2$a@2$7@1$0#k0^i6-i0\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2a0@1$1@1$0#k0\2a1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1T$3\2EE$3\2lo$3\1m$i0\2ms$b@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2@1$e@1$1@1$0#8\2j8@1$e@1$1@1$0#8@2$2~0\2m'~0@2$5@2$h7@2$5@2$i2^h3^h2@3$h2$b^f@7$h4@hf$h3^i7~1^i5^i4^e^d^c^i1^i0@2$4@1$0#k0^h3^i0@2$4@1$0#k0^h2^b^a^9^8^7^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^6^5^4^3^h5@2$4@1$0#k0+mgmlc^h4@1$d@1$1@1$0#k0^1@1$h5$6@2$5@2$i1^h2^h3@3$h2$b^f@7$h4@hf$h3@2$4@1$0#k0+mgml8~1^i5^i4^e^d^c^i1^i0^i1^i0@2$4@1$0#k0^h2^b^a^9^8^7^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^6^5^4^3^h5@2$4@1$0#k0$h9^h4@1$d@1$1@1$0#k0^1@1$h5$6@2$5@3$hb@3$8@2$h1$3$3@4$h6$3$3@2$a@2$7@1$0#k0^i6-i0@2$7@1$0#k0^i6@1$f@2$h1$3$3^h0^1@2$5@3$hd$6^h0^1@2$5@2$he$6^1@2$5@4$hc$6^1^h1@2$a@2$7@1$0#k0^i6-i0@4$hf$6^1@2$a@2$7@1$0#k0^i6-i0@3$8$9@2$haN8^2@3$8$9@1$c^i2@3$8$9@1$c^i3@3$8$9@1$c^i7@1$f$9").

  Lemma pvE : ltac2:(zQ "ha1!hc!jf!h9!khb!hnb!hn2!ki7!hie!ig5!ki1!ih2!iha!r1!kmb!ks1!lgf!llb!lpf!ind!jnf!is1!js9!jg6!kgf!hg4!hi4&@2$7@2$3Z^b@2$9^b@2$6+2+k0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$c@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h8>2lo$2>4temp$2>2Bg$2>1T$2>2EE$2>5chars$2>2j7@1$b@1$1@1$0#8>0@2$h5$5^8>0@4$h3$5^9^8@2$4@1$0#k0^i9>0@2$3@1$h0?5HCEIL^9>0@2$3@2$8^a+i0@2$4@1$0#k0^ib>0@4$h7$5^c@2$4@1$0#k0^i4@6$d^a^9^8^7^6^5>0@2$3@2$4@1$0#k0^id@2$4@1$0#k0^i5>0@2$3@2$8@2$4@1$0#k0^i6+k0@2$6+2+k0>0~0>0~0@3$h1$5@h8$e^j2^j1^j0^if^ib^ia^i9^i8^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h3^h2^d^c^h0^h1@7$h4@hf$h2^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3@2$h9@1$0#k0$f^h2@1$a@1$1@1$0#k0^h1@1$h6$5").
  Proof.
    intros until j7. intros MI ST CEIL ROOM VSH ABOVE A064 TR ER. unfold RVS_PUSH_U64V.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP; cbn in RSP.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0. hcb.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold vs_hdr_raw in VSH.
    carve_frame 32%nat ST.
    st1. st1. st1. st1. st1. st1. st1. st1.
    st1. if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      apply evt_done. unfold pvE_post. neexists 14. split; [left; split; [exact K| reflexivity]|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
    - rewrite ?unsigned_lit in K by lia.
      st1. st1. apply evt_done. unfold pvE_post, RVS_GROW_ONE. neexists 14. split; [right; split; [lia| reflexivity]|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
  Qed.
  (* [comment removed for export] *)
  Definition pvW_post : ltac2:(zQ "70!hc!jf!h9!iha!nb!r1!hg4>3rae@1$1@1$0#k0>3spe@1$1@1$0#k0>3s0e@1$1@1$0#k0>3s1e@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2vs@1$1@1$0#k0>7payload@1$1@1$0#k0>4temp$2>2Bg$2>1T$2>2EE$2>5chars$2>2j7@1$3@1$1@1$0#8>2lo$2>1m$6>0$4P") := ltac2:(zQ "i21!hc!jf!h9!hq1!hie!hn2!hi4!hu5!ig5!hnb!iha!ij3!ii2!ii9!jh1!hhe!nb!igc!kgf!ih2!ijb!r1!kmb!lq6!jn0!ind!jn6!jnf!jo6!is1!lqc!js9!jg6!hg4&>0@1$1@1$0#k0@1$d@1$1@1$0#8\3rae@1$1@1$0#k0\3spe@1$1@1$0#k0\3s0e@1$1@1$0#k0\3s1e@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2a4@1$1@1$0#k0\2a5@1$1@1$0#k0\2a6@1$1@1$0#k0\2a7@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2t0@1$1@1$0#k0\2t1@1$1@1$0#k0\2t2@1$1@1$0#k0\2t3@1$1@1$0#k0\2t4@1$1@1$0#k0\2t5@1$1@1$0#k0\2t6@1$1@1$0#k0\1F@2$h5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2vs@1$1@1$0#k0\7payload@1$1@1$0#k0\4temp$2\2Bg$2\1T$2\2EE$2\5chars$2\2j7@1$a@1$1@1$0#8\2lo$2\1m$i1\2ms$h0@2$f~0\2m'~0@2$f@1$a@1$1@1$0#8\2js@1$a@1$1@1$0#8@2$4@3$h4$h0^3@7$hd@hf$h9^ia^i9^i6^i5^h6^h5^h4^i8^i7@2$6@1$0#k0+1@2$6@1$0#k0Z@2$6@1$0#k0@2$8^9+h8@2$6@1$0#k0+3^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h3^h2^h1^h0^f@1$he^ia^e@1$h3@1$1@1$0#k0^2@1$i0$5@2$4@3$ha@3$3@2$b$2$2@4$e$2$2^9@2$8^9+h8@3$3@2$b$2$2@4$e$2$2@2$8@2$9@1$0#k0^d+h8@2$8@2$9@1$0#k0^d+i0@1$c@2$b$2$2^4^2@2$4@3$hc$5^4^2@2$4@2$hf$5^2@2$4@4$hb$5^2^5@2$9@1$0#k0^i9@2$4@4$h2$5^2@2$9@1$0#k0^d@6$h6^b^a@2$8^9+h8^8^7^6@4$h2$5^2^9@3$3$7@1$h1@2$6@1$0#k0Z@3$3$7@1$h7@2$6@1$0#8+3@3$3$7@2$h8N7^1@3$3$7@1$h1^c@1$c$7").

  Lemma pvW : ltac2:(zQ "hf0!hc!jf!hnb!h9!hu5!hn2!ig5!khb!hq1!iha!igc!kgf!hi4!ii2!llb!jn0!ih2!ijb!r1!kmb!lr6!lpf!ind!jnf!is1!js9!jg6!hg4!ki1!ls2!ki7>3rax@1$1@1$0#k0>3rae@1$1@1$0#k0>3spe@1$1@1$0#k0>3s0e@1$1@1$0#k0>3s1e@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2vs@1$1@1$0#k0>7payload@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$hb>2lo$3>4temp$3>2Bg$3>1T$3>2EE$3>5chars$3>2j7@1$9@1$1@1$0#8>2j8@1$9@1$1@1$0#8>4slot@1$9@1$1@1$0#8>0@2$h9$5^a>0@4$h7$5^b^a@2$6@2$2@1$0#k0^ic-i0>0@2$7Z^b>0@2$7@2$6^c+i0@2$2@1$0#k0^ie>0@4$b$5^e@2$6@2$2@1$0#k0^if-i0@3$8$4@2$fN8^6@3$8$4@1$a^id@3$8$4@1$a^ie@3$8$4@1$a^j0@1$d$4>0@4$b$5^f@2$2@1$0#k0^i8@6$h3^d^c^b^a^9^8>0@4$b$5^h0^c@3$8$4@2$fNh8^7@1$d$4>0@2$hcZ^d>0@3$h1$3@2$hd^e+8Z>0@2$7@2$6^f+h8@1$e?5HCEIL>0@2$7@1$e?5HCEIL^h3>0@2$7@2$2@1$0#k0^j6@2$2@1$0#k0^ie>0@2$7@2$6@2$2@1$0#k0^if+k0@2$he+2+k0@3$h5$5@i7$h4^j9^j8^j7^j6^j5^j4^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^j3^j2^j1^hd^hc^hb^ha^h9^h8^j0^if^h5^h4^h3^h2^h1^h0^h6^h7@7$h8@hf$h6^ja@2$c@1$0#k0@2$6@2$2@1$0#k0^j8-i0^j5^j4^j3^j2^j1^j0^if@2$c@1$0#k0^h3^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9@2$c@1$0#k0+mgmlc^h8@1$h0@1$1@1$0#k0^h7@1$ha$5").
  Proof.
    intros until slot. intros MI ST LO0 ROOM FR VSH SLOT T0 T8 THI CEIL ABOVE V64.
    pose proof (bv_unsigned_in_range _ vs) as RVS. unfold bv_modulus in RVS; cbn in RVS.
    pose proof (bv_unsigned_in_range _ spe) as RSP. unfold bv_modulus in RSP; cbn in RSP. hcb.
    pose proof (munch_refl [(T, T + 24); (bv_unsigned vs + 24, bv_unsigned vs + 32)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold vs_hdr_raw in VSH.
    st1. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }
    st1. st1. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. lia. }
    st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
    st1. st1. st1. st1. st1.
    st1. if_cases K4; zify_cond K4. { exfalso. revert K4. rewrite ?unsigned_lit by lia. lia. }
    st1. st1. if_cases K5; zify_cond K5. { exfalso. revert K5. unfold wz. rewrite ?unsigned_lit_wrap, ?unsigned_lit by lia. cbn. lia. }
    st1. st1. st1.
    st1. st1. st1. st1. st1.
    release_frame FR ST (bv_unsigned spe).
    apply evt_done. unfold pvW_post, vs_hdr_raw. eexists _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact VSH| exact SLOT].
  Qed.
End W.
End HCW.
