(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMalloc_fp.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc3maxhc3mulhc3sub89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh0RAllocSlot_iface3HCW~~~~~~kc9RAS_STACKhc2lehc2lt04Npos35stdpp9bitvectorbdefinitionsr52bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~t76mstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hhe3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hm86PState3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshqedmachine_state3h5LinuxProcessSemantics5Riscv7Preludehv65bvmap37Corelib4Init5Logicii53andii52exii52eq01Nt74aptrt76regionr5bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~imd5rsegst7cget_meta_rect7aget_stride37Corelib4Init9Datatypesisf3snd25stdpp9countableiuebN_countable35stdpp7numbers1Njge6eq_decisf6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jj34cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMalloc_fp~~~~~~jn7armalloc_fpt7ec_mmap_countert73ctxt76r_basehm85ps_fahm84ps_mhm85ps_so25stdpp4gmapkg14gmapisf4Noneisf4Someisf4consisf3fstisf3nilisf4pairisf4prodisf4unitii52or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~kl93rdv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~kqa8ticks_okhhebbrk_link_pshhe8pans_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9Malloc_fp~~~~~~lh34mrellh37slot_oklh39unk_agreejj32C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lnb3mkRlnb3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ls52MSls56ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mh27mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ml77seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~mq18rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~mu85rmrep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~nj38rauxv_oknj3crpres_exceptt76activet74optrt79s_regionshc3pow25stdpp4basenr45emptyr57Z_to_bvkg1agmap_emptyisf3natnj36rimplTt71M69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~nv65hceilkc8ras_postmu84RATPmu8h1ralloc_slot_entryt7aalloc_slott78full_lay" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition RAS_STACK : ltac2:(zQ "10!h9>2sc$0$0") := ltac2:(zQ "50!h9!j4!ja!k0!k6\2sc$0@2$1+hj0@2$3+p0@2$2Z@2$4+hb^1").   (* [comment removed for export] *)

Lemma RAS_STACK_ge : ltac2:(zQ "30!h9!p9!q5>2sc$0@2$2+hj0@1$1^1").
Proof. intros sc. try hcb. try hsb. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_mono : ltac2:(zQ "30!h9!p9!q5>1a$0>1b$0>0@2$2^2^1@2$2@1$1^2@1$1^3").
Proof. intros a b. try hcb. try hsb. unfold RAS_STACK. lia. Qed.
Lemma RAS_STACK_nest : ltac2:(zQ "50!h9!p9!q5!j4!qa>2sc$0>1j$0>0@2$4^2^1>0@2$2^2+ha@2$2@2$3@1$1^3+p0@1$1^4").
Proof. intros sc j. try hcb. try hsb. unfold RAS_STACK. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post : ltac2:(zQ "80!qf!t2!h9!hh5!hm1!hq4!hu5!ihc>6as_inv>0$3>0$3>0$3>0$2>0$2P>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1o$4>1m$4>3st0$3>2st$3>1s$5>2lo$2>2sc$2>3req$2>3st1$3>3idx$2>2s'$5>0$6P") := ltac2:(zQ "k63!qf!t2!ij9!ik0!h9!j4!ik6!ikc!hh5!ikf!il6!ilf!iqa!ir3!is2!iu7!hm1!q5!k0!ivf!jhf!ji9!hu5!jmf!jr9!js7!jt8!jte!hq4!ju7!jv0!jv8!qa!k6!kgd!kh5!khd!ki5!kid!kj4!kjb!kk3!kkb!kl3!ihc!kq3!kuc!kv8!lg7!ll5!lld!lm8!ln5!lr7!lre!mg2!mg8!mkc!mp6!mtc!nia!nn6!no2!np2!npb!nq2!nqe!ns0!ns9!nt3&>0@1$1@1$0#k0@1$h5@1$1@1$0#8&@2$5@2$5@1$hb^2@3$f$7$4^3+h0&@2$5~1@2$h2@1$e@2$d^h8^4^h7\6as_inv>0$8>0$8>0$8>0$4>0$4P\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$ic@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1o$h0\1m$h0\3st0$8\2st$8\1s$hc\2lo$4\2sc$4\3req$4\3st1$8\3idx$4\2s'$hc\3ms'$h6@2$3@1$1@1$0#k0\2t0@1$1@1$0#k0@2$3@1$1@1$0#k0\2t1@1$1@1$0#k0@2$3@1$1@1$0#k0\2t2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a1@1$1@1$0#k0@2$3@1$1@1$0#k0\2a2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a3@1$1@1$0#k0@2$3@1$1@1$0#k0\2a4@1$1@1$0#k0@2$3@1$1@1$0#k0\2a5@1$1@1$0#k0@2$3@1$1@1$0#k0\2a6@1$1@1$0#k0@2$3@1$1@1$0#k0\2a7@1$1@1$0#k0@2$3@1$1@1$0#k0\2t3@1$1@1$0#k0@2$3@1$1@1$0#k0\2t4@1$1@1$0#k0@2$3@1$1@1$0#k0\2t5@1$1@1$0#k0@2$3@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3~0\2m'~0@2$3@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2@3$6$h6^h1@7$j7@hf$j5^ie^id^ic^ib^h0^f^e^ia^i9@2$k4@1$0#k0^h3^d^c^b^a^9^8^7^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^6^5^4^3^he@1$j8^ie^hd@1$i3@1$1@1$0#k0^2@1$ja$c@2$2@2$j9$c^2@2$2@4$j6$c^2^h7@2$b@1$0#k0^id@2$2@4$jb$c^2@2$5@2$b@1$0#k0^ib-q4@3$i5$h7@1$j4^1@1$i7$h7@2$2@4$jd?5HCEIL?4HSEC^2@2$b@1$0#k0^id@2$2@4$jc?5HCEIL?4HSEC^h4^2@2$2@1$ie^h4@2$2@3$j3^h4^hc^2@2$2@3$je@4$h8^ha^h4^h7@2$b@1$0#k0^id^hb^2@2$2@2$j1^h9^h4@2$2@2$if^h4^h2@2$2@3$6$8@1$he^h2@1$he^h8@2$2@3$6@2$i9$4$4@1$hd^h2@1$hd^h8@2$2@3$6$ia@1$hf^h2@1$hf^h8@2$2@5^if^ha^h9^h4^h6^h3@2$2@2$2@2$h1Z@1$h9@1$ha^h4@2$i0@1$h9@1$ha^h4@2$k2+2+i0@2$ib@3$6$4^h3-1@2$2@2$h1Z^h3@2$3$9\1g$9@2$3$9\1b$9@2$3$a\1r$a@2$2@3$6$k0@2$jf^h7^h9@2$i4$9^3@2$2@6$j2^h7^3^2^1^h6^h8@2$2>1a$4>0@2$2@2$h1@2$i1~2+4^1@2$i0^1@2$i1@2$5~2@1$e@2$d^h8^4+4@5$h8^hf^h9^hc@2$b@1$0#k0^j2^2>0@3$6@4$i2$7$h4$h3$a@1$k1^hd@2$k3@4$i2$7$h4$h3$a@4$k5$7$h4$h3$a@3$6$4@5$id$h0$j0^i0^h8@4$i8$7$4@3$i6$7$4^3@2$5@2$5@3$f$7$4^3@2$5+h0@2$h2@1$e@2$d^h8^4^h7-3Z").

Definition ralloc_slot_stmt : ltac2:(zQ "30!hh5!h9!nu1>6as_pre>0$0>0$0>0$1>0$1>0$2P>6as_inv>0$0>0$0>0$0>0$1>0$1PP") := ltac2:(zQ "i91!qf!t2!h9!hh5!iqa!ns9!ilf!ik6!hq4!nu1!hu5!hm1!jmf!nu8!nv2!q5!kh5!ki5!kj4!ihc!kuc!kv8!lm8!oj1!ln5!lr7!lre!mg2!mkc!mp6!mtc!p9!oja!ok5!okd!nia!nn6!om3!on0!j4!k6&@3$7@1$1@1$0#k0^ib@2$5@1$0#k0^f\6as_pre>0$3>0$3>0$2>0$2>0$9P\6as_inv>0$3>0$3>0$3>0$2>0$2P>4fuel$9>1RT>1k>0$3>0$2@1$e^3>4bail@1$e^2>1o$b>1s$8>1Q>0^5>0$8>0$aP>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h3@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$b>3st0$3>2st$3>2lo$2>2sc$2>3req$2>4errv@1$1@1$0#k0>0@5^j1^6^5^3^2^if>0@4$i3?5HCEIL?4HSEC^6^8>0@1$h4^7>0@3$h6^8^ie^a>0@2$h5^9^ie>0@4$i4?5HCEIL?4HSEC^c@2$6@1$0#k0^ic>0@4$ha$4^d^a@2$6@1$0#k0^id>0@2$f@1$h7?5HCEIL^b>0@2$f^c@2$i8@2$6@1$0#k0^if@1$hf^b>0@4$he$4^h0@2$i7@2$6@1$0#k0^ie-q4@3$h1$c@1$h8^a@1$h2$c>0@2$hc$4^h1>0@3$7@1$1@1$0#k0^j0@2$5@1$0#k0$i1>0~0>0~0>0>3st1$3>3idx$2>2s'$8>3ms'$a>0@hf$i0^k2^ja^j9^j8^j7^j3^j2^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hb^ha^jd^h9^h8^h7^jc^h6^h5^h4^4^3^2^1@7$d?5HCEIL^k1^je@2^k0^5^4^3^jc^2@7$d?5HCEIL^jd^ja@8$i5^jd$i6^je^h4^h2^h1^jc^jb^j9^j8@7$hb@hf$h9^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@2$5@1$0#k0$i2^h7@1$h0@1$1@1$0#k0^h6@1$hd$4").

End HCW.


(* [comment removed for export] *)
