(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z04Npos35stdpp9bitvectorbdefinitionsi22bv37Corelib4Init9Datatypesk46optionk44prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~mc4bptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~qf5blockk43fstk43sndk44list37Corelib4Init5Logichh53andqf8blk_addrhh52exqf8blk_size36Stdlib5Lists4Listhkc2In46Stdlib6ZArith6BinInt1Zhm53addhm52lehm52lthh52orqf6RERRNOqf8RGOT_SSPqfaRSSP_GUARDqf7RVMLOCKqf4RCTXqf5RLIBChh53notqf8in_blockqfdralloc_staticqf3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hv82wahh52eqk44None3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsik55wview79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~io55rsegs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt2HC~~~~~~isbcrclient_addrhm53powisbarheap_pres69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~jje5hceil37Corelib5Lists7ListDefjo26Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jq33ivljq35munchjq35wmonoisbdrclient_rangehv88bytes_atk46lengthhm56of_nathv85wr_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kj18rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kn84cellkn8acells_sizehm56modulomc6PStateik5dmachine_state3h5LinuxProcessSemantics5Riscv7Preludekue5bvmapk44consi2bbv_unsignedk43nilk44pairmc5ps_famc5ps_soi27Z_to_bvk44unitkn82C4kn82CBjq33mkRjq33stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lna2MSlna6ret_pchv87mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~lt27seg_romisbcrblock_rangemc8ptr_addrhm56to_nat99OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt2HC5Iface~~~~~~mk1crmalloc_postqf4RATPqfdRMALLOC_STACKqfbRMALLOC_SYM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~msa5implMmcaraw_mallochm53submk1arfree_postqfbRFREE_STACKqf9RFREE_SYMmc8raw_freeisbh0rclient_write_okqfaRAUXV_CELLqf6blk_idjo23maphkc5NoDupmk1h6RHEAP_block_range_stmtmk1haRHEAP_blocks_disjoint_stmtmk1h7RHEAP_blocks_nodup_stmt" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RMALLOC_SYM : Z := 0xdfc04.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0xdfac4.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
Definition RATP : Z := 0x10ebf8.          (* [comment removed for export] *)
Definition RERRNO : Z := 0x10eb54.        (* [comment removed for export] *)
Definition RLIBC : Z := 0x12ee88.         (* [comment removed for export] *)
Definition RAUXV_CELL : Z := 0x12ee90.    (* [comment removed for export] *)
Definition RCTX : Z := 0x12f008.          (* [comment removed for export] *)
Definition RSSP_GUARD : Z := 0x12ec38.    (* [comment removed for export] *)
Definition RGOT_SSP : Z := 0xfbc78.      (* [comment removed for export] *)
Definition RVMLOCK : Z := 0x130030.       (* [comment removed for export] *)

Definition mem : ltac2:(zQ "00S") := ltac2:(zQ "30!hc!jf!lc>0@1$1@1$0#k0@1$2@1$1@1$0#8").
Definition block : ltac2:(zQ "00T") := ltac2:(zQ "30!m5!h9!q8@2$0@2$0$2$1$1").
Definition blk_id : ltac2:(zQ "20!va!q8>1b$0$1") := ltac2:(zQ "50!h9!hg2!q8!m5!va\1b$4@3$1$2$0@3$1@2$3$2$0$0^1").
Definition blk_addr : ltac2:(zQ "20!h9!va>1b$1$0") := ltac2:(zQ "60!h9!q8!hg2!m5!hg8!va\1b$5@3$4$1$0@3$2@2$3$1$0$0^1").
Definition blk_size : ltac2:(zQ "20!h9!va>1b$1$0") := ltac2:(zQ "50!h9!m5!hg8!va!q8\1b$3@3$2@2$1$4$0$0^1").
Definition in_block : ltac2:(zQ "30!hge!h9!va>2LB@1$0$2>1a$1P") := ltac2:(zQ "b0!va!hi9!hj0!hge!hjb!h9!hk1!hlf!hnd!ho4!hoa\2LB@1$3$0\1a$5@2$4$0\1b$0@2$1@3$7$0^1^3@2$1@2$9@1$2^1^2@2$a^2@2$8@1$2^1@1$6^1").

Definition ralloc_static : ltac2:(zQ "10!h9>1a$0P") := ltac2:(zQ "c0!hi9!hnd!ho4!hoa!hp0!hp6!hpf!hqa!hr7!h9!hs1!hs8\1a$9@2$4@2$0@2$2$b^1@2$3^1@2$1$a+jq0@2$4@2$0@2$2$5^1@2$3^1@2$1$5+4@2$4@2$0@2$2$7^1@2$3^1@2$1$7+8@2$4@2$0@2$2$6^1@2$3^1@2$1$6+8@2$0@2$2$8^1@2$3^1@2$1$8+4").

(* [comment removed for export] *)
Section HC.
  Context {HCEIL : HeapCeil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rclient_addr : ltac2:(zQ "30!h9!hge!va>2LB@1$1$2>2SP$0>1a$0P") := ltac2:(zQ "a0!hi9!hp0!h9!ho4!hge!ht0!va!ht7!hu2!hoa\2LB@1$4$6\2SP$2\1a$2@2$1@2$3^2^1@2$1@2$0@2$0@2$3+vkgg0^1@2$9^1+hjhgg0@1$5@1$8^1@2$7^3^1").

Definition rheap_pres : ltac2:(zQ "40!hv2!hge!h9!va>2LB@1$1$3>2SP$2>1m$0>2m'$0P") := ltac2:(zQ "h20!hc!jf!ij2!lc!ij8!ije!hi9!ht0!h9!inc!hv2!is2!hge!jh9!va!ho4!hoa!ji9\2LB@1$c$e\2SP$8\1m$a\2m'$a>1a$8>0@2$6@2$fZ^1@2$h0^1@2$h1+2+k0>0@3$d^6^5^2@2$6@3$4@1$3@1$1@1$0#8@1^4@1$2^3@1^5@1$2^3>0@1$7@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^3@1$5@1$1@1$0#8@1$7@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^4@1$5@1$1@1$0#8").

Lemma rheap_pres_refl : ltac2:(zQ "50!hge!h9!jj0!va!hv2>2LB@1$0$3>2SP$1>1m$4@4$2^3^2^1^1").
Proof. intros LB SP m a _ _. auto. Qed.

Lemma rheap_pres_trans : ltac2:(zQ "50!jj0!hv2!hge!h9!va>2LB@1$2$4>2SP$3>2m1$1>2m2$1>2m3$1>0@4$0^5^4^3^2>0@4$0^6^5^3^2@4$0^7^6^5^3").
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : ltac2:(zQ "70!va!hge!h9!jj0!hv2!hlf!ho4>2LB@1$1$0>3LB'@1$1$0>2SP$2>3SP'$2>1m$4>2m'$4>0@4$3^6^4^2^1>0@2$6^5^4>0>1b$0>0@3$5$0^1^8@3$5$0^2^a@4$3^8^6^5^4").
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_of_munch : ltac2:(zQ "h61!h9!hc!jf!va!ho4!hge!lc!m5!jn9!hg2!hg8!hi9!jp9!jtf!ju6!juf!jj0!hj0!hk1!is2!hlf!hnd&>0@1$2@1$1#k0@1$6@1$2@1$1#8>2LB@1$5$3>2SP$0>1W@1$5$d>1m~0>2m'~0>0@3$e^3^2^1>0@3$f$h3^3^2>0@3$c@2$7$0$0\2iv@2$7$0$0@2$b@2$4@1$8?5HCEIL@3$9$0$0^1@2$4@3$a$0$0^1^7^5>0>1b$3>0@3$h4$3^1^9@2$4@2$h5@1$h1^2@1$h2^2@1$8?5HCEIL@4$h0^9^8^6^5").
Proof.
  intros LB SP W m m' MU WM FW HB a Ha Hc.
  assert (OUT : outside W a).
  { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as [H1 H2]. cbn in H1, H2.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [lia| hcb; lia|].
    pose proof (HB b Hb). lia. }
  split.
  - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
  - intros Hw. apply WM. exact Hw.
Qed.

Definition rclient_range : ltac2:(zQ "30!h9!hge!va>2LB@1$1$2>2SP$0>1A$0>1n$0P") := ltac2:(zQ "h10!ho4!hnd!hi9!hp0!va!h9!hp6!hpf!hqa!hr7!hj0!hge!hjb!hs1!hs8!hk1!hlf\2LB@1$b$4\2SP$5\1A$5\1n$5@2$3@2$0^3^2@2$3@2$2@2$0+vkgg0^2@2$2@2$0@2$1^2^1+hjhgg0@2$2@2$3@2$0@2$1^2^1$e@2$0@2$1$d+jq0^2@2$2@2$3@2$0@2$1^2^1$6@2$0@2$1$6+4^2@2$2@2$3@2$0@2$1^2^1$8@2$0@2$1$8+8^2@2$2@2$3@2$0@2$1^2^1$7@2$0@2$1$7+8^2@2$3@2$0@2$1^2^1$9@2$0@2$1$9+4^2@2$c$4\1b$4@2$2@3$h0$4^1^5@2$2@2$0@1$a^1^3@2$0@2$1^3^2@2$1@1$a^1@1$f^1").

Lemma rclient_range_addr : ltac2:(zQ "90!h9!hge!hi9!jh9!jv8!va!hnd!ho4!hoa>2LB@1$1$5>2SP$0>1A$0>1n$0>1a$0>0@4$4^5^4^3^2>0@2$2@2$7^4^2@2$8^2@2$6^4^3@3$3^7^6^3").
Proof.
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

Lemma rclient_range_SP_mono : ltac2:(zQ "50!h9!jv8!hge!va!ho4>2LB@1$2$3>2SP$0>3SP'$0>1A$0>1n$0>0@4$1^5^4^2^1>0@2$4^4^5@4$1^7^5^4^3").
Proof. intros LB SP SP' A n [H|[H|H]] HS; [left; lia| right; left; exact H| right; right; exact H]. Qed.

Lemma rheap_pres_bytes_at : ltac2:(zQ "c0!hge!hc!h9!kg9!hv2!is2!jf!kh5!jv8!jj0!va!khe>2LB@1$0$a>2SP$2>1m$4>2m'$4>1A$2>2bs@1$0@1$6@1$1#8>0@4$9^6^5^4^3>0@4$3$5^5^3^2>0@4$8^8^7^4@1$b@2$7@1$6@1$1#8^3@4$3$5^6^5^4").
Proof.
  (intros LB SP m m' A bs HP nd_i1 HR; ndestruct nd_i1 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : ltac2:(zQ "80!h9!ki8!hv2!is2!hge!jv8!jj0!va>2LB@1$4$7>2SP$0>1m$2>2m'$2>1A$0>1n$0>0@4$6^6^5^4^3>0@4$1$3^5^3^2>0@4$5^8^7^4^3@4$1$3^6^5^4").
Proof.
  (intros LB SP m m' A n HP nd_i2 HR; ndestruct nd_i2 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : ltac2:(zQ "b0!hge!h9!kmc!hv2!is2!kr4!krc!jv8!jj0!va!khe>2LB@1$0$9>2SP$1>1m$3>2m'$3>1A$1>2cs@1$0$5>0@4$8^6^5^4^3>0@4$2$4^5^3^2>0@4$7^8^7^4@1$a@1$6^3@4$2$4^6^5^4").
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rblock_range : ltac2:(zQ "10!h9>1A$0>1n$0P") := ltac2:(zQ "90!hi9!ho4!h9!hnd!ij8!hp0!jn9!hoa!ksa\1A$2\1n$2@2$0@2$7Z^2@2$0@3$4$2@2$8^2+h0Z@2$0@2$1Z^1@2$0@2$1@2$3^2^1@1$6?5HCEIL@2$5@2$1@2$3^2^1+hggg0@2$1+hjhgg0^2").

(* [comment removed for export] *)
Definition rclient_write_ok : ltac2:(zQ "40!h9!hge!m5!va>2LB@1$1$3>2iv@2$2$0$0P") := ltac2:(zQ "h40!h9!ho4!hg2!hi9!hg8!hp0!hnd!va!hpf!hqa!hr7!hj0!hge!m5!hjb!jn9!hs1!hs8!hk1!hlf\2LB@1$c$7\2iv@2$d$0$0@2$5@2$1@1$f?5HCEIL@3$2$0$0^1@2$5@2$3@2$1+vkgg0@3$2$0$0^1@2$3@2$1@3$4$0$0^1+hjhgg0@2$3@2$5@2$1@3$4$0$0^1$h1@2$1@2$6$h0+jq4@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1$9@2$1@2$6$9+8@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1$8@2$1@2$6$8+8@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1$a@2$1@2$6$a+4@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1+vrpu0@2$1+vrqk0@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1+vrrg8@2$1+vrru8@3$2$0$0^1@2$3@2$5@2$1@3$4$0$0^1+vssv8@2$1+vstg0@3$2$0$0^1@2$5@2$1@3$4$0$0^1+vsuj8@2$1+vsuk8@3$2$0$0^1@2$e$7\1b$7@2$3@3$h3$7^1^3@2$3@2$1@1$b^1@3$2$0$0^2@2$1@3$4$0$0^2@2$6@1$b^1@1$h2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Iface.
  Context (RHEAP : PState -> list block -> mem -> Prop)
          (rauxv_ok : mem -> Z -> Prop)
          (raddr_exposed : PState -> Z -> Prop)
          (lb_remove : bptr -> list block -> list block).

Definition rmalloc_post : ltac2:(zQ "b0!hc!jf!h9!kt4!hge!lc!ktd!lh4!va!hv2!q8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$3>2LB@1$4$8>1n$2>2lo$2>1B$2>1m$9>1r@1$5$a>2s'$3>0$6P") := ltac2:(zQ "i81!hc!jf!hjb!hi9!h9!ij8!q8!lc!is2!m5!kr4!lhd!hge!li4!lj2!lj8!ktd!kmc!kt4!ljf!lk7!lkf!ije!ll9!lh4!lm0!lm6!lmc!ln3!lr7!lrd!ls7!mh1!mhc!jj0!va!hv2!mic!hnd!mj7&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$h2\2LB@1$c$i3\1n$4\2lo$4\1B$4\1m$i4\1r@1$7$6\2s'$h2\3ms'$h0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$3@3$5$h0^h2@7$hd@hf$hb^ic^ib^ia^i9^h1^h0^f^i8^i7^e^d^c^b^a^9^8^7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^6^5^4^3^hc@1$he^ic^hb@1$h6@1$1@1$0#k0^2@1$i0$8@2$3@2$hf$8^2@2$3@4$hc$8^2^h7@2$d@1$0#k0^ib@2$3@4$h1$8^2@2$i6@2$d@1$0#k0^i9-q4@3$b$a@1$h9^1@1$e$a@2$3@2?8rauxv_ok^2^h6@2$3@4$i2^h9@2$d@1$0#k0^ib^h5^2@2$3@3$5@2$9$4$4@1$h3^h3@1$h3^ha@2$3@3$5$h7@1$h4^h3@1$h4^haM7\1r@1$7$6P^h4\1p$6@2$2$4\1A$4@2$2@1$c@1$1@1$0#8\4junk@1$c@1$1@1$0#8@2$3@3$5@1$1@1$0#k0^h1@2$h5@1$0#k0^2@2$3@2$i1^2^hb@2$3@3?5RHEAP^h6@3$b@2$9@2$9$6$4$4@4$f@2$9$6$4$4@4$f$6$4^3^2^hb^hc^5@2$3@4$h1$8^5^2@3$b$a@2$ha@1$i7^hb^1@1$e$a>0@2?draddr_exposed^hd^hb@3$5$4^3@2$i5^h7^4@2$3@3$5@1$1@1$0#k0^e@2$h5@1$0#k0Z@3?5RHEAP^h3^h9^2").

Definition rmalloc_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i60!hc!jf!is2!ho4!li4!h9!lkf!ij8!kr4!kt4!ije!lhd!hge!lj2!lc!hi9!lh4!jn9!lm0!lmc!ln3!lr7!ls7!mh1!kmc!mp5!mq5!mqc!mrc!va!hv2!ng7!q8!nh0!hnd!hoa!ji9!nhd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$he>1s$9>2LB@1$c$hd>1n$5>2lo$5>1B$5>4errv@1$1@1$0#k0>0@3?5RHEAP^6^5^7>0@2?8rauxv_ok^8^3>0@2$3@2$4@1$0#k0^i9^4>0@4$h4$2^a^6@2$4@1$0#k0^ia>0@2$3@1$h1?5HCEIL^7>0@2$3^8@2$i5@2$4@1$0#k0^ic$hb>0@4$h8$2^d@2$i2@2$4@1$0#k0^ib-q4@3$b$8@1$h2^7@1$d$8>0@2$h6$2^e>0@3$7@1$1@1$0#k0^id@2$6@1$0#k0$ha>0@3$7@1$1@1$0#k0^i8@2$6@1$0#k0^d>0@2$f@2$3Z^e@2$i3^e@2$i4+2+i0@7$hf$9$2@1$e$i0@2$i1?5HCEIL^f^h1@h8$h9^j3^j2^j1^j0^ic^ib^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h4^h3^h1^h0^f^e^d^h2@7$h5@hf$h3^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4@2$6@1$0#k0$hc^h3@1$a@1$1@1$0#k0^h2@1$h7$2").

Definition rfree_post : ltac2:(zQ "b0!hc!jf!h9!kt4!hge!ll9!ktd!lh4!va!hv2!q8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$3>2LB@1$4$8>1p$a>2lo$2>1B$2>4errv@1$1@1$0#k0>1m$9>1r$5>2s'$3>0$6P") := ltac2:(zQ "i21!hc!jf!hjb!hi9!h9!is2!ij8!li4!lc!ll9!ktd!kr4!kt4!ljf!lk7!ije!lhd!hge!lj2!m5!lh4!lm0!lmc!ln3!lr7!lrd!ls7!mh1!kmc!jj0!va!hv2!q8!hnd&>0@1$1@1$0#k0@1$8@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h4@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$c\2LB@1$h1$he\1p$i0\2lo$4\1B$4\4errv@1$1@1$0#k0\1m$hf\1r$9\2s'$c\3ms'$a@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$3@3$6$a^h1@7$h8@hf$h6^ic^ib^ia^i9^h0^f^e^i8^i7^d^c^b^a^9^8^7^6^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^5^4^3^2^hc@1$h9^ic^hb@1$f@1$1@1$0#k0^1@1$hb$5@2$3@2$ha$5^1@2$3@4$h7$5^1^h7@2$7@1$0#k0^ib@2$3@4$hc$5^1@2$i1@2$7@1$0#k0^i9-q4@3$h0$b@1$h5^h5@1$h2$b@2$3@2?8rauxv_ok^1^h6@2$3@4$hd@2?9lb_remove^h8^h9@2$7@1$0#k0^ib^h4^1@2$3@3$6@2$h3$4$4@1$d^h2@1$d^ha@2$3@3$6$9@1$e^h2@1$e^ha@3?5RHEAP^h2@2?9lb_remove^h8^h9^1").

Definition rfree_stmt : ltac2:(zQ "00P") := ltac2:(zQ "i60!hc!jf!h9!is2!q8!li4!m5!ho4!lkf!lj8!ij8!kr4!kt4!ije!lhd!hge!lj2!ll9!lh4!jn9!lm0!lmc!ln3!lr7!ls7!mh1!kmc!ni4!mq5!nj2!nk0!va!hv2!ng7!nkc!hlf!hnd!nhd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i0>1s$c>2LB@1$f$hf>1p$4>1A$2>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>0@3?5RHEAP^8^7^9>0@3$i3@2$6@2$6$4$2$2@4$9@2$6$4$2$2@4$9$4$2^7^6^5^8>0@2?8rauxv_ok^b^4>0@2$7@2$5@1$0#k0^ic^5>0@4$h6$3^d^7@2$5@1$0#k0^id>0@2$7@1$h3?5HCEIL^8>0@2$7^9@2$i5@2$5@1$0#k0^if$hd>0@4$ha$3^h0@2$i4@2$5@1$0#k0^ie-q4@3$e$b@1$h4^8@1$h0$b>0@2$h8$3^h1>0@3$a@1$1@1$0#k0^j0@2$8@1$0#k0$hc>0@3$a@1$1@1$0#k0^ib@2$8@1$0#k0^f@7$i1$c$3$h1@2$i2?5HCEIL^h1^h3@h9$hb^j5^j4^j3^j2^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^h6^h5^h3^h2^h1^e^d^c^h4@7$h7@hf$h5^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6@2$8@1$0#k0$he^h5@1$d@1$1@1$0#k0^h4@1$h9$3").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RHEAP_frame_stmt : ltac2:(zQ "00P") := ltac2:(zQ "f0!hge!hc!h9!jf!lc!m5!jp9!jtf!ju6!juf!nl7!va!hv2!is2!kt4>1s$e>2LB@1$0$b>1m$c>2m'>0@1$3@1$1#k0@1$4@1$3@1$1#8>1W@1$0$7>0@3?5RHEAP^5^4^3>0@3$8^2^4^3>0@3$9$d^5^4>0@3$6@2$5$2$2@1$a^7^4@3?5RHEAP^9^8^6").
Definition rauxv_ok_frame_stmt : ltac2:(zQ "00P") := ltac2:(zQ "h30!h9!ho4!m5!hg8!hc!nmc!jf!hg2!hge!lc!hi9!hp0!jp9!jtf!ju6!juf!hv2!is2!hnd>1m$h0>2m'>0@1$6@1$4#k0@1$9@1$6@1$4#8>1B$0>1W@1$8$d>0@2?8rauxv_ok^4^2>0@3$e^2^5^4>0@3$f$h1^6^5>0@3$c@2$2$0$0\2iv@2$2$0$0@2$a@2$1@3$3$0$0^1^6@2$b@2$1@3$3$0$0^1$5@2$1@2$h2$5+8@3$7$0$0^1^4@2?8rauxv_ok^7^6").
Definition RHEAP_block_range_stmt : ltac2:(zQ "00P") := ltac2:(zQ "80!va!hge!mhc!hj0!hk1!hv2!kt4!hlf>1s$6>2LB@1$1$0>1m$5>1b$0>0@3?5RHEAP^4^3^2>0@3$7$0^2^4@2$2@1$3^3@1$4^3").
Definition RHEAP_blocks_disjoint_stmt : ltac2:(zQ "00P") := ltac2:(zQ "e0!va!hj0!nn9!hk1!hlf!hnd!ho4!hge!ij8!ht0!hp0!hv2!kt4!q8>1s$c>2LB@1$7$0>1m$b>2b1$0>2b2$0>0@3?5RHEAP^5^4^3>0@3$4$0^3^5>0@3$4$0^3^6>0@1$9@3$8$d@1$2^5@1$2^4@2$a@2$6@2$5@1$1^6@1$3^6@1$1^5@2$6@2$5@1$1^5@1$3^5@1$1^6").
Definition RHEAP_blocks_nodup_stmt : ltac2:(zQ "00P") := ltac2:(zQ "80!va!q8!hge!no2!nn9!hv2!kt4!no9>1s$6>2LB@1$2$0>1m$5>0@3?5RHEAP^3^2^1@2$7$1@4$3$0$1$4^3").

(* [comment removed for export] *)
Lemma fresh_block_disjoint_client : ltac2:(zQ "h00!h9!m5!q8!ho4!lj8!hnd!lhd!hge!hp0!jn9!np2!nqd!nsc!jv8!hv2!kt4>0$a>0$b>0$c>2s'$f>2LB@1$7@2$1@2$1$2$0$0>2m'$e>1p$2>1A$0>1n$0>2SP$0>1a$0>1k$0>0@3?5RHEAP^9@3$6@2$1@2$1$2$0$0@4$4@2$1$2$0$0@4$4$2$0^6^5^4^8^7>0@4$d^9^4^3^2>0@2$3@1$9?5HCEIL^5>0@2$3Z^4@2$8@2$3@2$5^6^5^9@2$3@2$5^9^8^6").
Proof.
  intros HBR HBD HND s' LB m' p A n SP a k HP HR CE Hk.
  pose proof (HBR _ _ _ (p, A, n) HP (or_introl eq_refl)) as (R1 & R2 & R3 & R4 & R5). cbn in R1, R2, R3, R4, R5.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]].
  - right. lia.
  - ndestruct H as (Ha & Hn & _). hcb. lia.
  - pose proof (HND _ _ _ HP) as ND. cbn in ND. inversion ND; subst.
    assert (NE : blk_id (p, A, n) <> blk_id b).
    { cbn. intros E. apply H3. apply in_map_iff. exists b. split; [symmetry; exact E| exact Hb]. }
    destruct (HBD _ _ _ (p, A, n) b HP (or_introl eq_refl) (or_intror Hb) NE) as [D|D]; cbn in D; lia.
Qed.
End Iface.
End HC.
(* [comment removed for export] *)
