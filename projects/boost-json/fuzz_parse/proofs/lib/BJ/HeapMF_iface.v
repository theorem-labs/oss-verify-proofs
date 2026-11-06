(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJFrame.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hcdRMALLOC_STACK46Stdlib6ZArith6BinInt1Zn63addhcbRFREE_STACK3h5LinuxProcessSemanticsfLinuxProcessSem3Runq26config79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~t75hs_SR04Npos35stdpp9bitvectorbdefinitionshi72bv37Corelib4Init5Logichka3andhka2eq37Corelib4Init9Datatypeshmb4prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshobdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Stateht35Modelhmb4Nonehmb4listhmb3nilhmb6optionq29cfg_modelq26cfg_msq25mkCfght38m_haltedht39m_vm_lazy79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~im13evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~iq35rsegst77hs_KREL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~iv26PStatet78hs_MPRESt78hs_RHEAPhch0RHEAP_frame_stmthch6RHEAP_block_range_stmthchaRHEAP_blocks_disjoint_stmthch7RHEAP_blocks_nodup_stmtt7bhs_rauxv_okhch3rauxv_ok_frame_stmthc5blockhc3mem36Stdlib7SortingbPermutationju8bPermutationiv24bptrt7chs_lb_removehmb4cons36Stdlib5Lists4Listkj22Inhmb4pairhka3nothc6blk_id37Corelib5Lists7ListDefkm33map3h5LinuxProcessSemantics5Riscv7Preludeko15bvmaphka2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kr64cellhi7bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lg98rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ll02wzhka2orkr62C4kr62CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lq33mkRlq33stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lud2MSlud6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mja7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mnf7seg_romhccrblock_rangehcarheap_presn66to_natn62le89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface5Iface~~~~~~mv3emalloc_mf_post69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~nkd5hceilhc4RATPn62ltn63pown63submv3h1malloc_mf_stmt_athcbRMALLOC_SYMmv3h0RMALLOC_REPLACEDhob6ms_memt7eRALIGNED_ALLOCmv3cfree_mf_postmv3ffree_mf_stmt_athc9RFREE_SYMt76ROPDELt77ROPDEL2t75framet75fr_spt79eh_staticmja2wahob5wviewhccrclient_addrt75fr_fnt78eh_fsizet76eh_slomv38chain_spt7beh_chain_okmv38in_saves79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJFrame~~~~~~orb7rin_ivst77eh_idlet77fr_livet7bfr_callsitehmb4boolhmb4truet74c_spt7h1eh_agrees_unsavedt7beh_saves_okt7aeh_site_okt75fr_ramv3dRLLVM_FUZZ_CSmv3dRLLVM_FUZZ_FNt7aeh_base_okt73csrt74c_s0t74c_s1t75c_s10t75c_s11t74c_s2t74c_s3t74c_s4t74c_s5t74c_s6t74c_s7t74c_s8t74c_s9hmb4Somehmb3appmv36at_padt74eh_Xt76eh_padt78exc_livehc8in_blockmv3eRUNWIND_RESUMEmv37eh_prest78eh_STACKt7eeh_resume_sitet7eeh_unsaved_nowt75mkCSRmv3h1RLLVM_AFTER_CATCHmv3fRLLVM_CATCH_PADmv3dopnew_ok_postt76ROPNEWt7cROPNEW_STACKmv39KREL_lawsmv3aMPRES_lawsmv3h1RHEAP_block_rangemv3h5RHEAP_blocks_disjointmv3h2RHEAP_blocks_nodupmv3bRHEAP_framemv3aRHEAP_permmv37SR_lawsmv3h0eh_X_LB_perm_lawmv3eeh_X_nopad_lawmv3ceh_X_pad_lawmv3ceh_catch_lawmv3h1eh_chain_base_lawmv3h1eh_chain_cons_lawmv3h2eh_chain_frame_lawmv3h1eh_idle_frame_lawmv3deh_resume_lawmv3h2eh_saves_frame_lawmv3h0eh_slo_range_lawmv3h3eh_static_range_lawmv3h2exc_live_frame_lawmv3cfree_mf_stmtmv3elb_remove_lawsmv3emalloc_mf_stmtmv3eopdel2_mf_stmtmv3dopdel_mf_stmtmv3dopnew_mf_stmtmv3brauxv_framet73hmft73ehk" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROPNEW    : Z := 0xf00d0.   (* [comment removed for export] *)
Definition ROPDEL    : Z := 0x94490.   (* [comment removed for export] *)
Definition ROPDEL2   : Z := 0x94494.   (* [comment removed for export] *)
Definition ROPDELA   : Z := 0x94498.   (* [comment removed for export] *)
Definition RALIGNED_ALLOC : Z := 0xdc760.  (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROPNEW_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!m6!oe@2$1+h0$0").   (* [comment removed for export] *)
Definition ROPDEL_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!p4$0").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Record hmf := {
  hs_SR        : (config -> Prop) -> config -> Prop ;
  hs_KREL      : PState -> Model -> Prop ;     (* [comment removed for export] *)
  hs_MPRES     : Model -> Model -> Prop ;      (* [comment removed for export] *)
  hs_RHEAP     : PState -> list block -> mem -> Prop ;
  hs_rauxv_ok  : mem -> Z -> Prop ;
  hs_lb_remove : bptr -> list block -> list block
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record csr := mkCSR { c_sp : word ; c_s0 : word ; c_s1 : word ; c_s2 : word ; c_s3 : word ; c_s4 : word ;
                      c_s5 : word ; c_s6 : word ; c_s7 : word ; c_s8 : word ; c_s9 : word ; c_s10 : word ; c_s11 : word }.

(* [comment removed for export] *)
Record frame := mkFrame {
  fr_fn       : Z ;              (* [comment removed for export] *)
  fr_callsite : Z ;              (* [comment removed for export] *)
  fr_sp       : Z ;              (* [comment removed for export] *)
  fr_ra       : word ;           (* [comment removed for export] *)
  fr_live     : csr              (* [comment removed for export] *)
}.

Record ehk := {
  eh_chain_ok : list frame -> mem -> Prop ;
  (* [comment removed for export] *)
  eh_site_ok  : Z -> Z -> bool ;                 (* [comment removed for export] *)
  eh_saves_ok : frame -> csr -> mem -> Prop ;    (* [comment removed for export] *)
  eh_agrees_unsaved : frame -> csr -> Prop ;     (* [comment removed for export] *)
  eh_unsaved_now : frame -> csr -> Prop ;        (* [comment removed for export] *)
  eh_base_ok  : Z -> Prop ;                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  eh_X        : list frame -> PState -> list block -> Z -> Z -> bv 32 -> config -> Prop ;
                (* [comment removed for export] *)
  exc_live    : list frame -> word -> list block -> mem -> Prop ;   (* [comment removed for export] *)
  eh_pad      : Z -> Z -> option Z ;   (* [comment removed for export] *)
  eh_resume_site : Z -> Z -> bool ;    (* [comment removed for export] *)
  eh_fsize    : Z -> Z ;               (* [comment removed for export] *)
  eh_slo      : Z -> Z ;               (* [comment removed for export] *)
  eh_STACK    : Z ;                    (* [comment removed for export] *)
  eh_idle     : mem -> Prop ;          (* [comment removed for export] *)
  eh_static   : Z -> Prop              (* [comment removed for export] *)
}.

Section Iface.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!suf$0").
  Variable E : ltac2:(zQ "10!sv5$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).  Notation rauxv_ok := (hs_rauxv_ok H).  Notation lb_remove := (hs_lb_remove H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SR_laws : ltac2:(zQ "00P") := ltac2:(zQ "h41!se!hh9!hi1!hk4!hle!hm5!ho3!hs2!ig1!iga!ih2!iha!ii1!iib!ij7!ik0!ik8!il4!ipc!itf&@2$6@1$3@1$2#k0@1$3@1$2#k0@2$4>1Q>0$0P>1c$0>0@1^2^1@3$1?1H^3^2@2$4>1Q>0$0P>2Q'>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@1^5^2@3$1?1H^4^3@2$4>2Q1>0$0P>2Q2>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@3$1?1H^5^2@3$1?1H^4^3>1P>0$7P>2ms$7>2mo$8>0@3$5@1$c@1$3@1$2#k0@1$h0^1@1$9@1$3@1$2#k0>0@3$5@1$a~0@1$h1^2@1$b~0>0@3$h2$h3^5^4@3$1?1H\1c$0@2$4@1^7@1$e^1@3$5$8@1$d^1^5@2$f^5^4").
  Definition KREL_laws : ltac2:(zQ "00P") := ltac2:(zQ "e1!hi1!hk4!ho3!hm5!iga!ih2!iha!ii1!hle!ig1!ik8!il4!iu8!jie&@2$2@1$1@1$0#k0@1$1@1$0#k0>1s$d>2mo$9>0@3$c?1H^2^1@2$8@3$3@1$7@1$1@1$0#k0@1$a^2@1$4@1$1@1$0#k0@3$3@1$5~0@1$b^2@1$6~0").
  Definition MPRES_laws : ltac2:(zQ "00P") := ltac2:(zQ "30!ig1!jj8!hle@2$2>2mo$0@3$1?1H^1^1>3mo1$0>3mo2$0>3mo3$0>0@3$1?1H^3^2>0@3$1?1H^3^2@3$1?1H^5^3").
  Definition RHEAP_frame : ltac2:(zQ "00P") := ltac2:(zQ "20!jk3!jke@2$1?5HCEIL@1$0?1H").
  Definition RHEAP_block_range : ltac2:(zQ "00P") := ltac2:(zQ "20!jk3!jm2@2$1?5HCEIL@1$0?1H").
  Definition RHEAP_blocks_disjoint : ltac2:(zQ "00P") := ltac2:(zQ "20!jk3!jnc@1$1@1$0?1H").
  Definition RHEAP_blocks_nodup : ltac2:(zQ "00P") := ltac2:(zQ "20!jk3!jpa@1$1@1$0?1H").
  Definition rauxv_frame : ltac2:(zQ "00P") := ltac2:(zQ "20!jr5!js3@1$1@1$0?1H").
  (* [comment removed for export] *)
  Definition RHEAP_perm : ltac2:(zQ "00P") := ltac2:(zQ "60!jta!ih2!jk3!ju2!jie!kg4>1s$4>2LB@1$1$0>3LB'@1$1$0>1m$3>0@4$2?1H^4^3^1>0@3$5$0^4^3@4$2?1H^6^4^3").
  Definition lb_remove_laws : ltac2:(zQ "00P") := ltac2:(zQ "e0!jta!kh3!h9!ih2!khb!kia!ho3!hm5!kk5!kkb!hle!kl3!kla!kna@2$a>1p$1>1A$2>1n$2>2LB@1$3$0>0@1$b@3$8$1^4@4$d$0$1$c^1@3$7@1$3$0@3$4?1H^5@3$5@2$6@2$6$1$2$2@4$9@2$6$1$2$2@4$9$1$2^5^4^3^2^2@2$a>1p$1>1b$0>2LB@1$3$0>0@1$b@3$7$1@1$c^2^3@3$7@1$3$0@3$4?1H^4@3$5$0^3^2@3$5$0^3@3$4?1H^4^2>1p$1>2LB@1$3$0>1b$0>0@3$8$0^1@3$4?1H^3^2@3$8$0^2^3").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_mf_post : ltac2:(zQ "a0!hi1!hk4!h9!ih2!se!ig1!kq7!jta!ju2!jie>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1n$2>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "id1!hi1!hk4!kr0!hle!h9!itf!kh3!kv2!kia!ih2!ho3!hm5!jie!kva!iha!ii1!kkb!iib!jk3!lk4!lob!iga!lp1!hs2!ij7!se!ig1!kq7!iu8!jj8!jr5!lp7!lpd!ltf!lu6!mia!mj0!mn4!mre!jta!ju2!ms9!mt8!oe!mu5&>0@1$1@1$0#k0@1$f@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$hb@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$c\2LB@1$9$i7\1n$4\2lo$4\1B$4\1m$i8\2mo$ha\1c$h9@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2$c\2s'$c@2$3@3$b$h7@1$h8^h3@7$i3@hf$i1^ic^ib^ia^i9^h2^h1^h0^i8^i7^f^e^d^c^b^a^9^8^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^7^6^5^4^hc@1$i4^ic^hb@1$h5@1$1@1$0#k0^3@1$i6$5@2$3@3$hc?1H^1@1$h1^h3@2$3@3$hd?1H^h4@1$h1^h3@2$3@2$i5$5^3@2$3@4$i2$5^3^h7@2$d@1$0#k0^ib@2$3@4$h3$5^3@2$ib@2$d@1$0#k0^i9-q4@3$8$7@1$hf^2@1$e$7@2$3@3$he?1H^3^h6@2$3@4$ia^h9@2$d@1$0#k0^ib^h5^3@2$h6@2$3@3$b@1$1@1$0#k0^f@1$h4Z@4$h2?1H^1^h9^3@2$2$4\1A$4@2$2@1$9@1$1@1$0#8\4junk@1$9@1$1@1$0#8@2$2$6\1p$6@2$3@3$b@1$1@1$0#k0^h2@1$h4^3@2$3@3$i9?5HCEIL^3^hb@2$3@4$h2?1H^4@3$8@2$a@2$a$6$4$4@4$h0@2$a$6$4$4@4$h0$6$4^1^3^hb^hc^6@4$h3$5^6^3@3$8$7@2$i0@1$ic^hb^2@1$e$7").

  Definition malloc_mf_stmt_at : ltac2:(zQ "10!h9>5entry$0>5stack$0P") := ltac2:(zQ "i60!hi1!hk4!h9!itf!mue!kva!lob!hm5!kv2!iga!kia!ih2!iha!hle!ik0!ig1!kq7!njb!iu8!jk3!hh9!jr5!no8!lp7!ltf!lu6!mia!mn4!mre!lk4!np1!jta!ju2!jie!oe!np8!npd!nq3\5entry$2\5stack$2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i0>1s$i1>2LB@1$b$hf>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$f>0@4$h3?1H^7^6^8>0@3$h2?1H^8^2>0@3$h5?1H^a^5>0@2$4@2$5@1$0#k0^ib^6>0@4$h9$3^c^8@2$5@1$0#k0^ic>0@2$4@1$h6?5HCEIL^9>0@2$4^a@2$i5@2$5@1$0#k0^ie^j0>0@4$hd$3^f@2$i2@2$5@1$0#k0^id-q4@3$a$8@1$h7^9@1$c$8>0@2$hb$3^h0>0@3$7@1$1@1$0#k0^if@1$6$he>0@3$7@1$1@1$0#k0^ia@1$6^f>0@2$d@2$4+1^h0@2$i3^h0@2$i4+2+i0@3$h4?1H@h9$h1^j5^j4^j3^j2^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^h6^h5^h3^h2^h1^h0^f^h4^d@2$e@7$ha@hf$h8^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6@1$6^j7^h5@1$9@1$1@1$0#k0^h4@1$hc$3^d").
  Definition malloc_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "30!nq9!m6!nrf@2$0$2$1").

  (* [comment removed for export] *)
  Definition RMALLOC_REPLACED : Z := 0x12be68.
  Definition aligned_alloc16_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "ic0!hi1!hk4!kv2!lob!itf!mue!kva!kia!iha!hm5!h9!lp7!lk4!hle!nsd!oe!iga!ih2!nu2!ij7!se!ik0!ig1!kq7!njb!nuc!iu8!jk3!hh9!jr5!no8!ltf!lu6!mia!mn4!mre!np1!m6!jta!ju2!jie!np8!npd!nq3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i7>1s$i8>2LB@1$h1$i6>1n$a>2lo$a>1B$a>4errv@1$1@1$0#k0>2mo$h6>0@4$hb?1H^7^6^8>0@3$ha?1H^8^2>0@3$hd?1H^a^5>0@2$5@2$6@1$0#k0^ib^6>0@4$i0$4^c^8@2$6@1$0#k0^ic>0@2$5@1$he?5HCEIL^9>0@2$5^a@2$ib@2$6@1$0#k0^ie@2$f+i0$i5>0@4$c$4^f@2$f@2$6@1$0#k0^id-q4@3$7$2@1$b^9@1$8$2>0@2$i2$4^h0>0@3$9@1$1@1$0#k0^if@1$3$i4>0@4$c$4^h2$e@3$7$2@1$b@1$3Z@1$8$2>0@3$9@1$1@1$0#k0^ib@1$3+h0>0@3$9@1$1@1$0#k0^ib@1$3^h1>0@2$d@2$5+1^h2@2$i9^h2@2$ia+2+i0@3$hc?1H\1c$h4@2$d@ha$h8^j8^j7^j6^j5^j1^j0^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^h9^h8^h6^h5^h4^h3^h2^h7^h0^1@4$c$4@1$h2@1$h3^1$e@3$7$2@1$b@1$3Z@1$8$2@2$h5@7$i1@hf$hf^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@1$3$h9^h7@1$h0@1$1@1$0#k0^h6@1$i3$4^f").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_mf_post : ltac2:(zQ "b0!hi1!hk4!h9!ih2!se!ig1!kq7!jta!ju2!jie!kh3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1p$a>2lo$2>1B$2>4errv@1$1@1$0#k0>1m$8>2mo$5>0$4P") := ltac2:(zQ "i71!hi1!hk4!kr0!hle!itf!jie!kva!ii1!h9!iib!khb!kv2!iga!kia!ih2!iha!hm5!hs2!ij7!se!ig1!kq7!iu8!jj8!jk3!jr5!lp7!ltf!lu6!mia!mj0!mn4!mre!lk4!jta!ju2!mt8!kh3!oe&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$5\2LB@1$e$i2\1p$i5\2lo$8\1B$8\4errv@1$1@1$0#k0\1m$i3\2mo$h4\1c$h3@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$5\2s'$5@2$3@3$h0$h1@1$h2^h2@7$hd@hf$hb^ic^ib^ia^i9^h1^h0^f^i8^i7^e^d^c^b^a^9^8^7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^6^5^4^3^hc@1$he^ic^hb@1$c@1$1@1$0#k0^2@1$i0$4@2$3@3$h6?1H^1@1$9^h2@2$3@3$h7?1H^h3@1$9^h2@2$3@2$hf$4^2@2$3@4$hc$4^2^h7@2$6@1$0#k0^ib@2$3@4$i1$4^2@2$i6@2$6@1$0#k0^i9-q4@3$d$b@1$ha^h5@1$f$b@2$3@3$h9?1H^2^h6@2$3@4$i4@3$a?1H^h8^h9@2$6@1$0#k0^ib^h4^2@4$h8?1H^1@3$a?1H^h8^h9^2").

  Definition free_mf_stmt_at : ltac2:(zQ "10!h9>5entry$0P") := ltac2:(zQ "i80!hi1!hk4!h9!itf!kh3!kva!ho3!lob!mue!kkb!hm5!kv2!iga!kia!ih2!iha!ik0!ig1!kq7!nvd!iu8!jk3!hh9!jr5!no8!lp7!ltf!lu6!mia!mn4!mre!lk4!np1!p4!jta!ju2!jie!kk5!oe!nq3\5entry$2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i3>1s$i4>2LB@1$e$i2>1p$4>1A$2>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$h1>0@4$h5?1H^9^8^a>0@3$h4?1H^a^2>0@3$i5@2$6@2$6$4$2$2@4$9@2$6$4$2$2@4$9$4$2^9^8^7^a>0@3$h7?1H^d^6>0@2$8@2$5@1$0#k0^ie^7>0@4$hb$3^f^9@2$5@1$0#k0^if>0@2$8@1$h8?5HCEIL^a>0@2$8^b@2$i7@2$5@1$0#k0^j1$i1>0@4$hf$3^h2@2$i6@2$5@1$0#k0^j0-q4@3$d$b@1$h9^a@1$f$b>0@2$hd$3^h3>0@3$a@1$1@1$0#k0^j2@1$7$i0>0@3$a@1$1@1$0#k0^id@1$7^h1@3$h6?1H@ha$h3^j7^j6^j5^j4^j0^if^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^h8^h7^h5^h4^h3^h0^f^e^h6^d@2$h0@7$hc@hf$ha^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@1$7^j8^h7@1$c@1$1@1$0#k0^h6@1$he$3^d").
  Definition free_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!ogd!oi0@1$0$1").
  Definition opdel_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!ogd!oic@1$0$1").
  Definition opdel2_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!ogd!oj5@1$0$1").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition chain_sp : ltac2:(zQ "30!ih2!h9!ojf>1G@1$0$2$1") := ltac2:(zQ "50!ih2!ojf!h9!ok7!npd\1G@1$0$1M0\1G@1$0$1$2^1@2$4+2+k0\1f$1\1l@1$0$1@1$3^2").
  (* [comment removed for export] *)
  Definition EH_IVS : ltac2:(zQ "30!h9!ih2!ho3@1$1@2$2$0$0") := ltac2:(zQ "50!h9!ho3!kia!kkb!iha@3$2@2$1$0$0@4$3$0$0+hgpso8+hgpur0@3$2@2$1$0$0@4$3$0$0+hgrlu0+hgrlu7@1$4@2$1$0$0").
  Definition eh_static_range_law : ltac2:(zQ "00P") := ltac2:(zQ "60!hle!mue!np8!lp1!h9!okf>1a$4>0@2$5?1E^1@2$3@2$0@2$1+hgpso8^2@2$2^2+hgpur0@2$0@2$1+hgrlu0^2@2$2^2+hgrlu7").
  (* [comment removed for export] *)
  Definition eh_pres : ltac2:(zQ "40!ju2!ih2!h9!jta>2LB@1$1$3>2SP$2>1m$0>2m'$0P") := ltac2:(zQ "h30!hi1!hk4!olb!ii1!hm5!kl3!iga!hle!h9!om1!ju2!itf!ih2!okf!jta!oma!mue!np8!npd\2LB@1$c$e\2SP$8\1m$a\2m'$a>1a$8>0@2$7@2$h0Z^1@2$h1^1@2$h2+2+k0>0@3$f^6^5^2>0@1$5@2$d?1E^3@2$7@3$4@1$3@1$1@1$0#8@1^5@1$2^4@1^6@1$2^4>0@1$5@3$4@1$3@1$1@1$0#8@3$9$b^6@1$2^4@1$6@1$1@1$0#8@1$5@3$4@1$3@1$1@1$0#8@3$9$b^6@1$2^5@1$6@1$1@1$0#8").
  (* [comment removed for export] *)
  Definition in_saves : ltac2:(zQ "30!ih2!h9!ojf>1G@1$0$2>1a$1P") := ltac2:(zQ "d0!ojf!hle!on9!ok7!oe!ih2!kr0!h9!oo1!ooc!kk5!mue!np8\1G@1$5$0\1a$7@2$6$0\1f$0@2$1@3$a$0^1^3@2$1@2$b@2$4@1$3^1@2$9?1E@1$2^1^2@2$c^2@2$4@1$3^1@2$8?1E@1$2^1").
  Definition eh_chain_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "h40!hi1!hk4!ii1!olb!hm5!iga!hle!kl3!h9!om1!op5!oq1!itf!mue!np8!npd!ih2!oqf!ojf!ju2>1G@1$h0$h2>1m$h3>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@3$b?1E^3^2>0>1a$8>0@2$6@2$d@1$a^5^1@2$e^1@2$f+2+k0>0@2$h1^6^2@3$4@1$2@1$1@1$0#8@1^5@1$3^3@1^6@1$3^3>0>1a$8>0@2$6@2$d@1$a^6^1@2$e^1@2$f+2+k0>0@1$7@3$4@1$2@1$1@1$0#8@3$9$c^6@1$3^2@1$5@1$1@1$0#8@1$7@3$4@1$2@1$1@1$0#8@3$9$c^6@1$3^3@1$5@1$1@1$0#8@3$b?1E^6^4").
  Definition eh_slo_range_law : ltac2:(zQ "00P") := ltac2:(zQ "50!ooc!mue!hle!h9!oo1>2fn$3@2$2@2$1Z@2$0?1E^1@2$1@2$0?1E^1@2$4?1E^1").
  (* [comment removed for export] *)
  Definition saves_clear : ltac2:(zQ "40!ih2!h9!ho3!ojf>1G@1$0$3>1X@1$0@2$2$1$1P") := ltac2:(zQ "f0!h9!ojf!ih2!on9!ok7!oe!ho3!hle!kl3!ov8!oo1!ooc!kk5!mue!np8\1G@1$2$1\1X@1$2@2$6$0$0>1f$1>1a$0>0@3$c$1^2^4>0@2$7@2$d@2$5@1$4^3@2$b?1E@1$3^3^2@2$e^2@2$5@1$4^3@2$a?1E@1$3^3@1$8@2$9^5^3").
  Definition eh_idle_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "d0!hi1!hk4!ii1!pg3!olb!hle!hm5!h9!okf!ju2!mue!np8!npd>1m$9>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@2$3?1E^2>0>1a$7>0@2$5@2$aZ^1@2$b^1@2$c+2+k0>0@2$8?1E^2@3$6@1$2@1$1@1$0#8@1^5@1$4^3@1^6@1$4^3@2$3?1E^3").
  (* [comment removed for export] *)
  Definition eh_chain_cons_law : ltac2:(zQ "00P") := ltac2:(zQ "h80!ojf!hm5!kia!pgd!ok7!hi1!h9!oq1!ph7!on9!oe!pi5!ih2!pid!pj5!pjc!oo1!pl1!plf!pmc!lob!ju2!hk4!kva>1G@1$c$0>1g$0>1f$0>1m$h5>0@3$7?1E@3$2$0^3^4^1>0@3$1$b@3$h2?1E@1$9^3@1$8^3$d>0@3$1$6@2$h7@1$5#k0@1$e@1$3^4@1$4^4>0@3$1$6@2$a@1$4^5@2$h0?1E@1$9^5@1$4^6>0@3$1@1$h6@1$5#k0@1$h3^6@1$h4@2$a@1$8^7+4>0@4$h1?1E^7@1$3^8^6>0@3$f?1E^8@1$3^9@3$7?1E@3$2$0^9@3$2$0^a^b^8").
  (* [comment removed for export] *)
  Definition RLLVM_FUZZ_FN : Z := 0x47978.
  Definition RLLVM_FUZZ_CS : Z := 0x47980.
  Definition eh_chain_base_law : ltac2:(zQ "00P") := ltac2:(zQ "h10!hm5!h9!ojf!ok7!kia!iha!hi1!pn4!po5!pj5!pp6!oq1!ph7!on9!pgd!ju2!kva>1f$2>1m$f>0@3$0$1@1$d^2$8>0@3$0$1@1$c^3$7>0@3$0$1@2$h0@1$6#k0@1$9@1$e^4@1$3^4>0@2$a?1E@1$3^5@3$b?1E@3$4$2^6@1$5$2^5").
  (* [comment removed for export] *)
  Definition eh_saves_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "h10!hi1!hk4!ii1!pl1!ok7!olb!hle!hm5!h9!pq3!oo1!on9!ojf!ju2!oe!mue!np8>1f$c>1R$9>1m$d>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@4$3?1E^4^3^2>0>1a$8>0@2$6@2$f@1$4^6^1@2$h0^1@2$e@1$4^6@2$a?1E@1$b^6@3$7@1$2@1$1@1$0#8@1^4@1$5^2@1^5@1$5^2@4$3?1E^6^5^3").

  (* [comment removed for export] *)
  Definition at_pad : ltac2:(zQ "50!hi1!hk4!h9!hs2!ojf>1f$4>1P$2>3tok@1$1@1$0#k0>2fc@1$1@1$0#i0>2ms$3P") := ltac2:(zQ "hf1!hi1!hk4!kr0!pgd!ii1!hm5!hs2!kq7!lob!iga!hle!h9!pq9!pr0!pr7!prf!ps7!pse!pt5!ptc!pu3!pua!pv1!pv8!pj5!ojf!ltf!mia!mre!np1!itf&>0@1$1@1$0#k0@1$4@1$1@1$0#8\1f$h9\1P$b\3tok@1$1@1$0#k0\2fc@1$1@1$0#i0\2ms$6@2$2@1$1@1$0#k0\2ra@1$1@1$0#k0@2$2@1$1@1$0#k0\2gp@1$1@1$0#k0@2$2@1$1@1$0#k0\2tp@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2@2$7@1$0#5@1$1@1$0#k0\1F@2$7@1$0#5@1$1@1$0#k0@2$2~0\1m~0@2$a@3$5$6^h4@7$hb@hf$ha^h3@1$h8@1$3^h8^h2^h1^h0^f^e@1$c@1$3^h8@1$d@1$3^h8^h6^d^c^b^a^9^8^7@1$h0@1$3^h8@1$h1@1$3^h8@1$h2@1$3^h8@1$h3@1$3^h8@1$h4@1$3^h8@1$h5@1$3^h8@1$h6@1$3^h8@1$h7@1$3^h8@1$e@1$3^h8@1$f@1$3^h8^6^5^4^3^2@1$8^h7^h5@1$9@1$1@1$0#k0^1@1$hc$he@3$5@1$1@1$0#k0^h1@1$8$hd").
  (* [comment removed for export] *)
  Definition eh_X_pad_law : ltac2:(zQ "00P") := ltac2:(zQ "i80!hle!ij7!nu2!hi1!h9!ojf!hk4!kia!ih2!jta!kr0!itf!kv2!pvf!qg7!iha!ii1!hm5!iib!se!qge!qh8!oq1!qhf!qi8!ph7!on9!ok7!iu8!jk3!jr5!lp7!lu6!mn4!lk4!lob!np1!jie!oe!kva>1f$5>1G@1$8$5>1s$i5>2LB@1$8$9>2lo$4>1B$4>2fc@1$6@1$3#i0>1c$h3>1P$4>0@8$h5?1E@3$7$5^9^8^7^6^5^4^3^2>0@3$h1@1$h0$4@3$h7?1E@1$ha^a@1$h9^a@2$d$4^2@2$a@1$6@1$3#k0\3tok@1$6@1$3#k0@2$a@1$8$9\3LBX@1$8$9@2$0@5$h4^d^5^2^7@1$1^6@2$0@4$hd?1H^b@3$e$9^1^a@1$2@1$1^6@2$0@3$hc?1H^b@1$h2^6@2$0@5$h8?1E@3$7$5^d^c^2^1@1$2@1$1^6@2$0@3$h6?1E@3$7$5^d^c@1$2@1$1^6@2$0@2$i1$b@1$2@1$1^6@2$0@4$i0$b@1$2@1$1^6^9@1$hb^d@2$0@3$he?1H@1$2@1$1^6^8@2$a@1$6@1$3#k0\4errv@1$6@1$3#k0@4$i2$b@1$2@1$1^7@2$i6@2$i7@1$3#k0@1$i3$i4-q4@3$7$c@1$hf^1@1$f$c").
  Definition eh_X_nopad_law : ltac2:(zQ "00P") := ltac2:(zQ "h00!h9!ojf!ih2!qh8!iga!kia!ii1!hm5!hi1!se!qhf!ph7!on9!jta!jie!hk4>1f$1>1G@1$2$1>1s$e>2LB@1$2$d>2lo$0>1B$0>2fc@1$f@1$8#i0>1c$9>0@8$3?1E@3$5$1^8^7^6^5^4^3^2^1>0@3$7@1$6$0@3$a?1E@1$c^9@1$b^9@1$4$0@8$3?1E^9^8^7^6^5^4^3").
  (* [comment removed for export] *)
  Definition eh_X_LB_perm_law : ltac2:(zQ "00P") := ltac2:(zQ "a0!ih2!jta!h9!qh8!hi1!se!ojf!jie!kg4!hk4>1G@1$0$6>1s$7>2LB@1$0$1>3LB'@1$0$1>2lo$2>1B$2>2fc@1$9@1$4#i0>1c$5>0@8$3?1E^8^7^6^4^3^2^1>0@3$8$1^7^6@8$3?1E^a^9^7^6^5^4^3").
  (* [comment removed for export] *)
  Definition exc_live_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "h20!hi1!hk4!ih2!ii1!qi8!olb!hle!hm5!lp1!h9!okf!ojf!jta!qj3!ju2!mue!np8!npd>1G@1$2$b>3tok@1$1@1$0#k0>3LBX@1$2$c>1m$e>2m'>1x@1$1@1$0#k0@1$3@1$1@1$0#8>0@5$4?1E^5^4^3^2>0>1a$9>0@2$6@2$fZ^1@2$h0^1@2$h1+2+k0>0@2$8@2$a?1E^2@2$d^6^2@3$7@1$3@1$1@1$0#8@1^5@1$5^3@1^6@1$5^3@5$4?1E^7^6^5^3").

  (* [comment removed for export] *)
  Definition RUNWIND_RESUME : Z := 0xd30f4.
  Definition eh_resume_law : ltac2:(zQ "00P") := ltac2:(zQ "j20!hi1!hk4!ok7!lob!ojf!ih2!h9!jta!itf!mue!kia!hle!hm5!iga!qg7!pi5!pid!nu2!iib!ij7!se!ik0!ig1!kq7!qje!ql0!qlb!qh8!oq1!qm6!qn7!qi8!on9!iu8!jj8!jk3!hh9!jr5!qo8!no8!ltf!lu6!mia!mn4!mre!np1!ju2!jie!oe!nq3>1f$4>1G@1$5$4>2rs$6>3tok@1$1@1$0#k0>1s$if>2LB@1$5$7>3LBX@1$5$7>1m$ie>2mo$h6>2lo$6>1B$6>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>0@4$i3?1H^i5@3$e$7^i3^i4^i2>0@3$i1?1H^i6^i2>0@5$hf?1E@3$a$4^ib^ia^i8^i5^i4>0@3$hc?1E@3$a$4^ic^ib^i5>0@3$c$f@3$hd?1E@1$i0^id^ib$h0>0@3$he?1E^ie@d$i6@1$3@1$2^ie^he^hd^h5^h4^h3^h2^h1^h0^f^e^d^c>0@3$i5?1H^i8^i5>0@2$9@1$2^j0^i6>0@4$i9$8^ia^i8@1$2^j1>0@2$9@1$i7?5HCEIL^i9>0@2$9^ia@2$j1@1$2^j3@1$ha?1E>0@2$ib$8^id>0@3$c@1$1@1$0#k0^i9@1$3$id@3$i4?1H\1c$h4@2$b@8$hb?1E^j6^j3^j2^ie^id^f^1@2$b@3$i2?1H^if@1$h2^1@4$h9^j2@1$2^j7^j0@1$h1@1$h3^1@2$h5@7$ia@hf$i8@1$3@2$j0^j4+4@1$3@1$2^j6^ib^ia^i9^i8^i7^i6^i5^j3^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@1$3$h8^e@1$d@1$1@1$0#k0^if@1$ic$8^ie").

  (* [comment removed for export] *)
  Definition RLLVM_CATCH_PAD : Z := 0x47994.
  Definition RLLVM_AFTER_CATCH : Z := 0x47984.
  Definition eh_catch_law : ltac2:(zQ "00P") := ltac2:(zQ "je1!hi1!hk4!kr0!hle!itf!ok7!ojf!kq7!lob!jta!jie!mue!iga!kia!ih2!iha!ii1!hm5!h9!iib!pq9!pr0!pr7!prf!ps7!pse!pt5!ptc!pu3!pua!pv1!pv8!pj5!iu8!jk3!jr5!ltf!lu6!mia!mn4!mre!qg7!hs2!ij7!se!ik0!ig1!qp0!qq6!ql0!pq3!qlb!oq1!pg3!qi8!pgd!jj8!hh9!no8!np1!ju2!nq3&>0@1$1@1$0#k0@1$h0@1$1@1$0#8>2fN$6>3tok@1$1@1$0#k0>1s$a>2LB@1$e$9>3LBX@1$e$9>1m$jc>2mo$ie>2lo$h2>1B$h2>2ra@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>0@4$i2?1H^ha@3$i9$9^h8^h9^h7>0@3$i1?1H^hb^h7>0@5$j6?1E@3$d$6^he@1$f$6^hd^ha^h9>0@3$j4?1E@3$d$6^hf@1$f$6^ha>0@3$i3?1H^hb^h8>0@2$b@1$5^i1^h9>0@4$i5$4^hd^hb@1$5^i2>0@2$b@1$ja?5HCEIL^hc>0@2$b^hd@2$jd@1$5^i4@1$j3?1E>0@2$i7$4^i0>0@3$h1@1$1@1$0#k0^hb@1$8$jb=1R$j2@1$j7^i7@3$j9?1H\1c$ic@2$2@1$1@1$0#k0\3ra'@1$1@1$0#k0@2$2@1$1@1$0#k0\3gp'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$2@2$7@1$0#5@1$1@1$0#k0\2F'@2$7@1$0#5@1$1@1$0#k0@2$2~0\2m'~0@2$2$a\2s'$a@2$3@3$h1$ia@1$ib^h5@7$i6@hf$i4^h4@1$i0^h6^h3^j2^h2^h1^h0@1$h4^h6@1$h5^h6^f^e^d^c^b^a^9^8@1$h8^h6@1$h9^h6@1$ha^h6@1$hb^h6@1$hc^h6@1$hd^h6@1$he^h6@1$hf^h6@1$h6^h6@1$h7^h6^7^6^5^4^3@1$8$if^i2@1$c@1$1@1$0#k0^2@1$i8$4@2$3@4$i2?1H^1^ja^2@2$3@3$i1?1H^1@1$h3^h5@2$3@3$j8?1H^j7@1$h3^h5@2$3@2$i7$4^2@2$3@4$i5$4^2^j6@1$5^jd@2$3@3$i3?1H^2^j5@2$3@2$j5?1E^2@4$j1^ja@1$5^jd^j8^2@2$id@7$i6@hf$i4^hf@1$i0^1^he^hd^hc^hb^ha@1$h4^1@1$h5^1^i7^h9^h8^h7^h6^h5^h4^h3@1$h8^1@1$h9^1@1$ha^1@1$hb^1@1$hc^1@1$hd^1@1$he^1@1$hf^1@1$h6^1@1$h7^1^h2^h1^h0^f^e@1$8$j0^d@1$c@1$1@1$0#k0^i3@1$i8$4^i2").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition opnew_ok_post : ltac2:(zQ "a0!hi1!hk4!h9!ih2!se!ig1!kq7!jta!ju2!jie>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1n$2>2lo$2>1B$2>1m$8>2mo$5>1c$4P") := ltac2:(zQ "ic1!hi1!hk4!kr0!hle!h9!itf!kh3!kv2!kia!ih2!ho3!jie!kva!iha!ii1!kkb!iib!lk4!iga!hm5!hs2!ij7!se!ig1!kq7!iu8!jj8!jk3!jr5!lp7!lpd!ltf!lu6!mia!mj0!mn4!mre!lob!jta!ju2!ms9!mt8!oe!mu5&>0@1$1@1$0#k0@1$e@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$b\2LB@1$9$i6\1n$4\2lo$4\1B$4\1m$i7\2mo$h7\1c$h6@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2$b\2s'$b@2$2$4\1A$4@2$2@1$9@1$1@1$0#8\4junk@1$9@1$1@1$0#8@2$2$6\1p$6@2$3@3$h3$h4@1$h5^h5@7$i1@hf$hf^ie^id^ic^ib^h4^h3^h2^ia^i9@1$i5^3^h1^h0^f^e^d^c^b^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^a^9^8^7^he@1$i2^ie^hd@1$h2@1$1@1$0#k0^6@1$i4$5@2$3@3$h9?1H^4@1$h0^h5@2$3@3$ha?1H^h6@1$h0^h5@2$3@2$i3$5^6@2$3@4$i0$5^6^h9@2$c@1$0#k0^id@2$3@4$h1$5^6@2$ia@2$c@1$0#k0^ib-q4@3$8$7@1$hd^5@1$d$7@2$3@3$hc?1H^6^h8@2$3@4$i9^hb@2$c@1$0#k0^id^h7^6@2$3@3$i8?5HCEIL^3^ha@2$3@4$hb?1H^4@3$8@2$a@2$a$6$4$4@4$f@2$a$6$4$4@4$f$6$4^1^3^ha^hb^6@4$h1$5^6^3@3$8$7@2$he@1$ib^ha^2@1$d$7").

  (* [comment removed for export] *)
  Definition opnew_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "j90!hi1!hk4!kva!hm5!ojf!lob!itf!mue!kia!hle!h9!jie!oe!ih2!kv2!iga!iha!kr0!lp1!nu2!iib!ij7!se!ik0!ig1!kq7!ql0!qr9!qsa!qt3!pq3!qlb!qh8!oq1!pg3!ph7!pgd!iu8!jj8!jk3!hh9!jr5!qo8!no8!lp7!ltf!lu6!mia!mn4!mre!lk4!np1!jta!ju2!np8!npd!nq3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j5>1s$b>2LB@1$d$j4>1n$a>2lo$a>1B$a>4errv@1$1@1$0#k0>2mo$h8>1G@1$d$4>1f$4>0@4$i7?1H^9^8^a>0@3$i5?1H^a^4>0@3$i9?1H^c^7>0@2$7@2$2@1$0#k0^id^8>0@4$ie$6^e^a@2$2@1$0#k0^ie>0@2$7@1$ib?5HCEIL^b>0@2$7^c@2$j8@2$2@1$0#k0^j0@2$c$hd@1$hf?1E>0@4$j2$6^h1@2$c@2$2@1$0#k0^if-q4@3$8$e@1$ic^b@1$h0$e>0@2$j0$6^h2>0@3$3@1$1@1$0#k0^j1@1$5$j3>0@3$3@1$1@1$0#k0^ic@1$5^h1>0@2$9@2$7+1^h2@2$j6^h2@2$j7+2+i0>0@2$i2?1E^h6>0@3$i1?1E@3$8$4^e^f^h7>0@3$3$he@1$i4^f@d$ia^j8^j2^j1^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf>0@3$3@1$1@1$0#k0^ja@1$5@2$c@1$i3^h0+4@3$i8?1H\1c$h6@2$h2@ha$hb^jc^jb^ja^j9^j5^j4^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^hd^hc^ha^h9^h8^h7^h6^hb^h4^1@2$h1$b\2s'$b@2$9@8$i0?1E@3$8$4^h3^h4^1^ha^h8^h7^hd^2@2$9@3$i6?1H^h5@1$h4^2@4$ha^ha@2$2@1$0#k0^jc^hc@1$h3@1$h5^2@2$h7@7$if@hf$id^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc@1$5$hc^hb@1$f@1$1@1$0#k0^ha@1$j1$6^h3").
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_mf_hyps : ltac2:(zQ "00P") := ltac2:(zQ "hf0!hle!qu2!quf!qvd!rh3!rid!rk4!rl3!rm1!rmc!ro1!rp3!rq3!rr3!rs9!rtf!rv6!sgc!shd!sj4!sk9!sm1!sn8!so8!spa!sqc!sre!ssf!su0!qlb!mue@2$0$8@2$0$1@2$0$2@2$0$6@2$0$3@2$0$4@2$0$5@2$0$7@2$0$hc@2$0$h7@2$0$h8@2$0$h6@2$0$ha@2$0$h9@2$0$hb@2$0@2$heZ@1$hd?1E@2$0$h4@2$0$f@2$0$h0@2$0$h2@2$0$h3@2$0$e@2$0$d@2$0$b@2$0$a@2$0$9@2$0$h5@2$0$h1$c").
  (* [comment removed for export] *)
End Iface.
(* [comment removed for export] *)
