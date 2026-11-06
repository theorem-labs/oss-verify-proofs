(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import BJFrame.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~hcdRMALLOC_STACK46Stdlib6ZArith6BinInt1Zn73addhcbRFREE_STACK3h5LinuxProcessSemanticsfLinuxProcessSem3Runq36config79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~t85hs_SR04Npos35stdpp9bitvectorbdefinitionshia2bv37Corelib4Init5Logichkd3andhkd2eq37Corelib4Init9Datatypeshme4prod3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshoedmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Stateht65Modelhme4Nonehme4listhme3nilhme6optionq39cfg_modelq36cfg_msq35mkCfght68m_haltedht69m_vm_lazy79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~im43evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~iq65rsegst87hs_KREL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~iv66PStatet88hs_MPRESt88hs_RHEAPhch0RHEAP_frame_stmthch6RHEAP_block_range_stmthchaRHEAP_blocks_disjoint_stmthch7RHEAP_blocks_nodup_stmtt8bhs_rauxv_okhch3rauxv_ok_frame_stmthc5blockhc3mem36Stdlib7SortingbPermutationjucbPermutationiv64bptrt8chs_lb_removehme4cons36Stdlib5Lists4Listkj62Inhme4pairhkd3nothc6blk_id37Corelib5Lists7ListDefkm73map3h5LinuxProcessSemantics5Riscv7Preludeko55bvmaphkd2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kra4cellhiabbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lgd8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ll42wzhkd2orkra2C4kra2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lq73mkRlq73stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lv12MSlv16ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mje7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mo37seg_romhccrblock_rangehcarheap_presn76to_natn72le69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mv75hceil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface5Iface~~~~~~njbemalloc_mf_posthc4RATPn72ltn73pown73subnjbh1malloc_mf_stmt_athcbRMALLOC_SYMnjbh0RMALLOC_REPLACEDhoe6ms_memt8eRALIGNED_ALLOCnjbcfree_mf_postnjbffree_mf_stmt_athc9RFREE_SYMt86ROPDELt87ROPDEL2t85framet85fr_spt89eh_staticmje2wahoe5wviewhccrclient_addrt85fr_fnt88eh_fsizet86eh_slonjb8chain_spt8beh_chain_oknjb8in_saves79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7BJFrame~~~~~~os17rin_ivst87eh_idlet87fr_livet8bfr_callsitehme4boolhme4truet84c_spt8h1eh_agrees_unsavedt8beh_saves_okt8aeh_site_okt85fr_ranjbdRLLVM_FUZZ_CSnjbdRLLVM_FUZZ_FNt8aeh_base_okt83csrt84c_s0t84c_s1t85c_s10t85c_s11t84c_s2t84c_s3t84c_s4t84c_s5t84c_s6t84c_s7t84c_s8t84c_s9hme4Somehme3appnjb6at_padt84eh_Xt86eh_padt88exc_livehc8in_blocknjbeRUNWIND_RESUMEnjb7eh_prest88eh_STACKt8eeh_resume_sitet8eeh_unsaved_nowt85mkCSRnjbh1RLLVM_AFTER_CATCHnjbfRLLVM_CATCH_PADnjbdopnew_ok_postt86ROPNEWt8cROPNEW_STACKnjb9KREL_lawsnjbaMPRES_lawsnjbh1RHEAP_block_rangenjbh5RHEAP_blocks_disjointnjbh2RHEAP_blocks_nodupnjbbRHEAP_framenjbaRHEAP_permnjb7SR_lawsnjbh0eh_X_LB_perm_lawnjbeeh_X_nopad_lawnjbceh_X_pad_lawnjbceh_catch_lawnjbh1eh_chain_base_lawnjbh1eh_chain_cons_lawnjbh2eh_chain_frame_lawnjbh1eh_idle_frame_lawnjbdeh_resume_lawnjbh2eh_saves_frame_lawnjbh0eh_slo_range_lawnjbh3eh_static_range_lawnjbh2exc_live_frame_lawnjbcfree_mf_stmtnjbelb_remove_lawsnjbemalloc_mf_stmtnjbeopdel2_mf_stmtnjbdopdel_mf_stmtnjbdopnew_mf_stmtnjbbrauxv_framet83hmft83ehk" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROPNEW    : Z := 0xf3578.   (* [comment removed for export] *)
Definition ROPDEL    : Z := 0x97938.   (* [comment removed for export] *)
Definition ROPDEL2   : Z := 0x9793c.   (* [comment removed for export] *)
Definition ROPDELA   : Z := 0x97940.   (* [comment removed for export] *)
Definition RALIGNED_ALLOC : Z := 0xdfc08.  (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROPNEW_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!m7!of@2$1+h0$0").   (* [comment removed for export] *)
Definition ROPDEL_STACK : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!p5$0").

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
  Variable H : ltac2:(zQ "10!sv7$0").
  Variable E : ltac2:(zQ "10!svd$0").
  Notation SR := (hs_SR H).  Notation KREL := (hs_KREL H).  Notation MPRES := (hs_MPRES H).
  Notation RHEAP := (hs_RHEAP H).  Notation rauxv_ok := (hs_rauxv_ok H).  Notation lb_remove := (hs_lb_remove H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SR_laws : ltac2:(zQ "00P") := ltac2:(zQ "h41!sf!hhc!hi4!hk7!hm1!hm8!ho6!hs5!ig4!igd!ih5!ihd!ii4!iie!ija!ik3!ikb!il7!ipf!iu3&@2$6@1$3@1$2#k0@1$3@1$2#k0@2$4>1Q>0$0P>1c$0>0@1^2^1@3$1?1H^3^2@2$4>1Q>0$0P>2Q'>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@1^5^2@3$1?1H^4^3@2$4>2Q1>0$0P>2Q2>0$0P>1c$0>0@3$1?1H^3^1>0>2c'$0>0@1^5^1@3$1?1H^5^2@3$1?1H^4^3>1P>0$7P>2ms$7>2mo$8>0@3$5@1$c@1$3@1$2#k0@1$h0^1@1$9@1$3@1$2#k0>0@3$5@1$a~0@1$h1^2@1$b~0>0@3$h2$h3^5^4@3$1?1H\1c$0@2$4@1^7@1$e^1@3$5$8@1$d^1^5@2$f^5^4").
  Definition KREL_laws : ltac2:(zQ "00P") := ltac2:(zQ "e1!hi4!hk7!ho6!hm8!igd!ih5!ihd!ii4!hm1!ig4!ikb!il7!iuc!jj2&@2$2@1$1@1$0#k0@1$1@1$0#k0>1s$d>2mo$9>0@3$c?1H^2^1@2$8@3$3@1$7@1$1@1$0#k0@1$a^2@1$4@1$1@1$0#k0@3$3@1$5~0@1$b^2@1$6~0").
  Definition MPRES_laws : ltac2:(zQ "00P") := ltac2:(zQ "30!ig4!jjc!hm1@2$2>2mo$0@3$1?1H^1^1>3mo1$0>3mo2$0>3mo3$0>0@3$1?1H^3^2>0@3$1?1H^3^2@3$1?1H^5^3").
  Definition RHEAP_frame : ltac2:(zQ "00P") := ltac2:(zQ "20!jk7!jl2@2$1?5HCEIL@1$0?1H").
  Definition RHEAP_block_range : ltac2:(zQ "00P") := ltac2:(zQ "20!jk7!jm6@2$1?5HCEIL@1$0?1H").
  Definition RHEAP_blocks_disjoint : ltac2:(zQ "00P") := ltac2:(zQ "20!jk7!jo0@1$1@1$0?1H").
  Definition RHEAP_blocks_nodup : ltac2:(zQ "00P") := ltac2:(zQ "20!jk7!jpe@1$1@1$0?1H").
  Definition rauxv_frame : ltac2:(zQ "00P") := ltac2:(zQ "20!jr9!js7@1$1@1$0?1H").
  (* [comment removed for export] *)
  Definition RHEAP_perm : ltac2:(zQ "00P") := ltac2:(zQ "60!jte!ih5!jk7!ju6!jj2!kg8>1s$4>2LB@1$1$0>3LB'@1$1$0>1m$3>0@4$2?1H^4^3^1>0@3$5$0^4^3@4$2?1H^6^4^3").
  Definition lb_remove_laws : ltac2:(zQ "00P") := ltac2:(zQ "e0!jte!kh7!h9!ih5!khf!kie!ho6!hm8!kk9!kkf!hm1!kl7!kle!kne@2$a>1p$1>1A$2>1n$2>2LB@1$3$0>0@1$b@3$8$1^4@4$d$0$1$c^1@3$7@1$3$0@3$4?1H^5@3$5@2$6@2$6$1$2$2@4$9@2$6$1$2$2@4$9$1$2^5^4^3^2^2@2$a>1p$1>1b$0>2LB@1$3$0>0@1$b@3$7$1@1$c^2^3@3$7@1$3$0@3$4?1H^4@3$5$0^3^2@3$5$0^3@3$4?1H^4^2>1p$1>2LB@1$3$0>1b$0>0@3$8$0^1@3$4?1H^3^2@3$8$0^2^3").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_mf_post : ltac2:(zQ "a0!hi4!hk7!h9!ih5!sf!ig4!kqb!jte!ju6!jj2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1n$2>2lo$2>1B$2>1m$8>2mo$5>0$4P") := ltac2:(zQ "id1!hi4!hk7!kr4!hm1!h9!iu3!kh7!kv6!kie!ih5!ho6!hm8!jj2!kve!ihd!ii4!kkf!iie!lk8!lof!jk7!igd!lp5!hs5!ija!sf!ig4!kqb!lpb!lq1!lu3!lua!mie!mj4!mn8!ms2!iuc!jjc!jr9!jte!ju6!msd!mtc!of!mu9&>0@1$1@1$0#k0@1$f@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$hb@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$c\2LB@1$9$i7\1n$4\2lo$4\1B$4\1m$i8\2mo$ha\1c$h9@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2$c\2s'$c@2$3@3$b$h7@1$h8^h3@7$i0@hf$he^ic^ib^ia^i9^h2^h1^h0^i8^i7^f^e^d^c^b^a^9^8^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^7^6^5^4^hc@1$i1^ic^hb@1$h5@1$1@1$0#k0^3@1$i3$5@2$3@3$i4?1H^1@1$h1^h3@2$3@3$i5?1H^h4@1$h1^h3@2$3@2$i2$5^3@2$3@4$hf$5^3^h7@2$d@1$0#k0^ib@2$3@4$h2$5^3@2$ib@2$d@1$0#k0^i9-q4@3$8$7@1$hc^2@1$e$7@2$3@3$i6?1H^3^h6@2$3@4$ia^h9@2$d@1$0#k0^ib^h5^3@2$h6@2$3@3$b@1$1@1$0#k0^f@1$h3Z@4$h4?1H^1^h9^3@2$2$4\1A$4@2$2@1$9@1$1@1$0#8\4junk@1$9@1$1@1$0#8@2$2$6\1p$6@2$3@3$b@1$1@1$0#k0^h2@1$h3^3@2$3@3$i9?5HCEIL^3^hb@2$3@4$h4?1H^4@3$8@2$a@2$a$6$4$4@4$h0@2$a$6$4$4@4$h0$6$4^1^3^hb^hc^6@4$h2$5^6^3@3$8$7@2$hd@1$ic^hb^2@1$e$7").

  Definition malloc_mf_stmt_at : ltac2:(zQ "10!h9>5entry$0>5stack$0P") := ltac2:(zQ "i60!hi4!hk7!h9!iu3!mv2!kve!lof!hm8!kv6!igd!kie!ih5!ihd!hm1!ik3!ig4!kqb!nj2!lpb!lu3!lua!mie!mn8!ms2!lk8!no5!iuc!jk7!hhc!jr9!np7!jte!ju6!jj2!of!npe!nq3!nq9\5entry$2\5stack$2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h0@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i0>1s$i1>2LB@1$b$hf>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$f>0@4$hb?1H^7^6^8>0@3$ha?1H^8^2>0@3$hd?1H^a^5>0@2$4@2$5@1$0#k0^ib^6>0@4$h4$3^c^8@2$5@1$0#k0^ic>0@2$4@1$h1?5HCEIL^9>0@2$4^a@2$i5@2$5@1$0#k0^ie^j0>0@4$h8$3^f@2$i2@2$5@1$0#k0^id-q4@3$a$8@1$h2^9@1$c$8>0@2$h6$3^h0>0@3$7@1$1@1$0#k0^if@1$6$he>0@3$7@1$1@1$0#k0^ia@1$6^f>0@2$d@2$4+1^h0@2$i3^h0@2$i4+2+i0@3$hc?1H@h9$h9^j5^j4^j3^j2^ie^id^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^h6^h5^h3^h2^h1^h0^f^h4^d@2$e@7$h5@hf$h3^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6@1$6^j7^h5@1$9@1$1@1$0#k0^h4@1$h7$3^d").
  Definition malloc_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "30!nqf!m7!ns5@2$0$2$1").

  (* [comment removed for export] *)
  Definition RMALLOC_REPLACED : Z := 0x12f3a8.
  Definition aligned_alloc16_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "ic0!hi4!hk7!kv6!lof!iu3!mv2!kve!kie!ihd!hm8!h9!lpb!lk8!hm1!nt3!of!igd!ih5!nu8!ija!sf!ik3!ig4!kqb!nj2!lu3!lua!mie!mn8!ms2!no5!nv2!iuc!jk7!hhc!jr9!np7!m7!jte!ju6!jj2!npe!nq3!nq9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i7>1s$i8>2LB@1$h1$i6>1n$a>2lo$a>1B$a>4errv@1$1@1$0#k0>2mo$h6>0@4$i1?1H^7^6^8>0@3$i0?1H^8^2>0@3$i3?1H^a^5>0@2$5@2$6@1$0#k0^ib^6>0@4$ha$4^c^8@2$6@1$0#k0^ic>0@2$5@1$h8?5HCEIL^9>0@2$5^a@2$ib@2$6@1$0#k0^ie@2$f+i0$i5>0@4$c$4^f@2$f@2$6@1$0#k0^id-q4@3$7$2@1$b^9@1$8$2>0@2$hc$4^h0>0@3$9@1$1@1$0#k0^if@1$3$i4>0@4$c$4^h2$e@3$7$2@1$b@1$3Z@1$8$2>0@3$9@1$1@1$0#k0^ib@1$3+h0>0@3$9@1$1@1$0#k0^ib@1$3^h1>0@2$d@2$5+1^h2@2$i9^h2@2$ia+2+i0@3$i2?1H\1c$h4@2$d@ha$he^j8^j7^j6^j5^j1^j0^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^h9^h8^h6^h5^h4^h3^h2^h7^h0^1@4$c$4@1$h2@1$h3^1$e@3$7$2@1$b@1$3Z@1$8$2@2$h5@7$hb@hf$h9^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@1$3$hf^h7@1$h0@1$1@1$0#k0^h6@1$hd$4^f").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_mf_post : ltac2:(zQ "b0!hi4!hk7!h9!ih5!sf!ig4!kqb!jte!ju6!jj2!kh7>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1p$a>2lo$2>1B$2>4errv@1$1@1$0#k0>1m$8>2mo$5>0$4P") := ltac2:(zQ "i71!hi4!hk7!kr4!hm1!iu3!jj2!kve!ii4!h9!iie!kv6!khf!igd!kie!ih5!ihd!hm8!hs5!ija!sf!ig4!kqb!lpb!lu3!lua!mie!mj4!mn8!ms2!lk8!iuc!jjc!jk7!jr9!jte!ju6!mtc!kh7!of&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h5@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$5\2LB@1$e$i2\1p$i5\2lo$8\1B$8\4errv@1$1@1$0#k0\1m$i3\2mo$h4\1c$h3@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2$5\2s'$5@2$3@3$h0$h1@1$h2^h2@7$h9@hf$h7^ic^ib^ia^i9^h1^h0^f^i8^i7^e^d^c^b^a^9^8^7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^6^5^4^3^hc@1$ha^ic^hb@1$c@1$1@1$0#k0^2@1$hc$4@2$3@3$he?1H^1@1$9^h2@2$3@3$hf?1H^h3@1$9^h2@2$3@2$hb$4^2@2$3@4$h8$4^2^h7@2$6@1$0#k0^ib@2$3@4$hd$4^2@2$i6@2$6@1$0#k0^i9-q4@3$d$a@1$h6^h5@1$f$a@2$3@3$i1?1H^2^h6@2$3@4$i4@3$b?1H^h8^h9@2$6@1$0#k0^ib^h4^2@4$i0?1H^1@3$b?1H^h8^h9^2").

  Definition free_mf_stmt_at : ltac2:(zQ "10!h9>5entry$0P") := ltac2:(zQ "i80!hi4!hk7!h9!iu3!kh7!kve!ho6!lof!mv2!kkf!hm8!kv6!igd!kie!ih5!ihd!ik3!ig4!kqb!nj2!lpb!lu3!lua!mie!mn8!ms2!lk8!og3!iuc!jk7!hhc!jr9!np7!p5!jte!ju6!jj2!kk9!of!nq9\5entry$2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h2@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i3>1s$i4>2LB@1$e$i2>1p$4>1A$2>1n$2>2lo$2>1B$2>4errv@1$1@1$0#k0>2mo$h1>0@4$hd?1H^9^8^a>0@3$hc?1H^a^2>0@3$i5@2$6@2$6$4$2$2@4$9@2$6$4$2$2@4$9$4$2^9^8^7^a>0@3$hf?1H^d^6>0@2$8@2$5@1$0#k0^ie^7>0@4$h6$3^f^9@2$5@1$0#k0^if>0@2$8@1$h3?5HCEIL^a>0@2$8^b@2$i7@2$5@1$0#k0^j1$i1>0@4$ha$3^h2@2$i6@2$5@1$0#k0^j0-q4@3$d$b@1$h4^a@1$f$b>0@2$h8$3^h3>0@3$a@1$1@1$0#k0^j2@1$7$i0>0@3$a@1$1@1$0#k0^id@1$7^h1@3$he?1H@ha$hb^j7^j6^j5^j4^j0^if^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^h8^h7^h5^h4^h3^h0^f^e^h6^d@2$h0@7$h7@hf$h5^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8@1$7^j8^h7@1$c@1$1@1$0#k0^h6@1$h9$3^d").
  Definition free_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!oh3!oi6@1$0$1").
  Definition opdel_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!oh3!oj2@1$0$1").
  Definition opdel2_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "20!oh3!ojb@1$0$1").

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition chain_sp : ltac2:(zQ "30!ih5!h9!ok5>1G@1$0$2$1") := ltac2:(zQ "50!ih5!ok5!h9!okd!nq3\1G@1$0$1M0\1G@1$0$1$2^1@2$4+2+k0\1f$1\1l@1$0$1@1$3^2").
  (* [comment removed for export] *)
  Definition EH_IVS : ltac2:(zQ "30!h9!ih5!ho6@1$1@2$2$0$0") := ltac2:(zQ "50!h9!ho6!kie!kkf!ihd@3$2@2$1$0$0@4$3$0$0+hgths8+hgtjv0@3$2@2$1$0$0@4$3$0$0+hguri0+hguri7@1$4@2$1$0$0").
  Definition eh_static_range_law : ltac2:(zQ "00P") := ltac2:(zQ "60!hm1!mv2!npe!lp5!h9!ol5>1a$4>0@2$5?1E^1@2$3@2$0@2$1+hgths8^2@2$2^2+hgtjv0@2$0@2$1+hguri0^2@2$2^2+hguri7").
  (* [comment removed for export] *)
  Definition eh_pres : ltac2:(zQ "40!ju6!ih5!h9!jte>2LB@1$1$3>2SP$2>1m$0>2m'$0P") := ltac2:(zQ "h30!hi4!hk7!om1!ii4!hm8!kl7!igd!hm1!h9!om7!ju6!iu3!ih5!ol5!jte!on0!mv2!npe!nq3\2LB@1$c$e\2SP$8\1m$a\2m'$a>1a$8>0@2$7@2$h0Z^1@2$h1^1@2$h2+2+k0>0@3$f^6^5^2>0@1$5@2$d?1E^3@2$7@3$4@1$3@1$1@1$0#8@1^5@1$2^4@1^6@1$2^4>0@1$5@3$4@1$3@1$1@1$0#8@3$9$b^6@1$2^4@1$6@1$1@1$0#8@1$5@3$4@1$3@1$1@1$0#8@3$9$b^6@1$2^5@1$6@1$1@1$0#8").
  (* [comment removed for export] *)
  Definition in_saves : ltac2:(zQ "30!ih5!h9!ok5>1G@1$0$2>1a$1P") := ltac2:(zQ "d0!ok5!hm1!onf!okd!of!ih5!kr4!h9!oo7!op2!kk9!mv2!npe\1G@1$5$0\1a$7@2$6$0\1f$0@2$1@3$a$0^1^3@2$1@2$b@2$4@1$3^1@2$9?1E@1$2^1^2@2$c^2@2$4@1$3^1@2$8?1E@1$2^1").
  Definition eh_chain_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "h40!hi4!hk7!ii4!om1!hm8!igd!hm1!kl7!h9!om7!opb!oq7!iu3!mv2!npe!nq3!ih5!or5!ok5!ju6>1G@1$h0$h2>1m$h3>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@3$b?1E^3^2>0>1a$8>0@2$6@2$d@1$a^5^1@2$e^1@2$f+2+k0>0@2$h1^6^2@3$4@1$2@1$1@1$0#8@1^5@1$3^3@1^6@1$3^3>0>1a$8>0@2$6@2$d@1$a^6^1@2$e^1@2$f+2+k0>0@1$7@3$4@1$2@1$1@1$0#8@3$9$c^6@1$3^2@1$5@1$1@1$0#8@1$7@3$4@1$2@1$1@1$0#8@3$9$c^6@1$3^3@1$5@1$1@1$0#8@3$b?1E^6^4").
  Definition eh_slo_range_law : ltac2:(zQ "00P") := ltac2:(zQ "50!op2!mv2!hm1!h9!oo7>2fn$3@2$2@2$1Z@2$0?1E^1@2$1@2$0?1E^1@2$4?1E^1").
  (* [comment removed for export] *)
  Definition saves_clear : ltac2:(zQ "40!ih5!h9!ho6!ok5>1G@1$0$3>1X@1$0@2$2$1$1P") := ltac2:(zQ "f0!h9!ok5!ih5!onf!okd!of!ho6!hm1!kl7!pg0!oo7!op2!kk9!mv2!npe\1G@1$2$1\1X@1$2@2$6$0$0>1f$1>1a$0>0@3$c$1^2^4>0@2$7@2$d@2$5@1$4^3@2$b?1E@1$3^3^2@2$e^2@2$5@1$4^3@2$a?1E@1$3^3@1$8@2$9^5^3").
  Definition eh_idle_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "d0!hi4!hk7!ii4!om1!pgb!hm1!hm8!h9!ol5!ju6!mv2!npe!nq3>1m$9>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@2$4?1E^2>0>1a$7>0@2$5@2$aZ^1@2$b^1@2$c+2+k0>0@2$8?1E^2@3$6@1$2@1$1@1$0#8@1^5@1$3^3@1^6@1$3^3@2$4?1E^3").
  (* [comment removed for export] *)
  Definition eh_chain_cons_law : ltac2:(zQ "00P") := ltac2:(zQ "h80!ok5!hm8!kie!ph5!okd!hi4!h9!oq7!phf!onf!of!pid!ih5!pj5!lof!pjd!pk4!oo7!pl9!pm7!pn4!ju6!hk7!kve>1G@1$c$0>1g$0>1f$0>1m$h5>0@3$7?1E@3$2$0^3^4^1>0@3$1$b@3$h3?1E@1$9^3@1$8^3$d>0@3$1$6@2$h7@1$5#k0@1$f@1$3^4@1$4^4>0@3$1$6@2$a@1$4^5@2$h1?1E@1$9^5@1$4^6>0@3$1@1$h6@1$5#k0@1$h4^6@1$e@2$a@1$8^7+4>0@4$h2?1E^7@1$3^8^6>0@3$h0?1E^8@1$3^9@3$7?1E@3$2$0^9@3$2$0^a^b^8").
  (* [comment removed for export] *)
  Definition RLLVM_FUZZ_FN : Z := 0x47534.
  Definition RLLVM_FUZZ_CS : Z := 0x4753c.
  Definition eh_chain_base_law : ltac2:(zQ "00P") := ltac2:(zQ "h10!hm8!h9!ok5!okd!kie!ihd!hi4!pnc!pod!pjd!ppe!oq7!phf!onf!ph5!ju6!kve>1f$2>1m$f>0@3$0$1@1$d^2$8>0@3$0$1@1$c^3$7>0@3$0$1@2$h0@1$6#k0@1$9@1$e^4@1$3^4>0@2$a?1E@1$3^5@3$b?1E@3$4$2^6@1$5$2^5").
  (* [comment removed for export] *)
  Definition eh_saves_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "h10!hi4!hk7!ii4!om1!pl9!okd!hm1!hm8!h9!pqb!oo7!onf!ok5!ju6!of!mv2!npe>1f$c>1R$9>1m$d>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@4$4?1E^4^3^2>0>1a$8>0@2$6@2$f@1$5^6^1@2$h0^1@2$e@1$5^6@2$a?1E@1$b^6@3$7@1$2@1$1@1$0#8@1^4@1$3^2@1^5@1$3^2@4$4?1E^6^5^3").

  (* [comment removed for export] *)
  Definition at_pad : ltac2:(zQ "50!hi4!hk7!h9!hs5!ok5>1f$4>1P$2>3tok@1$1@1$0#k0>2fc@1$1@1$0#i0>2ms$3P") := ltac2:(zQ "hf1!hi4!hk7!kr4!ph5!ii4!hm8!hs5!kqb!lof!igd!hm1!h9!lu3!mie!ms2!pr1!pr8!prf!ps7!psf!pt6!ptd!pu4!pub!pv2!pv9!qg0!pjd!ok5!np7!iu3&>0@1$1@1$0#k0@1$4@1$1@1$0#8\1f$hc\1P$b\3tok@1$1@1$0#k0\2fc@1$1@1$0#i0\2ms$6@2$2@1$1@1$0#k0\2ra@1$1@1$0#k0@2$2@1$1@1$0#k0\2gp@1$1@1$0#k0@2$2@1$1@1$0#k0\2tp@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2@2$7@1$0#5@1$1@1$0#k0\1F@2$7@1$0#5@1$1@1$0#k0@2$2~0\1m~0@2$a@3$5$6^h4@7$d@hf$c^h3@1$hb@1$3^h8^h2^h1^h0^f^e@1$f@1$3^h8@1$h0@1$3^h8^h6^d^c^b^a^9^8^7@1$h3@1$3^h8@1$h4@1$3^h8@1$h5@1$3^h8@1$h6@1$3^h8@1$h7@1$3^h8@1$h8@1$3^h8@1$h9@1$3^h8@1$ha@1$3^h8@1$h1@1$3^h8@1$h2@1$3^h8^6^5^4^3^2@1$8^h7^h5@1$9@1$1@1$0#k0^1@1$e$he@3$5@1$1@1$0#k0^h1@1$8$hd").
  (* [comment removed for export] *)
  Definition eh_X_pad_law : ltac2:(zQ "00P") := ltac2:(zQ "i80!hm1!ija!nu8!hi4!h9!ok5!hk7!kie!ih5!jte!kr4!iu3!kv6!qg7!qgf!ihd!ii4!hm8!iie!sf!lpb!lua!mn8!lk8!lof!qh6!qi0!oq7!qi7!qj0!phf!onf!okd!iuc!jk7!jr9!np7!jj2!of!kve>1f$5>1G@1$8$5>1s$i5>2LB@1$8$9>2lo$4>1B$4>2fc@1$6@1$3#i0>1c$h3>1P$4>0@8$ha?1E@3$7$5^9^8^7^6^5^4^3^2>0@3$h1@1$h0$4@3$hc?1E@1$hf^a@1$he^a@2$d$4^2@2$a@1$6@1$3#k0\3tok@1$6@1$3#k0@2$a@1$8$9\3LBX@1$8$9@2$0@5$h9^d^5^2^7@1$1^6@2$0@4$i2?1H^b@3$e$9^1^a@1$2@1$1^6@2$0@3$i1?1H^b@1$h2^6@2$0@5$hd?1E@3$7$5^d^c^2^1@1$2@1$1^6@2$0@3$hb?1E@3$7$5^d^c@1$2@1$1^6@2$0@2$h6$b@1$2@1$1^6@2$0@4$h5$b@1$2@1$1^6^9@1$i0^d@2$0@3$i3?1H@1$2@1$1^6^8@2$a@1$6@1$3#k0\4errv@1$6@1$3#k0@4$h7$b@1$2@1$1^7@2$i6@2$i7@1$3#k0@1$h8$i4-q4@3$7$c@1$h4^1@1$f$c").
  Definition eh_X_nopad_law : ltac2:(zQ "00P") := ltac2:(zQ "h00!h9!ok5!ih5!qi0!igd!kie!ii4!hm8!hi4!sf!qi7!phf!onf!jte!jj2!hk7>1f$1>1G@1$2$1>1s$e>2LB@1$2$d>2lo$0>1B$0>2fc@1$f@1$8#i0>1c$9>0@8$3?1E@3$5$1^8^7^6^5^4^3^2^1>0@3$7@1$6$0@3$a?1E@1$c^9@1$b^9@1$4$0@8$3?1E^9^8^7^6^5^4^3").
  (* [comment removed for export] *)
  Definition eh_X_LB_perm_law : ltac2:(zQ "00P") := ltac2:(zQ "a0!ih5!jte!h9!qi0!hi4!sf!ok5!jj2!kg8!hk7>1G@1$0$6>1s$7>2LB@1$0$1>3LB'@1$0$1>2lo$2>1B$2>2fc@1$9@1$4#i0>1c$5>0@8$3?1E^8^7^6^4^3^2^1>0@3$8$1^7^6@8$3?1E^a^9^7^6^5^4^3").
  (* [comment removed for export] *)
  Definition exc_live_frame_law : ltac2:(zQ "00P") := ltac2:(zQ "h20!hi4!hk7!ih5!ii4!om1!qj0!hm1!hm8!lp5!h9!ol5!ok5!jte!qjb!ju6!mv2!npe!nq3>1G@1$2$b>3tok@1$1@1$0#k0>3LBX@1$2$c>1m$e>2m'>1x@1$1@1$0#k0@1$3@1$1@1$0#8>0@5$5?1E^5^4^3^2>0>1a$9>0@2$6@2$fZ^1@2$h0^1@2$h1+2+k0>0@2$8@2$a?1E^2@2$d^6^2@3$7@1$3@1$1@1$0#8@1^5@1$4^3@1^6@1$4^3@5$5?1E^7^6^5^3").

  (* [comment removed for export] *)
  Definition RUNWIND_RESUME : Z := 0xd659c.
  Definition eh_resume_law : ltac2:(zQ "00P") := ltac2:(zQ "j20!hi4!hk7!okd!lof!ok5!ih5!h9!jte!iu3!mv2!kie!hm1!hm8!igd!qgf!pid!pj5!nu8!iie!ija!sf!ik3!ig4!kqb!nj2!lu3!lua!mie!mn8!ms2!qk6!ql8!qm3!qi0!oq7!qme!qnf!qj0!onf!iuc!jjc!jk7!hhc!jr9!qp0!np7!ju6!jj2!of!nq9>1f$4>1G@1$5$4>2rs$6>3tok@1$1@1$0#k0>1s$if>2LB@1$5$7>3LBX@1$5$7>1m$ie>2mo$h6>2lo$6>1B$6>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>0@4$i9?1H^i5@3$e$7^i3^i4^i2>0@3$i7?1H^i6^i2>0@5$i5?1E@3$a$4^ib^ia^i8^i5^i4>0@3$i2?1E@3$a$4^ic^ib^i5>0@3$c$f@3$i3?1E@1$i6^id^ib$h0>0@3$i4?1E^ie@d$ic@1$3@1$2^ie^he^hd^h5^h4^h3^h2^h1^h0^f^e^d^c>0@3$ib?1H^i8^i5>0@2$9@1$2^j0^i6>0@4$ha$8^ia^i8@1$2^j1>0@2$9@1$h8?5HCEIL^i9>0@2$9^ia@2$j1@1$2^j3@1$i0?1E>0@2$hc$8^id>0@3$c@1$1@1$0#k0^i9@1$3$id@3$ia?1H\1c$h4@2$b@8$i1?1E^j6^j3^j2^ie^id^f^1@2$b@3$i8?1H^if@1$h2^1@4$hf^j2@1$2^j7^j0@1$h1@1$h3^1@2$h5@7$hb@hf$h9@1$3@2$j0^j4+4@1$3@1$2^j6^ib^ia^i9^i8^i7^i6^i5^j3^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@1$3$he^e@1$d@1$1@1$0#k0^if@1$hd$8^ie").

  (* [comment removed for export] *)
  Definition RLLVM_CATCH_PAD : Z := 0x47550.
  Definition RLLVM_AFTER_CATCH : Z := 0x47540.
  Definition eh_catch_law : ltac2:(zQ "00P") := ltac2:(zQ "je1!hi4!hk7!kr4!hm1!iu3!okd!ok5!kqb!lof!jte!jj2!mv2!igd!kie!ih5!ihd!ii4!hm8!h9!iie!lu3!lua!mie!mn8!ms2!pr1!pr8!prf!ps7!psf!pt6!ptd!pu4!pub!pv2!pv9!qg0!pjd!iuc!jk7!jr9!qgf!hs5!ija!sf!ik3!ig4!nj2!qp8!qqe!ql8!pqb!qm3!oq7!pgb!qj0!ph5!jjc!hhc!np7!ju6!nq9&>0@1$1@1$0#k0@1$h0@1$1@1$0#8>2fN$6>3tok@1$1@1$0#k0>1s$a>2LB@1$e$9>3LBX@1$e$9>1m$jc>2mo$ie>2lo$h2>1B$h2>2ra@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$7@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>0@4$i7?1H^ha@3$i9$9^h8^h9^h7>0@3$i6?1H^hb^h7>0@5$j7?1E@3$d$6^he@1$f$6^hd^ha^h9>0@3$j5?1E@3$d$6^hf@1$f$6^ha>0@3$i8?1H^hb^h8>0@2$b@1$5^i1^h9>0@4$h5$4^hd^hb@1$5^i2>0@2$b@1$if?5HCEIL^hc>0@2$b^hd@2$jd@1$5^i4@1$j4?1E>0@2$h7$4^i0>0@3$h1@1$1@1$0#k0^hb@1$8$jb=1R$j3@1$j8^i7@3$ja?1H\1c$ic@2$2@1$1@1$0#k0\3ra'@1$1@1$0#k0@2$2@1$1@1$0#k0\3gp'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$2@2$7@1$0#5@1$1@1$0#k0\2F'@2$7@1$0#5@1$1@1$0#k0@2$2~0\2m'~0@2$2$a\2s'$a@2$3@3$h1$ia@1$ib^h5@7$h6@hf$h4^h4@1$i5^h6^h3^j2^h2^h1^h0@1$h9^h6@1$ha^h6^f^e^d^c^b^a^9^8@1$hd^h6@1$he^h6@1$hf^h6@1$i0^h6@1$i1^h6@1$i2^h6@1$i3^h6@1$i4^h6@1$hb^h6@1$hc^h6^7^6^5^4^3@1$8$j0^i2@1$c@1$1@1$0#k0^2@1$h8$4@2$3@4$i7?1H^1^ja^2@2$3@3$i6?1H^1@1$h3^h5@2$3@3$j9?1H^j7@1$h3^h5@2$3@2$h7$4^2@2$3@4$h5$4^2^j6@1$5^jd@2$3@3$i8?1H^2^j5@2$3@2$j6?1E^2@4$j2^ja@1$5^jd^j8^2@2$id@7$h6@hf$h4^hf@1$i5^1^he^hd^hc^hb^ha@1$h9^1@1$ha^1^i7^h9^h8^h7^h6^h5^h4^h3@1$hd^1@1$he^1@1$hf^1@1$i0^1@1$i1^1@1$i2^1@1$i3^1@1$i4^1@1$hb^1@1$hc^1^h2^h1^h0^f^e@1$8$j1^d@1$c@1$1@1$0#k0^i3@1$h8$4^i2").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition opnew_ok_post : ltac2:(zQ "a0!hi4!hk7!h9!ih5!sf!ig4!kqb!jte!ju6!jj2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1s$9>2LB@1$3$7>1n$2>2lo$2>1B$2>1m$8>2mo$5>1c$4P") := ltac2:(zQ "ic1!hi4!hk7!kr4!hm1!h9!iu3!kh7!kv6!kie!ih5!ho6!jj2!kve!ihd!ii4!kkf!iie!lk8!igd!hm8!hs5!ija!sf!ig4!kqb!lpb!lq1!lu3!lua!mie!mj4!mn8!ms2!lof!iuc!jjc!jk7!jr9!jte!ju6!msd!mtc!of!mu9&>0@1$1@1$0#k0@1$e@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1s$b\2LB@1$9$i6\1n$4\2lo$4\1B$4\1m$i7\2mo$h7\1c$h6@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$2$b\2s'$b@2$2$4\1A$4@2$2@1$9@1$1@1$0#8\4junk@1$9@1$1@1$0#8@2$2$6\1p$6@2$3@3$h3$h4@1$h5^h5@7$hd@hf$hb^ie^id^ic^ib^h4^h3^h2^ia^i9@1$i1^3^h1^h0^f^e^d^c^b^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^a^9^8^7^he@1$he^ie^hd@1$h2@1$1@1$0#k0^6@1$i0$5@2$3@3$i2?1H^4@1$h0^h5@2$3@3$i3?1H^h6@1$h0^h5@2$3@2$hf$5^6@2$3@4$hc$5^6^h9@2$c@1$0#k0^id@2$3@4$h1$5^6@2$ia@2$c@1$0#k0^ib-q4@3$8$7@1$h9^5@1$d$7@2$3@3$i5?1H^6^h8@2$3@4$i9^hb@2$c@1$0#k0^id^h7^6@2$3@3$i8?5HCEIL^3^ha@2$3@4$i4?1H^4@3$8@2$a@2$a$6$4$4@4$f@2$a$6$4$4@4$f$6$4^1^3^ha^hb^6@4$h1$5^6^3@3$8$7@2$ha@1$ib^ha^2@1$d$7").

  (* [comment removed for export] *)
  Definition opnew_mf_stmt : ltac2:(zQ "00P") := ltac2:(zQ "j90!hi4!hk7!kve!hm8!lof!ok5!iu3!mv2!kie!hm1!h9!jj2!of!ih5!kv6!igd!ihd!kr4!lp5!nu8!iie!ija!sf!ik3!ig4!kqb!nj2!lpb!lu3!lua!mie!mn8!ms2!lk8!ql8!qs1!qt2!qtb!pqb!qm3!qi0!oq7!pgb!phf!ph5!iuc!jjc!jk7!hhc!jr9!qp0!np7!jte!ju6!npe!nq3!nq9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$j5>1s$b>2LB@1$d$j4>1n$a>2lo$a>1B$a>4errv@1$1@1$0#k0>2mo$h8>1G@1$d$5>1f$5>0@4$if?1H^9^8^a>0@3$id?1H^a^4>0@3$j1?1H^c^7>0@2$7@2$2@1$0#k0^id^8>0@4$hd$6^e^a@2$2@1$0#k0^ie>0@2$7@1$ha?5HCEIL^b>0@2$7^c@2$j8@2$2@1$0#k0^j0@2$c$i5@1$i7?1E>0@4$i1$6^h1@2$c@2$2@1$0#k0^if-q4@3$8$e@1$hb^b@1$h0$e>0@2$hf$6^h2>0@3$3@1$1@1$0#k0^j1@1$4$j3>0@3$3@1$1@1$0#k0^ic@1$4^h1>0@2$9@2$7+1^h2@2$j6^h2@2$j7+2+i0>0@2$ia?1E^h6>0@3$i9?1E@3$8$5^e^f^h7>0@3$3$i6@1$ic^f@d$j2^j8^j2^j1^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf>0@3$3@1$1@1$0#k0^ja@1$4@2$c@1$ib^h0+4@3$j0?1H\1c$h6@2$h2@ha$i3^jc^jb^ja^j9^j5^j4^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^hd^hc^ha^h9^h8^h7^h6^hb^h4^1@2$h1$b\2s'$b@2$9@8$i8?1E@3$8$5^h3^h4^1^ha^h8^h7^hd^2@2$9@3$ie?1H^h5@1$h4^2@4$i2^ha@2$2@1$0#k0^jc^hc@1$h3@1$h5^2@2$h7@7$he@hf$hc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc@1$4$i4^hb@1$f@1$1@1$0#k0^ha@1$i0$6^h3").
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_mf_hyps : ltac2:(zQ "00P") := ltac2:(zQ "hf0!hm1!qua!qv7!rg5!rhb!rj5!rkc!rlb!rm9!rn4!ro9!rpb!rqb!rrb!rt1!ru7!rve!sh4!si5!sjc!sl1!sm9!so0!sp0!sq2!sr4!ss6!st7!su8!qm3!mv2@2$0$8@2$0$1@2$0$2@2$0$6@2$0$3@2$0$4@2$0$5@2$0$7@2$0$hc@2$0$h7@2$0$h8@2$0$h6@2$0$ha@2$0$h9@2$0$hb@2$0@2$heZ@1$hd?1E@2$0$h4@2$0$f@2$0$h0@2$0$h2@2$0$h3@2$0$e@2$0$d@2$0$b@2$0$a@2$0$9@2$0$h5@2$0$h1$c").
  (* [comment removed for export] *)
End Iface.
(* [comment removed for export] *)
