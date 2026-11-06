(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec HeapCeil LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsDriverLaws AsDrvDefs AsMainPre AsInstance FakeStackRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsImages AsPlanImages AsStartupHSF
  AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceConst AsMainIfacePre AsMainIfaceArgs AsMainIfaceDepot AsMainIfaceFS
  AsMainIfaceAlloc.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsMainSyms.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos46Stdlib6ZArith6BinInt1Zhf2lehf3sub35stdpp9bitvectorbdefinitionsk2bbv_unsigned37Corelib4Init5Logicmd3and3h5LinuxProcessSemanticsfLinuxProcessSem3Runo78valid_spk22bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~s38HeapCeil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAsInstanceMain~~~~~~hg9fmain_ceil_ranges3amkHeapCeilhg94mctx79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsMainSyms~~~~~~hn57pm_symshg93k_Ehg93k_h69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainFacts~~~~~~hse3Xofhsechole_granted37Corelib4Init9Datatypesii36optionhg92KXhg96k_FULLhg96k_brk0hg95k_sp069OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainIface~~~~~~im87pm_vmemo76confighg93k_Rhg97k_model69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainState~~~~~~isc6A_MAIN69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~jh45ASEGS79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~jlc6cfg_of69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jqa3fx0hg95k_Vsphg99main_ceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsInstance~~~~~~kg2h0as_instance_stmtisc6P_main79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~km13asrkm15as_St01Zkm1casan_rt_hypshg95KCEIL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAsDriverLaws~~~~~~ksah0asan_driver_lawsksa8ADRV_CNTksa9ADRV_LIVEkm1fas_LIVE_CNT_MAXkm1bas_LIVE_MAXmd2eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslm1dmachine_stateo76cfg_ms79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~lr25asegskm16as_VIShg93KVMhg94Kcfgjqa4mkstjqa7seg_romk27Z_to_bvkm18as_AKRELii33nilkm16as_RFSkm16fframekm18as_RHEAPkm15blockkm1bas_rauxv_okhf2lthf3powkm15as_AL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsMainPre~~~~~~mobaAMAIN_COST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsDrvDefs~~~~~~mt8badrv_traces" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Existing Instance fx0.   (* [comment removed for export] *)
Lemma main_ceil_range : ltac2:(zQ "71!h9!j7!jc!lf!o1!r3!re&@2$2@2$3@1$0#k0^2+ogggg0>3sp0@1$6@1$0#k0>0@1$5^1@2$4@2$1+nvvvnvogggg0~0@2$1~0+nvvvvvogggg0").
Proof. intros sp0 [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2. lia. Qed.
Definition main_ceil : ltac2:(zQ "40!h9!r3!ve!re>3sp0@1$3@1$0#k0>1V@1$1^1$2") := ltac2:(zQ "70!h9!r3!hkd!hm0!jc!re!lf\3sp0@1$5@1$0#k0\1V@1$1^1@2$3@2$4@2$6@1$0#k0^2+ogggg0@2$2^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Record mctx : Type := MCTX {
  k_sp0 : word; k_brk0 : word; k_rdraw : EntryDraw; k_inp : ProcInput;
  k_h : nat; k_ch : acs; k_E : env; k_R : bvmap 5 word; k_FULL : word -> option byte; k_model : Model;
  k_Vsp : valid_sp k_sp0;
  k_Vbrk : valid_brk ASEGS k_brk0;
  k_Vav : valid_argv (in_argv k_inp);
  k_Vev : valid_envp (in_envp k_inp);
  k_Vfit : entry_stack_fits k_sp0 (in_argv k_inp) (in_envp k_inp);
  k_Hh : HSF_asan k_h = Some k_ch;
  k_HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT
           (SINV0 APH k_sp0 k_rdraw k_brk0 (in_argv k_inp) (in_envp k_inp) (in_uid k_inp) (in_hwcap k_inp))
           (argH0 APH k_sp0 k_rdraw (in_argv k_inp) (in_envp k_inp) (in_uid k_inp) (in_hwcap k_inp)) (in_fs k_inp) k_E k_ch k_R k_FULL k_model }.

(* [comment removed for export] *)
Definition KX : ltac2:(zQ "20!hmd!hr5>1k$0$1") := ltac2:(zQ "50!hs0!hs7!hmd!igc!ih3\1k$2@2$3@1$4@1$1^1@1$0^1").
Definition KVM : ltac2:(zQ "40!h9!re!ijb!hmd>1k$3>0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "80!h9!lf!ik5!ikb!il5!ilf!hmd!iq6\1k$6@4$7@2$1@1$0#k0@1$5^1@2$1@1$0#k0@1$4^1@1$2^1@1$3^1").
Definition Kcfg : ltac2:(zQ "20!ir1!hmd>1k$1$0") := ltac2:(zQ "80!ikb!ira!is1!hmd!jga!jl3!jq0!ju5\1k$3@6$6$7$5@1$1^1$4@1$0^1@1$2^1").
Definition KCEIL : ltac2:(zQ "20!hmd!ve>1k$0$1") := ltac2:(zQ "40!juc!ilf!jv5!hmd\1k$3@2$2@1$1^1@1$0^1").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit.
  Variable KH : ltac2:(zQ "20!kpe!hmd>0$1$0").
  Variable KS0 : ltac2:(zQ "20!kq5!hmd>1k$1@1$0@1?2KH^1").
  Variable KB : ltac2:(zQ "20!kqe!hmd>0$1$0").
  Hypothesis K_rt : ltac2:(zQ "30!kr1!ks1!hmd>1k$2@2$0@1$1^1@1?2KH^1").
  Hypothesis K_dl : ltac2:(zQ "20!lgc!hmd>1k$1@1$0@1?2KH^1").
  Hypothesis K_live : ltac2:(zQ "70!j7!o1!li1!lid!lja!lkd!hmd>1k$6@2$1@2$0$3@1$5@1?2KH^1@2$0$2@1$4@1?2KH^1").
  Hypothesis K_vis : ltac2:(zQ "f0!llc!h9!lp8!lq9!lud!lv6!mg0!mg7!ira!hmd!jga!ju5!mgf!mh7!mi2>1k$9@3$0$2@3$5@1?2KH^1@1?3KS0^1@1$3@1$7^1@5$c$b@1$8^1@2$e@1$1#k0$a@1$6^1@1$d$4").
  Hypothesis K_krel : ltac2:(zQ "30!mic!mg7!hmd>1k$2@3$0@1?2KH^1@1?3KS0^1@1$1^1").
  Hypothesis K_rfs : ltac2:(zQ "50!mj8!mjf!mk9!mg0!hmd>1k$4@3$1@1?2KH^1@1$0$2@1$3^1").
  Hypothesis K_heap : ltac2:(zQ "50!mj8!ml3!mlf!mg0!hmd>1k$4@4$1@1?2KH^1@1?3KS0^1@1$0$2@1$3^1").
  Hypothesis K_aux : ltac2:(zQ "a0!o1!h9!mm8!mg0!ilf!hmd!j7!mn7!mnc!lf>1k$5@2$0@3$2@1?2KH^1@1$3^1@1?2KB^1@2$0@2$6@2$9@1$1#k0@1$4^1@1?2KB^1@2$7@1?2KB^1@2$8+2+k0").
  Hypothesis K_al : ltac2:(zQ "40!mo2!hmd!msa!j7>1k$1@2$3@1$2@1?2KH^1@2$0@1?2KH^1@1?3KS0^1").
  Hypothesis K_tr : ltac2:(zQ "20!nh7!hmd>1k$1@1$0@1?2KH^1").

  Theorem instance_of_kit : ltac2:(zQ "30!kk2!kl7!ju5@2$0$2$1").
  Proof.
    intros sp0 brk0 mbase rdraw inp c P.
    ndestruct (P_main_open sp0 brk0 mbase rdraw inp c P) as (h & ch & E & R & FULL & model & Vsp & Vbrk & Vav & Vev & Vfit & Hh & HC & Hc & HF & PMx & SOK & LZ & PG & MC & VMEQ).
    set (k := MCTX sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    destruct (AsMainIfacePre.pre_can sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [can Hcan].
    nexists (KCEIL k), (KH k), (KS0 k), R, (KVM k), (KB k), (ps_tid (KX k)), can.
    split; [exact (K_rt k)|]. split; [exact (K_dl k)|]. split; [exact (K_live k)|].
    assert (Hcfg : c = Kcfg k) by exact Hc.
    split.
    2:{ rewrite Hcfg. cbn [Kcfg cfg_of cfg_model]. exact (AsMainIfacePre.pre_fs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC). }
    npose (AsMainIfacePre.pre_regs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (R1 & R2 & R4 & R10 & R11).
    pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    rewrite Hcfg. unfold Kcfg, cfg_of. cbn [cfg_ms cfg_model].
    split.
    - (* [comment removed for export] *) exact (K_vis k).
    - (* [comment removed for export] *) exact (K_krel k).
    - exact R1.
    - exact R2.
    - exact R4.
    - exact R10.
    - exact R11.
    - exact Vsp.
    - (* [comment removed for export] *) cbn [KCEIL main_ceil hceil k k_sp0]. lia.
    - (* [comment removed for export] *) apply (AsMainIfacePre.pre_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC); unfold AMLO, ATR_STACK; cbn [KCEIL main_ceil hceil k k_sp0]; lia.
    - (* [comment removed for export] *) apply (AsMainIfacePre.pre_sh0 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC (KCEIL k) eq_refl).
      npose (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (PD1 & PD2 & PD3).
      unfold AMLO, ATR_STACK. lia.
    - (* [comment removed for export] *) exact (AsMainIfaceArgs.pre_args sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_inv sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_relro sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_glb sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfaceConst.aconst_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_cells sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_ax1 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).   (* [comment removed for export] *)
    - exact (AsMainIfacePre.pre_bj sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).    (* [comment removed for export] *)
    - exact (AsMainIfacePre.pre_out sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact (AsMainIfacePre.pre_tid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    - exact (AsMainIfacePre.pre_errno sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC).
    - exact Hcan.
    - (* [comment removed for export] *) exact (K_rfs k).
    - exact (AsMainIfacePre.pre_latch sp0 brk0 h E FULL).
    - (* [comment removed for export] *) exact (K_heap k).
    - (* [comment removed for export] *) exact (K_aux k).
    - (* [comment removed for export] *) exact (K_al k).
    - (* [comment removed for export] *) exact (K_tr k).
    - (* [comment removed for export] *) exact (AsMainIfacePre.pre_fds sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
  Qed.
End Kit.
(* [comment removed for export] *)
