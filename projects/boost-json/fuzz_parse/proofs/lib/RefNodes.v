(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the system-call robustness premise (sys_rob). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg Amb RelSpec
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes Gap04.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase RomWrite.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefNodes () := KReplay.lz_vm "#%Y1C47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?Krespectful_per_oblig!t3$_1C4ELinuxProcessSemantics?!s<22Fs4path!t6,4Init5Logic8eq_ind_r!stN2Fs!sT;5Riscv7Prelude5bvmap!tF86!tF%!tDK5State7PipeBufK!vP,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!vz#s2bv00I!u-19Datatypes4prod!sF?list!sF>6op!t4#00!utQ8m_haltedK!vo72eq01!v7G3I!w:QFdEntry!uF#!s^O5Model!uZS9m_vm_lazy!t<Q6VmMaps!w;/!xd4Z00!v>G1C79OSSVerify!~K#ofs:boost_json:fuzz_parse3!sn#FileSim;adv_eff_retC13~~~!smP:AgentNodes5epend!sj%K!yyA1K!vCP=SyscallEffect0!#3GK3Run<apply!uX#ect!s_O@advance_past_svcK!wh?2C!}N@4BvWfK!}qD!x1Q8PropExec6regupd!x,V!si,v_addi!si_4mks!yY&I!~G;!}BL>!#76#!sE+=machine_s!x~#!~1S7MemCopy!#51=3nat!|u/!u--4True!z3M!u02<write_to_mem!}XQCat!wa$wbytes!waV!sh'C!tR/_!su\!xX+7fp_regs!~JB!#8}&1!sHD2!zsZfp_csr!tU'!ypg!tz=!#<'$1!#50A!u@Q:Stream!uB#?adv_!#4Z$!wt$!wf&!uKY:fetch_word!shZ8is_ecall!~jZgetr!u9'!#5L>7Z!zU#bv!sLA;bv_unsignedC56Stdlib6ZArith6BinInt1Z3pow!sC<2lt!#=gP5m_fds!#>CQfd_lookup!|fZseg_rom!xjQ!tJ,remove!#B{Qwith!ua#K!#;bM6config01I!u^PShapeAlg8realizes00!#8~&!u%JMonad7outcome!#C&L!u&#9sys_inpu!xwNpecs<s!#?c$_spec!vzQ6in_argC5!ttJSys7!#@y%4fd32C6!s_M2Fs4Open:close!t{&!#:l53iffK!w5Y1!#OW>?eq_p!#Po#!s,#xy!sR?Mtrans_co_!#Mc#v_impl_m!sE&!}z<>pow_pos_nonneg!~J>e!sB<:!sj#!sf%K4!sJ&9micromega6VarMap1t01I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr01K!stL1!stE7!sI65Tauto8G!sm'5C!sJ<B!sJ&!sH6:Z!t_+=Z!sT$CheckerC!vJ<4f!#S2#!sq?C!sq0_sound!#Dn73and00!#6XP!#Kd#Lib7u64_lit!#6XV8in_sysno!#MvX!sd'_s!#H+V7RelSpec?!#44-_57!#>]_6ms_gpr!tWX=!#3f$!~r&!tU&!#57U7fd32_id!#P|Z=!u:%_!#Q'#0!vxW!wg&:!#7K$0!wf+c!yxPRef!t^$@!#<6&!#X:%'!ss_=!ss+lazy!xZ`8set!vG#0!w/\adv_!sk#!#U5,!srP5!sm$Brz_ret_only_silen!#Vma6rz!|g#!#Is&!#5JC4!#5J;5eKi!#3z3!#IO,unit!#7n7!se%4kin!#J7?!sf$!#U1Q!#Aa&4TSe!#S[8!t/-bool!#Qs3!sF31!#Wf?1!#SXP!#Z01!tJ=!#S^#1!#hBD>iff_Tran!#]c$!#`AQeven!#c?4!#Tm-!#=H6!#9{,;!#>e$!w]$!xY8!#<~03Op203!sMI5!#6eW9nodevnull!#J'Werrno!|~#!w_A2!#7`V5cm!#ErT5Ioctl:i!s+#!#Es$!#;Ld29!#<?]A!tY%tty!#:j1!#:-f1!#:-d1!#>n+!#K:PENOTTY!#S+<add!x&R9ReadWrite9read!x,k63!#>|UUac!s5#@!s,%_okb_intro!t^X@!uE$dir!xqv2!xqe2!xq+!#jMP!#o`'6!#3<QTASK_SIZE!z1SISDIR!tsZ2!t;Q4m_f!#Z5K!z{#fs!#Z2&!#AwX@ms!#_x#able_byt!#YVQ>!yz$!#eI#_!#yJ#!u0Nile_!se#C!#dn;length!~K<6of_nat!#_iAbv_wrap!sl=modul!|qQ!#]j'9u64_rang!#cXQ6BvBase;word_to!u=%!u}03Nat3sub!u-+5!u,$8Peano!sB#!s&#min!#5a<!sC?6!tB&!sc<!tH#!#?V68i!#vK#fl!#EF5;Zify!#A$%3inj!sIB5mkrel!tQ34Znat5Nat2Z9i!#X[C8max!#7X$!sH=in!sH$!#@^C5Psatz02!#Y0?2!#WID2!unB;rew_!ve%v!sQB9and!#\$$!#F]?3!tc>3P!#GD$!usI4!uUE4!w1<9mod_smal!xC?7inj_!zY#!#91V@!~p%_!#3B+!#9}T!}r+=!~x&64_mo!sp'!#3R?@!#l=%!#kt+!~MQ8len!#nu$!#>SVdelivered!#pQ$s!tzA6b!#{:#!#;jQfd_inser!#6SAC!v#'!v&V!#9/&w_count_clamp!scQD!sc1!z2&!|0+5Lists7!s+#Def6firstn!t0Q7in_w!#zqS!#BW%E!#;[0_prefix!#Aha!t\#!#_K`A!te$!|I$!#D?0!#QuC;r!$;9%ity!#9f=ax!#8@Dapp!sKB6!sK$2!$&C8or!#QvE!#4z%6K!#RsL!#8C@3!#YwE6!sJF!snG8!v=68!v=#Inst@!#A$$!#>p%_eq!#>\?!#>|-!#7/4;inj_sub_max!vHN1!#UnH1!|~Q<MAX_RW_COUNT!ux?7Inj_Z_Z!zsE=iff_!$C2,!#GEW8store_ok!#9YP!#k_&J!~h2of_!sw+!#D^O!te25wview!$3N9x00!xe9Z2!xg#!#hc\F!#JJ2!#dc-!#g1XD!#4B3!#hwa!#fN#r!#fN0!#iiY!sp#!#<X#1!#gCa6rz_d!$>~'!#{<U;ope!~N#!#WAi56!#WAT4Uapi:AT_FDCWD32!vrY5Hno!tL\8!tL'!|CZ<ms_!}F+!#<vW3mrb!xtV!|Q-B!tR/!ym0!#6,O6in!$;wT!u;&9!sb%!#?2+!zOVEmodeled_!zW#_flags_rd!#HUX3rdn!uz'!#:k&!#CG#4!s+#2In!$'o8not!t>Y:rdn_!#VX%!#Bq\H!x4$cstr_toolong_of_!uA-!#HEO!ss+!~<X:!wL$!sj#s!tLW<!#w5#copyins!#6&Y!#4O,_h!#NVX!uD'F!sr&!vu+!#cC[!#6|$J!#wA-!u\&!#wI0!vLQENAMETOOLONG!#r#P;!yE$resul!#s[#!sb\!#6|YB!}d-!}w&!#;g^!#:4#_!#48%!sn^7path_a!$M39!#FP#2l!$:m#!#^_4!#R@#!#rb:app!w'^!$V/X@!~v,!~n08!srN3Lib2Nd:and_elimF3!v}_<!v}&!#3f$!}N]D!}N&emp!#s\3!#:[PENOENT!#vaRNamei>!uC$has_slash!#:ZV!si%is_dirref!v&XE!v&&absent!v'1!$$7A!$LqP4ScfgGfamily_off_!tG&fals!wCX8alloc_f!#=CQ!$'7&6t_alt2!y]^8!#3<#out!sj^B!u|&dot!#8mc7rz!vs$!sg&!ygV=!|#'rrno!#</Y>!#7A$!xV&n!v:^C!y8'!#[-3!thZmprotect!#9%$!sq_5tid_I!uRV!z=+5!z=$!xZ\;node!w+&!#7>\9ex!#7=$1!tW\8rz_cas!$\VX!v''7!uD$!#VH'!zxN6Kernel4Fork@PID_MAX_ENVELOPE!#MtY>ms_svc_pending!#4DP5m_tid!u9[Dset!sf#_address!$QBU!$U>$t!#XjQ!#Se896!}u^E!uB'fresh!#f#:!#9P#6!sV#if9proj1_sigK!sF83sig!#@[Q6CatSimE!$m3-_no!$_a-!$g27!$KJ#1K!#],:1!#A<`!#9lV!#<-#8the_scfg!ve'!y}JRun<injected_arm!tHUAnot_spuriou!#zj#!#71_?!zc'!$Gk%!sr_=!sr+!$Gj+I!v7N9sstep_cfg!#L8L!s^#7!s]$to!$B1L!s\0!$@S2!{J/0!sxO!$`2&!s[P;I!x|&Arm!$SrQ!x}$D!yd/!x}$!#33'!#IRY!#8Q#!#39%!#9B^4!#mc#!~8%!sgX!$c;+!#Ks_:!v2#!zT#!#j?+!#{'Cn!#FJ\exi!#E^WExit!#w>#s!si$_no!#5l=2or!%-5-!s@2!$LhY7rz!u4/!#;3OA!%&l#materi!w{$!#}RQ8!sf#map!$lnQ>vm_backed_!scUA!sY#_subtract_!#~-#!sfO:liv!#ns$s!#z`=u!s|R?!uI,!t%$!$/dD5!sIE3!tRYing_us!x:S9page_siz!$=OQ;region_fre!#jjQMmap!#Xw$!sg+_cons!#@r7!|6%7f_equal!#[1;8list_i!$dI95False!%3zR:iv_overl!%:I3!#U%,negb!sD=andb!#iK'4Bool!s'$=!s\#_true_iff!sG6>!s_#!#U:$!sH$!zo<ltb!$=9<ltb_ge!t,6;!t,$!tN$r!seA!$xeR;iv!}Z+!s`Q=!~>0!#93XI!~B,_!tW-_l!#R_`!s|-app!ze3!$#e:CPreOrder!$ZV,!tOYK!tO-!#5\0l!$18K<t!tS'ity!tUYF!#7$3!}m/!y];;le_preo!v$#!ybRvm_no!$:Z$!s`Q7!#:|#p!#Z%YO!w5<!ui#l!#_\W=vm_!s},!tfYG!#9b1_le!sz$!{B_F!#921_simp!uYY8!uY$mi!$J2=le!#4\>eb!v{#!y9Treserv!#;=R<vm_start_brk!saQ6!vR#!s[S!t>#mmap_bas!u[R:vm_init_s!#o4Q!%F{&!$6IQ;!#P$#!#Cg$!ylYA!sh-!#Pm#!$rL_G!zb3!{^0!#GdPAllocSim>!tp/v!%2p&!#fzNMm8M!#dG%C!#dP0_next!#6aZ!sp5!#NV'!tm[B!s{+budget_ok!tlYC!$ML'!$%u%!ti,!$>d<6inj_le".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos3h5LinuxProcessSemanticsfLinuxProcessSem5Statehf8m_halted35stdpp9bitvectorbdefinitionsl82bv37Corelib4Init9Datatypesna4listna6optionna4prod37Corelib4Init5Logicq92eqhf7FdEntryhf5Modelhf8with_fdshf9m_vm_lazyhf8with_tidhf6VmMapshfbwith_vmmaps01Zhffvm_forget_rangena3nilna3natq91I3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshj2dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhnah0advance_past_svchnacapply_effecthf7MemCopyhf9mkEffectU3h5LinuxProcessSemantics5Riscv7Preludehu15bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAgentNodes~~~~~~ih05epend69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~il64mkstil66regupdil66v_addil82BVl84BvWfna4consna4pair69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~is76wbytesna4Somehna5mkCfghf5m_fdsil64getril67seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jj68realizesl87Z_to_bvna4Nonena4boolna4truehj2afetch_wordhj28is_ecallhf9fd_lookuphf9fd_removejj64TSet46Stdlib6ZArith6BinInt1Zjt62ltjt63powl8bbv_unsignedhf6ENOTTYhf9errno_ret69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~khe9nodevnullhf6EISDIRhf5FdDirhf9TASK_SIZEjt63addjt62lehj26ms_gprhfdSyscallEffect3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasekq98len_word3h5LinuxProcessSemanticsfLinuxProcessSem5Monadku47outcomehf6FdFileq93iff3h5LinuxProcessSemanticsfLinuxProcessSem2Fslic9file_readlic9fs_lookuplic4pathku42Okhj2h0ms_writable_bytehna9sys_input3h5LinuxProcessSemanticsfLinuxProcessSem5Specslq1csyscall_spechfcMAX_RW_COUNThf5eventhf9fd_inserthf4m_fshferead_bytes_map4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Uaccessmhah0delivered_writesl86bv_addhj28store_okjt66to_nat5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openmo2h2modeled_open_flagsna6lengthq93andna3appq93not37Corelib4Init3Natmu83add37Corelib4Init5Peanong12leil63rdn36Stdlib5Lists4Listni22Inhf6CstrOkhfbcstr_resulthf9read_cstr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7FileSim~~~~~~nle3mrb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib8RefNodes8WithSegs6Openat~~~~~~npf7path_athf8m_vmmapshfdmaps_subtracthfcmkVmMapsFullhf6vm_brkhfavm_init_sphf8vm_limithf7vm_mapshfcvm_mmap_basehfbvm_noaccesshfbvm_reservedhfcvm_start_brk5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm8Mprotectoo4h3mprotect_model_next79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8RefNodes8WithSegs~~~~~~ot4emprotect_model37Corelib4Init6Specifpia3sig5h5LinuxProcessSemanticsfLinuxProcessSem3Sys6Kernel4Forkpk6h0PID_MAX_ENVELOPEot45tid_Ipia9proj1_sighj2ems_svc_pendinghj28set_gpr0hf5m_tidjj67node_okq92orjj66t_exitl86bv_andhfh1m_vm_materializedhffvm_backed_byteshffvm_backing_usedhfbregion_freehfalive_byteshfbiv_subtracthfh1maps_subtract_allhfdvm_live_bytesoo4h2mprotect_budget_okkq9bword_to_natmu83sub46Stdlib5Arith8PeanoNat3Natqq63min3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeqs87Segment4h5LinuxProcessSemanticsfLinuxProcessSem3Sys4Uapirg88AT_FDCWDmo2h2open_ignored_flagsjt65ldiff" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* LPS 727298f3: [RomBase.sys_rob] at a system call whose specification does not read [in_mem],
   from the equation naming its number ([ShapeAlg.rz_node] asks it). *)
Ltac rob_mf Heq :=
  eapply RomBase.sys_rob_memfree;
    [ first [reflexivity | eassumption]
    | rewrite Heq; first [RomBase.memfree_lit | rewrite u64_lit by lia; RomBase.memfree_lit] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_halted' : ltac2:(zQ "a0!h9!kd!n5!p2!p9!q2!rd!s2!sc!t4>3fds@1$3@2$5@1$2@1$0#k0$7>1m$8@3$6@1$4@1$2@1$0#k0@1$1@2$9^2^1@1$1^1").
Proof. intros fds m. reflexivity. Qed.

Lemma with_fds_lazy : ltac2:(zQ "90!h9!n5!p2!q2!tf!rd!s2!sc!t4>3fds@1$2@2$3@1$1@1$0#k0$6>1m$7@3$5@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0@1$4@2$8^2^1@1$4^1").
Proof. intros fds m. reflexivity. Qed.

Lemma with_tid_halted : ltac2:(zQ "70!h9!kd!n5!p9!rd!sc!ub>1t@1$2@1$0#k0>1m$5@3$4@1$3@1$2@1$0#k0@1$1@2$6^2^1@1$1^1").
Proof. intros t m. reflexivity. Qed.

Lemma with_tid_lazy : ltac2:(zQ "80!h9!n5!tf!p2!q2!rd!sc!ub>1t@1$1@1$0#k0>1m$6@3$5@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0@1$2@2$7^2^1@1$2^1").
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_lazy' : ltac2:(zQ "90!h9!tf!n5!p2!q2!rd!sc!v6!vf>1h$7>1m$6@3$5@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0@1$1@2$8^2^1@1$1^1").
Proof. intros h m. reflexivity. Qed.

(* [comment removed for export] *)

Lemma vm_forget_range_halted : ltac2:(zQ "80!hgd!kd!p9!rd!h9!sc!hh0!n5>2lo$0>2hi$0>1m$5@3$3@1$2@1$7@1$4#k0@1$1@3$6^3^2^1@1$1^1").
Proof. reflexivity. Qed.
End FPX1.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!p2!qvd@1$0$1").
Context {SC : StepCfg}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : ltac2:(zQ "h53!h9!n5!hi2!q2!p9!p2!hi8!hie!rd!hm9!hq6!hrb!hsb!ht5!ig7!ikd!ip1!ip9!iq3!iqd!ir2&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$e@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0@3$8$9@1$a@2$b@6$f?2fx^6^5^4^3^2@6$d^1@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~2~2@1$2$c@1$2@2$3@1$1@1$0#k0$6@5$h0?2fx@3$h1^6@3$h3@1$0#5+aKv$7@2$h4@1$0#5+a^1@2$h2^5+4^4^3").
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_write1_epend : ltac2:(zQ "h84!h9!n5!hi2!q2!p2!p9!ir9!hi8!is0!hie!rd!hm9!hq6!hrb!hsb!ht5!ig7!ikd!jg1!ip1!ip9!iq3!iqd!ir2&>0@1$1@1$0#k0@1$5@1$1@1$0#8&@2$3@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2>4regs@2$h0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>3buf@1$1@1$0#k0>4data@1$4@1$1@1$0#8@3$a$b@1$c@2$d@6$h1?2fx^8^7^6^5^4@6$f^3@3$6~1@4$8@1$1@1$0#k0@1$4@1$1@1$0#8^2^1@1$2~1~3~3@1$2$e@1$2@2$3@1$1@1$0#k0$7@5$h3?2fx@3$h4^8@3$h6@1$0#5+aKv$9@2$h7@1$0#5+a^3@2$h5^7+4@3$h2^6^2^1^5").
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_close : ltac2:(zQ "i52!h9!n5!rd!p9!hie!s2!iqd!ir2!jgb!q2!jh2!jhb!ji3!ip1!jib!jn1!jnd!jo7!joe!p2!hi2!jp5!jpc!jqa!sc!jr6!js2!kd!tf!t4!ig7!ip9!iq3!jse!jue!jv4!jvb&@2$9@1$1@1$0#k0@1$1@1$0#k0&@3$6@1$0#5+aKv$4@2$7@1$0#5+a>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>5model$h8>1w@1$1@1$0#i0>2fd@1$1@1$0#k0>1e$5>1K$i1>0@3$2@1$3@1$1@1$0#i0@2$h6?4segs^7@2$8@1$1@1$0#i0^4>0@3$2$h2@1$h7^5$h5>0@3$2@1$3@1$1@1$0#k0@1$hb^7@1$h1@1$1@1$0#k0>0@3$2@1$h3~0@1$hc^8@1$h4~0>0@3$2@1$1@1$0#k0@2$c^c@3$6@1$0#5+h1Kv$4@2$7@1$0#5+h1@2$h0@1$0#k0+j9>0@3$2@1$1@1$0#k0@2$c^d~1^8>0@2$i2@2$i4@1$0#k0^9@2$i3+2+i0>0@3$2@1$3$5@2$h9@1$b^c^a@2$8$5^9>0@4$f?4segs?2SC@2$a@5$d?2fx@3$hf^h0~1@2$h0@1$0#k0Z@2$i0^f+4^e@1$e?4segs@2$hd@2$ha@1$b^d^b^d^9@4$f?4segs?2SC@2$a@5$d?2fx^h1^h0^f@1$e?4segs^e^a").
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | | | rob_mf H17 | rewrite adv_set_epend; exact Hc].
  - intros o. rewrite (syscall_spec_57 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, ms_gpr_epend0, Hfd, (fd32_id fd Hfd32). exact (close_outcome fd _ model e o Hlk).
  - rewrite with_fds_halted'. exact Hh.
  - rewrite with_fds_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_ioctl_winsz : ltac2:(zQ "i62!h9!n5!rd!p9!hie!iqd!ir2!s2!ji3!jgb!q2!jh2!ip1!jib!jn1!jnd!jo7!joe!p2!hi2!jp5!jpc!jqa!kg9!sc!kh2!jr6!jhb!kd!tf!ig7!ip9!iq3!kl8!jse!jue!jv4!jvb&@2$a@1$1@1$0#k0@1$1@1$0#k0&@3$5@1$0#5+aKv$4@2$6@1$0#5+a>4regs@2$he@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>5model$h8>1w@1$1@1$0#i0>2fd@1$1@1$0#k0>1e$7>1K$i2>0@3$2@1$3@1$1@1$0#i0@2$h5?4segs^7@2$9@1$1@1$0#i0^4>0@3$2$h1@1$h6^5$h4>0@3$2@1$3@1$1@1$0#k0@1$hc^7@1$h0@1$1@1$0#k0>0@3$2@1$h2~0@1$hd^8@1$h3~0>0@3$2@1$1@1$0#k0@2$8^c@3$5@1$0#5+h1Kv$4@2$6@1$0#5+h1@2$f@1$0#k0+hd>0@3$2@1$1@1$0#k0@2$8^d~1^8>0@2$i3@2$i5@1$0#k0^9@2$i4+2+i0>0@3$2@1$3$7@2$ha@1$hb^c^a@2$9$7@1$i1^9>0@3$2@1$1@1$0#k0@2$8^h0@3$5@1$0#5+bKv$4@2$6@1$0#5+b@2$f@1$0#k0+lkh3>0@4$e?4segs?2SC@2$b@5$c?2fx@3$hf^h1~1@1$h9$h7@2$i0^h0+4^f@1$d?4segs^e^a@4$e?4segs?2SC@2$b@5$c?2fx^h2^h1^h0@1$d?4segs^f^b").
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H11 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy
                             | eapply (RomWrite.ioctl_tty_rob segs _ model (getr regs 17));
                                 [reflexivity | rewrite H17; apply u64_lit; lia | rewrite ms_gpr_epend1, H11; reflexivity]
                             | rewrite adv_set_epend; exact Hc].
  intros o. rewrite (syscall_spec_29 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
  rewrite in_arg0_si, in_arg1_si, ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), H11.
  apply (ioctl_tty_outcome fd _ _ model e o Hlk). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_read_dir : ltac2:(zQ "i92!h9!n5!rd!hie!iqd!ir2!p9!ji3!jvb!jgb!q2!jh2!s2!ip1!jib!jn1!jo7!joe!p2!hi2!jp5!jpc!jqa!km5!kme!sc!kn6!kh2!jr6!jhb!kd!tf!ig7!ip9!iq3!jse!ko2!ko9!jue!jv4!jnd&@2$a@1$1@1$0#k0@1$1@1$0#k0&@3$4@1$0#5+aKv$3@2$5@1$0#5+a>4regs@2$i0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$6@1$1@1$0#8>5model$h9>1w@1$1@1$0#i0>2fd@1$1@1$0#k0>1K$i3>0@3$2@1$6@1$1@1$0#i0@2$h5?4segs^6@2$9@1$1@1$0#i0^3>0@3$2$h1@1$h6^4$h4>0@3$2@1$6@1$1@1$0#k0@1$he^6@1$h0@1$1@1$0#k0>0@3$2@1$h2~0@1$hf^7@1$h3~0>0@3$2@1$1@1$0#k0@2$7^b@3$4@1$0#5+h1Kv$3@2$5@1$0#5+h1@2$i8@1$0#k0+jf>0@3$2@1$1@1$0#k0@2$7^c~1^7>0@2$i6@2$8@1$0#k0^8@2$i7+2+i0>0@3$2@1$6$c@2$hc@1$hd^b^9@2$9$c$h8>0@2$i5@2$i4@2$8@1$0#k0@2$7^f@3$4@1$0#5+bKv$3@2$5@1$0#5+b@2$8@1$0#k0@2$7^f@3$4@1$0#5+cKv$3@2$5@1$0#5+c$ha>0@4$f?4segs?2SC@2$b@5$d?2fx@3$i1^h0~1@1$hb$h7@2$i2^f+4^e@1$e?4segs^d^a@4$f?4segs?2SC@2$b@5$d?2fx^h1^h0^f@1$e?4segs^e^b").
Proof.
  intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hdir Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rob_mf H17 | rewrite adv_set_epend; exact Hc].
  intros o. rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
  apply (read_dir_outcome fd _ _ _ model o Hlk). apply access_okb_intro. exact Hdir.
Qed.

(* [comment removed for export] *)
Lemma read_file_outcome_si : ltac2:(zQ "ic2!h9!n5!kof!p2!rd!jvb!hi2!jgb!p9!q2!kp9!kt8!lh2!s2!lhd!sc!jhb!ko9!jue!hi8!li6!hgd!ll7!lm4!ln1!ln9!hm9!lnf!lp4!lsf!ltf!hsb!kn6!lue!lv6!jr6!mg2!ht5!mg9!t4!mke!ko2!jv4!mm3&@2$9@1$1@1$0#k0@1$1@1$0#k0&@1$6~0>2ms$ha>2x8@1$1@1$0#k0>5model$f>2fd@1$1@1$0#k0>1p$h8>3off@1$1@1$0#k0>4data@1$3@1$1@1$0#8>2wv@1$3@1$1@1$0#8>0@3$4$h5@2$5@1$0#k0^7+jf>0@3$4@1$1@1$0#k0@2$2^9N0^6>0@2$h2@2$5@1$0#k0^7@2$ia+2+i0>0@3$4@1$8$d@2$i3@1$h0^9^8@2$7$d@2$e^7^6>0@3$4@1$8@1$3@1$1@1$0#8@2$h7@1$i4^a^8@2$7@1$3@1$1@1$0#8^6>0@3$4@1$8@1$3@1$1@1$0#8@3$i6@2$hb?4segs^d@2$2^dN1@2$2^dN2@2$7@1$3@1$1@1$0#8^6>0@2$h2Z@2$5@1$0#k0@2$2^eN2>0@2$h1@2$5@1$0#k0@2$2^fN2$he>0@2$h1@2$i9@2$5@1$0#k0@2$2^h0N1@2$5@1$0#k0@2$2^h0N2$i0=2bs@1$3@1$1@1$0#8@3$h6^b^c@2$2^h1N2=2m'$f@2$i7@3$i2@1$h0^h0^f@2$e^e@3$ib@1$0#k0^d@2$b@1$1@1$0#8^1^h0>1o@1$c$a@2$h4@3$hd@3$hc?4segs^h4^h3^h2^1@3$4@1$c$a^1@4$h9$a@6$i5@2$b@1$1@1$0#8^3@2$i8@2$2^h4N1^3~1~1@1$6$hf@1$6@2$9@1$1@1$0#k0$h3^2@1$6$i1").
Proof.
  intros ms x8 model fd p off data wv Hno H0 Hfd32 Hlk Hfs Hw Hpos Hcnt Hok. cbv zeta. intros o.
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, (fd32_id fd Hfd32).
  assert (Hcl : Z_to_bv 64 (rw_count_clamp (ms_gpr ms 2)) = ms_gpr ms 2).
  { rewrite (rw_count_clamp_small _ Hcnt). apply Z_to_bv_bv_unsigned. }
  rewrite (read_file_outcome fd (ms_gpr ms 1) (ms_gpr ms 2) (sys_input segs ms x8) model o p off data
             (firstn (word_to_nat (len_word (file_read data off (ms_gpr ms 2)))) wv) Hlk).
  - rewrite Hcl. reflexivity.
  - apply access_okb_intro. exact Hok.
  - exact Hfs.
  - rewrite Hcl, in_wmem_si. exact (read_bytes_map_prefix _ _ _ _ _ HL Hw).
Qed.

Lemma rz_read_file : ltac2:(zQ "j44!h9!n5!rd!hie!iqd!ir2!ji3!p2!p9!jgb!ko9!joe!q2!jp5!kt8!jh2!s2!lhd!jhb!ip1!jib!jn1!jue!jv4!jnd!jvb!jo7!hi2!hgd!ll7!lm4!ln1!jpc!jqa!mmc!ltf!sc!kn6!lv6!jr6!mg2!kd!tf!t4!ig7!jg1!ip9!iq3!jse!ko2!mn8!mm3&@2$c@1$1@1$0#k0@1$1@1$0#k0&@3$4@1$0#5+aKv$3@2$5@1$0#5+a&@3$4@1$0#5+cKv$3@2$5@1$0#5+c&@3$4@1$0#5+bKv$3@2$5@1$0#5+b>4regs@2$ic@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$8@1$1@1$0#8>5model$i4>1w@1$1@1$0#i0>2fd@1$1@1$0#k0>1p$hf>3off@1$1@1$0#k0>4data@1$7@1$1@1$0#8>3cnt$hc>1K$j0>0@3$2@1$8@1$1@1$0#i0@2$i0?4segs^a@2$9@1$1@1$0#i0^7>0@3$2$b@1$i1^8$d>0@3$2@1$8@1$1@1$0#k0@1$i9^a@1$ha@1$1@1$0#k0>0@3$2@1$7~0@1$ia^b@1$hb~0>0@3$2@1$1@1$0#k0@2$6^f@3$4@1$0#5+h1Kv$3@2$5@1$0#5+h1@2$h8@1$0#k0+jf>0@3$2@1$1@1$0#k0@2$6^h0~1^b>0@2$h6@2$h9@1$0#k0^c@2$h7+2+i0>0@3$2@1$8$h0@2$i7@1$h2^f^d@2$9$h0@2$h1^c^b>0@3$2@1$8@1$7@1$1@1$0#8@2$he@1$i8^h0^d@2$9@1$7@1$1@1$0#8^b>0@3$2@1$1@1$0#k0@2$6^h4~2@2$h8@1$0#k0^b>0@2$a+1^c>0@2$a^d$i3>0@2$h6^e@2$h7+2+k0>0@2$a@2$j1@2$h9@1$0#k0@2$6^h8~3^f$i5>0@3$2$b@4$i2?4segs^h7@2$6^h9~3@1$j2^h0$d=2bs@1$7@1$1@1$0#8@3$hd^h2^h3@2$6^ha~2>0@4$h5?4segs?2SC@2$f@5$h3?2fx@3$ie^hb~1@2$e@1$1@1$0#8^1@2$if^ha+4@3$id^h9@2$6^hb~3^1@1$h4?4segs@2$ib@3$i6@1$h2^h8^h6@2$h1^h5@3$j3@1$0#k0^h4@2$e@1$1@1$0#8^1^h8^h1@4$h5?4segs?2SC@2$f@5$h3?2fx^hc^hb^ha@1$h4?4segs^h9^h2").
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hover Hok bs Hc.
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
  { unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
  pose proof (read_file_outcome_si ms (getr regs 17) model fd p off data wv Hno
              ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
              ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
              ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; exact Hover)) as Hchk.
  unfold ms in Hchk. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
  subst bs. revert Hc Hchk.
  generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
  eapply (rz_det segs _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | exact Hchk
    | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | rob_mf H17 | ].
  destruct bs as [|b bsr]; cbn [delivered_writes].
  - unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
  - unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : ltac2:(zQ "60!h9!n5!jgb!p9!rd!jpc@3$4@1$3@1$1@1$0#i0@2$5?4segs?2pc@2$2@1$1@1$0#i0?1w").
  Hypothesis HE : ltac2:(zQ "40!joe!jp5!rd!jqa@3$2$0@1$3?1w$1").
  Hypothesis Hh : ltac2:(zQ "60!h9!n5!jo7!p9!rd!kd@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!h9!n5!q2!p2!hi2!rd!tf&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis H17 : ltac2:(zQ "80!h9!hie!rd!ji3!iqd!ir2!jnd!n5@3$2@1$7@1$0#k0@2$3?4regs@3$4@1$0#5+h1Kv$1@2$5@1$0#5+h1@2$6@1$0#k0+j8").
  Hypothesis H10 : ltac2:(zQ "80!h9!hie!rd!rj9!ji3!iqd!ir2!n5@3$2@1$7@1$0#k0@2$4?4regs@3$5@1$0#5+aKv$1@2$6@1$0#5+a$3").
  (* [comment removed for export] *)
  Hypothesis Hfl : ltac2:(zQ "a0!h9!hie!rd!hgd!rk5!ji3!rlc!iqd!ir2!jvb@3$2$3@2$6@2$9@1$0#k0@2$5?4regs@3$7@1$0#5+cKv$1@2$8@1$0#5+c$4Z").

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : ltac2:(zQ "80!h9!hie!rd!hgd!ji3!iqd!ir2!jvb@3$2$3@2$7@1$0#k0@2$4?4regs@3$5@1$0#5+h1Kv$1@2$6@1$0#5+h1+j8").
  Proof. rewrite H17. apply u64_lit. lia. Qed.

  (* [comment removed for export] *)
  Lemma openat_spec_head : forall o,
    syscall_spec (sys_input segs ms (getr regs 17)) model o <->
    openat_spec AT_FDCWD32 (getr regs 11) (getr regs 12) (sys_input segs ms (getr regs 17)) model o.
  Proof.
    intros o. cbv delta [ms].
    rewrite (syscall_spec_56 _ model o) by (rewrite in_sysno_si; exact Hno56).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10.
    reflexivity.
  Qed.

  Lemma open_in_mem : in_mem (sys_input segs ms (getr regs 17)) = mrb segs mem.
  Proof. cbv delta [ms]. rewrite in_mem_si, ms_read_byte_epend. reflexivity. Qed.

  (* LPS 727298f3: an openat whose path read does not fault reads the same over a larger backing *)
  Lemma openat_node_rob : read_cstr (mrb segs mem) (getr regs 11) <> CstrFault ->
    RomBase.sys_rob segs (mkCfg ms model).
  Proof.
    intros Hnf. apply (RomWrite.openat_rob segs ms model (getr regs 17) eq_refl Hno56).
    cbv delta [ms]. rewrite ms_read_byte_epend, ms_gpr_epend1. exact Hnf.
  Qed.

  Lemma open_flags_modeled : ltac2:(zQ "90!h9!joe!jp5!hie!rd!mr6!ji3!iqd!ir2@3$4$1@1$5@2$6?4regs@3$7@1$0#5+cKv$3@2$8@1$0#5+c$2").
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    (bv_unsigned (getr regs 11) + 4096 <= TASK_SIZE)%Z ->
    realizes segs (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hlo Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hlo Hrd) as Hp.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy
                                       | apply openat_node_rob; rewrite Hp; discriminate
                                       | rewrite adv_set_epend; exact Hc].
    intros o. fold ms. rewrite openat_spec_head.
    apply (openat_toolong_outcome _ _ _ _ model open_flags_modeled). rewrite open_in_mem. exact Hp.
  Qed.

  (* [comment removed for export] *)
  Definition path_at : ltac2:(zQ "30!p2!h9!n5>1p@1$0@1$2@1$1#8P") := ltac2:(zQ "h50!h9!n5!p2!msd!mt6!jnd!jgb!mtc!ir9!hi2!p9!hie!rd!mu2!mva!nh5!ji3!nhb!nj5!iqd!ir2\1p@1$2@1$1@1$0#8@2$4@2$f@2$3@1$1@1$0#8^1Nvvf@2$4@1$d@3$h2@1$1@1$0#8@2$5@1$0#8Z^1@3$c@1$a@1$2@1$1@1$0#8@4$h1?4segs?3mem@2$h0?4regs@3$h3@1$0#5+bKv$b@2$h4@1$0#5+b@2$e@2$3@1$1@1$0#8^1N1@2$6@1$2@1$1@1$0#8@3$7@1$1@1$0#8^1@3$8@1$1@1$0#8@2$5@1$0#8Z@1$9@1$1@1$0#8").

  Lemma path_at_cstr : forall p, path_at p ->
    (bv_unsigned (getr regs 11) + Z.of_nat (length p) < TASK_SIZE)%Z ->
    read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3) Hlo. apply read_cstr_of_rdn; assumption. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_empty : forall K,
    path_at [] ->
    (bv_unsigned (getr regs 11) < TASK_SIZE)%Z ->
    realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hlo Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy
                                       | apply openat_node_rob; rewrite (path_at_cstr [] Hp ltac:(cbn [length]; lia)); discriminate
                                       | rewrite adv_set_epend; exact Hc].
    intros o. fold ms. rewrite openat_spec_head.
    apply (openat_empty_outcome _ _ _ _ model open_flags_modeled). rewrite open_in_mem.
    exact (path_at_cstr [] Hp ltac:(cbn [length]; lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_absent : forall p K,
    path_at p ->
    (bv_unsigned (getr regs 11) + Z.of_nat (length p) < TASK_SIZE)%Z ->
    p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = None ->
    realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hlo Hne Hsl Hnd Hfs Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy
                                       | apply openat_node_rob; rewrite (path_at_cstr p Hp Hlo); discriminate
                                       | rewrite adv_set_epend; exact Hc].
    intros o. fold ms. rewrite openat_spec_head.
    apply (openat_absent_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl p);
      [rewrite open_in_mem; exact (path_at_cstr p Hp Hlo) | exact Hne | exact Hsl | exact Hnd | exact Hfs].
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.
  (* [comment removed for export] *)
  Context {FM : FsMayFail SC}.

  Lemma open_family_on : injected_family_off the_scfg (sys_input segs ms (getr regs 17)) = false.
  Proof. apply family_off_openat_false. rewrite in_sysno_si. exact Hno56. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_dot : forall p KA KB,
    path_at p ->
    (bv_unsigned (getr regs 11) + Z.of_nat (length p) < TASK_SIZE)%Z ->
    path_is_dirref p = true ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    realizes segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p KA KB Hp Hlo Hdr HA HB. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | apply open_family_on | | | | exact Hfree
                    | apply openat_node_rob; rewrite (path_at_cstr _ Hp Hlo); discriminate | |].
    - intros o. fold ms. rewrite openat_spec_head.
      apply (openat_dot_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl p);
        [rewrite open_in_mem; exact (path_at_cstr _ Hp Hlo) | exact Hdr].
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_file : forall p d KA KB,
    path_at p ->
    (bv_unsigned (getr regs 11) + Z.of_nat (length p) < TASK_SIZE)%Z ->
    p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    realizes segs (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hlo Hne Hsl Hnd Hfs HA HB. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_open; [exact Hh | exact Hlazy | reflexivity | apply open_family_on | | | | exact Hfree
                    | apply openat_node_rob; rewrite (path_at_cstr _ Hp Hlo); discriminate | |].
    - intros o. fold ms. rewrite openat_spec_head.
      apply (openat_file_outcome _ _ _ _ model open_flags_modeled eq_refl Hfl p d);
        [rewrite open_in_mem; exact (path_at_cstr p Hp Hlo) | exact Hne | exact Hsl | exact Hnd | exact Hfs].
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model : ltac2:(zQ "30!h9!sc!n5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h10!nv5!h9!jvb!n5!sc!og0!oh0!ohf!oi8!oj5!ok0!oka!ol9!om7!on5!vf!ko2\4addr@1$3@1$1#k0\1n@1$3@1$1#k0\1m$4@2$f@8$6@1$d@1$0^1@1$a@1$0^1@3$5@1$c@1$0^1@2$2@1$1#k0^3@2$h0@2$2@1$1#k0^3@2$2@1$1#k0^2@1$e@1$0^1@1$7@1$0^1@1$9@1$0^1@1$b@1$0^1@1$8@1$0^1^1").

Lemma mprotect_model_next_eq : ltac2:(zQ "60!h9!sc!n5!rd!orc!ph8>1m$1>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$1@3$4^3^2^1@3$5^2^1^3").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tid_I : ltac2:(zQ "00T") := ltac2:(zQ "70!h9!jue!n5!jvb!mt6!pjf!pne@2$5@1$2@1$0#k0\1t@1$2@1$0#k0@2$4@2$1Z@2$3@1$0#k0^1@2$1@2$3@1$0#k0^1$6").

Lemma one_tid_ok : ltac2:(zQ "61!h9!jue!jnd!jvb!mt6!pne&@2$3@1$0#k0@2$2@1$0#k0+1@2$4@2$1Z~0@2$1~0$5").
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

Lemma node_set_tid : ltac2:(zQ "hc4!h9!n5!rd!jvb!jue!p9!pp3!jo7!hi2!q2!mt6!ppc!jh2!pne!jgb!p2!hgd!hm9!pq9!prb!hq6!sc!lue!kd!ps7!tf!ub!psf&@2$9@1$1@1$0#k0@1$1@1$0#k0&@2$a@2$4Z@2$3@1$0#k0^1@2$4@2$3@1$0#k0^1$d&\1t@1$1@1$0#k0~1&@3$b@1$1@1$0#k0~2^1>2ms$h1>5model$h5>2x8@1$1@1$0#k0>0@3$2@1$5@1$1@1$0#k0@1$h7^2@1$7@1$1@1$0#k0>0@3$2@1$f~0@1$h9^3@1$8~0>0@3$2@1$5@1$1@1$0#k0@1$h2^5@2$e@1$1@1$0#k0^3>0@3$2$h0@2$3@1$0#k0^4+m0>0@3$2@1$5@1$1@1$0#k0@1$h8^6@1$7@1$1@1$0#k0@6$hb?4segs?2SC@2$c^8^7$6\0$6@1$8$h6\1i$6@2$c@1$h4@2$h3^9~3@2$ha~3^8").
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall o, syscall_spec (sys_input segs ms x8) model o <->
     exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t model) []).
  { intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_si; exact Hno).
    apply set_tid_fresh_outcome. exact Htid. }
  pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  assert (Hnode : node_ok segs (mkCfg ms model) tid_I (fun _ => [])
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
  { apply (node_family segs ms model x8 tid_I effs (fun i => with_tid (proj1_sig i) model) (fun _ => []) _
             Hh Hsvc Hchk).
    - intros [t Ht]. exists t. split; [exact Ht|reflexivity].
    - intros o (t & Ht & ->). exists (exist _ t Ht). reflexivity.
    - intros i. apply not_spurious_none. rewrite in_sysno_si, Hno. apply injected_arm_none_96.
    - intros i. rewrite with_tid_halted. exact Hh.
    - intros i. rewrite with_tid_lazy. exact Hlazy. }
  destruct Hnode as [Hn1 Hn2]. split.
  - intros i. rewrite Enx. apply Hn1.
  - intros e st Hss. destruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_set_tid : ltac2:(zQ "i22!h9!n5!rd!p9!jo7!q2!hie!jh2!ip1!jn1!jue!iqd!ir2!jvb!jgb!joe!p2!hi2!jp5!mt6!jpc!jqa!sc!kd!ps7!tf!ub!pne!ig7!ji3!ip9!iq3!jse!jnd&>0@1$1@1$0#k0@1$3@1$1@1$0#8&@2$5@1$1@1$0#k0@1$1@1$0#k0>4regs@2$hc@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$h6>1K$i0>1w@1$1@1$0#i0>0@3$2@1$3@1$1@1$0#i0@2$h4?4segs^6@2$e@1$1@1$0#i0^1>0@3$2$f@1$h5^2$h2>0@3$2@1$3@1$1@1$0#k0@1$h7^5@1$4@1$1@1$0#k0>0@3$2@1$h0~1@1$h9^6@1$h1~1>0@3$2@1$1@1$0#k0@2$hd^b@3$b@1$0#5+h1Kv$6@2$c@1$0#5+h1@2$i1@1$0#k0+m0>0@3$2@1$3@1$1@1$0#k0@1$h8^8@1$4@1$1@1$0#k0>0>3tid@1$1@1$0#k0>0@2$h3@2$aZ@2$d@1$0#k0^1@2$a@2$d@1$0#k0^1$hb@4$9?4segs?2SC@2$7@5$8?2fx@3$he^f@3$b@1$0#5+aKv$6@2$c@1$0#5+a^2@2$hf^e+4^d^c@2$ha^2^b^a@4$9?4segs?2SC@2$7@5$8?2fx^e^d^c^b^a^9").
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply rz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid]
                   | rob_mf H17 |].
  intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : ltac2:(zQ "hd4!h9!n5!rd!p9!hie!ji3!iqd!ir2!jnd!q2!jo7!jgb!joe!p2!hi2!jp5!pta!jpc!jqa!jh2!sc!mg2!kd!tf!ig7!ip1!jn1!ptf!pu9&>0@1$1@1$0#k0@1$3@1$1@1$0#8&@2$9@1$1@1$0#k0@1$1@1$0#k0&@3$6@1$0#5+h1Kv$4@2$7@1$0#5+h1&@2$5^b~2>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$h4>1w@1$1@1$0#i0>4code@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$h1?4segs^6@2$b@1$1@1$0#i0^2>0@3$2$c@1$h2^3$f>0@3$2@1$3@1$1@1$0#k0@1$h6^5@1$a@1$1@1$0#k0>0@3$2@1$d~1@1$h7^6@1$e~1>0@2$h0@3$2@1$1@1$0#k0~3@2$8@1$0#k0+le@3$2@1$1@1$0#k0~3@2$8@1$0#k0+ld>0@3$2@1$1@1$0#k0@2$5^c@3$6@1$0#5+aKv$4@2$7@1$0#5+a^6@4$ha?4segs?2SC@2$h3@5$h9?2fx^d^c^b^a^9@2$hb@3$hc@1$0#k0^7@2$8@1$0#k0+vf@1$h5^9").
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_simple : ltac2:(zQ "d1!h9!n5!rd!p2!hi2!q2!hgd!sc!tf!pv2!nv5!qg7!qh9&@2$5@1$1@1$0#k0@1$1@1$0#k0>1m$7>0@3$2@1$3~0@1$8^1@1$4~0>0@3$2@1$3@1$1@1$0#k0@1$9^2@1$4@1$1@1$0#k0@3$2$6@1$c^3@1$b@1$a^3").
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma region_free_In : ltac2:(zQ "e1!h9!n5!jvb!q2!ko2!ko9!joe!p2!is0!jp5!rd!pta!qib!nj5&@2$3@1$1@1$0#k0@1$1@1$0#k0>1l@1$7~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>1b@1$1@1$0#k0>1s@1$1@1$0#k0>0@3$a$6@3$c^5^4^3$9>0@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^3^2^6@2$b@2$5@2$4@2$2@1$0#k0^6@2$2@1$0#k0^5@2$2@1$0#k0^4@2$5@2$4@2$2@1$0#k0^4@2$2@1$0#k0^3@2$2@1$0#k0^6").
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : ltac2:(zQ "e1!h9!n5!jvb!q2!ko2!ko9!joe!p2!is0!jp5!rd!pta!qib!nj5&@2$3@1$1@1$0#k0@1$1@1$0#k0>1l@1$7~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>0>1b@1$1@1$0#k0>1s@1$1@1$0#k0>0@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1^5@2$b@2$5@2$4@2$2@1$0#k0^5@2$2@1$0#k0^4@2$2@1$0#k0^3@2$5@2$4@2$2@1$0#k0^3@2$2@1$0#k0^2@2$2@1$0#k0^5@3$a$6@3$c^4^3^2$9").
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_bytes_cons : ltac2:(zQ "b1!h9!n5!q2!qj9!ir9!p2!is0!rd!hgd!ko2!jvb&@2$2@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1l@1$5~0@3$7$8@1$3@3$4~0@4$6@1$1@1$0#k0@1$1@1$0#k0^3^2^1@2$9@2$a@1$0#k0^2@1$3^1").
Proof. reflexivity. Qed.

Lemma live_bytes_app : ltac2:(zQ "92!h9!n5!q2!qj9!p2!mtc!rd!hgd!ko2&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : ltac2:(zQ "70!h9!hgd!ko9!n5!qk6!qj9!jvb>1a@1$3@1$0#k0>2sz@1$3@1$0#k0>2lo$1>2hi$1>0@2$2^2^1@2$2@1$5@4$4^5^4^3^2@2$6@1$0#k0^4").
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : ltac2:(zQ "80!h9!hgd!qj9!ko9!n5!p2!q2!og0>1l@1$5@2$6@1$4@1$0#k0@1$4@1$0#k0>2lo$1>2hi$1>0@2$3^2^1@2$3@1$2@3$7^4^3^2@1$2^4").
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_cons : ltac2:(zQ "b2!h9!n5!q2!p2!jvb!ql4!ir9!is0!rd!og0!ko2&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>4maps~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>4cuts~1@3$8~1@2$5^4@3$6~0@4$7@1$1@1$0#k0@1$1@1$0#k0^3^2^1@2$5@3$9^4@2$4@1$0#k0^3@2$a@2$4@1$0#k0^3@2$4@1$0#k0^2^1").
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : ltac2:(zQ "72!h9!n5!p2!q2!qj9!ql4!ko9&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4cuts~1>4maps~1@2$6@1$4@2$5^1^2@1$4^1").
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : ltac2:(zQ "40!v6!qg7!qm9!ko9>1h$0@2$3@1$1^1@1$2^1").
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : ltac2:(zQ "d1!h9!n5!p2!hi2!q2!rd!sc!tf!pv2!nv5!qh9!qm9!ko9&@2$4@1$1@1$0#k0@1$1@1$0#k0>1m$6>0@3$5@1$2~0@1$7^1@1$3~0>0@3$5@1$2@1$1@1$0#k0@1$8^2@1$3@1$1@1$0#k0@2$c@1$a^3@1$b@1$9^3").
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : ltac2:(zQ "h01!h9!n5!rd!p2!hi2!q2!nv5!joe!jp5!sc!tf!pv2!oj5!qm9!qn9!ko9&@2$5@1$1@1$0#k0@1$1@1$0#k0>1m$9>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$2@1$3~0@1$a^3@1$4~0>0@3$2@1$3@1$1@1$0#k0@1$b^4@1$4@1$1@1$0#k0>0@2$f@1$d@1$6^5@1$c@1$6^5@3$2$7@3$e^6^5^4$8").
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

(* [comment removed for export] *)
Lemma file_read_length_eq : ltac2:(zQ "a0!h9!n5!msd!qp0!p2!hi8!rd!qpf!ll7!qs1>4data@1$4@1$1@1$0#8>3off@1$1@1$0#k0>5count@1$1@1$0#k0@3$6$5@2$2@1$1@1$0#8@3$8^3^2^1@2$9@1$3^1@2$7@2$2@1$1@1$0#8^3@1$3^2").
Proof. intros. rewrite length_file_read. reflexivity. Qed.

Lemma file_read_length_le : ltac2:(zQ "91!h9!n5!msd!nh5!qp0!ll7!p2!mt6!qpf&@2$2@1$1@1$0#8@3$5^3^2^1>4data@1$6@1$1@1$0#8>3off@1$1@1$0#k0>5count@1$1@1$0#k0@2$7@2$3~0@1$4^1@2$3~0@2$8@2$2@1$1@1$0#8^3@1$4^2").
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End FPX2.
(* [comment removed for export] *)
