(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanCeil Scfg RelSpec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeAlg Nodes StoreOk AgentLib AgentNodes SpecConsts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsanRefNodes () := KReplay.lz_vm "#$jAC47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?Krespectful_per_oblig!t3$_1C4ELinuxProcessSemantics?!s<22Fs4path!t6,4Init5Logic6eq_ind!srN2Fs!sTK5State7PipeBufK!u^,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!v0#s2bv00I!u\19Datatypes6op!sL#00!u4Q8m_haltedK!v]72eq01!uOG3I!tDP5Model!tzVvmmap!wgR;with!s`&I!u\;0K!u7W1!wU<4prod!wu>4list!tDS7Vm!s-$!tF#!s^PFd!s^%0I!t>Y!s^SIo!s^YFs!s^X9!s7#!s`X8Li!uYY9Time!s`X6VmMaps!{cS;vm_reserved!#4OQvm_!|DVvm_noac!s;#!s`Q<vm_start_brk!saQ6vm!s[U8vm_limit!tuU!~r#_base!saQ:vm_init_spK!xjX!#3>,!#8V3Z!y0#!#8V>;bv_unsign!xx#!sP?7Z_to_bv!sLA5bv_eq!spBbv_wrap!sLAD!th-_in_range!sYA=!t#&_small!sRA@!uE&!ut-!#7t58!#>1$_rI!#<Z>0!#8X73and00!#;7F!#@,;5Riscv7Prelude5bvmapC79OSSVerify6Proofs:boost_json:fuzz_parse3!tB#FileSim;adv_eff_retC13~~~!smP:AgentNodes5epend!sj%K!#:/@1!{6Q=SyscallEffect0!#C:K3Run<apply!uX#ect!s_O@advance_past_svcK!|[?2!yjA4BvWfK!#BVC1!wBP8PropExec6regupd!x,V!si,v_addi!si_4mks!yY&!#:IJ>!{+$!sE+=machine_s!#;8V7MemCopy!#AE=3nat!}//!}J-4True!wGSAllocSim?!y{%zeros_one!{kC!#C<#1!|3B2!zlO;!tP-!~fQMmapSim5zfill!xn&!|nUun!#>:#!yOX7fp_regs!vTB!#KA&1!sHD2!{jZfp_csr!tU'!{%g1!#AzQ!#7/&!tKY7ms!vg%!#9'G9!#9'#_s!t=\8ms_f!t>?!sfB9ms_pc_val!sgZ>ms_svc_pending!vT`sv!se^f!yM#!seY6ms_mem!sd^rom!#E-Q!y|#!}g&!s_P9!s_#!#3i$!t?Ucopies!#3aU!s_Q!t@-writ!t@X!s_'!#=E>6b!#;x#!#3pYb_npc4!#6l@!}d16!#Ge#b!#Eb79False!#\p$!#EE6not!tvY:!tC%_neq!#=o&!#:Q:bool!#<I3!sF32!#Az?1!#GS75!uS$!#Gp9!#=L$0!#;8W6un!#;9,56Stdlib6ZArith6BinInt1Z3leb!sC=!xp#!s`=t!wu3!v--and!sD=3orbC4!s~&4Bool!s'$;orb_f!xZ$r!sb=fst!sC=s!y:#!t#&5Lists4!s+#7ex!s2#b!sB-!v}#HFunc!{U#alExtens!s1$ityIf!s?+_e!s@0!v,<2lt!sB>e!ve=!{\#!sC;7!z\&K!u-'9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!{E#!sQ47Env!sT#5PExpr01!sIE2K!t?L!st75Tauto8G!sJ'7C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!vJ<4fi!yS-!sq8C!sq0_soundC5!#6~ISys7!#OO%5w_is0C6!s`M2Mm4!~6#7min!#Zz#!sbV;brk_grow_ok!#f@8or00!#6a8iff!#n@>?eq_p!#oX#!s,#xy!~;6=!~p#_true_!ssBIr!#oy&_!s0,!s}&!s\3>!s\+_Prop@and!t,#_m!s=&!tW6<or!tV?!sx2?or!sw2!w?I2Fs9!#9T%eq!ud?:!#qs+!sM?NR!v%,artial_app!te+!#OZ7!#Y~#1K!xY;2!s@<!#IMQ?page_r!{t#_up_Z!#BTQalloc_top!#7}<app!#6?<sub!t@Q;region_free!|WW=!|W#budget_ok!yy7!{R$!#:h&!u/;:ltb_ir!{J#!sJ<6!sJ#ge!#8N?1!sD@3!~/85proj2!#UdXA!uu#resolut!ve#ok!#Pa&!#7sC4!sJF8!{m?Mtrans_co_!#b~#v_impl!}S-!s`=F!#3R/!#4X4!t_35eKind!#D?<unit!#;x7!se%4kin!#XR?!sf$1!#E#A1!uH5!$##2>iff_T!v4#!#e%#I!#:_?;!yu%!xY$!u38!#=?03Op205!sMI!tyF=!ty#!$$~,!#3+O!#3j#size!t]I3!~7W>!{@#model_next!siW@for!~v#vm!#k~$!#O?Q=maps_subtrac!tOX:!#=|$ants!se\!#SC%!seVD!u60!uy&c!#3mN<AsanRef!#k:#?!$#[,_eta!#3o$!sv]:!sq3!#d>Y!vC,_keep!srd!wv%!srd9!z~+!#O\Bpow!#S9X9u64!#t@%!t1A>pow_pos_nonneg!#;L<!sN#!sJ%!#5c;!#iN#!#JvD5Psatz!sOM6K!#6'L2!#LgD5!sIE7!wX=mul!xcRgentLib7!wX#li!#u4&!#>+67f_equal!#[9Dsub!u<E4!u<<4of_N!#<A5;Zify!#8T%!$8[#!#HH-!tw-8i!#gG#fl!sjB3inj!sIB5mkre!snC9and!#>|$!sOB;rew_!tk%!#~FA:bv!}9#ulu!#_HA?!w5%!#|u+!#49cgrow!#49j!sr-!#Er;!u]$o!vX69SatDivModCZ!v'#!~>&!~iC7di!vZ$!|3=div!sC<=!t7#pos_b!#TE$!sM?!t[#!sM15!u/$8PreO!s/#1Z;!t[#0_r_ext!sL>!st#!sL&!#FZE3!sJF!#3ME3!{bEapp!}>C!sK$2!#6s@1!#5yM1!t?68!t?#Inst7Inj_Z_Z!#=R\;!zX$_ok_na!zXC!#S}%!#Ml?!#`>=6leb_le!#@F]!tz-_pin!#j$@!#Fp9errno!#v,#!#f}ORelSpecB!se+!#3h+!tTV>!#TL'_room!#iW?3!zx>3Pol!yd8!#=07!#P6F!#asF:!sJ<!#N^$2!v'Q6ENOMEM!#qbQtwo_pow_64!wARstack_max!#Lf#!scQB!sc1_val!{5]F!{5%!{2%_not_!ys$!#H\b>mprotect!#F2/!u]J!#xx5gpr!vCQ<map_contains!$0\KMonad7outcom!#qSR!#<Z'F!#^r1!#:,$s!uzQ3Run9sys_inpu!$BWMpecs<s!#hZ$_spec!{mRin_arg!#P-Q8M!x\&=!xe+!tI$!#53V@!si+err_ou!#F{&!t`ZB!su+!#`d,!v0O8in_sysno!uDQ!$?J&!sd'_s!$9XV!v3+!x@/_226!v3aC!}T1!#X`V!sr+I!sr+grows!}&#fli!w6#!wye!tl$ed_b!vSXG!y`,xpose_!~6&!#Md2!#]j:;!#b5&ity!#6_]!w26_!$#{&!yjX:!}Z%2!yiZ!sl11!slh0!sl+K!#6iX!$YfQ!$G=1!$AeQ5event0!#wLO6Kernel4Fork@PID_MAX_ENVELOPE!#>tQiv_overla!#o}<4neg!$%~6:!#n=#assoc!sb<8list_i!$%e82In!xWQ!$,I%@!#pg,!~B#s!#EHV:live_bytes".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos3h5LinuxProcessSemanticsfLinuxProcessSem5Statehf8m_halted35stdpp9bitvectorbdefinitionsl82bv37Corelib4Init9Datatypesna6option37Corelib4Init5Logicpb2eqhf5Modelhf8with_tidhf8m_vmmapshfbwith_vmmapshf6VmMapshfcmkVmMapsFullhf6vm_brkhfavm_init_sphf8vm_limithf7vm_mapshfcvm_mmap_basehfbvm_noaccesshfbvm_reservedhfcvm_start_brk01Zl87Z_to_bvl8bbv_unsignedhffvm_forget_rangena3nilna4prodna4listna3natpb1I3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshq8dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhv0h0advance_past_svchv0capply_effecthf7MemCopyhf9mkEffectU3h5LinuxProcessSemantics5Riscv7Preludeil75bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAgentNodes~~~~~~io65epend69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~isc4mkstisc6regupdisc6v_addil82BVl84BvWfna4consna4pair69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~jjd5zfilljjd6unfill46Stdlib6ZArith6BinInt1Zjoa2lena4boolna4truepb3andpb3iffpb2or5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapjs7bbrk_grow_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AllocSim~~~~~~kgah1brk_resolution_okjoa2ltkga9brk_modeljoa3addhf9page_sizejoa6modulojoa3powna4andbna3apphf9alloc_tophfbregion_freejoa3eqbjoa3lebjoa3ltb79OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanRefNodes8WithSegs~~~~~~ksefgrant_ok_na_pinksebgrant_ok_napb3nothf6ENOMEMhf9errno_rethfdmaps_subtract5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm8Mprotectlm3h3mprotect_model_nextkseemprotect_modelhq86ms_gprhfdSyscallEffect3h5LinuxProcessSemanticsfLinuxProcessSem5Monadltf7outcomehfcmap_containshffpage_round_up_Zltf2Okhv09sys_input3h5LinuxProcessSemanticsfLinuxProcessSem5Specsmkccsyscall_spechf5eventhfatwo_pow_64lm3h2mprotect_budget_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~mr6h0mprotect_err_out37Corelib4Init6Specifng53sig5h5LinuxProcessSemanticsfLinuxProcessSem3Sys6Kernel4Forkni1h0PID_MAX_ENVELOPE36Stdlib5Lists4Listnme2Inhfalive_bytes3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypenp47Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_tid_halted : ltac2:(zQ "70!h9!kd!n5!p2!qf!r4!rc>1t@1$2@1$0#k0>1m$5@3$4@1$3@1$2@1$0#k0@1$1@2$6^2^1@1$1^1").
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_eta : ltac2:(zQ "40!r4!qf!s7!t2>1m$0@3$1$0@2$3@1$2^1^1^1").
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : ltac2:(zQ "b0!u0!qf!u9!v8!hg1!hge!hh9!hi3!hj2!hk0!hke>1h$0@3$1$0@8$2@1$9^1@1$6^1@1$8^1@1$a^1@1$3^1@1$5^1@1$7^1@1$4^1^1").
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : ltac2:(zQ "60!h9!qf!hld!n5!hm0!hma>1a@1$3@1$0#k0>1z$2>0@3$1$2^1@2$5@1$0#k0^2@3$1@1$3@1$0#k0@2$4@1$0#k0^2^3").
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)

Lemma vm_forget_range_halted : ltac2:(zQ "80!hld!kd!p2!qf!h9!r4!hn8!n5>2lo$0>2hi$0>1m$5@3$3@1$2@1$7@1$4#k0@1$1@3$6^3^2^1@1$1^1").
Proof. reflexivity. Qed.
End FPX1.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hp7!ns9@1$0$1").
Context {SC : StepCfg}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : ltac2:(zQ "h53!h9!n5!hoa!hp0!p2!hp7!hpe!hq4!qf!htf!ihc!ij1!ik1!ikb!ind!is3!jg7!jgf!jh9!ji3!ji8&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$e@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0@3$8$9@1$a@2$b@6$f?2fx^6^5^4^3^2@6$d^1@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~2~2@1$2$c@1$2@2$3@1$1@1$0#k0$6@5$h0?2fx@3$h1^6@3$h3@1$0#5+aKv$7@2$h4@1$0#5+a^1@2$h2^5+4^4^3").
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_zeros1_epend : ltac2:(zQ "h83!h9!n5!hoa!hp0!p2!jif!hp7!hpe!jj6!hq4!qf!htf!ihc!ij1!ik1!ikb!ind!is3!jn7!jg7!jgf!jh9!ji3!ji8&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$h0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$a$b@1$c@2$d@6$h1?2fx^8^7^6^5^4@6$f^3@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8@3$5~1@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1~2~2@1$2$e@1$2@2$3@1$1@1$0#k0$7@5$h3?2fx@3$h4^8@3$h6@1$0#5+aKv$9@2$h7@1$0#5+a^3@2$h5^7+4@3$h2^2^1^6^5").
Proof.
  intros. unfold epend.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_unmaps1_epend : ltac2:(zQ "h83!h9!n5!hoa!hp0!p2!jif!hp7!hpe!jj6!hq4!qf!htf!ihc!ij1!ik1!ikb!ind!is3!jo0!jg7!jgf!jh9!ji3!ji8&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$h0@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$a$b@1$c@2$d@6$h1?2fx^8^7^6^5^4@6$f^3@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~2@3$5~1@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1~2@1$2$e@1$2@2$3@1$1@1$0#k0$7@5$h3?2fx@3$h4^8@3$h6@1$0#5+aKv$9@2$h7@1$0#5+a^3@2$h5^7+4@3$h2^2^1^6^5").
Proof.
  intros. unfold epend.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

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
Lemma brk_r_ok_grow_cases : ltac2:(zQ "h20!h9!hma!n5!qf!v8!jq2!jq8!jqf!jr6!jrc!js2!r4!u0!s7!hke!jvb!kk5!klb>1m$b>3req@1$2@1$0#k0>1r@1$2@1$0#k0=1h$c@1$d^3>0@2$h1Z@2$1@1$0#k0^3>0@2$5@2$1@1$0#k0@1$e^2@2$1@1$0#k0^4>0@2$5@2$1@1$0#k0@1$4^3@2$1@1$0#k0^5@2$9@3$h0^7^6^5@2$a@3$3@1$2@1$0#k0^5@1$4^4@2$8@3$3@1$2@1$0#k0^5^6@3$3$6@3$f^7^6^6$7").
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  (* 08b1429: the grant is the page-rounded range [brk_page_range]; both ends
     are page-aligned here, so it is the one range [(b, d)]. *)
  assert (Pb : page_round_up_Z (bv_unsigned b) = bv_unsigned b).
  { unfold page_round_up_Z. unfold page_size in *. Z.div_mod_to_equations. lia. }
  assert (Preq : page_round_up_Z (bv_unsigned req) = bv_unsigned req).
  { rewrite Hureq. unfold page_round_up_Z. unfold page_size in *. Z.div_mod_to_equations. lia. }
  rewrite Pb, Preq. unfold Mmap.brk_page_range.
  rewrite (proj2 (Z.ltb_lt (bv_unsigned b) (bv_unsigned req))) by lia.
  cbn [app maps_subtract_ranges fold_left].
  rewrite (Z_to_bv_bv_unsigned _ b), Hureq.
  replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model : ltac2:(zQ "30!h9!r4!n5>1a@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h12!h9!n5!s7!jif!jj6!hp0!r4!u9!v8!hg1!hge!hh9!hi3!hj2!hk0!hke!t2&@2$5@1$1@1$0#k0@1$1@1$0#k0&@4$4@1$1@1$0#k0@1$1@1$0#k0^3^2\1a@1$1@1$0#k0\1n@1$1@1$0#k0\1m$6@2$h0@8$7@1$e@1$2^1@3$3~0~1@1$b@1$2^1@3$3~0~1@1$d@1$2^1@1$f@1$2^1@1$8@1$2^1@1$a@1$2^1@1$c@1$2^1@1$9@1$2^1^1").

(* [comment removed for export] *)
Definition grant_ok_na_pin : ltac2:(zQ "50!jq8!h9!hld!r4!n5>1m$3>1a@1$4@1$1#k0>1n$2$0") := ltac2:(zQ "h40!h9!kp2!s7!n5!hma!kp9!hp0!hld!r4!kpf!kn5!kqb!hh9!hk0!kme!kr9!ks0!ks7!ko1!hm0\1m$8\1a@1$3@1$0#k0\1n$7@2$1@2$1@2$1@2$f@2$h2@2$4@1$0#k0^2$aZ@2$h1Z@2$4@1$0#k0^2@2$h0@2$e@2$4@1$0#k0^2^1@1$9@1$2^3@3$b@3$5@2$6@1$3@1$0#k0@1$3@1$0#k0@1$d@1$2^3@1$c@1$2^3^2@2$h3@1$0#k0^1").
(* 08b1429: a fresh anonymous grant lands where Linux's placement rule puts it
   ([Checks.Placement.linux_place_is]), not merely at some admissible address --
   [RelSpec.mmap_rw_outcome] and [RelSpec.mmap_noaccess_outcome] now conclude
   [linux_place].  [grant_ok_na_pin] stays exactly the admissibility that address
   then has ([Placement.linux_place_is_admissible]), so every consumer that reads
   the four conjuncts through [grant_ok_na_unpack] is unchanged, and the TYPE of
   [grant_ok_na] is unchanged, so no caller's statement moves.
   PROVENANCE, cited BY BRANCH, read per hunk with git show on the branch below:
     a donor tree
       projects/spirv-tools/spvtools_binary_parser_fuzzer/proofs/lib/bpA/Start/
         AsanRefNodes.v:157-198 -> grant_ok_na, grant_ok_na_pin_of_gate,
         grant_ok_na_place, grant_ok_na_of_place (statements and proofs)
       projects/boost-beast/http_request/proofs/lib/As/AsanRefNodes.v:292-320
         -> the same shape in the other tree of this fork
   DIFFERENCES from the donors: [Placement.]-qualified names, because this file
   does not Import Checks.Placement (it now Requires it); [andb] spelled out
   rather than [&&], because this file sits under [Open Scope bv_scope]; and the
   zQ-encoded definition it replaces is written out as text (rule 11g), since its
   body had to change.  The donors carry no address and no constant, so none was
   taken. *)
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  andb (Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a)
       (grant_ok_na_pin m a n).

Lemma grant_ok_na_pin_of_gate : forall hint m a n,
  grant_ok_na hint m a n = true -> grant_ok_na_pin m a n = true.
Proof. intros hint m a n H. unfold grant_ok_na in H. apply andb_true_iff in H as [_ H]. exact H. Qed.

Lemma grant_ok_na_place : forall hint m a n,
  grant_ok_na hint m a n = true ->
  Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof. intros hint m a n H. unfold grant_ok_na in H. apply andb_true_iff in H as [H _]. exact H. Qed.

(* [linux_place_is] decides the address and implies the other four conjuncts. *)
Lemma grant_ok_na_of_place : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  grant_ok_na hint m a n = true.
Proof.
  intros hint m a n Hn Hal Hpl.
  destruct (Placement.linux_place_is_admissible _ _ _ _ _ Hn Hal Hpl) as (G1 & G2 & G3 & G4).
  unfold grant_ok_na, grant_ok_na_pin. rewrite Hpl.
  rewrite (proj2 (Z.eqb_eq _ _) G1), (proj2 (Z.ltb_lt _ _) G2), (proj2 (Z.leb_le _ _) G3), G4.
  reflexivity.
Qed.

Lemma grant_ok_na_unpack : ltac2:(zQ "h70!h9!n5!jr6!qf!s7!hma!jq8!jqf!hld!kp9!hp0!r4!kpf!kn5!kqb!hh9!hk0!li9!kme!jq2!klb!ko1!hm0>4hint@1$1@1$0#k0>1m$b>1a@1$1@1$0#k0>1n$8>0@3$3$6@4$h1^4^3^2^1$7@2$2@3$3$8@2$h5@2$5@1$0#k0^3$dZ@2$2@2$h4Z@2$5@1$0#k0^3@2$2@2$h3@2$h2@2$5@1$0#k0^3^2@1$c@1$4^4@3$3$6@3$e@3$9@2$a@1$1@1$0#k0@1$1@1$0#k0@1$h0@1$4^4@1$f@1$4^4^3@2$h6@1$0#k0^2$7").
Proof.
  intros hint m a n H. apply grant_ok_na_pin_of_gate in H. unfold grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. auto.
Qed.

Lemma grant_na_pin_not_errno : ltac2:(zQ "c0!qf!h9!n5!jq8!jqf!lj8!hld!lje!r4!lk7!lh6!jq2>1m$8>1a@1$2@1$1#k0>1n$6>0@2$bZ^1>0@3$0$3@3$a^4^3^2$4@1$5@3$0@1$2@1$1#k0^4@1$9$7").
Proof.
  intros m a n Hn Hg. unfold grant_ok_na_pin in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Htop]. apply Z.leb_le in Htop.
  intros E. apply (f_equal bv_unsigned) in E.
  rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
  alloc_top_bounds. unfold two_pow_64, ENOMEM in *. lia.
Qed.

(* [comment removed for export] *)

Lemma grant_na_not_errno : ltac2:(zQ "c0!h9!n5!qf!jq8!jqf!lj8!hld!lje!r4!lk7!li9!jq2>4hint@1$1@1$0#k0>5model$8>1a@1$1@1$0#k0>1n$6>0@2$bZ^1>0@3$2$3@4$a^5^4^3^2$4@1$5@3$2@1$1@1$0#k0^4@1$9$7").
Proof.
  intros hint model a n Hn Hg.
  exact (grant_na_pin_not_errno model a n Hn (grant_ok_na_pin_of_gate _ _ _ _ Hg)).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model : ltac2:(zQ "30!h9!r4!n5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "h10!s7!h9!hma!n5!r4!ll3!u9!v8!hg1!hge!hh9!hi3!hj2!hk0!hke!t2!kme\4addr@1$3@1$1#k0\1n@1$3@1$1#k0\1m$4@2$f@8$6@1$d@1$0^1@1$a@1$0^1@3$5@1$c@1$0^1@2$2@1$1#k0^3@2$h0@2$2@1$1#k0^3@2$2@1$1#k0^2@1$e@1$0^1@1$7@1$0^1@1$9@1$0^1@1$b@1$0^1@1$8@1$0^1^1").

Lemma mprotect_model_next_eq : ltac2:(zQ "60!h9!r4!n5!qf!lpb!lr3>1m$1>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$1@3$4^3^2^1@3$5^2^1^3").
Proof. reflexivity. Qed.

(* RESTORED.  A bulk "devbox checkpoint", DELETED this lemma from
   this file (15 lines, no replacement) while AsanNodesMmLib's srz_mprotect1
   replay still names it, so that replay could not resolve
   [AsanRefNodes.mprotect_outcome_si] -- the error a farm round
   reported at AsanNodesMmLib.v:746 on source
   d483421a1fa6c878c40c53bce51497785858582a.  This is a dangling reference, not
   a proof failure, and it is independent of the grant_ok_na work above; it had
   been masked by the earlier error at :392.
   The statement is NOT the deleted one: [mprotect_expose_outcome] has gained
   the revision's vDSO/vvar gate, so the lemma now carries
   [region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model)))
    addr n = true] as a premise, between the register premises and the two
   [map_contains] ones.  That is the ported shape, not an invention.
   PROVENANCE, cited BY BRANCH, read per hunk with git show on the branch below:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/As/AsanRefNodes.v:363-392
         -> statement and proof, the plain-text twin in the other tree of the
            fork
   DIFFERENCE: [in_sysno_si] rather than the donor's [ExitSim.in_sysno_sys_input],
   because that is the spelling the deleted boost-json text used and the one
   this file has in scope.  The donor carries no address and no constant, so
   none was taken. *)
Lemma mprotect_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vdso_reserved (m_kernel model) (vdso_top (m_vmmaps model))) addr n = true ->
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mprotect_err_out model o
    \/ (mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []).
Proof.
  intros ms x8 model addr len Hno H0 Hal H1 Hlen Hnw H2 n Hvd Hna Hma o.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr).
    unfold two_pow_64 in *. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len)
    by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (syscall_spec_226 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H2.
  rewrite <- mprotect_model_next_eq. subst n. rewrite <- Hu1.
  apply (mprotect_expose_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) _ model o);
    [vm_compute; reflexivity | exact Hal | | rewrite Hu1; exact Hnw | vm_compute; reflexivity
    | rewrite Hu1; exact Hvd | rewrite Hu1; exact Hna | rewrite Hu1; exact Hma].
  unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  apply Z.eqb_neq. lia.
Qed.

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

Definition tid_I : ltac2:(zQ "00T") := ltac2:(zQ "70!h9!klb!n5!hma!jr6!nha!nl9@2$5@1$2@1$0#k0\1t@1$2@1$0#k0@2$4@2$1Z@2$3@1$0#k0^1@2$1@2$3@1$0#k0^1$6").

Lemma one_tid_ok : ltac2:(zQ "61!h9!klb!hm0!hma!jr6!nl9&@2$3@1$0#k0@2$2@1$0#k0+1@2$4@2$1Z~0@2$1~0$5").
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

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

End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
Lemma region_free_app : ltac2:(zQ "92!h9!n5!hp0!kqb!hp7!kp2!kp9!jq8!qf&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1>2lo@1$1@1$0#k0>1n@1$1@1$0#k0@3$8$7@3$3@3$6~0^4^3^2^1@2$5@3$3^4^2^1@3$3^3^2^1").
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : ltac2:(zQ "e1!h9!n5!hma!hp0!kme!jq2!jq8!hp7!jj6!jqf!qf!js2!kqb!no1&@2$3@1$1@1$0#k0@1$1@1$0#k0>1l@1$7~0>2lo@1$1@1$0#k0>1n@1$1@1$0#k0>1b@1$1@1$0#k0>1s@1$1@1$0#k0>0@3$a$6@3$c^5^4^3$9>0@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^3^2^6@2$b@2$5@2$4@2$2@1$0#k0^6@2$2@1$0#k0^5@2$2@1$0#k0^4@2$5@2$4@2$2@1$0#k0^4@2$2@1$0#k0^3@2$2@1$0#k0^6").
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma live_bytes_app : ltac2:(zQ "92!h9!n5!hp0!no7!hp7!kp9!qf!hld!kme&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

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

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX2.
(* [comment removed for export] *)
