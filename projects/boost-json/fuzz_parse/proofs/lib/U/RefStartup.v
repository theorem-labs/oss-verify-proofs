(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb ShapeAlg Nodes RefNodes FileSim StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefImg RefStartupDefs RefStartup1 RefMemset RefStartup2 RefStartup3 RefStartup4 Ub_code_46e98_47484 Ub_code_726ec_72728 Ub_code_dd254_dddf4.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefStartup () := KReplay.lz_vm "#$WXC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI!sD19Datatypes4list00K!sF+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00!tT<6op!sL#00!uh;?!s<25State8m_haltedK!t#C2I!v=72eq!tc>4prod!taS9m_vm_lazyK!w9A1I79OSSVerify6Proofs:boost_json:fuzz_parse3lib6CatSim6msteps00C13~~~K!tiJ3Run6config!tFR8ShapeAlg8realize!tJ+C!smX9rz_!u:%!slV:StartupTac3bwd!sh%I!uzJ<MemImageType7Segment!xl#!xLO5Model00!usY4TSet!x$'!|~E3!tjK>!~m$!sE+=machine_s!u%#!t{R4Scfg=hunspell_scfg!wp&!~=@;bv_unsignedC56Std!zs#ZArith6BinInt1Z2le!#3I=Z02!s`<6modulo!}{83and!#4oH1!~%Q<sp_window_lo!sa\hiI!uj?0!v0@1!v0<3pow!w/>ti8!xcN1U:Ref!|l&:main_entry!~J+!xj@4BvWfK!#8LC1!|CQPropExec7seg_rom!tX'!#5HLAs!~C%s_reserved!tPP3Amb<mk!sz#InputC!tPQ!xw%:!ux#_model!#:yQwith_tid!vTY9u64_range!#3v2!#;E1!{zR5m!tb#c!ys\6bwd_rz!viA!#@m0;!#@m#_empty!zGA7Z_to_bv!vQY6regup!#9L%!|i<4of_N!vRQ7in_argv!s\Uenvp!s\Q6in_uid!z&Rin_hwcap!v}A5bv_eq!#BIC!~FRMemSplit4cmem!#>SU!}]#5a!uk$!scY7a!us&!#@eU!u3'9wfJ_cons!#=u%C!|/Q;!|/,16p1_run!snd9regs_!x&#!sqd2J1!v;V7Cat!|f#<cat!{f$_ptr!snWArgvEnv8!{t#!sj-!#;`;subC4!sC&5Lists4!s+#2In!#I{9x!#CWR!#39&4ge!t]'!#IdA2!uiQSeq!#4A#v_jal!vSW5Hoare6ret_ok!vOCmulK!v8;!#?h34Zdiv1Z>mod_!s&#divide!#Q476!#Q4$!sB<sym!wo+!t+/BZminus!t,$idemp_l!sN+9micromega9SatDivModCZ!sQ$nonneg!s,&!ud<>pow_pos!sNC:!sN#!sJB7div!tI#!uX83not!w:=div!sC=ad!#Gk<=!ua#!u6#boun!sMB!v,#!sM15!vY$8PreO!s/#1Z;!u9#0_r_ext!sL>!st#!sL&K!wQ56VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr02!sIE1!sIE4!yq65Tauto8B!t[&!sH6:Z!u%+=Z!sT$CheckerC!uv<4f!{r$!sq?C!sq0_s!x%#!u8E7K!vtL1!#45QtepTac6u_Z2bv!#5?A3nat02C!#QjX@word_to_le_bytes!#9aW6w!sb%!#9[\5argcN!#>I^:wfJ_!tV\!sm+3wfJ!sf_6win_lo!#8IA6of_nat!#ar8iff_ref!#6z6;ZifyClasses3inj!sIB5mkre!snC;rew_!tB%v!ujYAstore_ok_cmem_wi!#A|X9RefMemset=m!s,$304!#Bq,!ymPZS!ta#s5zeros!#=^[:!#CR#agre!#O5%!ww89False!#<`#!ugQ>!#Cr+Defs6!#BG#w!t88!#Ie,length!#>]4nat5Nat2Z9i!#<S&!#9%?1!sD@3!#5VD5C3!#K}$7tactics<f_equal_help!#Cz8or00!vDa5J_lsm!ywX!sp5aux!spg4pn!w~+!xqaD_libc!#4/V!#SU'v_addi!siWRefNodes?!#XR&!#lT%!sr_=!sr+lazy!~%WGrChainAgr_reg_neq_o!z##b!vD_9getr_same!w}hargc!xpi8canary!ss'!#[8]J_ma!#70Y!zT5!sql!#QG#!vHiaux_bas!x0h5rnd!te'!#NR7!#id#1k!wU\!#f\-1!u$X!#Up,46fin_c9!snj8!snj7!snj6!snc36tls_c5!snj4!snj3!snj2!snj!zFd26p3!#C$a<!#@]$_!#C/Z!#E['?!#Ir$!#EY2!srX9!sk$!#`R,!#9ZX!#nB$k!#b{'!#pRM;!sb$!#~y$!tLY4!tG-!sgX8wrap_!#gC'K!#T];G!#RD&4!sJF8!#E-D3!#LDDapp!sKB6!sK$2K!#E\:1!s@<2!vMY:!#?8#other!|eX!#:/13rb!{%X!#BV&:rz_set!#tx#!z<TB!zx%!$$]-!tT/!tM96images5Ubsan1M?loaded_!#x[&!zI_3fx!$0H'!w|64True!#YZ0!tqH5phdrs!{E<!#Zj03Op2!zY8!{H%5eKind!$4B<unit!#_C7!se%4kind!zS4!sf3!#y'Q>stack_max_size!#7FPMmapSimB!sj1_val!vO%I!#\~?!#OKR!#UR+;!#UR$_clob!t88!xb%5!#S{#!t6TCUb_code_dd254_dddf47W_dd7d!#=|X!sw8F!swsE!sw0!{NS7!~,$pc!~gQ2Fs2Fs!$6fP;!$'8#Stream00!#L'\3H!#_%&!sj_hi!sje!{U5!$Az50!#es@1I!#4d<!#ka6!#hh,;!#Z|$!u'$!$A%>bool!tU>!sF%1!#5;H5!#5;58ZifyInst7Inj_Z_Z!v-=!$7^+0!t>I1C6!#:9ISys6Kernel4Fork@PID_MAX_ENVELOPE!uvB2!#;JN8valid_sp!s[O9!s[%brk!s\O:!s\%!$-&N!s]-!$-'#!#8%N3Amb6amb_of!#;B&!~BO9P!$6X&!#:-R;fs_seed_tmp!}J]?ref_s!s2%_sec!}V'!tXI;StackLayout9EntryDraw!$D~R!uz-!s`R8NetQue!~X%!s_O6VaSize!#6T^6me_!$1cX!#Bh+rd!#Mp_>rdn!#Na$above!#BZ;!#JU25!t=Y6in!#Orb;!t|%t!sn-!#viX8!#p4&!tVY<!tV'data!uG_=!wI+!sp,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk14prod37Corelib4Init5Logicm72eqk14Nonek13nilk16option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypep67Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticst5dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhhc5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehl15Modelhl18m_haltedhl19m_vm_lazy69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hq1dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~hu94TSethu98realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3libaStartupTac~~~~~~ij83bwd46Stdlib6ZArith6BinInt1Zinc2lehfbbv_unsigned01Zinc6modulo69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~ir5floaded_segments69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~ivecmkProcInputCinc2ltm71Im73and3h5LinuxProcessSemanticsfLinuxProcessSem2Fsjl42Fshhcbinit_confighhch1segments_reservedhl1bInputStreamhl1ainit_modelhl18with_tid3h5LinuxProcessSemantics5Riscv7Preludejt35bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~kg23fx0kg24mkstkg27seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefStartup~~~~~~kl7amain_entryir57init_pcir55phdrsinc3powhf2BVhf4BvWfhl17in_argvhl17in_envphhcavalid_argvhhc9valid_brkhhcavalid_envphhc8valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutlh69EntryDrawhl19ProcInputive6amb_ofkg23rdnk13native7a_hwcapive5a_uidkg28wrap_meminc3addinc6of_natm73nothl1estack_max_sizeinc3subk14boolk14truet58store_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UeRefStartupDefs~~~~~~lu46D_main" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
Lemma bwd_rz : ltac2:(zQ "h21!h9!jc!l9!m0!nb!o0!o7!od!sb!hgc!hk8!hnf!ho8!hp4!ht8!ii4!iic!in5&@2$3@1$1@1$0#k0@1$1@1$0#k0>4segs@1$2$8>5model$b>1K$f>0@3$4@1$7@1$1@1$0#k0@1$c^2@1$5@1$1@1$0#k0>0@3$4@1$2~0@1$d^3@1$6~0@2$h1^5\2st$9@4$h0^6$e@2$a^1^5^4").
Proof.
ltac2:(KReplay.run1 (kr_t_RefStartup ()) ["FPX1"] "h02sth12Hhh25Hlazyh33Hmsh44Hst'h51Kh65modelh74segsh83st'p;1p;3p;2p;4p;:p10000p4p7210p1000\p4p710p8g001:j11Tg001Zj10Tg002?j1:Tg002]j15Tg003@j1?Tg003bj1<Tg004Yj1;Tg005;j32Tg005Uj29Tg0065j16Tg006mj17Tg007Mj38Tg008Pj23Tg009Ej44Tg00:Ll:>Tg00;Rj2=Tg00<T#1g00=Sg00>Ig00?J#0#0#0#0#0#0#:#5R0#?f1R1#<%;0321900R0#1f2R2#6%7032g00?oR0f6R3f0R4781f7R5g00A6R61313f5R7C4f8P6f3R8P2P5P3P7f4R3P1P4M:>W4W3X80W0P7P61343P8C4X00,=3eW2W1W5W6W7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev a_uid a_hwcap (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0xdd368) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x12ee88)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0xdd370)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xdd564)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xdd4b4)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xf46b8)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xdd4b4)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xf46b8)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (rnd : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xdd574;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x10ebf8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x46fe4;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap rnd) J (D_main sp0 av ev a_hwcap rnd tid)
}.
End FPX1.

Section Assembly.
  #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Context {AMB : Amb}.
  Variable sp : word.
  Variables argv envp : list (list byte).
  Variable rnd : ltac2:(zQ "10!lka$0").
  Hypothesis Hva : ltac2:(zQ "10!ku1@1$0?4argv").
  Hypothesis Hve : ltac2:(zQ "10!kvc@1$0?4envp").
  Hypothesis Hvsp : ltac2:(zQ "10!lga@1$0?2sp").

  Lemma Hlo : ltac2:(zQ "30!h9!ip4!ipa@2$1+nvvvogggggg0@2$2@1$0#k0?2sp").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Assembly"] "##&Fh01Hh12_Hh21vp;1p;2p;3g002?j1:Tg00B<j28!s/$fj24Tg00CBj17!s/$`j2;Tg005;j39Tg00D@R0j25!s1$[j13Tg001Zj12Tf0R1#2!s$%p=0%21#2p=6%31#3p=1p,4Hvspg00E@g00?JR2#0R3#6#:p,2sp'8R4'4R5g00F;,44g00G6%73,;!s1$T39'5R3'5P0P5P3%32#1!s$02#6#0!s$07/44P1f1R4X13X05P4P1O2n20010!s#$12!s-%0b2o"). Qed.
  Lemma Hhi : ltac2:(zQ "30!h9!ip4!ipa@2$1@2$2@1$0#k0?2sp+ogggggggggg0").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Assembly"] "##&nh01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g002?j17Tg00B<j25!s/$fj22Tg00CBj14!s/$`j28Tg005;j36Tg00D@R0j23Tg001Zj10Tf0R1#0!s$%p=:%01#0p=9!s-$!s$/p=1p,4Hvspg00E@g00?J#:R2#9R3#7p,2sp'5R4'2R5g00F;,24R6g00G6%42,84g00GT36R2'3R7'3P0P5P7%03#1!s$+4,24R4P1P0P6P2P4P1f1R4X32X06P4P1O2n20010!s#$12!s-%0X17X25!sF6!s/&b4o"). Qed.
  Lemma Hal : ltac2:(zQ "50!nb!h9!iq8!iqb!ipa@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Assembly"] "##&9h01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g001Zj10Tg002?j17Tg00B<j23!s/$fj21Tg00CBj16!s/$`j25Tg005;j34Tg00D@R0j22Tp,4Hvspg00E@g00?J#0!s$%R1!s-$7p,2sp'3R2'1R3g00F;,12R4g00G6%61,52g00GT34R2'2R1'2P0P3P1P2f0R5P0P4P2P2P5P5X02X34f1R4P5O2n20010!s#$12!s-%0X11X23P!sF<b4o"). Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : ltac2:(zQ "he0!h9!jc!iub!jj4!ht8!iic!jk4!ipa!od!jka!jke!iq8!jnf!jo5!hk8!jp4!jqa!jr9!js7!jv9!kjd!kk4!kkc!ii4!kp6!kq4!kqf!kr8!krf!ks4>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3lim$b>3fs0$c>6stdin0$h0>1K$h7>0>3tid@1$1@1$0#k0>4regs@2$h3@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@2$a@2$6Z@2$7@1$0#k0^3@2$6@2$7@1$0#k0^3@2$hb+2+h6>0@8$h8?3AMB?2sp?4argv?4envp?3rnd^4^3^2@4$5$2$4@2$e@5$h5$h4^4Kd@3$hc@1$0#k0+kmvu4Kv$9@2$hd@1$0#k0+kmvu4@1$1@1$0#k0^3@1$h6$2@2$h2^5@6$h1@1$f$2^b^a?2sp^9@5$3?3AMB?4argv?4envp^8^7^6@4$5$2$4@9$d$2$h9$ha?2sp^7^6?3rnd^5@5$3?3AMB?4argv?4envp^4^3^2").
Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model in_argv in_envp in_uid in_hwcap].
    set (model := init_model (segments_reserved rsegs) brk mbase sp lim (mkProcInputC argv envp fs0 stdin0)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x46e98 : word) by (apply bv_eq; reflexivity).
    rewrite cmem_init. fold (regs_init sp).
    destruct (p1_run sp argv envp a_uid a_hwcap rnd Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    assert (A1' : getr regs1 1 = (0xdd284 : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp a_uid a_hwcap rnd) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0xdd284 : word) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (realizes SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp argv envp a_uid a_hwcap rnd) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
    intros regs3 C1 C2 C10 C18 G3.
    carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
    assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
        clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
    pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
    pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
    pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
    pose proof (Cz 27 ltac:(in_list)) as Z27.
    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    unfold RZ at 1.
    eapply (rz_set_tid SEGS regs4 (0xdd7d4 : word) _ (seg_rom SEGS) model K W_dd7d4 F_dd7d4 E_dd7d4);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid'.
    assert (Htid : (0 < bv_unsigned tid < 2^22)%Z) by (unfold Fork.PID_MAX_ENVELOPE in Htid'; exact Htid').
    replace (v_addi (0xdd7d4 : word) 4) with (0xdd7d8 : word) by (apply bv_eq; reflexivity).
    set (model' := with_tid tid model).
    assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
    assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 argv envp a_uid a_hwcap rnd) with (G := RZ'); try side Hva Hve HG'.
    intros regs9; intros.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
      + unfold J_main, J_tls, D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Section FPX2. #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
Theorem ref_startup : ltac2:(zQ "i40!h9!jc!iub!ksb!kt6!ht8!iic!jk4!ipa!od!jka!jke!iq8!jo5!hk8!jp4!ku1!kuf!kvc!lga!lka!ll7!jr9!js7!jv9!lm4!kjd!kk4!kkc!ii4!kp6!kq4!kqf!kr8!krf!ks4>2sp@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3rnd$h4>3lim$c>3inp$h5>1K$hd>0@1$h3^7>0@2$h1$2^7>0@1$h0@1$3^4>0@1$h2@1$4^5>0>3tid@1$1@1$0#k0>4regs@2$h8@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$9@1$1@1$0#8>0@2$b@2$7Z@2$8@1$0#k0^3@2$7@2$8@1$0#k0^3@2$i1+2+h6>0@8$he@1$h9^a^f@1$3^a@1$4^a^c^4^3^2@4$6$2$5@2$e@5$hb$ha^4Kd@3$i2@1$0#k0+kmvu4Kv$a@2$i3@1$0#k0+kmvu4@1$1@1$0#k0^3@1$hc$2@2$h7^5@6$h6@1$f$2^f^e^h0^c^b^a@4$6$2$5@9$d$2$hf$i0^c^b^a^9^8^7^6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["FPX2"] "##8}p'0h01Kh13memh24regsh33tidh42HKh54Hbrkh63Hsph73Hvah83Hveh96abtermh:4argvh;3brkh<4envph=3fs0h>3gidh?6groupsh@5hwcaphA3inphB3limhC5mbasehD3nethE6nofilehF3rndhG7sigmaskhH2sphI6stdin0hJ3tmphK3uidhL4urndhM4vaszi00Ain_abort_terminali017in_argvi027in_envpi036in_gidi049in_!ts%i058in_!tw$i06;in_image_fsi076in_neti089in_!tz%i09:in_!tx&i0:8in_!tw$i0;6in_tmpi0<6in_uidi0=:in_urandomi0>:in_va_sizei0?1pp;1p;2p;8p;3p;5p;6p;?p;4p;9g001Zj10Tg002?j19!s/$]j1?Tg02WHj1ATg02X=j2CTg00VHj14Tg02Y3j1@Tg00W>j13!s8$jj1=Tg00D[j11Tg0000j2HTg003@j1FTg00B<j2ETg00HOj2DTg00CBj18!s8$2j2Q!se$@j2PTg02Zaj17!sA$kj8BTg00J[j3OTg00K>j1NTg022>j5KTg00LBj1JTg00NDj6>Tg00O=j2:Tg008Pj2;Tg001:j16Tg02[_l?2Tg02\Yj2ITg02]Sl?GTg009Ej4LTg021Fl9MTg02<CR0g00A6f1R1f0R2CLp=5P0g02JNg02>ff5R3f4R4f3R5f2R6P1P2M9Mp=<g00?J#0R7#0#0R8#0!s$$9R9#?R:g02^cg00G6g02_cR;P;g00>IR;f7R<#A1C0<%45#@%34#=%17R=#9/H:R>%98#?R?#F\:R@g00GT1E96RA'D%87%1=#0#8'Q,DA'PRAf9R=#7f?R7%4=%3=f<RBP5P6P1GBg02=JP5%18#1#0#1!s$00!s8$0#0#8g02>J5O9P6%N0DKR9%J0R8P7f>RCf@RDPBf:REE>,:4';/5=[[]1]2^3:PBf;RFPEP=f8RGf6RHE</53[[[[[]0P2%6?#6R?g02KMRIg02L;RJ%6:g02`]g02RHg02aVfTRK!v/$KfARKPDP7PCf=R0PBP!t'$PGP<PHP3P4P5M?2#4#@fBRLP!sQ&P!sO6M?2#3#=fGRMfFRNfEROfDRPfCRQP!s_6M?2RR#7f\RS%4R%3RfYRR!ve'P8PSf[f]PRfHPMPNPOPPP!sm6M?2!vB$,;9/5=[\A^1@^2>^3:!sV9!t~'M?2R7#7PRPPPQfVRQP6P1P4fXRPfWRDfUR>1ILHPKP3P2M?G!sO$DPQP>P7!w6$eW4W8W7W5W6X0;XJIXLJWMW9X@:XG:XE:WDW?X>:XK:WIW=X<?W:!vU9!ui%P2O?n0110?0001?110110210610:10<10310410710810910510010>10=10;WAWBWFXC:X;:WHo"). Qed.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable rnd : ltac2:(zQ "10!lka$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!jv9!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!h9!jc!od>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis ME : ltac2:(zQ "10!kp6@8$0?3AMB?3sp0?2av?2ev?3rnd?3tid?4regs?3mem").

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : ltac2:(zQ "h10!h9!ipa!l9!lme!ip4!jc!ln5!od!nb!sb!lnb!lo6!lof!kqf!lpb!lq2!kr8>4segs@1$2$9>1a@1$5@1$0#k0>1n$6>0@2$4@2$1@1$0#k0?3sp0@2$1@1$0#k0^2>0@2$4@2$e@2$1@1$0#k0^3@1$f^2@2$h0+2+k0@3$8@1$7@1$2@1$5@1$0#8@4$3^5?3mem^4^3@4$3^5@7$c$d?3sp0?2av?2ev@1$b?3AMB@1$a?3AMB?3rnd^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##4Op'0h01Hh13s1vh21Jh32MEh42HJh52Hah62Hnh72_Hh81ah91eh:3memh;1nh<4segsi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001:j19Tg001Zj14Tg002?j1>!s/$]j1:Tg00B<j27!s/$fj2?Tg01A8j1ETg00oNj2DTg00CBj1;Tg00H2j2ATg02bMl9@Tg003@j18Tg01?5j25Tg01Z:j56Tg005;j30Tg00[gj1ITg00\dj1HTg023?j7GTg01[Aj6FTg00Zfj42Tg00D@R0j23Tg00e@R1j2=Tg02cTj41!tP$kj8<Tg02dTl9CTg000\j7BTg00<T#9g00?J#4R2#4#4R3#4!s-$4#>R5#:R6g02DTp,3sp0R7,75f1R8,75'?f2R9,75%E8'D%;2%;4'A'?p,3AMBR4P7p,2avR2p,2evR5p,3rndR:p,3tidR;p,4regsR<p,3memR=p,2MER>M9@%>3#:R3#8\6R?1578P4P7P2P5f0R@D6RA90?8P7g02>f!s?%%I4%H4RBP:FGRCP8!s<%PBP:P;EFRBC290?='3'3X16,=6RDX2?RE'=P1P?PE%93#8R3f6REP=f5RFf4RGC1PEPCPFPGC130P@P1P61579A0?9AP7PCP9P!t#1f:R9P=f9R1f8REC1P9PCP1PEC1503P@157GA0?G!sc%G!sc/P0157F!u]'P8D690?F!sN$F!sN,f>RAP=f=R9f<RHC1PA!tS$H!t-&f7RI,57!sl+G!sl$E!sl$E!sl,P0!sH+F!sH$1!sH$1!sH'fBR1P=fARFf@R0C1P1!tT$0!t4';!se+ID650?!sd$H!sd'P?!v9,R9!sQ+:P;P<P@G<fGRHP8fFRIfE!t+$HPCPI!t+&]3X:?!sZ29G<!sx$IPAPBP0fDfCP1M9CW3P=P@P>FBW0W7P8P@O2n20010!s#$12!s/&W0W4!sD?X16!sE7!s0%X0DX2?!sF=b9W6W5W;W8W<o"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : ltac2:(zQ "c0!h9!ipa!jc!o0!od!jke!nb!lqc!lr2!ip4!jk4!ls4>1a@1$2@1$0#k0>0@2$5@2$9@2$b@2$1@1$0#k0?3sp0$8@2$1@1$0#k0^1@2$a@2$1@1$0#k0^1@2$1@1$0#k0?3sp0@1$7@3$6@1$4@1$2@1$0#8@1?3mem^2@1$3@1$2@1$0#8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##9?p'0h01Hh13s1vh21Jh32MEh44__x1h54__x2h64__x3h72HJh82Hah92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?1eh@3memhA1oi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001Zj14Tg002?j1C!s/$]j1@Tg00B<j28Tg00dLj2;!s8$fj2:Tg00HOj29Tg00D@R0j21Tg02bMl9MTg003@j1GTg01?5j26Tg01Z:j55Tg005;j30Tg00[gj1]Tg00\dj1VTg023?j7UTg01[Aj6RTg00Zfj42j5[Tg00e@R1j2BTg004Yj1ATg00nXj13!t\$kj8=Tg006mj1OTg001:j1NTg012Ej2<Tg01KVj4L!s8$cj1KTg013Aj1H!s/$lj27Tg0152j3I!uL$[j1JTg018Wj4>Tg02e_j7FTg024hj8E!sS$Uj2PTg00Q:j2QTg0167j2D!s/$cj3STg017Bj4TTg02fCj2\Tg02gFj6ZTg000\j6Wj7X!sz$Dj7YTf1R2g02@JR3g02@iR4P4g02AIR5f0R6g02AiFYp=?g00?JR7#4R8#4#4R9#4!s$$CR:#@R;p,3sp0R<,8:R=g02BIR>';18:6R?':19?='1p,3AMBR?P<p,2avR@p,2evRAp,3rndRBp,3tidRCp,4regsRDp,3memREp,2MERFM9M%C9#@R9#GRG\;RH16<2P?P<P@PAP6D5RI90H2P<g02>f!s=%%]?%V?RJPBFURKP2!sS&JPBPCERRJC290HE'1'1X1;,B;RLX2HRM'BP1PHPMPEf3RMO1%A9R950G#3P6P1P;f2R1,6<A0H1IP<PKP1P!sq1PEf7RNO1=0G9#3P6f4RO!sW%O!sW%O!sW/P0f5RI,6<!uD+2D590H!sQ%I!sQ,PEf;RP!s},16<Nf8RQ!s^+OD550H!s]$Q!s]-0f9R0!sK+I!sK,0!sK'PEf?!s~,!sQ+N!tV$PP<PKf<!sR+!sb$f=PJC2RP!sR+BPCPDP6G=P2fD!us,]3X@H!sK2PG=PGf>RPfCRDO1A0G69#3XAGf6PDg00G6RGg02Q\R9#O%N9PG1<G1P21<GMCL%KG%HGR9P3P4P4P5P!s0,G17G7R317G85IGg02?c%J7,7GR7C>,?9PGP7g02SHP3!s6$FFR3%A4P3GE1P95P6P1g02RHR9g02RhR5'Q1D61=095dg00GT=SG2CTb;b<b=X4GX5GW61;62/:11916'11;21/:M19M2'1[^4G^5G^6GP618:NP>P=PDO4b:1\<DeR=O2!wM$PPJPDD[!s2,P=EZEWW3PEP6PFFXW0W9P2P6O2n20010!s#$12!s/&W0W7!sD?X1;!sE7!s0%X0LX2H!sF=b?W8W>o"). Qed.

  Lemma main_entry_store_ok_win : ltac2:(zQ "f0!h9!ipa!ip4!lsb!l9!ln5!lt2!nb!sb!lt9!lr2!lpb!lq2!ls4!jc>4segs@1$4$8>1a@1$e@1$0#k0>1n$5>0@2$2@2$d@2$1@1$0#k0?3sp0$a@2$1@1$0#k0^2>0@2$2@2$b@2$1@1$0#k0^3@1$c^2@2$1@1$0#k0?3sp0@3$7$3@4$9^5?3mem^4^3$6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##:sp'0h01Hh14__x1h24__x2h34__x3h43s1vh51Jh62MEh77__arithh84__ffh98__varmaph:5__with;4cstrh<2HJh=3Hhih>3Hloh?2_Hh@1ahA1ehB3memhC1nhD4segsi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8p;:g001:j1FTg001Zj15Tg002?j1C!s/$]j1@Tg00B<j29Tg00dLj2=!s8$fj22Tg01A8j1;Tg00oNj2:Tg02bMl9NTg003@j1JTg01?5j26Tg01Z:j57Tg005;j30Tg00[gj1\Tg00\dj1VTg023?j7UTg01[Aj6TTg00Zfj43Tg00D@R0j21Tg00e@R1j2DTg02hNj48Tg00Hkj8BTg01JSj1QTg006mj1PTg012Ej2ATg01KVj4O!s8$cj1MTg013Aj1K!s/$lj2<Tg0152j3I!t>$[j1LTg018Wj4>Tg004Yj1H!sJ$Uj2GTg00Q:j2RTg0167j2S!s/$cj3_Tg017Bj4^Tg01@5j1]Tg025Lj3[Tg01Cil:WTg000\j7XTg024Dj7Y!s/$hj8ZTg02RHR2f0R3g02RhR430p=4f1R5g02@JR6g02@iR7P7g02AIR8P3g02AiFYp=?f3R9P6P7P7P8f2R6P5P3GZp=Eg00<T#Fg00?JR:#5R;#5#5R<#5!s$$CR=#@R>g02DTp,3sp0R?,9=R@g02BIRA'=19=5'219=6%;5':/2@p,3AMBRBP?p,2avRCp,2evRDp,3rndREp,3tidRFp,4regsRGp,3memRHp,2MERIM9N%C<#@#J\>R<16?5PBP?PCPDP3D7RJ90<5P?g02>f!s=%%\B%VBRKPEFURLP5!sS&KPEPFETRKC390<H'1'1X4>,D>RMX5<RN'DP1P<PNf6RNPHf5ROf4RPC8#4P3P1P>16?6A0<6JP?PLP6P!sn1f:PHf9R1f8RQ!sZ%16?PA0<P!sV%P!sV/P016?O!u=+5D790<O!sN$O!sN,f>RJPHf=RRf<RS!s{%f7RT,6?!sa+P!sa$Q!sa$Q!sa,P0!sH+O!sH$1!sH$1!sH'fBPHfAf@!s{&;!sT+TD750<!sS$S!sS'P!s6%RPKC3RR!sQ+EPFPGP3GBfGRSP5fFRTfER1C8#4]6XB<!sO2RGB!sm$TPJPKP1fDRKPN%QKRNg00GTRJ%;K'2RLg00G6RRg02Q\RG#PRF%FGRGPR1AR6P51AR9CORE%MRRD%KRRCPR1<R:RB1<R;R;5IRg02?cRO%L:,<RR:C>,?CR0%H7R7P0CE1GC8R8P3P61R241S36#4dA_RJ5C^RJb8b9b:X1RX2RW31=35/261=56/29[^1R^2R^3RP319=SRSPAP@P1O4b7b;%]?19=1'2ePNPL!uj$EPDPCPRA[RB;POP!tY&CP7PCCEP8P!t<0X3R1:!t=%:!t=4P@%;TPSPK!t:%M:WW6PHP3PIFXW0W?P5P3O2n20010!s#$12!s/&W0W<!sD?X4>!sE7!s0%X0MX5<!sF=bAW=W>WCW@WDo"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : ltac2:(zQ "a0!h9!jc!ipa!od!nb!lr2!lnb!mi7!jk4!ls4>1a@1$1@1$0#k0>0@2$8@2$2@1$0#k0^1@2$9@2$2@1$0#k0?3sp0$5@3$4@1$3@1$1@1$0#8@1?3mem^2@7$7?3sp0?2av?2ev@1$6?3AMB?3rnd?3tid^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##3Rp'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001Zj13Tg002?j1<!s/$]j1;Tg00B<j27Tg00dLj2FTg00HOj2:Tg02bMl9CTg003@j1@Tg01?5j25Tg01Z:j54Tg005;j30Tg00[gj1>Tg00\dj1=Tg023?j7ETg01[Aj6Dj76Tg00Zfj41Tg00D@R0j22Tg00e@R1j28!tJ$kj89Tg01@5j1BTg02iNj6ATg000\j7?Tg00?J#3#3#3R2!s-%#<R3#;R4f0R5,73p,3sp0R6,73g02BI'F':p,3AMBR7P6p,2avR8p,2evR9p,3rndR:p,3tidR;p,4regsR<p,3memR=p,2MER>M9C%<2#;#@R2\4R?f1R@,56P7P6P8P9P5D4RA90?@P6g02>f!s=%%>7%=7RBP:FERCP@!sS&BP:P;EDRDC190?='2'2X14,84REX2?RF'8P1P?PFP=f3RFO1!s]/PFF6502P5P1P4f2R1,56A0?1AP6PCP1P!sz1P=f7R1!sh21!sh&f4RF!sd%F!sd%F!sd/P0f5RA!uZ/@D490?!sQ%A!sQ,P=f;RG!t22G!t2&1561f8RH!sk+FD450?!sj$H!sj-0f9R0!sK+A!sK,0!sK'P=f?R0!t520!v''!s`'1!tr$GP6PCf<!sa+!sq$f=PDC1RG!sR+:P;P<P5G9P@fD!vD:]3X9?!sX2GG9!sv$>PDfCRDfB173D%B6':eEAW3P=P5P>F?W0W6P@P5O2n20010!s#$12!s/&W0W4!sD?X1!sE8!s0%X0EX2?!sF=b8W5W7o"). Qed.

  Lemma main_entry_rdn_data : ltac2:(zQ "h00!h9!l9!lme!jc!ipa!ln5!od!nb!sb!lr2!lnb!mi7!lpb!ip4!lq2!ls4>4segs@1$1$8>1a@1$3@1$0#k0>1n$5>0@2$d@2$c@2$4@1$0#k0^2@1$e^1@2$f@2$4@1$0#k0?3sp0$9@3$7@1$6@1$1@1$3@1$0#8@4$2^4?3mem^3^2@4$2^4@6$b?3sp0?2av?2ev@1$a?3AMB?3rnd?3tid^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##4Hp'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memh:1nh;4segsi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001:j1@Tg001Zj14Tg002?j1=!s/$]j19Tg00B<j27Tg01A8j1<Tg00oNj2;Tg00dLj2D!sJ$fj2>Tg02bMl9ATg003@j18Tg01?5j25Tg01Z:j56Tg005;j30Tg00[gj1ITg00\dj1HTg023?j7GTg01[Aj6FTg00Zfj43Tg00D@R0j22Tg00e@R1j2:Tg02cTj41Tg00Hkj8?Tg01@5j1CTg02jWj8ETg000\j7BTg00<T#@g00?J#4#4#4R2!s-%#=R3#9R4g02DTf1R5,73f0R6#<';p,3sp0R7,73g02BI'D'>p,3AMBR8P7p,2avR9p,2evR:p,3rndR;p,3tidR<p,4regsR=p,3memR>p,2MER?M9A%=2#9R2#8\4R@1575P8P7P9P:P6D6RA90@5P7g02>f!s=%%I8%H8RBP;FGRCP5!sS&BP;P<EFRBC390@>'2'2X14,:4RDX2@RE':P1P@PE%@2#8R2f5REP>f4RFf3RGC1PEPBPFPGC130P6P1P4f2R1,57A0@1AP7PCP1P!t&1f9R1P>f8RGf7RHC1P1PBPGPHC1502P6157FA0@F!sc%F!sc/P0157E!u^+5D690@E!sN$E!sN,f=RAP>f<RIf;RJC1PAPBPIPJ!t-,H!si+F!si$G!si$G!si,P0!sH+E!sH$1!u@1fA!u9$@REf?R0!u9&EP0!t1&!sc+H!sc$J!sc$I!sc'P@!s6$APBC3RA!sR+;P<P=P6G?fFRIP5fERJfD!v>$IPBPJ!v>&]3X9@!sZ2AG?!sx$Jf>PBPHfCRBfB173H%<B';%C7'>eGEW3P>P6P?FBW0W6P5P6O2n20010!s#$12!s/&W0W4!sD?X1!sE8!s0%X0DX2@!sF=b8W5W:W7W;o"). Qed.
End Consumers.
(* [comment removed for export] *)
