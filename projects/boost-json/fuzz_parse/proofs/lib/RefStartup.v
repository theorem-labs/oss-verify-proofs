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

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Amb ShapeAlg Nodes RefNodes FileSim
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs
  RefStartup1 RefMemset RefStartup2 RefStartup3 RefStartup4
 Ref_code_47284_47870 Ref_code_d9dac_da94c    .
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefStartup () := KReplay.lz_vm "#$VeC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI!sD19Datatypes4list00K!sF+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00!tT<6op!sL#00!uh;?!s<25State8m_haltedK!t#C2I!v=72eq!tc>4prod!taS9m_vm_lazyK!w9A1I79OSSVerify6Proofs:boost_json:fuzz_parse3lib6CatSim6msteps00C13~~~K!tiJ3Run6config!tFR8ShapeAlg8realize!tJ+C!smX9rz_!u:%!slV:StartupTac3bwd!sh%I!uzJ<MemImageType7Segment!xl#!xLO5Model00!usY4TSet!x$'!|~E3!tjK>!~m$!sE+=machine_s!u%#!t{R4Scfg=hunspell_scfg!wp&!~=@;bv_unsignedC56Std!zs#ZArith6BinInt1Z2le!#3I=Z02!s`<6modulo!}{83and!#4oH1!~%Q<sp_window_lo!sa\hiI!uj?0!v0@1!v0<3pow!w/>ti!|gPRef!|j&:main_entry!~H+!xh@4BvWfK!#8JC1!|AQPropExec7seg_rom!tX'!#5FLAs!~A%s_reserved!tPP3Amb<mk!sz#InputC!tPQ!xu%:!ux#_model!#:wQwith_tid!vTY9u64_range!#3t2!#;C1!{xR5m!tb#c!yqZ6bwd_rz!vgA!#@i0;!#@i#_empty!zEA7Z_to_bv!vOY6regup!#9H%!|e<4of_N!vPQ7in_argv!s\Uenvp!s\Q6in_uid!z$Rin_hwcap!v}A5bv_eq!#BEC!~DRMemSplit4cmem!#>OU!}[#5a!uk$!scY7a!us&!#@aU!u3'9wfJ_const!slV;!|,,16p1_run!slb9regs_!w~#!sob2J1!shV7Cat!|`#<cat!{`$_ptr!snWArgvEnv8!{n#!sj-!#;V;subC4!sC&5Lists4!s+#2In!#Iq9x!#CMR!#33&4ge!t]'!#IZA2!uiQSeq!#4;#v_jal!vSW5Hoare6ret_ok!vOCmulK!v8;!#?^34Zdiv1Z>mod_!s&#divide!#Q&76!#Q&$!sB<sym!wo+!t+/BZminus!t,$idemp_l!sN+9micromega9SatDivModCZ!sQ$nonneg!s,&!ud<>pow_pos!sNC:!sN#!sJB7div!tI#!uX83not!w:=div!sC=ad!#Ga<=!ua#!u6#boun!sMB!v,#!sM15!vY$8PreO!s/#1Z;!u9#0_r_ext!sL>!st#!sL&K!wQ56VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr02!sIE1!sIE4!yq65Tauto8B!t[&!sH6:Z!u%+=Z!sT$CheckerC!uv<4f!{r$!sq?C!sq0_s!x%#!u8E7K!vtL1!#45QtepTac6u_Z2bv!#5?A3nat02C!#Q`X@word_to_le_bytes!#9aW6w!sb%!#9[\5argcN!#>C^:wfJ_!tV\!sm+3wfJ!sf_6win_lo!#8IA6of_nat!#ah8iff_ref!#6z6;ZifyClasses3inj!sIB5mkre!snC;rew_!tB%v!ujYAstore_ok_cmem_wi!#AxV9RefMemset=m!s,$304!#BkY7ZS!t_#s5zeros!#=\[:!#CN#agre!#O'%!wu89False!#<^#!t1O>!#Cn+Defs6!#BC#w!t68!#I[,length!#>Y4nat5Nat2Z9i!#<O&!#8}?1!sD@3!#5RD5C3!#Ks$7tactics<f_equal_help!#Cv8or!#CvQ!vB25J_ls!#KkV!sn5aux!sne4pn!wx+!xi_D_libc!#3{V!#SC'v_addi!siWRefNodes?!#X>&!#l>%!sr_=!sr+lazy!}wWGrChainAgr_reg_neq_o!yw#b!vD_9getr_same!w{fargc!xlg8canary!sq'!#Zx[J_ma!#6vW!zL5!soj!#Q1#!v@gaux_bas!w|f5rnd!ta'!#N87!#i@#1k!wKZ!#f8-!#ThV!#UR,46fin_c9!slh8!slh7!slh6!sla36tls_c5!slh4!slh3!slh2!slh!z4b26p3!#BRa<!#@1$_!#BYZ!#E''?!#IB$!#E%^!#aW+!sk$!#_xY!#96+!#mb$k!#bE'!#orM;!sb$!#~?$!tLY4!tG-!sgX8wrap_!#fe'K!#T,;G!#Ql&4!sJF8!#DZD3!#KlDapp!sKB6!sK$2K!#E0:1!s@<2!vMY:!#>l#othe!#a>V!#9o13rb!{#X!#B0&:rz_set!#t>#!z:TB!zv%!$#y-!tT/!tM96images5Plain1M?loaded_!#wy&!zG_3fx!$/d'!wz64True!#Y$0!tqH5phdrs!{C<!#Z803Op2!zW8!{F%5eKind!$3^<unit!#^i7!se%4kind!zQ4!sf3!#xIQ>stack_max_size!#7DPMmapSimB!sj1_val!vO%I!#\L?!#NuP!#Tx+;!#Tx$_clob!t68!x`%5!#SI#!t4RDRef_code_d9dac_da94c7W_da32!#McV!sv9F!svrE!sv;!{IH7!~$$pc!~bQ2Fs2Fs!$5}P;!$&Q#Stream00!#K\Z3H!#^H&!sh]hi!shc!{J5!$A350!#e6@1I!#4Y<!#j|6!#h',;!#ZC$!u%$!$@:>bool!tU>!sF%1!#50H5!#5058ZifyInst7Inj_Z_Z!v-=!$6o+0!t>I1C6!#:-ISys6Kernel4Fork@PID_MAX_ENVELOPE!uvB2!#;?N8valid_sp!s[O9!s[%brk!s\O:!s\%!$,?N!s]-!$,@#!{FO3Amb6amb_of!#;7&!~<O9P!$5k&!#9{R;fs_seed_tmp!}H[?ref_s!s2%_sec!}T'!tVI;StackLayout9EntryDraw!$D5R!ux-!s`R8NetQue!~V%!s_O6VaSize!#6L\6me_!$0tX!#BY+rd!#M__>rdn!#NP$above!#BK;!#JD25!t=Y6in!#Oab;!t|%t!sn-!#v$X8!#oK&!tVY<!tV'data!uG_=!wI+!sp,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk14prod37Corelib4Init5Logicm72eqk14Nonek13nilk16option3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypep67Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticst5dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhhc5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehl15Modelhl18m_haltedhl19m_vm_lazy69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hq1dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~hu94TSethu98realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3libaStartupTac~~~~~~ij83bwd46Stdlib6ZArith6BinInt1Zinc2lehfbbv_unsigned01Zinc6modulo69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~ir5floaded_segments69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~ivecmkProcInputCinc2ltm71Im73and3h5LinuxProcessSemanticsfLinuxProcessSem2Fsjl42Fshhcbinit_confighhch1segments_reservedhl1bInputStreamhl1ainit_modelhl18with_tid3h5LinuxProcessSemantics5Riscv7Preludejt35bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~kg23fx0kg24mkstkg27seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefStartup~~~~~~kl7amain_entryir57init_pcir55phdrsinc3powhf2BVhf4BvWfhl17in_argvhl17in_envphhcavalid_argvhhc9valid_brkhhcavalid_envphhc8valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutlh49EntryDrawhl19ProcInputive6amb_ofkg23rdnk13native7a_hwcapive5a_uidkg28wrap_meminc3addinc6of_natm73nothl1estack_max_sizeinc3subk14boolk14truet58store_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs~~~~~~lu26D_main" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

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
              (Z_to_bv 64 0xd9ec0) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x12b948)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0xd9ec8)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xda0bc)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xda00c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xf1210)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xda00c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xf1210)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (rnd : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xda0cc;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x10b6b8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x473d0;
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
  Variable rnd : ltac2:(zQ "10!lk8$0").
  Hypothesis Hva : ltac2:(zQ "10!ktf@1$0?4argv").
  Hypothesis Hve : ltac2:(zQ "10!kva@1$0?4envp").
  Hypothesis Hvsp : ltac2:(zQ "10!lg8@1$0?2sp").

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

  Theorem ref_startup_sec : ltac2:(zQ "he0!h9!jc!iub!jj4!ht8!iic!jk4!ipa!od!jka!jke!iq8!jnf!jo5!hk8!jp4!jqa!jr9!js7!jv9!kjd!kk4!kkc!kp4!ii4!kq2!kqd!kr6!krd!ks2>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3lim$b>3fs0$c>6stdin0$h0>1K$h8>0>3tid@1$1@1$0#k0>4regs@2$h3@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@2$a@2$6Z@2$7@1$0#k0^3@2$6@2$7@1$0#k0^3@2$hb+2+h6>0@8$h7?3AMB?2sp?4argv?4envp?3rnd^4^3^2@4$5$2$4@2$e@5$h5$h4^4Kd@3$hc@1$0#k0+knjt0Kv$9@2$hd@1$0#k0+knjt0@1$1@1$0#k0^3@1$h6$2@2$h2^5@6$h1@1$f$2^b^a?2sp^9@5$3?3AMB?4argv?4envp^8^7^6@4$5$2$4@9$d$2$h9$ha?2sp^7^6?3rnd^5@5$3?3AMB?4argv?4envp^4^3^2").
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
    replace (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) with (0x47284 : word) by (apply bv_eq; reflexivity).
    rewrite cmem_init. fold (regs_init sp).
    destruct (p1_run sp argv envp a_uid a_hwcap rnd Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    assert (A1' : getr regs1 1 = (0xd9ddc : word)) by (rewrite A1; apply bv_eq; reflexivity).
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp a_uid a_hwcap rnd) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0xd9ddc : word) A1')
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
    eapply (rz_set_tid SEGS regs4 (0xda32c : word) _ (seg_rom SEGS) model K W_da32c F_da32c E_da32c);
      [exact Hh | exact Hlazy | assumption | exact Ht0 |].
    intros tid Htid'.
    assert (Htid : (0 < bv_unsigned tid < 2^22)%Z) by (unfold Fork.PID_MAX_ENVELOPE in Htid'; exact Htid').
    replace (v_addi (0xda32c : word) 4) with (0xda330 : word) by (apply bv_eq; reflexivity).
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
Theorem ref_startup : ltac2:(zQ "i40!h9!jc!iub!ks9!kt4!ht8!iic!jk4!ipa!od!jka!jke!iq8!jo5!hk8!jp4!ktf!kud!kva!lg8!lk8!ll5!jr9!js7!jv9!lm2!kjd!kk4!kkc!kp4!ii4!kq2!kqd!kr6!krd!ks2>2sp@1$1@1$0#k0>3brk@1$1@1$0#k0>5mbase@1$1@1$0#k0>3rnd$h4>3lim$c>3inp$h5>1K$he>0@1$h3^7>0@2$h1$2^7>0@1$h0@1$3^4>0@1$h2@1$4^5>0>3tid@1$1@1$0#k0>4regs@2$h8@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$9@1$1@1$0#8>0@2$b@2$7Z@2$8@1$0#k0^3@2$7@2$8@1$0#k0^3@2$i1+2+h6>0@8$hd@1$h9^a^f@1$3^a@1$4^a^c^4^3^2@4$6$2$5@2$e@5$hb$ha^4Kd@3$i2@1$0#k0+knjt0Kv$a@2$i3@1$0#k0+knjt0@1$1@1$0#k0^3@1$hc$2@2$h7^5@6$h6@1$f$2^f^e^h0^c^b^a@4$6$2$5@9$d$2$hf$i0^c^b^a^9^8^7^6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["FPX2"] "##8}p'0h01Kh13memh24regsh33tidh42HKh54Hbrkh63Hsph73Hvah83Hveh96abtermh:4argvh;3brkh<4envph=3fs0h>3gidh?6groupsh@5hwcaphA3inphB3limhC5mbasehD3nethE6nofilehF3rndhG7sigmaskhH2sphI6stdin0hJ3tmphK3uidhL4urndhM4vaszi00Ain_abort_terminali017in_argvi027in_envpi036in_gidi049in_!ts%i058in_!tw$i06;in_image_fsi076in_neti089in_!tz%i09:in_!tx&i0:8in_!tw$i0;6in_tmpi0<6in_uidi0=:in_urandomi0>:in_va_sizei0?1pp;1p;2p;8p;3p;5p;6p;?p;4p;9g001Zj10Tg002?j19!s/$]j1?Tg02VAj1ATg02W6j2CTg00VDj14!s8$lj1@Tg00W:j13Tg02Xcj1=Tg00D[j11Tg0000j2HTg003@j1FTg00B<j2ETg00HOj2DTg00CBj18!s8$2j2Q!se$@j2PTg02YZj17!sA$kj8BTg00JYj3OTg00K<j1NTg021Dj5KTg00L@j1JTg00NBj6>Tg00O;j2:Tg008Pj2;Tg001:j16Tg02ZXl?2Tg02[Rj2ITg02\Ll?GTg009Ej4LTg020Ll9MTg02;GR0g00A6f1R1f0R2CLp=5P0g02IMg02=jf5R3f4R4f3R5f2R6P1P2M9Mp=<g00?J#0R7#0#0R8#0!s$$9R9#?R:g02]Zg00G6g02^ZR;P;g00>IR;f7R<#A1C0<%45#@%34#=%17R=#9/H:R>%98#?R?#F\:R@g00GT1E96RA'D%87%1=#0#8'Q,DA'PRAf9R=#7f?R7%4=%3=f<RBP5P6P1GBg02<NP5%18#1#1!tk$1!s$&0!s6&0#0#8g02=N5O9P6%N0DKR9%J0R8P7f>RCf@RDPBf:REE>,:4';/5=[[]1]2^3:PBf;RFPEP=f8RGf6RHE</53[[[[[]0P2%6?#6R?g02JLRIg02K:RJ%6:g02_Tg02QAg02`MfTRK!v/$KfARKPDP7PCf=R0PBP!t'$PGP<PHP3P4P5M?2#4#@fBRLP!sQ&P!sO6M?2#3#=fGRMfFRNfEROfDRPfCRQP!s_6M?2RR#7f\RS%4R%3RfYRR!ve'P8PSf[f]PRfHPMPNPOPPP!sm6M?2!vB$,;9/5=[\A^1@^2>^3:!sV9!t~'M?2R7#7PRPPPQfVRQP6P1P4fXRPfWRDfUR>1ILHPKP3P2M?G!sO$DPQP>P7!w6$eW4W8W7W5W6X0;XJIXLJWMW9X@:XG:XE:WDW?X>:XK:WIW=X<?W:!vU9!ui%P2O?n0110?0001?110110210610:10<10310410710810910510010>10=10;WAWBWFXC:X;:WHo"). Qed.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable rnd : ltac2:(zQ "10!lk8$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!jv9!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!h9!jc!od>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis ME : ltac2:(zQ "10!kp4@8$0?3AMB?3sp0?2av?2ev?3rnd?3tid?4regs?3mem").

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : ltac2:(zQ "h10!h9!ipa!l9!lmc!ip4!jc!ln3!od!nb!sb!ln9!lo4!lod!kqd!lp9!lq0!kr6>4segs@1$2$9>1a@1$5@1$0#k0>1n$6>0@2$4@2$1@1$0#k0?3sp0@2$1@1$0#k0^2>0@2$4@2$e@2$1@1$0#k0^3@1$f^2@2$h0+2+k0@3$8@1$7@1$2@1$5@1$0#8@4$3^5?3mem^4^3@4$3^5@7$c$d?3sp0?2av?2ev@1$b?3AMB@1$a?3AMB?3rnd^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##4Op'0h01Hh13s1vh21Jh32MEh42HJh52Hah62Hnh72_Hh81ah91eh:3memh;1nh<4segsi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001:j19Tg001Zj14Tg002?j1>!s/$]j1:Tg00B<j27!s/$fj2?Tg01@nj1ETg00oDj2DTg00CBj1;Tg00H2j2ATg02aDl9@Tg003@j18Tg01>kj25Tg01Y`j56Tg005;j30Tg00[cj1ITg00\`j1HTg022Ej7GTg01Zej6FTg00Zbj42Tg00D@R0j23Tg00e6R1j2=Tg02bIj41!tP$kj8<Tg02cIl9CTg000\j7BTg00<T#9g00?J#4R2#4#4R3#4!s-$4#>R5#:R6g02CXp,3sp0R7,75f1R8,75'?f2R9,75%E8'D%;2%;4'A'?p,3AMBR4P7p,2avR2p,2evR5p,3rndR:p,3tidR;p,4regsR<p,3memR=p,2MER>M9@%>3#:R3#8\6R?1578P4P7P2P5f0R@D6RA90?8P7g02=j!s?%%I4%H4RBP:FGRCP8!s<%PBP:P;EFRBC290?='3'3X16,=6RDX2?RE'=P1P?PE%93#8R3f6REP=f5RFf4RGC1PEPCPFPGC130P@P1P61579A0?9AP7PCP9P!t#1f:R9P=f9R1f8REC1P9PCP1PEC1503P@157GA0?G!sc%G!sc/P0157F!u]'P8D690?F!sN$F!sN,f>RAP=f=R9f<RHC1PA!tS$H!t-&f7RI,57!sl+G!sl$E!sl$E!sl,P0!sH+F!sH$1!sH$1!sH'fBR1P=fARFf@R0C1P1!tT$0!t4';!se+ID650?!sd$H!sd'P?!v9,R9!sQ+:P;P<P@G<fGRHP8fFRIfE!t+$HPCPI!t+&]3X:?!sZ29G<!sx$IPAPBP0fDfCP1M9CW3P=P@P>FBW0W7P8P@O2n20010!s#$12!s/&W0W4!sD?X16!sE7!s0%X0DX2?!sF=b9W6W5W;W8W<o"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : ltac2:(zQ "c0!h9!ipa!jc!o0!od!jke!nb!lqa!lr0!ip4!jk4!ls2>1a@1$2@1$0#k0>0@2$5@2$9@2$b@2$1@1$0#k0?3sp0$8@2$1@1$0#k0^1@2$a@2$1@1$0#k0^1@2$1@1$0#k0?3sp0@1$7@3$6@1$4@1$2@1$0#8@1?3mem^2@1$3@1$2@1$0#8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##9?p'0h01Hh13s1vh21Jh32MEh44__x1h54__x2h64__x3h72HJh82Hah92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?1eh@3memhA1oi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001Zj14Tg002?j1C!s/$]j1@Tg00B<j28Tg00dBj2;!s8$fj2:Tg00HOj29Tg00D@R0j21Tg02aDl9MTg003@j1GTg01>kj26Tg01Y`j55Tg005;j30Tg00[cj1]Tg00\`j1VTg022Ej7UTg01Zej6RTg00Zbj42j5[Tg00e6R1j2BTg004Yj1ATg00nNj13!t\$kj8=Tg006mj1OTg001:j1NTg012;j2<Tg01KHj4L!s8$Yj1KTg0137j1H!s/$bj27Tg014hj3I!uL$[j1JTg018Mj4>Tg02dTj7FTg023nj8ETg015Kj2PTg00Q8j2Q!s8$mj2DTg016Yj3STg0178j4TTg02e8j2\Tg02f;j6ZTg000\j6Wj7X!sz$Jj7YTf1R2g02?NR3g02?mR4P4g02@MR5f0R6g02@mFYp=?g00?JR7#4R8#4#4R9#4!s$$CR:#@R;p,3sp0R<,8:R=g02AMR>';18:6R?':19?='1p,3AMBR?P<p,2avR@p,2evRAp,3rndRBp,3tidRCp,4regsRDp,3memREp,2MERFM9M%C9#@R9#GRG\;RH16<2P?P<P@PAP6D5RI90H2P<g02=j!s=%%]?%V?RJPBFURKP2!sS&JPBPCERRJC290HE'1'1X1;,B;RLX2HRM'BP1PHPMPEf3RMO1%A9R950G#3P6P1P;f2R1,6<A0H1IP<PKP1P!sq1PEf7RNO1=0G9#3P6f4RO!sW%O!sW%O!sW/P0f5RI,6<!uD+2D590H!sQ%I!sQ,PEf;RP!s},16<Nf8RQ!s^+OD550H!s]$Q!s]-0f9R0!sK+I!sK,0!sK'PEf?!s~,!sQ+N!tV$PP<PKf<!sR+!sb$f=PJC2RP!sR+BPCPDP6G=P2fD!us,]3X@H!sK2PG=PGf>RPfCRDO1A0G69#3XAGf6PDg00G6RGg02PUR9#O%N9PG1<G1P21<GMCL%KG%HGR9P3P4P4P5P!s0,G17G7R317G85IGg02>g%J7,7GR7C>,?9PGP7g02RAP3!s6$FFR3%A4P3GE1P95P6P1g02QAR9g02QaR5'Q1D61=095dg00GT=SG2CTb;b<b=X4GX5GW61;62/:11916'11;21/:M19M2'1[^4G^5G^6GP618:NP>P=PDO4b:1\<DeR=O2!wM$PPJPDD[!s2,P=EZEWW3PEP6PFFXW0W9P2P6O2n20010!s#$12!s/&W0W7!sD?X1;!sE7!s0%X0LX2H!sF=b?W8W>o"). Qed.

  Lemma main_entry_store_ok_win : ltac2:(zQ "f0!h9!ipa!ip4!ls9!l9!ln3!lt0!nb!sb!lt7!lr0!lp9!lq0!ls2!jc>4segs@1$4$8>1a@1$e@1$0#k0>1n$5>0@2$2@2$d@2$1@1$0#k0?3sp0$a@2$1@1$0#k0^2>0@2$2@2$b@2$1@1$0#k0^3@1$c^2@2$1@1$0#k0?3sp0@3$7$3@4$9^5?3mem^4^3$6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##:sp'0h01Hh14__x1h24__x2h34__x3h43s1vh51Jh62MEh77__arithh84__ffh98__varmaph:5__with;4cstrh<2HJh=3Hhih>3Hloh?2_Hh@1ahA1ehB3memhC1nhD4segsi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8p;:g001:j1FTg001Zj15Tg002?j1C!s/$]j1@Tg00B<j29Tg00dBj2=!s8$fj22Tg01@nj1;Tg00oDj2:Tg02aDl9NTg003@j1JTg01>kj26Tg01Y`j57Tg005;j30Tg00[cj1\Tg00\`j1VTg022Ej7UTg01Zej6TTg00Zbj43Tg00D@R0j21Tg00e6R1j2DTg02gCj48Tg00Hkj8BTg01JEj1QTg006mj1PTg012;j2ATg01KHj4O!s8$Yj1MTg0137j1K!s/$bj2<Tg014hj3I!t>$[j1LTg018Mj4>Tg004Yj1HTg015Kj2GTg00Q8j2R!s8$mj2STg016Yj3_Tg0178j4^Tg01?kj1]Tg024Rj3[Tg01C_l:WTg000\j7XTg023Jj7Y!s/$nj8ZTg02QAR2f0R3g02QaR430p=4f1R5g02?NR6g02?mR7P7g02@MR8P3g02@mFYp=?f3R9P6P7P7P8f2R6P5P3GZp=Eg00<T#Fg00?JR:#5R;#5#5R<#5!s$$CR=#@R>g02CXp,3sp0R?,9=R@g02AMRA'=19=5'219=6%;5':/2@p,3AMBRBP?p,2avRCp,2evRDp,3rndREp,3tidRFp,4regsRGp,3memRHp,2MERIM9N%C<#@#J\>R<16?5PBP?PCPDP3D7RJ90<5P?g02=j!s=%%\B%VBRKPEFURLP5!sS&KPEPFETRKC390<H'1'1X4>,D>RMX5<RN'DP1P<PNf6RNPHf5ROf4RPC8#4P3P1P>16?6A0<6JP?PLP6P!sn1f:PHf9R1f8RQ!sZ%16?PA0<P!sV%P!sV/P016?O!u=+5D790<O!sN$O!sN,f>RJPHf=RRf<RS!s{%f7RT,6?!sa+P!sa$Q!sa$Q!sa,P0!sH+O!sH$1!sH$1!sH'fBPHfAf@!s{&;!sT+TD750<!sS$S!sS'P!s6%RPKC3RR!sQ+EPFPGP3GBfGRSP5fFRTfER1C8#4]6XB<!sO2RGB!sm$TPJPKP1fDRKPN%QKRNg00GTRJ%;K'2RLg00G6RRg02PURG#PRF%FGRGPR1AR6P51AR9CORE%MRRD%KRRCPR1<R:RB1<R;R;5IRg02>gRO%L:,<RR:C>,?CR0%H7R7P0CE1GC8R8P3P61R241S36#4dA_RJ5C^RJb8b9b:X1RX2RW31=35/261=56/29[^1R^2R^3RP319=SRSPAP@P1O4b7b;%]?19=1'2ePNPL!uj$EPDPCPRA[RB;POP!tY&CP7PCCEP8P!t<0X3R1:!t=%:!t=4P@%;TPSPK!t:%M:WW6PHP3PIFXW0W?P5P3O2n20010!s#$12!s/&W0W<!sD?X4>!sE7!s0%X0MX5<!sF=bAW=W>WCW@WDo"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : ltac2:(zQ "a0!h9!jc!ipa!od!nb!lr0!ln9!mi3!jk4!ls2>1a@1$1@1$0#k0>0@2$8@2$2@1$0#k0^1@2$9@2$2@1$0#k0?3sp0$5@3$4@1$3@1$1@1$0#8@1?3mem^2@7$7?3sp0?2av?2ev@1$6?3AMB?3rnd?3tid^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##3Rp'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001Zj13Tg002?j1<!s/$]j1;Tg00B<j27Tg00dBj2FTg00HOj2:Tg02aDl9CTg003@j1@Tg01>kj25Tg01Y`j54Tg005;j30Tg00[cj1>Tg00\`j1=Tg022Ej7ETg01Zej6Dj76Tg00Zbj41Tg00D@R0j22Tg00e6R1j28!tJ$kj89Tg01?kj1BTg02hCj6ATg000\j7?Tg00?J#3#3#3R2!s-%#<R3#;R4f0R5,73p,3sp0R6,73g02AM'F':p,3AMBR7P6p,2avR8p,2evR9p,3rndR:p,3tidR;p,4regsR<p,3memR=p,2MER>M9C%<2#;#@R2\4R?f1R@,56P7P6P8P9P5D4RA90?@P6g02=j!s=%%>7%=7RBP:FERCP@!sS&BP:P;EDRDC190?='2'2X14,84REX2?RF'8P1P?PFP=f3RFO1!s]/PFF6502P5P1P4f2R1,56A0?1AP6PCP1P!sz1P=f7R1!sh21!sh&f4RF!sd%F!sd%F!sd/P0f5RA!uZ/@D490?!sQ%A!sQ,P=f;RG!t22G!t2&1561f8RH!sk+FD450?!sj$H!sj-0f9R0!sK+A!sK,0!sK'P=f?R0!t520!v''!s`'1!tr$GP6PCf<!sa+!sq$f=PDC1RG!sR+:P;P<P5G9P@fD!vD:]3X9?!sX2GG9!sv$>PDfCRDfB173D%B6':eEAW3P=P5P>F?W0W6P@P5O2n20010!s#$12!s/&W0W4!sD?X1!sE8!s0%X0EX2?!sF=b8W5W7o"). Qed.

  Lemma main_entry_rdn_data : ltac2:(zQ "h00!h9!l9!lmc!jc!ipa!ln3!od!nb!sb!lr0!ln9!mi3!lp9!ip4!lq0!ls2>4segs@1$1$8>1a@1$3@1$0#k0>1n$5>0@2$d@2$c@2$4@1$0#k0^2@1$e^1@2$f@2$4@1$0#k0?3sp0$9@3$7@1$6@1$1@1$3@1$0#8@4$2^4?3mem^3^2@4$2^4@6$b?3sp0?2av?2ev@1$a?3AMB?3rnd?3tid^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStartup ()) ["Consumers"] "##4Hp'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memh:1nh;4segsi001xp;1p;2p;9p;5p;3p;7p;6p;4p;8g001:j1@Tg001Zj14Tg002?j1=!s/$]j19Tg00B<j27Tg01@nj1<Tg00oDj2;Tg00dBj2D!sJ$fj2>Tg02aDl9ATg003@j18Tg01>kj25Tg01Y`j56Tg005;j30Tg00[cj1ITg00\`j1HTg022Ej7GTg01Zej6FTg00Zbj43Tg00D@R0j22Tg00e6R1j2:Tg02bIj41Tg00Hkj8?Tg01?kj1CTg02iLj8ETg000\j7BTg00<T#@g00?J#4#4#4R2!s-%#=R3#9R4g02CXf1R5,73f0R6#<';p,3sp0R7,73g02AM'D'>p,3AMBR8P7p,2avR9p,2evR:p,3rndR;p,3tidR<p,4regsR=p,3memR>p,2MER?M9A%=2#9R2#8\4R@1575P8P7P9P:P6D6RA90@5P7g02=j!s=%%I8%H8RBP;FGRCP5!sS&BP;P<EFRBC390@>'2'2X14,:4RDX2@RE':P1P@PE%@2#8R2f5REP>f4RFf3RGC1PEPBPFPGC130P6P1P4f2R1,57A0@1AP7PCP1P!t&1f9R1P>f8RGf7RHC1P1PBPGPHC1502P6157FA0@F!sc%F!sc/P0157E!u^+5D690@E!sN$E!sN,f=RAP>f<RIf;RJC1PAPBPIPJ!t-,H!si+F!si$G!si$G!si,P0!sH+E!sH$1!u@1fA!u9$@REf?R0!u9&EP0!t1&!sc+H!sc$J!sc$I!sc'P@!s6$APBC3RA!sR+;P<P=P6G?fFRIP5fERJfD!v>$IPBPJ!v>&]3X9@!sZ2AG?!sx$Jf>PBPHfCRBfB173H%<B';%C7'>eGEW3P>P6P?FBW0W6P5P6O2n20010!s#$12!s/&W0W4!sD?X1!sE8!s0%X0DX2@!sF=b8W5W:W7W;o"). Qed.
End Consumers.
(* [comment removed for export] *)
