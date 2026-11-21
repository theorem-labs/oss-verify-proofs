(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec ShapeAlg SpinAlg AgentLib Scfg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit
  AsanNodesIface AsanNodesAux AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanSmear
  BothImages BothPlanImages Bs_code_startx BsSmearCode SumsBothSpecs SumsBothClose.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~03acs37Corelib4Init9Datatypesk34listk33natk36option79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~n14exprk34Nonek34prod37Corelib7Numbers7BinNumss71Z06spieces74Npos35stdpp9bitvectorbdefinitionsv32bvn13envk34bool3h5LinuxProcessSemanticsfLinuxProcessSem2Fshi22Fs3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehl37Segment06atable79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~hpb8ext_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BsStartup4FPX1~~~~~~hub3XN069OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ij37StepCfghpb9emit_stmthub3XE0hpb9ext2_stmthub3XB069OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ipd4TSet37Corelib4Init5Logiciu02eqk34true05shapehpb2sdhubaholes_onlyipd4t_eq69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~ji43APH69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~jmc5LIMITjmc5SINV0jmc5argH003NX005xnodehpb6x_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~jt86BOTH_Hji45ASEGSij3dhunspell_scfgiu02ex04plank34Someiu03and03COk05check04cres07loopctx0emk_itab_ranges69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BsStartup~~~~~~kne3XB0kne3XE0kne3XN0kneaholes_only79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BsStartup7Startup~~~~~~ktd5HOLES69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lia3fx03h5LinuxProcessSemanticsfLinuxProcessSem5Statelmc5Modellmc4m_fs3h5LinuxProcessSemantics5Riscv7Preludelqb5bvmap02pchpb6cfg_ofhpb5cs_okhpbaholes_stmtipd5t_nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~mg89srealizeskneflevel_certified3h5LinuxProcessSemanticsfLinuxProcessSem3Runmm2binit_configjmc2E0jmc3inp69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~mqa7init_pc3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutmuf9EntryDrawmm28valid_spmm2avalid_argvmm2avalid_envpmm2h0entry_stack_fitslmcbInputStreamlmc8NetQueuelmc6VaSizemm29valid_brkmm28valid_idmm2bvalid_hwcaplmc5in_fsjt85hinitk33nillmc5event" s.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition XN0 : ltac2:(zQ "50!je!lb!m2!m8!r2>2id$2>4args@1$1$4>2cs$0@1$3$0") := ltac2:(zQ "50!je!r9!lb!m2!r2\2id$3\4args@1$2$4\2cs$0@1$1$0").
Definition XE0 : ltac2:(zQ "80!lb!s0!je!m2!m8!u0!u4!r2>2id$3>4args@1$0$7>2cs$2@1$4@2$1@2$1$5@1$0$6$2") := ltac2:(zQ "80!lb!s0!je!r9!m2!u0!u4!r2\2id$4\4args@1$0$7\2cs$2@1$3@2$1@2$1$5@1$0$6$2").
Definition XB0 : ltac2:(zQ "60!je!lb!m2!m8!s0!r2>2id$2>4args@1$1$5>2cs$0@1$3@2$4$0$0") := ltac2:(zQ "60!je!r9!lb!m2!s0!r2\2id$3\4args@1$2$5\2cs$0@1$1@2$4$0$0").

Lemma XN0_sound : ltac2:(zQ "e0!uc!hh0!hh5!hhb!lb!m2!m8!u0!hkd!ho8!hp3!htf!iic!ima>4SEGS@1$4$9>2SC$d>1A$a>3nx0$5>5LIMIT$7>4SINV>0$2>0>0@1$1@1$0#k0@1$6@1$1@1$0#8P>4argH>0$2>0@1$1@1$0#k0$3>3FS0$8@a$b?2fx^8^7^6^5^4$c^3^2^1").
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : ltac2:(zQ "e0!uc!hh0!hh5!hhb!lb!m2!m8!u0!hkd!ho8!hp3!in5!io2!ima>4SEGS@1$4$9>2SC$d>1A$a>3nx0$5>5LIMIT$7>4SINV>0$2>0>0@1$1@1$0#k0@1$6@1$1@1$0#8P>4argH>0$2>0@1$1@1$0#k0$3>3FS0$8@a$b?2fx^8^7^6^5^4$c^3^2^1").
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : ltac2:(zQ "e0!uc!hh0!hh5!hhb!lb!m2!m8!u0!hkd!ho8!hp3!io9!ip6!ima>4SEGS@1$4$9>2SC$d>1A$a>3nx0$5>5LIMIT$7>4SINV>0$2>0>0@1$1@1$0#k0@1$6@1$1@1$0#8P>4argH>0$2>0@1$1@1$0#k0$3>3FS0$8@a$b?2fx^8^7^6^5^4$c^3^2^1").
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Lemma sd_holes_only : ltac2:(zQ "b0!it8!m2!iv4!hkd!hh5!hhb!iva!jg1!jg8!jge!jhc>5HOLES>1x$1>2x0$4>2x1$3$0>1D$0>1E$4>2fs$3>1T$0>1s$7>0>1h$1@3$2$0@3^7^1^5^4^3>0@3$2$5@1$9^2$6@2$a@5$8^8^7^6^5^3^4").
Proof.
  intros HOLES D E fs T s HT. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; cbn [holes_only sd]; intros H; try discriminate.
  - apply andb_prop in H as [H1 H2]. intros tr. unfold t_alt2. specialize (IHa H1 tr). specialize (IHb H2 tr). tauto.
  - apply andb_prop in H as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - rewrite HT. intros tr. tauto.
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section XAll.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  (* LPS 727298f3 port: AsanInit's Section Init takes the run's launch pieces and the mmap base,
     and its lemmas are generalised over them; the argument lists below are the ones the
     the probe printed (notes/probe-boost-json__fuzz_parse.md).  Shape of
     boost-beast/http_request's lib/As/AsStartup.v [Section XAll].  [Proof using All] fixes
     this theorem's arguments to every variable below, in order. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variables argv envp : list (list byte).
  Variables (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue)
            (nofile sigmask : word) (abterm : bool) (vasz : VaSize) (urnd : InputStream) (tmp : Fs.Fs)
            (kern : KernelBuild) (execfn : list byte) (chrdr sigdfl sigterm : bool).
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc).
  #[local] Notation argH := (argH0 sp rdraw argv envp kern execfn).
  Let AH := argH0_high sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc Hsp Hva Hve Hlau.
  Let AS := argH0_sp0 sp rdraw argv envp kern execfn.
  Let AA := argH0_agree sp rdraw argv envp kern execfn.
  Let SF := SINV0_frame APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc.
  Let SA := SINV0_agree APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc.

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS ASAN_H NX0 AsanInit.LIMIT SINV argH FS0 x.
  Proof using All.
    intros [ | | | | | | | | | | | ].
    - exact (asan_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - eapply (init_x_sound_envscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_1907b8 W_1907bc W_1907c0
                ltac:(cbn [x_envscan x_envscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_1907b8) (fetch_lit _ _ _ _ eq_refl F_1907bc) (fetch_lit _ _ _ _ eq_refl F_1907c0)
                ltac:(repeat split; reflexivity)
                D_1907b8 D_1907bc D_1907c0
                sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc FS0 Hsp Hva Hve Hlaunch Hlau SINV (fun E M H => H) SF).
    - eapply (init_x_sound_pnscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_190874 W_190878 W_19087c W_190880 W_190884
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_190874) (fetch_lit _ _ _ _ eq_refl F_190878) (fetch_lit _ _ _ _ eq_refl F_19087c)
                (fetch_lit _ _ _ _ eq_refl F_190880) (fetch_lit _ _ _ _ eq_refl F_190884)
                ltac:(repeat split; reflexivity)
                D_190874 D_190878 D_19087c D_190880 D_190884
                sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc FS0 Hsp Hva Hve Hlau SINV (fun E M H => H) SF SA).
    - apply (init_x_sound_layout ASEGS ASAN_H sp rdraw argv envp kern execfn FS0 SINV).
    - exact (asan_node_x_sound_XIStrncpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XPopFree NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - (* [comment removed for export] *)
      intros args cs cs' E R FULL model T _ _ H. discriminate H.
    - (* [comment removed for export] *)
      exact (x_sound_smear ASEGS ASAN_H NX0 AsanInit.LIMIT SINV argH FS0 asan_wx asan_in_hull asan_hull_ok SF asan_smear_x asan_smear_fwa).
  Qed.
End XAll.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition level_certified : ltac2:(zQ "30!m2!m8!je>3KC0$0>5BFUEL$0>4FUEL$0>3HSs>0$0@1$1$2>3HSt>0$0@1$1$2P") := ltac2:(zQ "hc0!m2!je!m8!iv4!kj9!lb!s0!u0!kjf!jg1!khf!r9!kk5!hhb!iva!kkc!jq7!kl3!js2!kl8!klf!km5!kme!kh5!kra!ks1!ks8!ksf\3KC0$0\5BFUEL$0\4FUEL$0\3HSs>0$0@1$2$1\3HSt>0$0@1$2$1>1h$0>2ch$1>0@3$3@1$2$1@1^4^2@2$c$1^1@2$4@1$5@2$6$7$0\2rs@1$5@2$6$7$0@2$4$8\1p$8@2$4$9\1s$9@2$f@3$3$h4@f$h3$a@2$h6$a^3$h7$h2$h0$ha$h9$h8^7^b^a^9@1$b$h5^5^2@1$h1^1@3$3$d@1$hb^1$e").
End FPX2.

Section Startup.
  Let fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState := OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Local Existing Instance fx.
  (* LPS 727298f3 port: restated over AsanInit's Section Init at the revision (probe-read argument
     lists, notes/probe-boost-json__fuzz_parse.md); [init_cs_ok] takes the mmap base fact and the
     two launch facts.  Shape of boost-beast/http_request's lib/As/AsStartup.v [Section Startup]. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variables argv envp : list (list byte).
  Variables (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue)
            (nofile sigmask : word) (abterm : bool) (vasz : VaSize) (urnd : InputStream) (tmp : Fs.Fs)
            (kern : KernelBuild) (execfn : list byte) (chrdr sigdfl sigterm : bool).
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* LPS 727298f3: the launch's channel reader, fed to [init_cs_ok] ([cs_ok]'s [co_rdr]) *)
  Hypothesis Hrdr : in_channel_reader INP = true.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc).
  #[local] Notation argH := (argH0 sp rdraw argv envp kern execfn).
  #[local] Notation E0a := (E0 sp rdraw brk0 argv envp uid gid hw kern execfn).
  #[local] Notation LIM := AsanInit.LIMIT.
  Variable fsr : Fs.Fs.
  Hypothesis Hfsr : in_fs INP = fsr.
  Variable RANGES : ltac2:(zQ "40!lb!m2!s0!u0@1$0@2$2$3$1").          (* [comment removed for export] *)
  Variables HS1 HSC HSA HSF : nat -> option acs.
  Variable plan1 : ltac2:(zQ "10!kjf$0").
  Variable shape1 : ltac2:(zQ "10!jg1$0").
  Variables KC0 BFUEL FUEL : nat.
  #[local] Notation IT := (mk_itab_ranges ASEGS RANGES).
  Hypothesis cert1 : check ASEGS IT ASAN_H NX0 LIM XN0 XE0 XB0 HS1 KC0 BFUEL FUEL None (hinit (rseq_z (kb_rseq kern))) plan1 = COk shape1.
  Hypothesis shape1_holes : ltac2:(zQ "40!hhb!iva!iv4!ksf@3$2$0@1$3?6shape1$1").
  #[local] Notation LEVEL := (level_certified KC0 BFUEL FUEL).
  Hypothesis cert2 : ltac2:(zQ "10!mkf@5$0?3KC0?5BFUEL?4FUEL?3HS1?3HSC").
  Hypothesis cert3 : ltac2:(zQ "10!mkf@5$0?3KC0?5BFUEL?4FUEL?3HSC?3HSA").
  Hypothesis cert4 : ltac2:(zQ "10!mkf@5$0?3KC0?5BFUEL?4FUEL?3HSA?3HSF").
  Variable T : ltac2:(zQ "10!it8$0").
  Hypothesis T_nil : ltac2:(zQ "20!nsc!nt2@1?1T@1$0$1").
  Definition HOLES : ltac2:(zQ "40!m2!hkd!hh5!it8>1h$0>1E$2>4fsr'$1$3") := ltac2:(zQ "30!m2!hkd!hh5\1h$0\1E$2\4fsr'$1?1T").
  Hypothesis HOLESF_sound : holes_stmt ASEGS ASAN_H LIM HSF SINV argH HOLES fsr.

  Let AH := argH0_high sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc Hsp Hva Hve Hlau.
  Let AS := argH0_sp0 sp rdraw argv envp kern execfn.
  Let AA := argH0_agree sp rdraw argv envp kern execfn.
  Let SF := SINV0_frame APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc.
  Let SA := SINV0_agree APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc.
  Let SP := SINV0_pg APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc Hsp Hva Hve Hlau SINV (fun E M H => H).

  Lemma asan_check_sound : forall RS HS,
    holes_stmt ASEGS ASAN_H LIM HS SINV argH HOLES fsr ->
    forall fuel bfuel p cs s,
      check ASEGS (mk_itab_ranges ASEGS RS) ASAN_H NX0 LIM XN0 XE0 XB0 HS KC0 bfuel fuel None cs p = COk s ->
      forall E R FULL model, cs_ok ASEGS ASAN_H LIM SINV argH fsr E cs R FULL model ->
        srealizes ASEGS (cfg_of ASEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
  Proof.
    intros RS HS HS_sound fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound ASEGS (mk_itab_ranges ASEGS RS) (itab_ranges_ok RS) ASAN_H NX0 LIM HS XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH E_SP0 AA SF SA
              HOLES (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => T_nil) (fun _ _ _ _ => eq_refl) fsr KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_H NX0 LIM SINV argH fsr asan_res_len asan_hull_ok asan_shadow_ok AA SF SA AS E_SP0)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_hull_ok asan_shadow_ok AH SF asan_res_len asan_res_cover AS)
              (node_mmap1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_hull asan_res_cover asan_hull_ok asan_shadow_ok AH AS E_SP0 AA SF SA SP)
              (node_mmapin1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_cover asan_hull_ok asan_shadow_ok AH AS SF)
              (node_mprotect1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_cover asan_hull_ok asan_shadow_ok AH AS SF)
              (node_mmapgaps_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_cover asan_hull_ok asan_shadow_ok AH AS E_SP0 AA SF SA SP)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_H LIM SINV argH fsr)
              (asan_node_x_sound_all sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm fsr Hsp Hva Hve Hfit Hlaunch Hlau)
              (node_join_sound ASEGS ASAN_H NX0 LIM SINV argH fsr)
              (XN0_sound _ _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HS_sound
              (* LPS 727298f3 port: [check_sound] takes the fill/zero-node soundness (probe: asan_node_fillfz_sound). *)
              (asan_node_fillfz_sound NX0 LIM SINV argH AH E_SP0 AA SF SA fsr)
              fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
  Qed.

  Lemma level_sound : forall HSs HSt, level_certified KC0 BFUEL FUEL HSs HSt ->
    holes_stmt ASEGS ASAN_H LIM HSt SINV argH HOLES fsr -> holes_stmt ASEGS ASAN_H LIM HSs SINV argH HOLES fsr.
  Proof.
    intros HSs HSt CERT HSt_sound h ch Hh E R FULL model HC. ndestruct (CERT h ch Hh) as (rs & p & s & Hc & Hho). unfold HOLES.
    eapply srz_conseq; [exact (asan_check_sound rs HSt HSt_sound FUEL BFUEL p ch s Hc E R FULL model HC)|].
    apply sd_holes_only; [intros; reflexivity | exact Hho].
  Qed.

  Lemma HOLESA_sound : holes_stmt ASEGS ASAN_H LIM HSA SINV argH HOLES fsr.
  Proof. exact (level_sound HSA HSF cert4 HOLESF_sound). Qed.
  Lemma HOLESC_sound : holes_stmt ASEGS ASAN_H LIM HSC SINV argH HOLES fsr.
  Proof. exact (level_sound HSC HSA cert3 HOLESA_sound). Qed.
  Lemma HOLES1_sound : holes_stmt ASEGS ASAN_H LIM HS1 SINV argH HOLES fsr.
  Proof. exact (level_sound HS1 HSC cert2 HOLESC_sound). Qed.

  Theorem as_startup_shape :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM INP) (sd HOLES t_nil E0a fsr shape1).
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS ASAN_H APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS ASAN_H APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm AsanUbsan.M.init_pc
                  IMG Hsp Hbrk Hmb Hva Hve Huid Hhw eq_refl Hlaunch Hlau Hrdr) as HC.
    rewrite Hfsr in HC.
    pose proof (asan_check_sound RANGES HS1 HOLES1_sound FUEL BFUEL plan1 (hinit (rseq_z (kb_rseq kern))) shape1 cert1 _ _ _ _ HC) as R.
    replace (m_fs (model0 ASEGS sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp kern execfn chrdr sigdfl sigterm)) with fsr in R by (symmetry; exact Hfsr).
    exact R.
  Qed.

  Theorem as_startup_T :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM INP) T.
  Proof using All.
    eapply srz_conseq; [exact as_startup_shape|]. apply sd_holes_only; [intros; reflexivity | exact shape1_holes].
  Qed.
End Startup.
