(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec ShapeAlg SpinAlg AgentLib Scfg AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums AsanInit
  AsanNodesIface AsanNodesAux AsanNodesMmA AsanNodesMmB AsanNodesStartX AsanNodesStartXInit AsanPopFree AsanSmear
  AsImages AsPlanImages As_code_startx AsSmearCode SumsAsanSpecs SumsAsanClose.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~03acs37Corelib4Init9Datatypesk34listk33natk36option79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~n14exprk34Nonek34prod37Corelib7Numbers7BinNumss71Z06spieces74Npos35stdpp9bitvectorbdefinitionsv32bvn13envk34bool3h5LinuxProcessSemanticsfLinuxProcessSem2Fshi22Fs3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehl37Segment79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsStartup4FPX1~~~~~~hp33XN006atable79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~hu38ext_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ij37StepCfghp33XE0hu39emit_stmthp33XB0hu39ext2_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ipd4TSet37Corelib4Init5Logiciu02eqk34truehp3aholes_only05shapehu32sdipd4t_eq69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~ji43APH69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~jma6ASAN_Hji45ASEGS69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~jr85LIMITjr85SINV0jr85argH003NX005xnodehu36x_stmtij3dhunspell_scfgiu02ex04plank34Someiu03and69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsStartup~~~~~~kkf3XB0kkf3XE0kkf3XN0kkfaholes_only03COk05check04cres07loopctx0emk_itab_ranges79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsStartup7Startup~~~~~~kt95HOLES69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~li63fx03h5LinuxProcessSemanticsfLinuxProcessSem5Statelm85Modellm84m_fs3h5LinuxProcessSemantics5Riscv7Preludelq75bvmap02pchu36cfg_ofhu35cs_okhu3aholes_stmtipd5t_nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~mg49srealizeskkfflevel_certified3h5LinuxProcessSemanticsfLinuxProcessSem3Runmlebinit_configjr82E0jr83inp69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~mq67init_pc3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutmu69EntryDrawmle8valid_spmleavalid_argvmleavalid_envpmleh0entry_stack_fitslm8bInputStreamlm88NetQueuelm86VaSizemle9valid_brkmle8valid_idmlebvalid_hwcaplm85in_fsjma5hinitk33nillm85event" s.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition XN0 : ltac2:(zQ "50!je!lb!m2!m8!r2>2id$2>4args@1$1$4>2cs$0@1$3$0") := ltac2:(zQ "50!je!r9!lb!m2!r2\2id$3\4args@1$2$4\2cs$0@1$1$0").
Definition XE0 : ltac2:(zQ "80!lb!s0!je!m2!m8!u0!u4!r2>2id$3>4args@1$0$7>2cs$2@1$4@2$1@2$1$5@1$0$6$2") := ltac2:(zQ "80!lb!s0!je!r9!m2!u0!u4!r2\2id$4\4args@1$0$7\2cs$2@1$3@2$1@2$1$5@1$0$6$2").
Definition XB0 : ltac2:(zQ "60!je!lb!m2!m8!s0!r2>2id$2>4args@1$1$5>2cs$0@1$3@2$4$0$0") := ltac2:(zQ "60!je!r9!lb!m2!s0!r2\2id$3\4args@1$2$5\2cs$0@1$1@2$4$0$0").

Lemma XN0_sound : ltac2:(zQ "e0!uc!hh0!hh5!hhb!lb!m2!m8!u0!hkd!ho8!ht4!htb!ii7!ima>4SEGS@1$4$9>2SC$d>1A$b>3nx0$5>5LIMIT$7>4SINV>0$2>0>0@1$1@1$0#k0@1$6@1$1@1$0#8P>4argH>0$2>0@1$1@1$0#k0$3>3FS0$8@a$c?2fx^8^7^6^5^4$a^3^2^1").
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : ltac2:(zQ "e0!uc!hh0!hh5!hhb!lb!m2!m8!u0!hkd!ho8!in5!htb!inc!ima>4SEGS@1$4$9>2SC$d>1A$b>3nx0$5>5LIMIT$7>4SINV>0$2>0>0@1$1@1$0#k0@1$6@1$1@1$0#8P>4argH>0$2>0@1$1@1$0#k0$3>3FS0$8@a$c?2fx^8^7^6^5^4$a^3^2^1").
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : ltac2:(zQ "e0!uc!hh0!hh5!hhb!lb!m2!m8!u0!hkd!ho8!io9!htb!ip0!ima>4SEGS@1$4$9>2SC$d>1A$b>3nx0$5>5LIMIT$7>4SINV>0$2>0>0@1$1@1$0#k0@1$6@1$1@1$0#8P>4argH>0$2>0@1$1@1$0#k0$3>3FS0$8@a$c?2fx^8^7^6^5^4$a^3^2^1").
Proof. intros ? ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b | SAlt2 a b => holes_only a && holes_only b
  | _ => false
  end.

Lemma sd_holes_only : ltac2:(zQ "b0!it8!m2!iv4!hkd!hh5!hhb!iva!jg1!jgf!jh6!jhc>5HOLES>1x$1>2x0$4>2x1$3$0>1D$0>1E$4>2fs$3>1T$0>1s$8>0>1h$1@3$2$0@3^7^1^5^4^3>0@3$2$5@1$7^2$6@2$a@5$9^8^7^6^5^3^4").
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
  Variable sp : word.
  Variable rdraw : ltac2:(zQ "10!nha$0").
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable FS0 : ltac2:(zQ "10!hkd$0").
  Hypothesis Hsp : ltac2:(zQ "10!ni7@1$0?2sp").
  Hypothesis Hva : ltac2:(zQ "10!nj3@1$0?4argv").
  Hypothesis Hve : ltac2:(zQ "10!nk1@1$0?4envp").
  Variables uid hw : word.
  Hypothesis Hfit : ltac2:(zQ "10!nkf@3$0?2sp?4argv?4envp").
  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AS := argH0_sp0 APH sp rdraw argv envp uid hw.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  (* [comment removed for export] *)
  Theorem asan_node_x_sound_all : ltac2:(zQ "a0!jm3!jq5!jqf!jv3!jvc!kg5!kge!kh3!kha!ki4>1x$7@a$8?2fx$2$9$1$6$3@8$4$0?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw@7$5$0?2sp?5rdraw?4argv?4envp?3uid?2hw?3FS0^1").
  Proof.
    intros [ | | | | | | | | | | | ].
    - exact (asan_node_x_sound_XIMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XIMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemset NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemcpy NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - exact (asan_node_x_sound_XMemIsZero NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA FS0).
    - eapply (init_x_sound_envscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_193a40 W_193a44 W_193a48
                ltac:(cbn [x_envscan x_envscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_193a40) (fetch_lit _ _ _ _ eq_refl F_193a44) (fetch_lit _ _ _ _ eq_refl F_193a48)
                ltac:(repeat split; reflexivity)
                D_193a40 D_193a44 D_193a48
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF).
    - eapply (init_x_sound_pnscan ASEGS ASAN_H APH asan_wx asan_in_hull asan_hull_ok
                W_193afc W_193b00 W_193b04 W_193b08 W_193b0c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_H]; lia)
                (fetch_lit _ _ _ _ eq_refl F_193afc) (fetch_lit _ _ _ _ eq_refl F_193b00) (fetch_lit _ _ _ _ eq_refl F_193b04)
                (fetch_lit _ _ _ _ eq_refl F_193b08) (fetch_lit _ _ _ _ eq_refl F_193b0c)
                ltac:(repeat split; reflexivity)
                D_193afc D_193b00 D_193b04 D_193b08 D_193b0c
                sp rdraw brk0 argv envp FS0 Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF SA).
    - apply (init_x_sound_layout ASEGS ASAN_H APH sp rdraw argv envp FS0 uid hw SINV).
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
Definition level_certified : ltac2:(zQ "30!m2!m8!je>3KC0$0>5BFUEL$0>4FUEL$0>3HSs>0$0@1$1$2>3HSt>0$0@1$1$2P") := ltac2:(zQ "hc0!m2!je!m8!iv4!kj5!lb!s0!u0!jqf!kjb!jgf!r9!kk1!hhb!iva!kk8!jq5!kob!kp2!kp9!kq0!jv3!kqe!kge!kr3!kra!ks0!ks9\3KC0$0\5BFUEL$0\4FUEL$0\3HSs>0$0@1$2$1\3HSt>0$0@1$2$1>1h$0>2ch$1>0@3$3@1$2$1@1^4^2@2$c$1^1@2$4@1$5@2$6$7$0\2rs@1$5@2$6$7$0@2$4$9\1p$9@2$4$a\1s$a@2$f@3$3$h9@f$h8$8@2$hb$8^3$h0$h7$h5$h3$h2$h1^7^b^a^9@1$b$ha^5^2@1$h6^1@3$3$d@1$h4^1$e").
End FPX2.

Section Startup.
  (* [comment removed for export] *)
  Let fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState := OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Local Existing Instance fx.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : ltac2:(zQ "10!nha$0").
  Variables brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : ltac2:(zQ "10!hkd$0").
  Variable stdin : ltac2:(zQ "10!nm4$0").
  Variables uid gid hw : word.
  Variable groups : ltac2:(zQ "30!lb!uc!hh0@1$0@1$2@1$1#k0").
  Variable net : ltac2:(zQ "10!nn3$0").
  Variables nofile sigmask : word.
  Variable abterm : bool.
  Variable vasz : ltac2:(zQ "10!nnf$0").
  Variables (urnd : InputStream) (tmp : Fs.Fs).   (* [comment removed for export] *)
  Hypothesis Hsp : ltac2:(zQ "10!ni7@1$0?2sp").
  Hypothesis Hbrk : ltac2:(zQ "20!no9!jqf@2$0$1?4brk0").
  Hypothesis Hva : ltac2:(zQ "10!nj3@1$0?4argv").
  Hypothesis Hve : ltac2:(zQ "10!nk1@1$0?4envp").
  Hypothesis Hfit : ltac2:(zQ "10!nkf@3$0?2sp?4argv?4envp").
  Hypothesis Huid : ltac2:(zQ "10!np6@1$0?3uid").
  Hypothesis Hhw : ltac2:(zQ "10!nq2@1$0?2hw").

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation LIM := AsanInit.LIMIT.
  #[local] Notation INP := (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp).
  (* [comment removed for export] *)
  Variable fsr : ltac2:(zQ "10!hkd$0").
  Hypothesis Hfsr : ltac2:(zQ "40!iv4!hkd!nr1!mpf@3$0$1@1$2@f$3?4argv?4envp?2fs?5stdin?3uid?3gid?2hw?6groups?3net?6nofile?7sigmask?6abterm?4vasz?4urnd?3tmp?3fsr").

  (* [comment removed for export] *)
  Variable RANGES : ltac2:(zQ "40!lb!m2!s0!u0@1$0@2$2$3$1").          (* [comment removed for export] *)
  Variables HS1 HSC HSA HSF : nat -> option acs.
  Variable plan1 : ltac2:(zQ "10!kjb$0").
  Variable shape1 : ltac2:(zQ "10!jgf$0").
  Variables KC0 BFUEL FUEL : nat.
  #[local] Notation IT := (mk_itab_ranges ASEGS RANGES).
  Hypothesis cert1 : ltac2:(zQ "f0!jqf!r9!iv4!jq5!nra!kob!kp2!kp9!jv3!kqe!kge!kr3!kra!ks0!ks9@3$2$c@f$b$0@2$e$0?6RANGES$3$a$8$7$6$5?3HS1?3KC0?5BFUEL?4FUEL@1$1$d$4?5plan1@1$9?6shape1").
  Hypothesis shape1_holes : ltac2:(zQ "40!hhb!iva!iv4!kq0@3$2$0@1$3?6shape1$1").
  #[local] Notation LEVEL := (level_certified KC0 BFUEL FUEL).
  Hypothesis cert2 : ltac2:(zQ "10!mkb@5$0?3KC0?5BFUEL?4FUEL?3HS1?3HSC").
  Hypothesis cert3 : ltac2:(zQ "10!mkb@5$0?3KC0?5BFUEL?4FUEL?3HSC?3HSA").
  Hypothesis cert4 : ltac2:(zQ "10!mkb@5$0?3KC0?5BFUEL?4FUEL?3HSA?3HSF").

  (* [comment removed for export] *)
  Variable T : ltac2:(zQ "10!it8$0").
  Hypothesis T_nil : ltac2:(zQ "20!ns3!ns9@1?1T@1$0$1").
  Definition HOLES : ltac2:(zQ "40!m2!hkd!hh5!it8>1h$0>1E$2>4fsr'$1$3") := ltac2:(zQ "30!m2!hkd!hh5\1h$0\1E$2\4fsr'$1?1T").
  Hypothesis HOLESF_sound : ltac2:(zQ "a0!jm3!jq5!jqf!lhd!jv3!jvc!kg5!lud!lm1!ki4@a$7$8$2$9$1$4?3HSF@8$5$0?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw@7$6$0?2sp?5rdraw?4argv?4envp?3uid?2hw$3?3fsr").

  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AS := argH0_sp0 APH sp rdraw argv envp uid hw.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.
  (* [comment removed for export] *)
  Let SP := SINV0_pg APH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV (fun E M H => H).

  (* [comment removed for export] *)
  Lemma asan_check_sound : ltac2:(zQ "i92!jqf!m2!uc!jm3!jq5!jv3!hh0!m8!lhd!jvc!kg5!je!lm1!ki4!r9!lb!s0!iv4!u0!lp6!lpf!lsd!kob!kp2!kp9!kqe!kge!kr3!kra!ks0!ks9!lt6!kjb!jgf!lta!lu4!lud!jh6!hh5!lvb!mje&@8$9$3?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw&@7$a$3?2sp?5rdraw?4argv?4envp?3uid?2hw>2RS@1$f@2$h0$h2$1>2HS>0$1@1$7$b>0@a$i4$c$0$d$4$5^1~0~1$8?3fsr>4fuel$1>5bfuel$1>1p$i0>2cs$b>1s$i1>0@3$h1$hc@f$hb$0@2$he$0^8$4$ha$5$h8$h7$h6^7?3KC0^4^5@1$e$hd^2^3@1$h9^1>1E$i6>1R@2$h5@1$2#5@1$6@1$2#k0>4FULL>0@1$6@1$2#k0@1$7@1$6@1$2#8>5model$h3>0@b$i3$0$4$5~0~1?3fsr^4^7^3^2^1@4$i8$0$d@6$i2$c$0^4@1$hf^8^3^2@5$i5$8$i7^5@1$h4^2^7").
  Proof.
    intros RS HS HS_sound fuel bfuel p cs s Hc E R FULL model HC.
    exact (check_sound ASEGS (mk_itab_ranges ASEGS RS) (itab_ranges_ok RS) ASAN_H NX0 LIM HS XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH E_SP0 AA SF SA
              HOLES (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => T_nil) (fun _ _ _ _ => eq_refl) fsr KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_H NX0 LIM SINV argH fsr asan_res_len asan_hull_ok asan_shadow_ok AA SF SA AS E_SP0)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_hull_ok asan_shadow_ok AH SF asan_res_len asan_res_cover AS)
              (node_mmap1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_hull asan_res_cover asan_hull_ok asan_shadow_ok AH AS E_SP0 AA SF SA SP)
              (node_mmapin1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_hull asan_res_cover asan_hull_ok asan_shadow_ok AH AS SF)
              (node_mprotect1_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_hull asan_res_cover asan_hull_ok asan_shadow_ok AH AS SF)
              (node_mmapgaps_sound_OBL ASEGS ASAN_H NX0 LIM SINV argH fsr asan_in_hull asan_res_len asan_res_cover asan_hull_ok asan_shadow_ok AH AS E_SP0 AA SF SA SP)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_H LIM SINV argH fsr)
              (asan_node_x_sound_all sp rdraw brk0 argv envp fsr Hsp Hva Hve uid hw Hfit)
              (node_join_sound ASEGS ASAN_H NX0 LIM SINV argH fsr)
              (XN0_sound _ _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _ _)
              HS_sound
              (asan_node_fillfz_sound NX0 AsanInit.LIMIT SINV argH AH E_SP0 AA SF SA fsr)   (* [comment removed for export] *)
              fuel bfuel None p cs s Hc E R FULL model t_nil HC I eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma level_sound : ltac2:(zQ "e2!jm3!m2!m8!jq5!jqf!lhd!jv3!jvc!kg5!je!lud!lm1!ki4!mkb&@8$7$0?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw&@7$8$0?2sp?5rdraw?4argv?4envp?3uid?2hw>3HSs>0$1@1$2$9>3HSt>0$1@1$2$9>0@5$d?3KC0?5BFUEL?4FUEL^2^1>0@a$a$b$4$c$3$6^2~0~1$5?3fsr@a$a$b$4$c$3$6^4~0~1$5?3fsr").
  Proof.
    intros HSs HSt CERT HSt_sound h ch Hh E R FULL model HC. ndestruct (CERT h ch Hh) as (rs & p & s & Hc & Hho). unfold HOLES.
    eapply srz_conseq; [exact (asan_check_sound rs HSt HSt_sound FUEL BFUEL p ch s Hc E R FULL model HC)|].
    apply sd_holes_only; [intros; reflexivity | exact Hho].
  Qed.

  Lemma HOLESA_sound : ltac2:(zQ "a0!jm3!jq5!jqf!lhd!jv3!jvc!kg5!lud!lm1!ki4@a$7$8$2$9$1$4?3HSA@8$5$0?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw@7$6$0?2sp?5rdraw?4argv?4envp?3uid?2hw$3?3fsr").
  Proof. exact (level_sound HSA HSF cert4 HOLESF_sound). Qed.
  Lemma HOLESC_sound : ltac2:(zQ "a0!jm3!jq5!jqf!lhd!jv3!jvc!kg5!lud!lm1!ki4@a$7$8$2$9$1$4?3HSC@8$5$0?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw@7$6$0?2sp?5rdraw?4argv?4envp?3uid?2hw$3?3fsr").
  Proof. exact (level_sound HSC HSA cert3 HOLESA_sound). Qed.
  Lemma HOLES1_sound : ltac2:(zQ "a0!jm3!jq5!jqf!lhd!jv3!jvc!kg5!lud!lm1!ki4@a$7$8$2$9$1$4?3HS1@8$5$0?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw@7$6$0?2sp?5rdraw?4argv?4envp?3uid?2hw$3?3fsr").
  Proof. exact (level_sound HS1 HSC cert2 HOLESC_sound). Qed.

  Theorem as_startup_shape : ltac2:(zQ "c0!jm3!jqf!moa!lhd!mp9!jv3!mpf!jh6!ki4!lvb!mje!mtb@4$a$1$8@9$2$1$b$0?2sp?4brk0?5mbase?5rdraw$5@f$6?4argv?4envp?2fs?5stdin?3uid?3gid?2hw?6groups?3net?6nofile?7sigmask?6abterm?4vasz?4urnd?3tmp@5$7$3$9@8$4$0?2sp?5rdraw?4brk0?4argv?4envp?3uid?2hw?3fsr?6shape1").
  Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS ASAN_H APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp
               Asan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS ASAN_H APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp
                  IMG Hsp Hbrk Hva Hve Hfit Huid Hhw) as HC.
    rewrite Hfsr in HC.
    pose proof (asan_check_sound RANGES HS1 HOLES1_sound FUEL BFUEL plan1 hinit shape1 cert1 _ _ _ _ HC) as R.
    replace (m_fs (model0 ASEGS sp brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp)) with fsr in R by (symmetry; exact Hfsr).
    exact R.
  Qed.

  Theorem as_startup_T : ltac2:(zQ "80!jqf!moa!jm3!jv3!mpf!ki4!mje!mtb@4$6$0$5@9$1$0$7$2?2sp?4brk0?5mbase?5rdraw$3@f$4?4argv?4envp?2fs?5stdin?3uid?3gid?2hw?6groups?3net?6nofile?7sigmask?6abterm?4vasz?4urnd?3tmp?1T").
  Proof.
    eapply srz_conseq; [exact as_startup_shape|]. apply sd_holes_only; [intros; reflexivity | exact shape1_holes].
  Qed.
End Startup.
