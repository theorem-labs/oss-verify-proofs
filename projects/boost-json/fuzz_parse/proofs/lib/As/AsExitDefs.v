(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive LibKnowFrame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import RefExitBase RefStdioDefs AsStdioCall AsPrintfFirst.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsCarryKeep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsExitDefs () := KReplay.lz_vm "#$:8K47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!sg+4Init9Datatypes6op!sL#!sH>4list00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S7know_okC13~~~!t<,5Lists7!s+#Def6Forall00C46Std!sF+4!s+#2In!s=7=!sZ%_f!s,$!tvc9kentry!tx+!t@76filter!vQ25Logic3and!u599!s\%_Inc!trO2As:AsExi!v>#s>keep_nonshadow!tr'!tW65proj1!t9`n_drop_!t9/!uj82eq00I!t8O8!w?'3SX26!w9%00!t18!zH-bool00K!sFA1!tW]3env!tT'!}NG3C7!t9,!t296images4Asan1M?loaded_segments!ug'!yy6Ex!s2#!y`97e!sC$bK!w9d1!yW&!so\9saddr_eqb!sp&5!t}'Arith8PeanoNat3!s&#!sL#!x'<andb!tV]8exp!tU/!t5;9!t5#_prop!#3/b<!up+_eq!veV!sy6;!u;'!sx,!vm>6!sO&!}H78eq_ind_r!y9e2!{v&!sod3!sok4!sok5!sok6!sok7!sok8!yV26Z!yW$6BinInt1Z!}B$!sC;!yp&!#92];!#<4%eqb2!#6N2!#9/11!{#86!{#%!sB89False!sE#!#89\5!}t$!#8;4!#9I72!u384True01I!#8w;1Z!#B5=3nat!#;{^4expr!#;y9!#>?%!vE$!tQ4!u3/0!xQ^6kn_su!#6n'!#:D5!#Bo$b!sB7>!sB&!#C;%!#?<9x!#;E8>!#;E%_!s-%!#B+`!ze+!#6r'!#?f<prod!#?f-!#>X<1K!y+?2!z-=!#H;#1K!#<~]ym_state!#=rd8!sr#exec!#<BA3fst!sC=sndK!vpA1K!|3@2I!v+g!|8'!v+^ideco!#IT#!sqb7scrip!#Cd#!sp$!{$^4rX3g!sld5XFUEL!smd6XSTOPS!uKescr!v9e6srX3if!wsc6s!#Kd/!w+_kn!ws+!{YA1C!#:w]_log!~YV2As;AsCarryKeep:c!s0#_keep!x>ec!zchcX3xf!smeexX3f!wL8!#Tp,1!#;``!z7,!#7q\!#=x$1!yFB!#Z_&1!t7c!#C-3!#:W53!t3c!#Izc!#C>%1!v{i!#H=V!|6%StdioCall9s!s0#_res!#<_d4s_p!#<[&7!skRDrive5kread!sh&!#aL?4BvWfK!#aoC!#47]6sr_get!#48[!w$+:!w$%call!{rB!#At$2!{%@!#[eP!x[=!#JX'ELinuxProcessSemantics5Riscv5Instr5aluop!#3Y_4rX1f!#7-f!slf5cX2i!smfkn!uJhrX2!v8h2!v8h3!v8j!t\gsr!uKj4!uKj3!uKi3!yLh4!yLh4!uIi4!w#i!smgx_sc!w#h5!sle;AEXIT_ECALL!wtg5!~Bixc!smeexX3!sme!#EA$c!wug1c!w$g!slf!#9V#c!{vh1!v8h2!v8h2!v8h3!v8j!t\gsr!uKj4!uKj3!uKi3!yLh4!yLh4!yLixn!smeexX3!sme!#4`$n!w$g1n!w$g!slf!#4`#n!{%h1!v8h2!v8h2!v8h3!v8j!t\gsr!uKj4!uKj3!uKi3!yLh4!yLh!sl'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nat37Corelib4Init7Decimalja2D0ja2D2ja3Nil37Corelib4Init3Natm0bof_num_uint37Corelib4Init6Numbero0bUIntDecimalhc4listhc4conshc3nilhc4prodhc4pairhc4bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~sc6kentrysc2SAsc4ELitsc4EVarsc5KWordsc3KWrsc4KImghc3appsc6KRange79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~hkb8kn_cells89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsExitDefs4FPX1~~~~~~hq8eax_flush_cellshq8cax_lit_cellshq8dax_lit_cells2hkb6ASP_HIhkb6ASP_LOsc6KAlignsc7scriptssc3SCRsc4exprhc4truesc5saddr08positive3h5LinuxProcessSemantics5Riscv5Instrimd5aluopimd5mulophc4andbhc4negb46Stdlib6ZArith6BinInt1Zir13lebir13ltbhq8ekeep_nonshadow36Stdlib5Lists4Listiu96filter04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~jgc7know_ok69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~jlcfloaded_segments35stdpp9bitvectorbdefinitionsjq42bvhc6optionhq8ekn_drop_shadowsc3envhc5falseir13eqbsc9saddr_eqbsc8expr_eqb46Stdlib5Arith8PeanoNat3Natkge3eqb37Corelib4Init5Logickj02eqhq8bkentry_eqb2iu97existsbiu97forallbhq86kn_subhq8dx3_extra_addrsc8sidecondsc9sym_statehc3fsthq84rX3ghc3sndhq85XFUELhq86XSTOPShq85knX3ghq84scr0hq86srX3ifsc2SSsc6sentrysc8sym_exechq84cX3g79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsCarryKeep~~~~~~lg4acarry_keepsc5s_loghq85cX3xfhq85exX3fkj03andhq86knX3ifsc4s_pchc4Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~loc5kreadkj01Ihq84rX1fhq84rX2fhq84rX4fhq84rX5f79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsStdioCall~~~~~~lv59stdio_ressc6sr_getjq42BVjq44BvWfhq8bAEXIT_ECALLhq84cX1fhq84cX2fhq85cX2ifhq85cX3ifhq84cX4fhq85cX4ifhq84cX5fhq85knX1fhq85knX2fhq85knX3fhq85knX4fhq85srX2fhq85srX3fhq85srX4fhq85x_scflv5astdio_callhq85cX3xchq85exX3chq86knX3ichq84rX1chq84rX2chq84rX4chq84cX1chq84cX2chq85cX2ichq85cX3ichq84cX4chq85cX4ichq85knX1chq85knX2chq85knX3chq85srX2chq85srX3chq85cX3xnhq85exX3nhq86knX3inhq84rX1nhq84rX2nhq84rX4nhq84cX1nhq85cX2inhq84cX2nhq85cX3inhq85cX4inhq84cX4nhq85knX1nhq85knX2nhq85knX3nhq85srX2nhq85srX3n" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition AEXIT : Z := 0x1944fc.
Definition AEXIT_ECALL : Z := 0x194208.
Definition XFUEL : nat := 20000.
Definition XSTOPS : ltac2:(zQ "20!q3!h9@1$0$1") := ltac2:(zQ "30!h9!qa!r1@3$1$0+hprtu8@1$2$0").

Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x6f43d8%Z | 10 => EVar 2
                          | _ => EVar (8 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition ax_lit_cells : ltac2:(zQ "40!r7!h9!q3!j4@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!j4!re!qa!r1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkmk8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkmmbN1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkicN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkj0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkj8N8+nhkkk0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkk8N8+hpkkq8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhklk8N8+qujo0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+iligu0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrsrt0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnjq0N8+hrnjq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrsro0N8+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrvqpcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgij8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtqv0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtql0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlq0N8+hqlqi8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhtu0N8+vvvvvvvvvvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkru0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqgo4N4+vvvvvvvf@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition ax_lit_cells2 : ltac2:(zQ "40!r7!h9!q3!j4@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!j4!re!qa!r1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkmk8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkmmbN1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkicN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkj0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkj8N8+nhkkk0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkk8N8+hpkkq8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhklk8N8+qujo0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkkl0N8+hpkkq8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkll0N8+rutk8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+mviop4N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+iligu0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrsrt0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnjq0N8+hrnjq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrsro0N8+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrvqpcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgij8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtqv0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtql0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnlq0N8+hqlqi8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ilhtu0N8+vvvvvvvvvvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhkru0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqgo4N4+vvvvvvvf@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition ax_flush_cells : ltac2:(zQ "40!r7!h9!q3!j4@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!j4!re!qa!r1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqgj0N8+nhkrv8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqgk0N8+hprtu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqgl0N8+nhkrv8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqgl8N8+kg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqgn0N4+1@1$5@2$1@2$1$0$2$0").

Definition ax_kn : ltac2:(zQ "30!s5!q3!hgb>3two$0>2fl$0@1$1$2") := ltac2:(zQ "h71!hgb!qa!hh4!hh9!hi0!hi7!hif!s5!hj5!hjc!r1!hk2!q3!r7!h9!hpc!j4!hud!hvf!igf!ii0!iia!ij4&@3$5@2$2@1$3Z+hrqgi0N8@1$4N4\3two$7\2fl$7@3$9$0@3$1$0@2$h6@1$4N0+h0@3$1$0@3$b@1$4N0$h5$h4@3$1$0@2$6@2$2@1$4N0-hp0+hp0@3$1$0@3$b@1$4N1+1+nvvvvvvf@3$1$0@2$8+hggg0+mngg0@3$1$0@2$8+hqtgg0+hrngg0@3$1$0@2$8+hrpvv0+hrpvv8@3$1$0@2$8+hrqgu0+hrsro0@3$1$0@3$5@2$2@1$3Z+mvkjj0N4@1$4N1@3$1$0@3$5@2$2@1$3Z+nhkkh8N8@1$4N3@3$1$0@3$5@2$2@1$3Z+hrpvj0N8@1$4N5@3$1$0@3$5@2$2@1$3Z+hrpvk0N8@1$4N5@3$1$0@3$5@2$2@1$3Z+hrpvh0N8@1$4N6@3$1$0@3$5@2$2@1$3Z+hrpvh8N8@1$4N6@3$1$0@3$5@2$2@1$3Z+hrqgg0N8@1$4N7@3$1$0@3$5@2$2@1$3Z+hrqgg8N8@1$4N7@3$1$0@2$6@2$2@1$3Z+nhkki8+i0@3$1$0@2$6@2$2@1$3Z+nhkmk8+4@3$1$0@2$6@2$2@1$3Z+hrsrt0+1@3$1$0@2$6@2$2@1$3Z+hrsro0+8@3$1$0@2$6@2$2@1$3Z+hrtqv0+8@3$1$0@2$6@2$2@1$3Z+mvipp0+h0@3$1$0@2$6@2$2@1$3Z+nvvvqgg0+ugsg0@3$1$0@2$6@2$2@1$3Z+hrpvv8+u8@1$a$0@3$9$0M7\2fl$7@1$c$0^1@3$9$0@3$1$0~0@3$1$0@3$b@1$4N4+nhkrv9+nhkvv8@1$a$0@1$f$h1@3$1$0~0@3$1$0@3$5@2$2@1$3Z+hrqgj0N8@1$4N4@1$a$0@1$fM7\3two$7@1$c@2$d@2$d$e$h0$e^2$h3$h2").

Definition scr0 : ltac2:(zQ "10!ijd$0") := ltac2:(zQ "40!r1!s5!ik7!ikd@3$2@1$0$1@1$0$3@1$0$1").

(* [comment removed for export] *)
Definition keep_nonshadow : ltac2:(zQ "20!s5!hgb>1K$1$0") := ltac2:(zQ "e0!ikd!il4!h9!ilb!j4!s5!hgb!im3!ip1!ipa!iq3!iqa!is9!it0\1K$6M6\1K$6$5^1\2a0$3\1w$4\1v$0M3\2a0$3$5^3\6a_base$0\1a$2M0\6a_base$0$5^2\1z$2M2\1z$2$5^1@1$b@2$a@2$c+nvvvggg0^2@2$d^2+pggggggg0\1p$7$1\1p$7$1\1n$4$1\2op$8\2a1$0\1b$0$1\2op$8\2a1$0\1b$0$1\2op$9\2a1$0\1b$0$1\2op$9\2a1$0\1b$0$1\2sx$5\2lo$4\1n$4\1e$0$1\2sx$5\1k$4\1i$2\1n$4$1\1a$3\1n$0$1\1a$3\1n$0\1k$4$1\2lo$2\2hi$2$1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\1a$3\1n$2$1\2a1$3\2n1$2\2a2$3\2n2$2$1").
Definition kn_drop_shadow : ltac2:(zQ "20!q3!hgb>2kn@1$0$1@1$0$1") := ltac2:(zQ "40!hgb!q3!it7!ivc\2kn@1$1$0@3$3$0$2^1").
Lemma know_ok_drop_shadow : ltac2:(zQ "90!jg6!jl1!jp1!js1!q3!js7!jt0!ju2!hgb>1E$7>1M>0@1$3@1$0#k0@1$5@1$3@1$0#8>2kn@1$4$8>0@4$1$2^3^2^1@4$1$2^4^3@1$6^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##0[h01xh11Ah21lh32HKh42H0h51Ph61fh71Eh81Hh91Kh:1Mh;2_Hh<2knp;1p;4p;3p;2p;6g0000j12Tg000Uj1>Tg0013j1<!s/$Vj1?Tg0028j1:!s/$Xj4=Tg003fj34Tg004Gj30!s/$^j3;Tg005@j38j47Tg006Pj35!s/$kR0j26Tg007Fj4C!s/$dR1j19Tg0094j6B!s/$Oj1ATg00:_j3@Tg00;9R2f1R3f0R430p=3g00<BR5g00<b7@4p=1g00=Bg00>H#2#2#2R6!s-%#>#<%>6#<#?[%:2g00>mR6f2R7P3P4C=g00@3p4p710R8p-0\4R9%:3R:P0A4734f3R;f4R<?047P<P3O1[]0R=[A0;43P;!s7$^07A4;73[R>A4<;7\=A;734P4n20010!s#$12!s-%0W2W5W1P>^2:^59^18P4P2A86<;A5217A521;,34g00@P!tf'P5\4R5%:7R9P0A5;7490;3A0<73P;P7O1#1'6[R:A0;34P7P3!s8%A5<;390<7R>[f5R=?0;7P<P;!sD%\>P;P!u|%CP3!ty9X03W6W1P:^29^03^65!u#&P1P7P=P3O5137=%97#1'6P0f6R0,3;%9;#1P6f9R1f8R8P<C7P413=8%90#1f<R0f;R8586R=f:R<5421340P6f?f>R5P3C7[^02[1348P6P5f=!s;,A8650=428[A;2=<P1f7P3EBW;W3P3P4O2!u?7b3b4W3X92O4b4P6P;P7%A3C=eW8W<W:W7o"). Qed.

(* [comment removed for export] *)
Definition kentry_eqb2 : ltac2:(zQ "20!hgb!s5>1x$0>1y$0$1") := ltac2:(zQ "c1!h9!ju8!ilb!ikd!hgb!j4!iq3!s5!jv0!jv7!kg3!ki9&\2a1$2\2n1$0\2a2$2\2n2$0$1\1x$4\1y$4M4\1x$4$7^2\1a$2\1w$5\1v$3M4\1y$4$7^4\2a'$2\2w'$5\2v'$3@2$6@2$6@2$9^6^3@2$b^5^2@2$a^4^1\2a0$2\1n$3$1\2a0$2\1n$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a0$2\1n$0$1~0\1a$2\1n$3M4\1y$4$7^3\2a0$2\1w$5\1v$3$1\2a'$2\2n'$3@2$6@2$9^4^2@2$a^3^1\2a0$2\2n0$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a0$2\2n0$0$1~0\1a$2\1n$3\1k$5M4\1y$4$7^4\2a0$2\1w$5\1v$3$1\2a0$2\2n0$3$1\2a'$2\2n'$3\2k'$5@2$6@2$6@2$9^6^3@2$a^5^2@2$b^4^1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a0$2\2n0$0$1~0\2lo$0\2hi$0M4\1y$4$7^3\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\3lo'$0\3hi'$0@2$6@2$8^4^2@2$8^3^1\1e$3\1m$0$1\1e$3\3lo0$0\3hi0$0$1\1a$2\1n$0$1~0\1e$3\1m$0M4\1y$4$7^3\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\2lo$0\2hi$0$1\2e'$3\2m'$0@2$6@2$a^4^2@2$8^3^1\2e0$3\2lo$0\2hi$0$1\1a$2\1n$0$1~0\1e$3\2lo$0\2hi$0M4\1y$4$7^4\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\3lo0$0\3hi0$0$1\2e0$3\1m$0$1\2e'$3\3lo'$0\3hi'$0@2$6@2$6@2$a^6^3@2$8^5^2@2$8^4^1\1a$2\1n$0$1~0\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$3$1\2a0$2\2n0$3$1\2a0$2\2n0$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a'$2\2n'$0@2$6@2$9^4^2@2$8^3^1~0\2a1$2\2n1$0\2a2$2\2n2$0M4\1y$4$7^5\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\1a$2\1n$0$1\2b1$2\2m1$0\2b2$2\2m2$0@2$6@2$6@2$6@2$9^8^4@2$8^7^3@2$9^6^2@2$8^5^1").
Lemma kentry_eqb2_eq : ltac2:(zQ "50!hgb!kk4!s5!il4!kka>1x$0>1y$0>0@3$1$2@2$4^2^1$3@3$1$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##oxp'0h01Hh12H0h21ni001nh31ai011ah42a0h51ei021eh62hii032hih72loi042loh81mi051mh92H1h:2n0h;2a1i062a1h<2a2i072a2h=1ki081kh>2n1i092n1h?2n2i0:2n2h@1vi0;1vhA1wi0<1whB2H2hC2e0hD3hi0hE3lo0hF2H3hG2a3hH2e1hI2k0hJ2m0hK2n3hL2v0hM2w0hN1xhO1yi0=1bp%0p;3p;2p;6p;4g00@lj39Tg00B5j28Tg00C?j2G!s/$_j2ETg00D=j2;Tg00EFj3<!s/$ij3LTg00:_j34Tg00G<j3OTg00HNj2UTg00I1j6F!s/$Oj2CTg00JXj3:Tg00Kaj2>Tg00Ljj2?Tg00N3j37Tg00O<j2=Tg00PEj46Tg00QNj25Tg006kR0j2M!s:$kj2TTg00RKj2STg00SXj2RTg00T2j6Q!s/$Nj2PTg00<BR1f1R2f0R3'Sg00<bR434p=0g00;9R5?423p=2A4134p=3!s-$,M2p=A1E23=414p=B18!s1'H1R53p=Jg00TmR6f4R7f3R8f2R9P2P3EFp=KP1g00V5P2g00VUP4P3EQp=NA4592/P3p=115!sv'@g00W1R4!tU%DP4P7P8P!sr+I1023P510391228]0P9g00WOR:g00WnR;A9923R<f7R='0P5A9789R>/03f5R??978R@/22]0f8RAf9RB?9A=RC/0<f:RD/88RE1GB9RF'ERG1;A2RH;<3%3G/AHP0f;RH/87RG1GD8'B1;B9RI#3f<RJ?9HD/2@P3f=R@f6RK'8RL1GJ?RM'B1;J?RN#3f?RO/8ARPf>RQ/G=RR;<2%3PRS/ARP0f@RR/HBRT1GOA#3fARU?9RORVA9DBA'2P3fBRW/HHRX1GWH#3fDRY?L@2RZA46Y@R[fCR\?OJKA4;\JP01G23#3A4:92[R]A4:231G92#3R^[A4:89\^1U23P2n20010!s#$12!s-%0X8:X2:R^P]^8:^2:R]P3fFR_POP8O3A4:_OPUfHR`fGRa593A9WURRb'2X36P:PRA9W3a/2bXA:P;POA9WU3/2bX@;%JVP_P9EFPaP3EFP`P8DKb9bBb1b0W9W0P2P3O!tc8b0W1!sFB0XL;XM:X46!yM%O3A9=K?RV1C23Rb'0P1p-0P3g00Y5Rcg00YRn0110=000!sn$RdX51/N3RePc1C89Rf=1C3b1W0X2;X46!tM%A:923Rg,0CPePcA9HDBRhA:789Ri;1!sU%=:!sX&!tX&1>23Rj,0VPePc1>89Rk!t%+64X74!t%%1?23Rl,0VPdXC!tX$mPc1?89Rn!sU+84X5;!tX&7923Ro,0CPmPcA7789Rp=1h!s~-X5;!tR+=23Rq!tR'=89RV!uU,4!uU+!}+'C6RC,0h!uZ%@JHP?!}H%C6Rh!u]'?4X<6X>4X;6!s]'O4!vr$800083110110<10;20!s1$03!s-&10820104103201021053!s-%!s9'11004010610910710:P3O1W0W@WAX3!vx,0b?P510f31C78Rr!~C$PK1CA=Rs/0<!uc$CDBRt?1>!u+%@;XA!y=/1CK?Ru/0b18=9Rv1;K2Rw!~\$vRx/AwP01HA8S001;=9Rw#3Ry1CBARz/2rP31HD?Rr1;D?#3R{ALJ=2S01A46J=R|AOJ=2R}A4;J=R~PB1C3Q/2tX36P;PA1CD3/2tX2;%JzP@!{z$QP2DK!{v$!{VE:!zS,10sg!wq$1ti!zA+:!zA00uj!sH%sk!z750ul!yZ$1sn!y}410so!sC%tp!yq:0uq!t&&V!sH%:!yg,10t!|8$1CJH?!z['!yPC0!yPvX2;X3!tc+g=P510i3A:?78Rt!yN%AA:B!yO-A:HDBRu!yP<A:=K?Rz/0b!ut&f!ut&!w_11EEIRI1GA2RE!yn$I/AEP01;D8RE,BG%3FA:JHD/2tP31BLN%3M1;Q=RM=<P21ASMP0PT1;OART#3RMA:URORSA:!#8l%1;WH#3RPPZP[AOY@2R[A4;Y@RZP^P]P3fER]PQPAO3A4:]QPUA:3`aA:WURR^!#7^$;PRA:W3a/2^X2;P:POA:WU3/2^X=:%JSP_!z\$aP9!#7^'1bBb9b0W9X0X!#7_aI!zj4z!zj?z!zjGu!zj<z!zj?u!zj$A:@!zka1!zkd!#99$!#5?-j?P510k31>78Ru!#5?&>!zn-1>DBRz!zm2!si->K?RX!zl4!{}0!#3M&zi!#:h-!tU/Xj15=9RS15K2R^!{6$SRS%3^RN'MP01@A8PS1>BA/2uP31@D?RuP01@231D92[RL1D231@92Rt[1D89\t1T!#?r<4X24RtPL^84^24RLP3PJP=P2O31DJ=PtPLP3POPDP7O31DODPH1>3R1>JHRF'2X74PD1>J3/2FX641>HD#JPOP9DIPRP3DIb0b9b1b9X1u!zdDD4XE!zB+X!zBGz!zB&!s`$!zB0X!zB224!wJ-z!zB%1F!#6'g1!z>Y!}$0l!z9$n31?78RF!z9'?A=Rz/0<PmPc1?DBRs!z9=?!z9'!v7%!z97zg!vq&!z9>!se&!~t7XlA<w^31MyNP01;A8#3PS1?BA/2FP3P}P~!yD&@PAP9O3R~1D@AR}P;PD1?3O1?HD!yJ$5;PB1?H!yJ$84%JsPQP3DIPOP9EFb1b9b0X1uX0{!yFBJ4XC!y%+zoPdXH1/N3R1!u[$!#4M/C!y11!u[%!y17sC!w3%!#<9~!y4G!{U0o=P510p3A7?78Rs!#<9&7B!y6-A7HDBRX!y7<A7=K?Rd!y8IX!y8<d!y82!}j0dlP!wB$z!}j,!wg/15B9R1,EERE15A2R{;<3%3E/A{P01;H715D8'B%31A7JHD/2sP31;@K15J?Rs'B%3s15Q=Rs=<T21AMsP01;RB#31@OAA7UROA7!#=G&@WHP[PZ!zO&YP@P=O31DY@!s8&aPR!#5#$aRP;PWfIRZ=73`A7\WUR[!zb%UA7\3`/2[X74PRA7\W3/2[X64A7WUR#JPaP9DIP`!zz$ZP7EF!#N%%B!#=K$P!#=KU1!#5e2!zx0d!zx?X!#Kk%@!zy|1!#5/M!#73/q?P510V31=78RX!#54&=!z|'ePc1=DBRd!#J`<=K?RP!#<G'z!#D56z!#<G%d!#Hn;P!#A&%!#547P!#9f%z!#9f6z!#9f%d!#A&;PqA<v^31MxNP0Q00PS1=BA/2XP3Q01P|!z6$~P}PD1=3O1=HDR}!#DH$B1=H3/2}X24%Jd!#5a+DK!#5a,r!#KpB!#BA-d!#J,$=!#4r~!xwG!z]0CBP510h3PK!#RG$C6Rh!xx%DPDPBPAP=C6Rd!x~&PJPHPDPBC6R<!#5%;PAP=PKP?C6R>!y2+d!#5-6d!y2&<!#5-;>!y2&d!y27>!y2&d!y27d!y2&<!y2<>!#?r%d!}m7<C18@715J8'E18H9'ER<15D2RC;<3%3</ACP018Q?RC15@7'E18J8'B1@H9POPQP@PJC6/2hP318R=R=15OK'E/BC1@Q?18WB15UA'ERC?<=2%3C/A=P018\D15WB'B1HUAPYP\PWPUC6!w;%PAC6'2P318]J15YH'B1HYH18aQRH15_@R];<2%3H/A]P01H`O1@aQPZP`PaP_C6R0PR!ti%!sm%fJRQ/HU1@QUALQU?A46QUfMRU?LY9A46UY!|'$3fLRUP\P@O31DU\!s:&PRLPaP?O31DLaPZP3fRRtfQRUPLC6P!tD&C6R\'2X;6P`PQP3P!sC$/2\X>4Pa!sK$3!s8'<6P_!s]&3!s8%?4%J0f!#F1$LP?DKPU!}9$tP7DKbBbFb1bFb0b9WB!#7YA9!sFB!#8ADK4XG6!~'&!}]x1!}]6!#\SM1!#N<4!#F|&1!#8s41!tC>O5XN5o"). Qed.
Definition kn_sub : ltac2:(zQ "30!q3!hgb!s5>1a@1$0$1>1b@1$0$1$2") := ltac2:(zQ "50!hgb!q3!kka!kl9!km4\1a@1$1$0\1b@1$1$0@3$4$0\1K$0@3$3$0@1$2^1^2^2").
Lemma kn_sub_ok : ltac2:(zQ "c0!q3!jg6!hgb!jl1!jp1!js1!s5!js7!il4!kk4!kmf!ju2>1E$b>1M>0@1$5@1$1#k0@1$7@1$5@1$1#8>1a@1$0$2>1b@1$0$2>0@3$9$6@2$a^2^1$8>0@4$3$4^5^4^2@4$3$4^6^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##4Lp'0h01xi001xh11Kh21Ah31lh41Hh53HK'h62HXh73Heqh82K'h91Ph:1fh;1Eh<2HKh=3HKah>2Hsh?1Mh@1ahA1bp;1p;2p;4p;3p;6p;7g0000j14Tg000Uj1?Tg0013j1=!s/$Vj1DTg0028j1CTg00Ynj2I!s8$Xj4<Tg003fj37Tg004Gj38!s/$^j3;Tg005@j3:j46Tg00RKj1Bj25Tg00@PR0j33Tg00[6j3@!s/$Rj3HTg0094j6>Tg006kR1j22Tg00\5R2j29!s1$Oj3GTg00]2j3FTg00:_j3ATg00T2j7ETg00<BR3f0R4g00<b3Ap=0g00;9R5f1R6;84p=1g00=Bg00>H#4#4#4R7!s-%#?#=%?7#=#D[%C5R71I64#0g00>mR8f4R9f3R:P6C<g00@3p4p710R;p-0\4R<%C6R=P1f2R>?764A894>R?P9P6O1[^0:R@[A8:46RAP:!s:&>A7:>6[RBA79:>\@A;>64P4n20010!s#$12!s-%0W3W9W2PB^3=^9<^2;P4P5f6R;f5R<5:8P9114<%B4RB=35;X15R@=@5;#0f8RC,14RDf9RE935BX15P6O1#0[^05[f7RF,14A35BC!s@0A35BFX15=@5F#0[AH5@;P9P6P4E>P@!sN%P0!u{&0P3\4R3P1A3>64#0P:P4O1#0,2?X0:,9:[R?P>!s:'AX0>,9>A3:>6#0RA[A8<4:P9!sF%'2X09,99\AAG>64P6!v-7X3=W:W2P?^3=^:3^20P4P5%B:PFP6O41594#0,2DX05,95P2P5114E15<4!t/%5P8f<R2f;RDP<C6P4114D15F!sE$P1116215C6#0P8f@RCf?R1PEC6P4f>RE,1:15D9#0AF2<4AA52<P5f=R2fBRD,14P8fFRFfER0P1C6]5X85fA,12fDR29:80R1=75D1142P8fHfGR2P6C6!wU%CR3!sh$P2PF!s<'A:8F0=753[A;51DPCPEP4E>W5P;P4P>FEb7W7W5P6P4O2!yT84X8!sE8!s0%b6b4b6W=X15O4b4P8P<P9P:C<eW<W>XA7W@W?W;o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true true) 40) []).
Definition srX1f := Eval vm_compute in (s_regs (fst (fst rX1f))).
Definition cX1f := Eval vm_compute in (carry (s_log (fst (fst rX1f))) (ax_kn true true) []).
Definition knX1f := Eval vm_compute in (fst (fst cX1f)).
(* [comment removed for export] *)
Definition srX2if := Eval vm_compute in (sr_upd (sr_upd srX1f (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x714648) 4 (sr_get srX1f 12)] knX1f []).
Definition knX2if := Eval vm_compute in (fst (fst cX2if)).
(* [comment removed for export] *)
Definition rX2f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x194528 srX2if [] knX2if 40) []).
Definition srX2f := Eval vm_compute in (s_regs (fst (fst rX2f))).
Definition cX2f := Eval vm_compute in (carry (s_log (fst (fst rX2f))) knX2if []).
Definition knX2f := Eval vm_compute in (fst (fst cX2f)).
(* [comment removed for export] *)
Definition srX3if := Eval vm_compute in (sr_upd (sr_upd srX2f (ridx 13) (sr_get srX2f 12)) (ridx 15) (ELit 0)).
Definition cX3if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1bdaf0) 8 (sr_get srX2f 14)] knX2f []).
Definition knX3if := Eval vm_compute in (fst (fst cX3if)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x3_extra_addr : ltac2:(zQ "20!s5!h9>1a$1$0") := ltac2:(zQ "50!h9!qa!r1!kl9!jv0\1a$0@3$3$0@1$4^1@3$1$0+hrqgj0@3$1$0+hrqgk0@3$1$0+hrqgl0@3$1$0+hrqgl8@3$1$0+hrqgn0@3$1$0+mviop4@3$1$0+nhkkj0@3$1$0+nhkkl0@3$1$0+nhkll0@1$2$0").
Definition x3_core : ltac2:(zQ "20!s5!hgb>1K$1$0") := ltac2:(zQ "d0!ikd!j4!il4!h9!s5!ilb!ip1!ipa!hgb!im3!ju8!iqa!kn9\1K$8M8\1K$8$4^1\2a0$5\1w$1\1v$0M5\2a0$5$4^3\6a_base$0\1a$3M0\6a_base$0$4^2\1z$3M3\1z$3$4^1@1$b@1$c^2\1p$9$2\1p$9$2\1n$1$2\2op$6\2a1$0\1b$0$2\2op$6\2a1$0\1b$0$2\2op$7\2a1$0\1b$0$2\2op$7\2a1$0\1b$0$2\2sx$4\2lo$1\1n$1\1e$0$2\2sx$4\1k$1\1i$3\1n$1$2\1a$5\1n$0$2\1a$5\1n$0\1k$1$2\2lo$3\2hi$3$2\1e$0\1m$3$2\1e$0\2lo$3\2hi$3M0\1e$0$4^3\1z$3$2\1n$1M1\1n$1$4^1$2\2n0$1M1\2n0$1$4^1$2\2n1$1M1\2n1$1$4^1$2\2n2$1M1\2n2$1$4^1$2\2n3$1M1\2n3$1$4^1$a\2n4$1$2\2op$6\1a$0\1b$0$2\2op$6\1a$0\1b$0$2\2op$7\1a$0\1b$0$2\2op$7\1a$0\1b$0$2\2sx$4\3lo0$1\1n$1\2e0$0$2\2sx$4\1k$1\1i$3\1n$1$2\1a$5\1n$3$2\2a1$5\2n1$3\2a2$5\2n2$3$2").
Definition knX3g := Eval vm_compute in (List.filter x3_core knX3if).
(* [comment removed for export] *)
Definition x3_fact : ltac2:(zQ "20!s5!hgb>1K$1$0") := ltac2:(zQ "80!h9!ilb!ju8!ikd!il4!hgb!j4!s5\1K$5M5\1K$5$7^1\1a$1\1w$6\1v$3$2\1a$1\1n$3$2\1a$1\1n$3\1k$6$2\2lo$0\2hi$0$2\1e$3\1m$0$4\1e$3\2lo$0\2hi$0$4\1a$1\1n$0$2\2a1$1\2n1$0\2a2$1\2n2$0$4").
Definition x3_facts := Eval vm_compute in (List.filter x3_fact knX3g).
Definition exX3f := Eval vm_compute in (List.filter (fun K => negb (x3_core K)) knX3if ++ x3_facts).
Definition rX3g := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77ba0 srX3if [] knX3g 40) []).
Lemma rX3g_eq : ltac2:(zQ "h50!koa!q3!kp5!r7!ijd!kq1!kq7!r1!re!kqf!il4!kk4!kr5!kre!ks8!kt1!kt9!ku3!ku8!kv1!jp1@3$b@2$3@2$3$2@1$1$0$4@7$h3$h4$c$a$d$f@5$h1+nnrq0$h0@1$7$h2$eNi8@1$7$0@4$8@2$3$2@1$1$0$4@4$8$2@1$1$0@3$5$2@1$1$0@3$5@2$3$2@1$1$0$4$6@3$9$2@1$1$0@3$5@2$3$2@1$1$0$4$6@3$9@2$3$2@1$1$0$4$6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##'#p;1p;2p;5p;7p;3p;4g0028j1>Tg00^Bj28Tg00SXj2;!s8$bj10Tg0000j12Tg00_Gj1<!s/$ej17Tg00`Ej5:Tg00aQj79Tg00bZj34Tg00c7j36!s/$Tj45Tg00:_j3=Tg00d4j11Tf0#1!s$1p=3g00dSR0g00e_R1#>R2'8R3g00fjR4'8R5g00h4R6';g00>mg00i:g00<bg00jAg00kIg00>H#0#0#2!s+$!s0/2!s&$!s$'<g00lOg00mW#7g00n`g00og#3!s$'D:%71F9P3P4P0P2A4346R19402A6021C5A6346C55=5do"). Qed.
Definition srX3f := Eval vm_compute in (s_regs (fst (fst rX3g))).
Definition cX3g := Eval vm_compute in (carry_keep keep_nonshadow (s_log (fst (fst rX3g))) knX3g []).
Lemma cX3g_eq : ltac2:(zQ "h21!q3!koa!hgb!r7!s5!kq1!kvc!re!kqf!kp5!r1!kk4!lk5!it7!ks8!kq7!ll3!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$b@2$3@2$3@1$0$2@1$0$1@1$0$4@4$c$d@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$a$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Bj22Tg00SXj25Tg00bZj30Tg010Fj19Tg00_ej18Tg011Lj47Tg00c7j33Tg00cTj44Tg00:_j36Tg00;9#1R0g00e_#1R1'2R2g00<BR3#1R4'2R5g012YR6'5g007dg00dSR71271g00fjg00h430701#9g00n`%83C7P2P4P0P1A0246R39001A3013C4A3246C4565do"). Qed.
Definition cX3xf := Eval vm_compute in (carry_keep (fun _ => false) (s_log (fst (fst rX3g))) exX3f []).
Lemma cX3xf_eq : ltac2:(zQ "h21!q3!koa!hgb!r7!s5!kq1!llb!re!kqf!kp5!ju8!r1!kk4!lk5!lm4!kq7!ll3!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$c@2$3@2$3@1$0$2@1$0$1@1$0$4@4$d\0$2$a@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$b$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Bj22Tg00SXj25Tg00bZj30Tg010Fj19Tg00_ej18Tg011Lj47Tg00c7j33Tg00cTj44Tg00:_j36Tg00;9R0#1R1g00e_#1R2'2R3g00<BR4#1R5'2R6g013_R7'5g00V5V0g00dSR01202g00fjg00h430702#9g014f%84C7P3P5P1P2A0357R49012A3124C4A3357C4566do"). Qed.
Definition knX3f := Eval vm_compute in (kn_drop_shadow (fst (fst cX3g)) ++ fst (fst cX3xf)).
Lemma x3_facts_f : ltac2:(zQ "h00!q3!koa!s5!kk4!il4!lmd!ln4!kmf!hgb!kq1!r1!r7!kqf!llb!lm4!ks8@2$5@3$3$2@2$7$f$6$4@2$5@3$3$2@2$7$e$6$4@3$3@1$0$1@3$c@1$0$8@1$0$1@3$9@2$b@1$0$8@1$0$1@1$0$2$d@1$a$1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;3p;1p;2p;4g00:_j30Tg0028j12Tg00_ej19Tg006kj21Tg00SXj25Tg015mj44Tg00Ynj23Tg00^Bj28Tg00bZj37Tg00c7j36Tg00<BR0g00<bR1;01R2g00e_R3#2R4%93R3;03R5,121501R6P2P5P61543C4C4g00n`g016HR6'3=001g014f/36=001g00;9#2R11814%20g013_37764=043'1'1do"). Qed.
(* [comment removed for export] *)
Definition srX4if := Eval vm_compute in (sr_upd (sr_upd srX3f (ridx 6) (sr_get srX3f 10)) (ridx 7) (ELit 0)).
Definition cX4if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1bdaf0) 8 (sr_get srX3f 5)] knX3f []).
Definition knX4if := Eval vm_compute in (fst (fst cX4if)).
(* [comment removed for export] *)
Definition rX4f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77f10 srX4if [] knX4if 40) []).
Definition srX4f := Eval vm_compute in (s_regs (fst (fst rX4f))).
Definition cX4f := Eval vm_compute in (carry (s_log (fst (fst rX4f))) knX4if []).
Definition knX4f := Eval vm_compute in (fst (fst cX4f)).
(* [comment removed for export] *)
Definition x_scf : stdio_res := Eval vm_compute in
  (match stdio_call 40 srX4f knX4f with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
Definition rX5f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS (sc_ret x_scf) (sc_sr x_scf) [] (sc_kn x_scf) 72) []).
Definition cX5f := Eval vm_compute in (carry (s_log (fst (fst rX5f))) (sc_kn x_scf) []).

Lemma x_itinerary_flush : ltac2:(zQ "j10!q3!koa!kq1!kk4!lmd!kp5!r7!hgb!r1!kqf!ijd!s5!ikd!h9!lne!lo5!js7!jg6!hh9!ls7!jp1!lt0!lt5!ltd!kq7!lu5!lud!mj6!mk3!mkc!ml2!mla!mm9!mn1!mn9!kvc!mo2!mob!mp3!mpc!mq4!mqd!mr6!mrf!ms8!mt1!mta!mu3!muc@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h6+hpklhc@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h6@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i0@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i2@1$8$1@2$4@3$3@1$h0$c@5$h3$h4$i8@1$h2Z+nhkmk8N4@2$f$c@1$h2Z@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h7+nnrp4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h7@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i1@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i4@1$8$1@2$4@3$3@1$h0$c@5$h3$h4$i9@1$h2Z+hrtqv0N8@2$f$c@2$hc$ic@3$hd@1$h1#5+cKv$h5@2$he@1$h1#5+c@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h8+nnvg4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h8@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i3@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i6@1$8$1@2$4@3$3@1$h0$c@5$h3$h4$ia@1$h2Z+hrtqv0N8@2$f$c@2$hc$id@3$hd@1$h1#5+aKv$h5@2$he@1$h1#5+a@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h9+hprtu8@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h9@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i5@1$8$1@2$4@3$3@1$h0$hb@3$j0Ni8$ie$ib@2$f$hb$if@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$ha$hf@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$ha@1$8$1@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i7@1$8$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##UQp%0p&0p;1p;3p;2p;4p;<p;5g00^bj11Tg0000j10Tg0028j1kTg00_ej1jTg00:_j3ITg001Vj1qTg017Pj1ATg018Wj2]!sS$Gj15Tg00d4j12Tg0199j16Tg01:@j1b!s/$^j3yTg01;ej2=Tg01<mk402Tg00Ljk20!tW$N3j3oTg00Kaj2eTg01>4l<}Tg006kj24Tg00SXj2LTg015mj4nTg00^Bj2vTg00bZj3CTg01?Bj1`Tg01@Gj5m!uY$Uj1|Tg01AIj2u!s/$lj3tTg01BOj2sTg01CVj3{Tg00c7j3iTg01Dcj3<Tg00@lj3QTg00O<j2zTf0R0#1#0#0#0p=?%1!s-$7%0!s-$>%10#1#1#0p=N%00#5p=dg00W1R1f1R2;I0p=J!sK&p=Y%00#1p=3!s8%!si$W!sy$!si%G!s>$p=B!t,$!sF%8!s2+!s$'p=E%50#Ap=K!tM'1p=V!sN'5p=;!t6$!sR%X%20#2p=r!s-$#2#2p=O!sR%5#Ap=Tg00WnR3%62;<0p=af2R4#6%62=<305<3p=SA<3209<34p=R!tA+!s$'p=Z%b0,=2p=h!tR&p=D!uL%0p=g!ub&p=p%5!sM%x!tM&!s3$ff3R5/=4?Q20p=w%10#5p>00g00;9R6?<20p=~A<6209<64p=\f4R7%55'=?Q42=<60p=9%05!v=&5,=7!s?,:%1!s?9Ff6R8f5R9;Q7AQ5!s=%5<6p=[1z!sK'M%b!s\1@!s7%%02!v]%7Q4!s?%PP8P9P7P5P4P2P0CnCnp=HAi542=I70p=_AC4209i75p=UAI897AI542/40'4p=^1420,44p=c!s='p=lg00>HR0#1R5#0R4#0R2#1R9#0R8#?S00#7S01#7R7#>#N#dR:/J:g00e_R;#kR<%j;R;;I;R=%q3R>g01EC#AR?,]3R@;I@RA%15!t%$B#1RC#YRD#3#W#G#dRE/JES02%BDRD#7#8#7#dRF/JFS03%00RG#0RH#0RI#0RJ#0RK#0#8RL#>#8RM#8#E!s$'RN#K,]3RO=I>OS04%19R9#3#N#V#3#;RP/JPS05g01EaRQ#qRR%14R4#1RS#1RT#0RU#3#VRV#1S06#YRW#1#;RX%50R0%?9R9#7#3!to&Y%>BRB#1#XRZ#1R[#3#VS07#WS08#0#KR\g00ogR]#2R^#2R_#2R`#2Ra#6S09P\%KLS0:P?P?g01Fo%6]RL%bKRb#A3yRc%2aRd#2Re#2Rf#2Rg#2Rh#rRi#2#ORj#2Rk#2#O#ORl#2Rm#2Rn#2Ro#2Rp#2Rq#2Rr#2Rs#2Rt#2Ru!s\$v%AY%1T!u`$Y#1Rw#8#BRx#B#3#7#T%2v#ORy#6%2yRy!s'%AX%6k%Oy!s=2!s'76qS0;%6rS0<%6sS0=%6tS0>%6uRu%2y#r!t|$!sn3%j3'a3S3R3R3R,ap9Sno9Slm3S3S3S5R?3R3S3R,ai7Rc'aP?%?URU#>Rc#0Ri#0Rm#0Rl#1Pg%Z[#;R[#AP?%1mRm#0PgP\!s3$PgP\1=LbPg%6_%02R_,hLPg%17#G#T%3Y#3RY#BR7#8#;Rb,=?S0?PgP?%GwRw#1Rm#YRo#0#;S0@,=?RnPgP?PL%1HRp#1Ry#?Pg%0N#KRNPL%DyRy#0Pg%AbPL%0pRp#gRt#0RsPg!{m%8Rr#1#?#3#3#K!sJ'DPg%KGPL%1IRq!sx$A0RkPL%8qPgPNPL%?JPg%0D#W#7P?%>YRY#p#3RD#0RN#1Rq#0Rz#1P^P?%0NRN#0R{#0,x?R|!s:$1D!sQ$}#0R~!s>$P^P?P?%0z!s/&1!s[$!s3'!sT%!sw&P?%1}R}!s3,~!s/'qRq!s<,N!s/'{!s/&7D!t330}!s/'q!s/$L%04R4#0Rq#>Pg%Vp#W#B#!s>$SRS!s:$!|x$0Rp#B#WR}#1Rz#0RD#>PL%>8R8Pg%gzPL%D_Pg%7DPL%DCRCPg%1GRG!sP$0R_#p#KPLPrPg%0m#WPL!wP%DPg%7oPLPBPg%?U#8PL%1GRU#1Ro#DPgPuPL%8UPgQ0>PL%1DRU#DPgQ0=!t?&Q0<PLPyPgQ0;%17#X,f?R7P^Pk%3ZRZ#0Ry#>R_#0Ru!y_$3Rr#0,f?RzP^Pk!z]$S0;!z'$7Z#3RZ#0#3#;S0<,=?RmPag00<bP]Pa%6^R]H021hLJPg%6jPLPIPg%6h%5JRJ-01LRh%B5#ZR5#0#V#N!#5s%;!ua%Y#V#ZRj#1R{!s2&N#55oLR~%08R8,hL%58%5j9o]0Rj%5M%>9#8#;'e%14#G!so$NSRS#0R4#D!s@&0W#;/eX%1cRc#!s2$bP?%0x#3#7#;PaP]CwP?%3uPg%6`P?%0VRV#0R`#BPg%6dRdP?%gVPgPdP?%3`R`Pg%6eReP?P`PgPeP?%0lRlPg%6fRfP?PlPgPf%5KRK%5HQ0?%5IRI%05R5#?#E,f?%1B#?#8#;1=?X%5CP?%GZ#B!z4&grPa!zX%_!w\$r!~%$?PrPgQ01#0#!~r$RrP?%G!}~'1U#?!vl$TP?%7t#8#!{N$%Y4#X#;R4,=!}d$4%NT#G#3#B,f?!xL&3}!s/&>p#?!uj$85#E!so$3w#3Pa!xr%S#3#GPg%1q!vW$?#G!sI$Ys#3#NPg%1N#Z#Z#KP?Q07#0!u&%Q06!yC$XPa%K{R{P?%Dc#XPaP{P?Q0;Pa%AKQ09Q08$00;o[P?%1iRi#0R[#>#;Pg%AP!we$1[R[!#6+$P[PgQ0:P?%Bi!tk'_PgPrP?%1yPg%po#B#3#X#7!tp$0Y#7!tQ$^P?%j6,~j9\h~D9D:!s$$FD:3\D:D9!s8+:DFDFF[!s-%!s@%3M3M9M|J9MnI3M9M705Mm5Mz!sF$F!s\'3\!s$$M3\D@F[!sj$@!s$+P!s$$!s-'P!t>$!s$6F[D9!sN$!s$+F[!tZ$:DFM<},]QRz;IzRmQ00#3#8#3#;R7/J7R014==RI'4Rn'4RJ,4=R|,4=R~'4Rh'4Rj,4=R^,4=RY,4=Ro'4Ry,4ARr,4=R_,4=Rk,4=Ri'4R['4R\,4=RK,4=R{'41L1:P=P{1L<;R{P=PKP{P=P\P{PAP[1L>@R[Q02Pi1L1EP=Pk!sE$_!s+$r!sK$yP[Q03Po1L1FP=PY!sA$^!s+$jP{Q04Ph1L>OQ05P~1L1PP=P|!sD$JP{PmPn1LRzP0PI1L17P=P=P{P{CnFH!s$5g00dSR{1v{<R=g00fjR7g01G[3CRI7C<#`/J:P<P{P<PIP;D_P<%k6R6P<1v6<RIg00<B#kR:g01HaDUP;P<P6!sS$:g01Ig!s9$>g00>mR0g01JnP?Q0<PaDmP@g01L59C=7R@9C{!t;$E!t;&@!t;%!sr-M;!t,4NA!t,%P0g01OHP?Q0@PgDmg01PO%|GRG%52R2g00VUR@1uG2d3t's,]3g00h4!tH$2!tH'F!tH&2!tH42Y!tH4QV!tH-R]!tH/Sd%5DRDP@1uGDd5tG!t?&1Tk!t?$3!t?'P!t?&3!t?4V1!t+$Rg01W7g01X>5{vg01YE,]QP1g01ZL!sr$7!sr%g01[RP<Ai{<7!tw'g01\_9CI:P;D_F^F^3cCl!s+3do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn false false) 40) []).
Definition srX1c := Eval vm_compute in (s_regs (fst (fst rX1c))).
Definition cX1c := Eval vm_compute in (carry (s_log (fst (fst rX1c))) (ax_kn false false) []).
Definition knX1c := Eval vm_compute in (fst (fst cX1c)).
(* [comment removed for export] *)
Definition srX2ic := Eval vm_compute in (sr_upd (sr_upd srX1c (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x714648) 4 (sr_get srX1c 12)] knX1c []).
Definition knX2ic := Eval vm_compute in (fst (fst cX2ic)).
(* [comment removed for export] *)
Definition rX2c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x194528 srX2ic [] knX2ic 40) []).
Definition srX2c := Eval vm_compute in (s_regs (fst (fst rX2c))).
Definition cX2c := Eval vm_compute in (carry (s_log (fst (fst rX2c))) knX2ic []).
Definition knX2c := Eval vm_compute in (fst (fst cX2c)).
(* [comment removed for export] *)
Definition srX3ic := Eval vm_compute in (sr_upd (sr_upd srX2c (ridx 13) (sr_get srX2c 12)) (ridx 15) (ELit 0)).
Definition cX3ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1bdaf0) 8 (sr_get srX2c 14)] knX2c []).
Definition knX3ic := Eval vm_compute in (fst (fst cX3ic)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exX3c := Eval vm_compute in (List.filter (fun K => negb (x3_core K)) knX3ic ++ x3_facts).
Definition srX3c := srX3f.
Definition cX3xc := Eval vm_compute in (carry_keep (fun _ => false) (s_log (fst (fst rX3g))) exX3c []).
Lemma cX3xc_eq : ltac2:(zQ "h21!q3!koa!hgb!r7!s5!kq1!mva!re!kqf!kp5!ju8!r1!kk4!lk5!ng3!kq7!ll3!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$c@2$3@2$3@1$0$2@1$0$1@1$0$4@4$d\0$2$a@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$b$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Bj22Tg00SXj25Tg00bZj30Tg010Fj19Tg00_ej18Tg011Lj47Tg00c7j33Tg00cTj44Tg00:_j36Tg00;9R0#1R1g00e_#1R2'2R3g00<BR4#1R5'2R6g01]eR7'5g00V5V0g00dSR01202g00fjg00h430702#9g01^l%84C7P3P5P1P2A0357R49012A3124C4A3357C4566do"). Qed.
Definition knX3c := Eval vm_compute in (kn_drop_shadow (fst (fst cX3g)) ++ fst (fst cX3xc)).
Lemma x3_facts_c : ltac2:(zQ "h00!q3!koa!s5!kk4!il4!lmd!ngc!kmf!hgb!kq1!r1!r7!kqf!mva!ng3!ks8@2$5@3$3$2@2$7$f$6$4@2$5@3$3$2@2$7$e$6$4@3$3@1$0$1@3$c@1$0$8@1$0$1@3$9@2$b@1$0$8@1$0$1@1$0$2$d@1$a$1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;3p;1p;2p;4g00:_j30Tg0028j12Tg00_ej19Tg006kj21Tg00SXj25Tg015mj44Tg00Ynj23Tg00^Bj28Tg00bZj37Tg00c7j36Tg00<BR0g00<bR1;01R2g00e_R3#2R4%93R3;03R5,121501R6P2P5P61543C4C4g00n`g01`3R6'3=001g01^l/36=001g00;9#2R11814%20g01]e37764=043'1'1do"). Qed.
(* [comment removed for export] *)
Definition srX4ic := Eval vm_compute in (sr_upd (sr_upd srX3c (ridx 6) (sr_get srX3c 10)) (ridx 7) (ELit 0)).
Definition cX4ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1bdaf0) 8 (sr_get srX3c 5)] knX3c []).
Definition knX4ic := Eval vm_compute in (fst (fst cX4ic)).
(* [comment removed for export] *)
Definition rX4c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77f10 srX4ic [] knX4ic 40) []).
Definition srX4c := Eval vm_compute in (s_regs (fst (fst rX4c))).
Definition cX4c := Eval vm_compute in (carry (s_log (fst (fst rX4c))) knX4ic []).
Definition knX4c := Eval vm_compute in (fst (fst cX4c)).

Lemma x_itinerary_clean : ltac2:(zQ "ia0!q3!koa!kq1!kk4!lmd!kp5!r7!hgb!r1!kqf!ijd!s5!ikd!jg6!h9!hh9!lne!lo5!js7!ls7!jp1!lt0!nh6!nhe!kq7!ni6!mk3!mkc!ml2!mla!nie!nj6!nje!kvc!nk7!nl0!nl8!nm1!nma!nn3!nnc!no5@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h6+hpklhc@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h6@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$he@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i0@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i5@1$fZ+nhkmk8N4@2$h1$c@1$fZ@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h7+nnrp4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h7@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$hf@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i2@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i6@1$fZ+hrtqv0N8@2$h1$c@2$ha$i8@3$hb@1$d#5+cKv$h5@2$hc@1$d#5+c@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h8+nnvg4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h8@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i1@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i4@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i7@1$fZ+hrtqv0N8@2$h1$c@2$ha$i9@3$hb@1$d#5+aKv$h5@2$hc@1$d#5+a@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h9$hd@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h9@1$8$1@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i3@1$8$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##5]p;1p;3p;2p;4p;5g00^bj1;Tg0000j11Tg0028j1GTg00_ej1RTg00:_j39Tg001Vj1PTg017Pj1ITg018Wj2@Tg006kj20Tg00SXj2=Tg015mj4HTg00^Bj2NTg00bZj32Tg01?Bj1BTg00c7j37Tg00d4j1:Tg01@Gj5F!t^$Uj1Q!tU$Gj1MTg01AIj2L!s/$lj3KTg01BOj2JTf0R0#;#1p=3%10#1p=4%;0#;p=5%10#Mp=8g00W1R1f1R2;90p=<%1!sG$?!sW$#1#1p=O!s2+!s$'p=>f6R3f5R4f4R5f3R6f2R7P2P0CHCHp=6A7672=950p=AA9672/00p=DA9345!s6''0p=C1020,07p=Eg00>HR7#;R2#1R0#1R6#3#3#4R5!s-%#5#3#8R4/<4g00e_R3#GR8%R3R3;93R9g00WnR:#PR;g01EC#IR<,@:R=;9=R>%32R2#5#5R?#?#5#4!s{$8R@/<@RA%5?#3#O!s8$?/<?RB%17R7#4#>!s$08#I,@:RC=9;CRD%?5#O#?#4#8R5/<5RE1099RF'0RG'0RH,09RI,09RJ,09RK'0RL,0>RM,09RN,09RO,09RP'0RQ'0RR,09RS,09RT'01=14P9PT1=83RTP9PSPTP9PRPTP>PQ1=;=RQPAPP1=1@P9PO!sD$N!s+$M!sJ$LPQPBPK1=1?P9PJ!s@$I!s+$HPTPDPG1=;CPEPF1=15P9P9PTPTCHF6!s$1g00dSRT1NT8!w$$fjR5g01a;32RF728#B/<4P8PTP8PFP3DAP8g00;9#GRF1NF8R4g00<B#GREg01bA32778P3P8g01cG924E97F8P3P;g00>mRCg01dNP<%42!xd+4#3!w'%g00og#:!s$%R2DFP=g01eU9295R=92T!t]$@!t]&=!t]'1f[!t7-8g01ga!tH/PCg01hhP<%;0!y{$5#!y:%3!xH$0%:2!tA,g01io%;7R7#QR=%M6R6g00VUR@1L=6d3K'J,@:g00h4!te$6!te'?!te&6!te+2Y!te2k6!te4l=P<P0P!tG%mD%87R7P@1L=7d5K=!t:$P1g01nK!t<$5!t<%g01[RP8A7T85P3!wa$8g01oQ924EP3DACDFCFC3ECD!s+,do"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1n := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true false) 40) []).
Definition srX1n := Eval vm_compute in (s_regs (fst (fst rX1n))).
Definition cX1n := Eval vm_compute in (carry (s_log (fst (fst rX1n))) (ax_kn true false) []).
Definition knX1n := Eval vm_compute in (fst (fst cX1n)).
(* [comment removed for export] *)
Definition srX2in := Eval vm_compute in (sr_upd (sr_upd srX1n (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2in := Eval vm_compute in (carry [SE (SA (ELit 0) 0x714648) 4 (sr_get srX1n 12)] knX1n []).
Definition knX2in := Eval vm_compute in (fst (fst cX2in)).
(* [comment removed for export] *)
Definition rX2n := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x194528 srX2in [] knX2in 40) []).
Definition srX2n := Eval vm_compute in (s_regs (fst (fst rX2n))).
Definition cX2n := Eval vm_compute in (carry (s_log (fst (fst rX2n))) knX2in []).
Definition knX2n := Eval vm_compute in (fst (fst cX2n)).
(* [comment removed for export] *)
Definition srX3in := Eval vm_compute in (sr_upd (sr_upd srX2n (ridx 13) (sr_get srX2n 12)) (ridx 15) (ELit 0)).
Definition cX3in := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1bdaf0) 8 (sr_get srX2n 14)] knX2n []).
Definition knX3in := Eval vm_compute in (fst (fst cX3in)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exX3n := Eval vm_compute in (List.filter (fun K => negb (x3_core K)) knX3in ++ x3_facts).
Definition srX3n := srX3f.
Definition cX3xn := Eval vm_compute in (carry_keep (fun _ => false) (s_log (fst (fst rX3g))) exX3n []).
Lemma cX3xn_eq : ltac2:(zQ "h21!q3!koa!hgb!r7!s5!kq1!noe!re!kqf!kp5!ju8!r1!kk4!lk5!np7!kq7!ll3!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$c@2$3@2$3@1$0$2@1$0$1@1$0$4@4$d\0$2$a@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$b$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Bj22Tg00SXj25Tg00bZj30Tg010Fj19Tg00_ej18Tg011Lj47Tg00c7j33Tg00cTj44Tg00:_j36Tg00;9R0#1R1g00e_#1R2'2R3g00<BR4#1R5'2R6g020WR7'5g00V5V0g00dSR01202g00fjg00h430702#9g021^%84C7P3P5P1P2A0357R49012A3124C4A3357C4566do"). Qed.
Definition knX3n := Eval vm_compute in (kn_drop_shadow (fst (fst cX3g)) ++ fst (fst cX3xn)).
Lemma x3_facts_n : ltac2:(zQ "h00!q3!koa!s5!kk4!il4!lmd!nq0!kmf!hgb!kq1!r1!r7!kqf!noe!np7!ks8@2$5@3$3$2@2$7$f$6$4@2$5@3$3$2@2$7$e$6$4@3$3@1$0$1@3$c@1$0$8@1$0$1@3$9@2$b@1$0$8@1$0$1@1$0$2$d@1$a$1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;3p;1p;2p;4g00:_j30Tg0028j12Tg00_ej19Tg006kj21Tg00SXj25Tg015mj44Tg00Ynj23Tg00^Bj28Tg00bZj37Tg00c7j36Tg00<BR0g00<bR1;01R2g00e_R3#2R4%93R3;03R5,121501R6P2P5P61543C4C4g00n`g022eR6'3=001g021^/36=001g00;9#2R11814%20g020W37764=043'1'1do"). Qed.
(* [comment removed for export] *)
Definition srX4in := Eval vm_compute in (sr_upd (sr_upd srX3n (ridx 6) (sr_get srX3n 10)) (ridx 7) (ELit 0)).
Definition cX4in := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1bdaf0) 8 (sr_get srX3n 5)] knX3n []).
Definition knX4in := Eval vm_compute in (fst (fst cX4in)).
(* [comment removed for export] *)
Definition rX4n := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77f10 srX4in [] knX4in 40) []).
Definition srX4n := Eval vm_compute in (s_regs (fst (fst rX4n))).
Definition cX4n := Eval vm_compute in (carry (s_log (fst (fst rX4n))) knX4in []).
Definition knX4n := Eval vm_compute in (fst (fst cX4n)).

Lemma x_itinerary_clean2 : ltac2:(zQ "ia0!q3!koa!kq1!kk4!lmd!kp5!r7!hgb!r1!kqf!ijd!s5!ikd!jg6!h9!hh9!lne!lo5!js7!ls7!jp1!lt0!nqa!nr2!kq7!nra!mk3!mkc!ml2!mla!ns2!nsa!nt3!kvc!ntb!nu4!nud!nv5!nve!og7!oh0!oh9@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h6+hpklhc@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h6@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$he@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$hf@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i5@1$fZ+nhkmk8N4@2$h1$c@1$fZ@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h7+nnrp4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h7@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i0@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i2@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i6@1$fZ+hrtqv0N8@2$h1$c@2$ha$i8@3$hb@1$d#5+cKv$h5@2$hc@1$d#5+c@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h8+nnvg4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h8@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i1@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i3@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i7@1$fZ+hrtqv0N8@2$h1$c@2$ha$i9@3$hb@1$d#5+aKv$h5@2$hc@1$d#5+a@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h9$hd@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h9@1$8$1@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i4@1$8$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##5]p;1p;3p;2p;4p;5g00^bj1;Tg0000j11Tg0028j1GTg00_ej1RTg00:_j39Tg001Vj1PTg017Pj1ITg018Wj2@Tg006kj20Tg00SXj2=Tg015mj4HTg00^Bj2NTg00bZj32Tg01?Bj1BTg00c7j37Tg00d4j1:Tg01@Gj5F!t^$Uj1Q!tU$Gj1MTg01AIj2L!s/$lj3KTg01BOj2JTf0R0#;#1p=3%10#1p=4%;0#;p=5%10#Mp=8g00W1R1f1R2;90p=<%1!sG$?!sW$#1#1p=O!s2+!s$'p=>f6R3f5R4f4R5f3R6f2R7P2P0CHCHp=6A7672=950p=AA9672/00p=DA9345!s6''0p=C1020,07p=Eg00>HR7#;R2#1R0#1R6#3#3#4R5!s-%#5#3#8R4/<4g00e_R3#GR8%R3R3;93R9g00WnR:#PR;g01EC#IR<,@:R=;9=R>%32R2#5#5R?#?#5#4!s{$8R@/<@RA%5?#3#O!s8$?/<?RB%17R7#4#>!s$08#I,@:RC=9;CRD%?5#O#?#4#8R5/<5RE1099RF'0RG'0RH,09RI,09RJ,09RK'0RL,0>RM,09RN,09RO,09RP'0RQ'0RR,09RS,09RT'01=14P9PT1=83RTP9PSPTP9PRPTP>PQ1=;=RQPAPP1=1@P9PO!sD$N!s+$M!sJ$LPQPBPK1=1?P9PJ!s@$I!s+$HPTPDPG1=;CPEPF1=15P9P9PTPTCHF6!s$1g00dSRT1NT8!w$$fjR5g023m32RF728#B/<4P8PTP8PFP3DAP8g00;9#GRF1NF8R4g00<B#GREg025332778P3P8g0269924E97F8P3P;g00>mRCg027@P<%42!xd+4#3!w'%g00og#:!s$%R2DFP=g028G9295R=92T!t]$@!t]&=!t]'29M!t7-8g02:S!tH/PCg02;ZP<%;0!y{$5#!y:%3!xH$0%:2!tA,g02<a%;7R7#QR=%M6R6g00VUR@1L=6d3K'J,@:g00h4!te$6!te'?!te&6!te'12Y!te2=h!te4>oP<P0P!tG%@6%87R7P@1L=7d5K=!t:$P1g02A=!t<$5!t<%g01[RP8A7T85P3!wa$8g02BC924EP3DACDFCFC3ECD!s+,do"). Qed.
End FPX1.
(* [comment removed for export] *)
