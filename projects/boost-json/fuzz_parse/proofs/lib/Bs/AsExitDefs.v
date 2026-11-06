(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive LibKnowFrame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import RefExitBase RefStdioDefs AsStdioCall AsPrintfFirst.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AsCarryKeep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsExitDefs () := KReplay.lz_vm "#$:=K47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!sg+4Init9Datatypes6op!sL#!sH>4list00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib=SymExec2Sound4SX2S7know_okC13~~~!t<,5Lists7!s+#Def6Forall00C46Std!sF+4!s+#2In!s=7=!sZ%_f!s,$!tvc9kentry!tx+!t@76filter!vQ25Logic3and!u599!s\%_Inc!trO2Bs:AsExi!v>#s>keep_nonshadow!tr'!tW65proj1!t9`n_drop_!t9/!uj82eq00I!t8O8!w?'3SX26!w9%00!t18!zH-bool00K!sFA1!tW]3env!tT'!}NG3C7!t9,!t296images9AsanUbsan1M?loaded_segments!ul'!y~6Ex!s2#!ye97e!sC$bK!w>d1!y\&!so\9saddr_eqb!sp&5!t}'Arith8PeanoNat3!s&#!sL#!x0<andb!tV]8exp!tU/!t5;9!t5#_prop!#34b<!up+_eq!veV!sy6;!u;'!sx,!vm>6!sO&!}M78eq_ind_r!y9e2!{{&!sod3!sok4!sok5!sok6!sok7!sok8!yV26Z!yW$6BinInt1Z!}B$!sC;!yp&!#97];!#<9%eqb2!#6S2!#9411!{#86!{#%!sB89False!sE#!#8>\5!}t$!#8@4!#9N72!u384True01I!#8|;1Z!#B:=3nat!#<$^4expr!#;~9!#>D%!vE$!tQ4!u3/0!xQ^6kn_su!#6n'!#:D5!#Bt$b!sB7>!sB&!#C@%!#?A9x!#;E8>!#;E%_!s-%!#B1`!ze+!#6r'!#?k<prod!#?k-!#>]<1K!y+?2!z-=!#H@#1K!#<~]ym_state!#=rd8!sr#exec!#<BA3fst!sC=sndK!vpA1K!|3@2I!v+g!|8'!v+^ideco!#IY#!sqb7scrip!#Cd#!sp$!{$^4rX3g!sld5XFUEL!smd6XSTOPS!uKescr!v9e6srX3if!wsc6s!#Ki/!w+_kn!ws+!{YA1C!#:w]_log!~YV2Bs;AsCarryKeep:c!s0#_keep!x>ec!zchcX3xf!smeexX3f!wL8!#Tu,1!#;``!z7,!#7q\!#=x$1!yFB!#Zd&1!t7c!#C-3!#:W53!t3c!#Izc!#C>%1!v{i!#H=V!|6%StdioCall9s!s0#_res!#<_d4s_p!#<[&7!skRDrive5kread!sh&!#aQ?4BvWfK!#atC!#47]6sr_get!#48[!w$+:!w$%call!{rB!#At$2!{%@!#[jP!x[=!#JX'ELinuxProcessSemantics5Riscv5Instr5aluop!#3Y_4rX1f!#7-f!slf5cX2i!smfkn!uJhrX2!v8h2!v8h3!v8j!t\gsr!uKj4!uKj3!uKi3!yLh4!yLh4!uIi4!w#i!smgx_sc!w#h5!sle;AEXIT_ECALL!wtg5!~Bixc!smeexX3!sme!#EA$c!wug1c!w$g!slf!#9V#c!{vh1!v8h2!v8h2!v8h3!v8j!t\gsr!uKj4!uKj3!uKi3!yLh4!yLh4!yLixn!smeexX3!sme!#4`$n!w$g1n!w$g!slf!#4`#n!{%h1!v8h2!v8h2!v8h3!v8j!t\gsr!uKj4!uKj3!uKi3!yLh4!yLh!sl'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nat37Corelib4Init7Decimalja2D0ja2D2ja3Nil37Corelib4Init3Natm0bof_num_uint37Corelib4Init6Numbero0bUIntDecimalhc4listhc4conshc3nilhc4prodhc4pairhc4bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~sc6kentrysc2SAsc4ELitsc4EVarsc5KWordsc3KWrsc4KImghc3appsc6KRange79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~hkb8kn_cells89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsExitDefs4FPX1~~~~~~hq8eax_flush_cellshq8cax_lit_cellshq8dax_lit_cells2hkb6ASP_HIhkb6ASP_LOsc6KAlignsc7scriptssc3SCRsc4exprhc4truesc5saddr08positive3h5LinuxProcessSemantics5Riscv5Instrimd5aluopimd5mulophc4andbhc4negb46Stdlib6ZArith6BinInt1Zir13lebir13ltbhq8ekeep_nonshadow36Stdlib5Lists4Listiu96filter04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~jgc7know_ok69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~jlcfloaded_segments35stdpp9bitvectorbdefinitionsjq92bvhc6optionhq8ekn_drop_shadowsc3envhc5falseir13eqbsc9saddr_eqbsc8expr_eqb46Stdlib5Arith8PeanoNat3Natkh33eqb37Corelib4Init5Logickj52eqhq8bkentry_eqb2iu97existsbiu97forallbhq86kn_subhq8dx3_extra_addrsc8sidecondsc9sym_statehc3fsthq84rX3ghc3sndhq85XFUELhq86XSTOPShq85knX3ghq84scr0hq86srX3ifsc2SSsc6sentrysc8sym_exechq84cX3g79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsCarryKeep~~~~~~lg9acarry_keepsc5s_loghq85cX3xfhq85exX3fkj53andhq86knX3ifsc4s_pchc4Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~lp15kreadkj51Ihq84rX1fhq84rX2fhq84rX4fhq84rX5f79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsStdioCall~~~~~~lva9stdio_ressc6sr_getjq92BVjq94BvWfhq8bAEXIT_ECALLhq84cX1fhq84cX2fhq85cX2ifhq85cX3ifhq84cX4fhq85cX4ifhq84cX5fhq85knX1fhq85knX2fhq85knX3fhq85knX4fhq85srX2fhq85srX3fhq85srX4fhq85x_scflvaastdio_callhq85cX3xchq85exX3chq86knX3ichq84rX1chq84rX2chq84rX4chq84cX1chq84cX2chq85cX2ichq85cX3ichq84cX4chq85cX4ichq85knX1chq85knX2chq85knX3chq85srX2chq85srX3chq85cX3xnhq85exX3nhq86knX3inhq84rX1nhq84rX2nhq84rX4nhq84cX1nhq85cX2inhq84cX2nhq85cX3inhq85cX4inhq84cX4nhq85knX1nhq85knX2nhq85knX3nhq85srX2nhq85srX3n" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition AEXIT : Z := 0x191274.
Definition AEXIT_ECALL : Z := 0x190f80.
Definition XFUEL : nat := 20000.
Definition XSTOPS : ltac2:(zQ "20!q3!h9@1$0$1") := ltac2:(zQ "30!h9!qa!r1@3$1$0+hporm0@1$2$0").

Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x6f1318%Z | 10 => EVar 2
                          | _ => EVar (8 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition ax_lit_cells : ltac2:(zQ "40!r7!h9!q3!j4@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!j4!re!qa!r1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhlo8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhlqbN1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjmcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn8N8+nhhjo0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo8N8+hphii0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhko8N8+qujhc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikvgi0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrprh0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkho0N8+hrkho0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpqs0N8+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrsptcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrthn8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqqj0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqpp0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjo0N8+hqinq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikuti0N8+vvvvvvvvvvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhri0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmupcN4+vvvvvvvf@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition ax_lit_cells2 : ltac2:(zQ "40!r7!h9!q3!j4@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!j4!re!qa!r1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhlo8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhlqbN1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjmcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjn8N8+nhhjo0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjo8N8+hphii0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhko8N8+qujhc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhjp0N8+hphii0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhkp0N8+rusu4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+muvnt4N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikvgi0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrprh0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkho0N8+hrkho0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpqs0N8+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrsptcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrthn8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqqj0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrqpp0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjo0N8+hqinq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikuti0N8+vvvvvvvvvvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nhhri0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmupcN4+vvvvvvvf@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition ax_flush_cells : ltac2:(zQ "40!r7!h9!q3!j4@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!j4!re!qa!r1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuk8N8+nhhrj8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmul8N8+hporm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmum8N8+nhhrj8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmun0N8+kg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmuo8N4+1@1$5@2$1@2$1$0$2$0").

Definition ax_kn : ltac2:(zQ "30!s5!q3!hgb>3two$0>2fl$0@1$1$2") := ltac2:(zQ "h71!hgb!qa!hh4!hh9!hi0!hi7!hif!s5!hj5!hjc!r1!hk2!q3!r7!h9!hpc!j4!hud!hvf!igf!ii0!iia!ij4&@3$5@2$2@1$3Z+hrmuj8N8@1$4N4\3two$7\2fl$7@3$9$0@3$1$0@2$h6@1$4N0+h0@3$1$0@3$b@1$4N0$h5$h4@3$1$0@2$6@2$2@1$4N0-hp0+hp0@3$1$0@3$b@1$4N1+1+nvvvvvvf@3$1$0@2$8+hggg0+mngg0@3$1$0@2$8+hqqgg0+hrkgg0@3$1$0@2$8+hrmug8+hrmuh0@3$1$0@2$8+hrmuv8+hrpqs0@3$1$0@3$5@2$2@1$3Z+mvhin0N4@1$4N1@3$1$0@3$5@2$2@1$3Z+nhhjl8N8@1$4N3@3$1$0@3$5@2$2@1$3Z+hrmtk8N8@1$4N5@3$1$0@3$5@2$2@1$3Z+hrmtl8N8@1$4N5@3$1$0@3$5@2$2@1$3Z+hrmti8N8@1$4N6@3$1$0@3$5@2$2@1$3Z+hrmtj0N8@1$4N6@3$1$0@3$5@2$2@1$3Z+hrmuh8N8@1$4N7@3$1$0@3$5@2$2@1$3Z+hrmui0N8@1$4N7@3$1$0@2$6@2$2@1$3Z+nhhjm8+i0@3$1$0@2$6@2$2@1$3Z+nhhlo8+4@3$1$0@2$6@2$2@1$3Z+hrprh0+1@3$1$0@2$6@2$2@1$3Z+hrpqs0+8@3$1$0@2$6@2$2@1$3Z+hrqqj0+8@3$1$0@2$6@2$2@1$3Z+muvot0+h0@3$1$0@2$6@2$2@1$3Z+nvvvqgg0+ugmg0@3$1$0@2$6@2$2@1$3Z+hrmuh0+u8@1$a$0@3$9$0M7\2fl$7@1$c$0^1@3$9$0@3$1$0~0@3$1$0@3$b@1$4N4+nhhrj9+nhhvj8@1$a$0@1$f$h1@3$1$0~0@3$1$0@3$5@2$2@1$3Z+hrmuk8N8@1$4N4@1$a$0@1$fM7\3two$7@1$c@2$d@2$d$e$h0$e^2$h3$h2").

Definition scr0 : ltac2:(zQ "10!ijd$0") := ltac2:(zQ "40!r1!s5!ik7!ikd@3$2@1$0$1@1$0$3@1$0$1").

(* [comment removed for export] *)
Definition keep_nonshadow : ltac2:(zQ "20!s5!hgb>1K$1$0") := ltac2:(zQ "e0!ikd!il4!h9!ilb!j4!s5!hgb!im3!ip1!ipa!iq3!iqa!is9!it0\1K$6M6\1K$6$5^1\2a0$3\1w$4\1v$0M3\2a0$3$5^3\6a_base$0\1a$2M0\6a_base$0$5^2\1z$2M2\1z$2$5^1@1$b@2$a@2$c+nvvvggg0^2@2$d^2+pggggggg0\1p$7$1\1p$7$1\1n$4$1\2op$8\2a1$0\1b$0$1\2op$8\2a1$0\1b$0$1\2op$9\2a1$0\1b$0$1\2op$9\2a1$0\1b$0$1\2sx$5\2lo$4\1n$4\1e$0$1\2sx$5\1k$4\1i$2\1n$4$1\1a$3\1n$0$1\1a$3\1n$0\1k$4$1\2lo$2\2hi$2$1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\1a$3\1n$2$1\2a1$3\2n1$2\2a2$3\2n2$2$1").
Definition kn_drop_shadow : ltac2:(zQ "20!q3!hgb>2kn@1$0$1@1$0$1") := ltac2:(zQ "40!hgb!q3!it7!ivc\2kn@1$1$0@3$3$0$2^1").
Lemma know_ok_drop_shadow : ltac2:(zQ "90!jg6!jl1!jp6!js6!q3!jsc!jt5!ju7!hgb>1E$7>1M>0@1$3@1$0#k0@1$5@1$3@1$0#8>2kn@1$4$8>0@4$1$2^3^2^1@4$1$2^4^3@1$6^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##0[h01xh11Ah21lh32HKh42H0h51Ph61fh71Eh81Hh91Kh:1Mh;2_Hh<2knp;1p;4p;3p;2p;6g0000j12Tg000Uj1>Tg0013j1<!s/$Vj1?Tg0028j1:!s/$Xj4=Tg003fj34Tg004Gj30!s/$^j3;Tg005@j38j47Tg006Pj35!s/$kR0j26Tg007Fj4C!s/$dR1j19Tg0094j6B!s/$Oj1ATg00:_j3@Tg00;9R2f1R3f0R430p=3g00<BR5g00<b7@4p=1g00=Bg00>H#2#2#2R6!s-%#>#<%>6#<#?[%:2g00>mR6f2R7P3P4C=g00@8p4p710R8p-0\4R9%:3R:P0A4734f3R;f4R<?047P<P3O1[]0R=[A0;43P;!s7$^07A4;73[R>A4<;7\=A;734P4n20010!s#$12!s-%0W2W5W1P>^2:^59^18P4P2A86<;A5217A521;,34g00@U!tf'P5\4R5%:7R9P0A5;7490;3A0<73P;P7O1#1'6[R:A0;34P7P3!s8%A5<;390<7R>[f5R=?0;7P<P;!sD%\>P;P!u|%CP3!ty9X03W6W1P:^29^03^65!u#&P1P7P=P3O5137=%97#1'6P0f6R0,3;%9;#1P6f9R1f8R8P<C7P413=8%90#1f<R0f;R8586R=f:R<5421340P6f?f>R5P3C7[^02[1348P6P5f=!s;,A8650=428[A;2=<P1f7P3EBW;W3P3P4O2!u?7b3b4W3X92O4b4P6P;P7%A3C=eW8W<W:W7o"). Qed.

(* [comment removed for export] *)
Definition kentry_eqb2 : ltac2:(zQ "20!hgb!s5>1x$0>1y$0$1") := ltac2:(zQ "c1!h9!jud!ilb!ikd!hgb!j4!iq3!s5!jv5!jvc!kg8!kie&\2a1$2\2n1$0\2a2$2\2n2$0$1\1x$4\1y$4M4\1x$4$7^2\1a$2\1w$5\1v$3M4\1y$4$7^4\2a'$2\2w'$5\2v'$3@2$6@2$6@2$9^6^3@2$b^5^2@2$a^4^1\2a0$2\1n$3$1\2a0$2\1n$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a0$2\1n$0$1~0\1a$2\1n$3M4\1y$4$7^3\2a0$2\1w$5\1v$3$1\2a'$2\2n'$3@2$6@2$9^4^2@2$a^3^1\2a0$2\2n0$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a0$2\2n0$0$1~0\1a$2\1n$3\1k$5M4\1y$4$7^4\2a0$2\1w$5\1v$3$1\2a0$2\2n0$3$1\2a'$2\2n'$3\2k'$5@2$6@2$6@2$9^6^3@2$a^5^2@2$b^4^1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a0$2\2n0$0$1~0\2lo$0\2hi$0M4\1y$4$7^3\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\3lo'$0\3hi'$0@2$6@2$8^4^2@2$8^3^1\1e$3\1m$0$1\1e$3\3lo0$0\3hi0$0$1\1a$2\1n$0$1~0\1e$3\1m$0M4\1y$4$7^3\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\2lo$0\2hi$0$1\2e'$3\2m'$0@2$6@2$a^4^2@2$8^3^1\2e0$3\2lo$0\2hi$0$1\1a$2\1n$0$1~0\1e$3\2lo$0\2hi$0M4\1y$4$7^4\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\3lo0$0\3hi0$0$1\2e0$3\1m$0$1\2e'$3\3lo'$0\3hi'$0@2$6@2$6@2$a^6^3@2$8^5^2@2$8^4^1\1a$2\1n$0$1~0\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$3$1\2a0$2\2n0$3$1\2a0$2\2n0$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\2a'$2\2n'$0@2$6@2$9^4^2@2$8^3^1~0\2a1$2\2n1$0\2a2$2\2n2$0M4\1y$4$7^5\1a$2\1w$5\1v$3$1\1a$2\1n$3$1\1a$2\1n$3\1k$5$1\2lo$0\2hi$0$1\1e$3\1m$0$1\1e$3\2lo$0\2hi$0$1\1a$2\1n$0$1\2b1$2\2m1$0\2b2$2\2m2$0@2$6@2$6@2$6@2$9^8^4@2$8^7^3@2$9^6^2@2$8^5^1").
Lemma kentry_eqb2_eq : ltac2:(zQ "50!hgb!kk9!s5!il4!kkf>1x$0>1y$0>0@3$1$2@2$4^2^1$3@3$1$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##oxp'0h01Hh12H0h21ni001nh31ai011ah42a0h51ei021eh62hii032hih72loi042loh81mi051mh92H1h:2n0h;2a1i062a1h<2a2i072a2h=1ki081kh>2n1i092n1h?2n2i0:2n2h@1vi0;1vhA1wi0<1whB2H2hC2e0hD3hi0hE3lo0hF2H3hG2a3hH2e1hI2k0hJ2m0hK2n3hL2v0hM2w0hN1xhO1yi0=1bp%0p;3p;2p;6p;4g00A1j39Tg00B:j28Tg00CDj2G!s/$dj2ETg00DBj2;Tg00EKj3<!s/$nj3LTg00:_j34Tg00GAj3OTg00HSj2UTg00I6j6F!s/$Tj2CTg00J]j3:Tg00Kfj2>Tg00Loj2?Tg00N8j37Tg00OAj2=Tg00PJj46Tg00QSj25Tg006kR0j2MTg00R0j2T!s/$Pj2STg00S]j2RTg00T7j6Q!s/$Sj2PTg00<BR1f1R2f0R3'Sg00<bR434p=0g00;9R5?423p=2A4134p=3!s-$,M2p=A1E23=414p=B18!s1'H1R53p=Jg00U2R6f4R7f3R8f2R9P2P3EFp=KP1g00V:P2g00VZP4P3EQp=NA4592/P3p=115!sv'@g00W6R4!tU%DP4P7P8P!sr+I1023P510391228]0P9g00WTR:g00X3R;A9923R<f7R='0P5A9789R>/03f5R??978R@/22]0f8RAf9RB?9A=RC/0<f:RD/88RE1GB9RF'ERG1;A2RH;<3%3G/AHP0f;RH/87RG1GD8'B1;B9RI#3f<RJ?9HD/2@P3f=R@f6RK'8RL1GJ?RM'B1;J?RN#3f?RO/8ARPf>RQ/G=RR;<2%3PRS/ARP0f@RR/HBRT1GOA#3fARU?9RORVA9DBA'2P3fBRW/HHRX1GWH#3fDRY?L@2RZA46Y@R[fCR\?OJKA4;\JP01G23#3A4:92[R]A4:231G92#3R^[A4:89\^1U23P2n20010!s#$12!s-%0X8:X2:R^P]^8:^2:R]P3fFR_POP8O3A4:_OPUfHR`fGRa593A9WURRb'2X36P:PRA9W3a/2bXA:P;POA9WU3/2bX@;%JVP_P9EFPaP3EFP`P8DKb9bBb1b0W9W0P2P3O!tc8b0W1!sFB0XL;XM:X46!yM%O3A9=K?RV1C23Rb'0P1p-0P3g00Y:Rcg00YWn0110=000!sn$RdX51/N3RePc1C89Rf=1C3b1W0X2;X46!tM%A:923Rg,0CPePcA9HDBRhA:789Ri;1!sU%=:!sX&!tX&1>23Rj,0VPePc1>89Rk!t%+64X74!t%%1?23Rl,0VPdXC!tX$mPc1?89Rn!sU+84X5;!tX&7923Ro,0CPmPcA7789Rp=1h!s~-X5;!tR+=23Rq!tR'=89RV!uU,4!uU+!}+'C6RC,0h!uZ%@JHP?!}H%C6Rh!u]'?4X<6X>4X;6!s]'O4!vr$800083110110<10;20!s1$03!s-&10820104103201021053!s-%!s9'11004010610910710:P3O1W0W@WAX3!vx,0b?P510f31C78Rr!~C$PK1CA=Rs/0<!uc$CDBRt?1>!u+%@;XA!y=/1CK?Ru/0b18=9Rv1;K2Rw!~\$vRx/AwP01HA8S001;=9Rw#3Ry1CBARz/2rP31HD?Rr1;D?#3R{ALJ=2S01A46J=R|AOJ=2R}A4;J=R~PB1C3Q/2tX36P;PA1CD3/2tX2;%JzP@!{z$QP2DK!{v$!{VE:!zS,10sg!wq$1ti!zA+:!zA00uj!sH%sk!z750ul!yZ$1sn!y}410so!sC%tp!yq:0uq!t&&V!sH%:!yg,10t!|8$1CJH?!z['!yPC0!yPvX2;X3!tc+g=P510i3A:?78Rt!yN%AA:B!yO-A:HDBRu!yP<A:=K?Rz/0b!ut&f!ut&!w_11EEIRI1GA2RE!yn$I/AEP01;D8RE,BG%3FA:JHD/2tP31BLN%3M1;Q=RM=<P21ASMP0PT1;OART#3RMA:URORSA:!#8l%1;WH#3RPPZP[AOY@2R[A4;Y@RZP^P]P3fER]PQPAO3A4:]QPUA:3`aA:WURR^!#7^$;PRA:W3a/2^X2;P:POA:WU3/2^X=:%JSP_!z\$aP9!#7^'1bBb9b0W9X0X!#7_aI!zj4z!zj?z!zjGu!zj<z!zj?u!zj$A:@!zka1!zkd!#99$!#5?-j?P510k31>78Ru!#5?&>!zn-1>DBRz!zm2!si->K?RX!zl4!{}0!#3M&zi!#:h-!tU/Xj15=9RS15K2R^!{6$SRS%3^RN'MP01@A8PS1>BA/2uP31@D?RuP01@231D92[RL1D231@92Rt[1D89\t1T!#?r<4X24RtPL^84^24RLP3PJP=P2O31DJ=PtPLP3POPDP7O31DODPH1>3R1>JHRF'2X74PD1>J3/2FX641>HD#JPOP9DIPRP3DIb0b9b1b9X1u!zdDD4XE!zB+X!zBGz!zB&!s`$!zB0X!zB224!wJ-z!zB%1F!#6'g1!z>Y!}$0l!z9$n31?78RF!z9'?A=Rz/0<PmPc1?DBRs!z9=?!z9'!v7%!z97zg!vq&!z9>!se&!~t7XlA<w^31MyNP01;A8#3PS1?BA/2FP3P}P~!yD&@PAP9O3R~1D@AR}P;PD1?3O1?HD!yJ$5;PB1?H!yJ$84%JsPQP3DIPOP9EFb1b9b0X1uX0{!yFBJ4XC!y%+zoPdXH1/N3R1!u[$!#4M/C!y11!u[%!y17sC!w3%!#<9~!y4G!{U0o=P510p3A7?78Rs!#<9&7B!y6-A7HDBRX!y7<A7=K?Rd!y8IX!y8<d!y82!}j0dlP!wB$z!}j,!wg/15B9R1,EERE15A2R{;<3%3E/A{P01;H715D8'B%31A7JHD/2sP31;@K15J?Rs'B%3s15Q=Rs=<T21AMsP01;RB#31@OAA7UROA7!#=G&@WHP[PZ!zO&YP@P=O31DY@!s8&aPR!#5#$aRP;PWfIRZ=73`A7\WUR[!zb%UA7\3`/2[X74PRA7\W3/2[X64A7WUR#JPaP9DIP`!zz$ZP7EF!#N%%B!#=K$P!#=KU1!#5e2!zx0d!zx?X!#Kk%@!zy|1!#5/M!#73/q?P510V31=78RX!#54&=!z|'ePc1=DBRd!#J`<=K?RP!#<G'z!#D56z!#<G%d!#Hn;P!#A&%!#547P!#9f%z!#9f6z!#9f%d!#A&;PqA<v^31MxNP0Q00PS1=BA/2XP3Q01P|!z6$~P}PD1=3O1=HDR}!#DH$B1=H3/2}X24%Jd!#5a+DK!#5a,r!#KpB!#BA-d!#J,$=!#4r~!xwG!z]0CBP510h3PK!#RG$C6Rh!xx%DPDPBPAP=C6Rd!x~&PJPHPDPBC6R<!#5%;PAP=PKP?C6R>!y2+d!#5-6d!y2&<!#5-;>!y2&d!y27>!y2&d!y27d!y2&<!y2<>!#?r%d!}m7<C18@715J8'E18H9'ER<15D2RC;<3%3</ACP018Q?RC15@7'E18J8'B1@H9POPQP@PJC6/2hP318R=R=15OK'E/BC1@Q?18WB15UA'ERC?<=2%3C/A=P018\D15WB'B1HUAPYP\PWPUC6!w;%PAC6'2P318]J15YH'B1HYH18aQRH15_@R];<2%3H/A]P01H`O1@aQPZP`PaP_C6R0PR!ti%!sm%fJRQ/HU1@QUALQU?A46QUfMRU?LY9A46UY!|'$3fLRUP\P@O31DU\!s:&PRLPaP?O31DLaPZP3fRRtfQRUPLC6P!tD&C6R\'2X;6P`PQP3P!sC$/2\X>4Pa!sK$3!s8'<6P_!s]&3!s8%?4%J0f!#F1$LP?DKPU!}9$tP7DKbBbFb1bFb0b9WB!#7YA9!sFB!#8ADK4XG6!~'&!}]x1!}]6!#\SM1!#N<4!#F|&1!#8s41!tC>O5XN5o"). Qed.
Definition kn_sub : ltac2:(zQ "30!q3!hgb!s5>1a@1$0$1>1b@1$0$1$2") := ltac2:(zQ "50!hgb!q3!kkf!kle!km9\1a@1$1$0\1b@1$1$0@3$4$0\1K$0@3$3$0@1$2^1^2^2").
Lemma kn_sub_ok : ltac2:(zQ "c0!q3!jg6!hgb!jl1!jp6!js6!s5!jsc!il4!kk9!kn4!ju7>1E$b>1M>0@1$5@1$1#k0@1$7@1$5@1$1#8>1a@1$0$2>1b@1$0$2>0@3$9$6@2$a^2^1$8>0@4$3$4^5^4^2@4$3$4^6^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##4Lp'0h01xi001xh11Kh21Ah31lh41Hh53HK'h62HXh73Heqh82K'h91Ph:1fh;1Eh<2HKh=3HKah>2Hsh?1Mh@1ahA1bp;1p;2p;4p;3p;6p;7g0000j14Tg000Uj1?Tg0013j1=!s/$Vj1DTg0028j1CTg00Z3j2I!s8$Xj4<Tg003fj37Tg004Gj38!s/$^j3;Tg005@j3:j46Tg00RPj1Bj25Tg00@UR0j33Tg00[;j3@!s/$Wj3HTg0094j6>Tg006kR1j22Tg00\:R2j29!s1$Tj3GTg00]7j3FTg00:_j3ATg00T7j7ETg00<BR3f0R4g00<b3Ap=0g00;9R5f1R6;84p=1g00=Bg00>H#4#4#4R7!s-%#?#=%?7#=#D[%C5R71I64#0g00>mR8f4R9f3R:P6C<g00@8p4p710R;p-0\4R<%C6R=P1f2R>?764A894>R?P9P6O1[^0:R@[A8:46RAP:!s:&>A7:>6[RBA79:>\@A;>64P4n20010!s#$12!s-%0W3W9W2PB^3=^9<^2;P4P5f6R;f5R<5:8P9114<%B4RB=35;X15R@=@5;#0f8RC,14RDf9RE935BX15P6O1#0[^05[f7RF,14A35BC!s@0A35BFX15=@5F#0[AH5@;P9P6P4E>P@!sN%P0!u{&0P3\4R3P1A3>64#0P:P4O1#0,2?X0:,9:[R?P>!s:'AX0>,9>A3:>6#0RA[A8<4:P9!sF%'2X09,99\AAG>64P6!v-7X3=W:W2P?^3=^:3^20P4P5%B:PFP6O41594#0,2DX05,95P2P5114E15<4!t/%5P8f<R2f;RDP<C6P4114D15F!sE$P1116215C6#0P8f@RCf?R1PEC6P4f>RE,1:15D9#0AF2<4AA52<P5f=R2fBRD,14P8fFRFfER0P1C6]5X85fA,12fDR29:80R1=75D1142P8fHfGR2P6C6!wU%CR3!sh$P2PF!s<'A:8F0=753[A;51DPCPEP4E>W5P;P4P>FEb7W7W5P6P4O2!yT84X8!sE8!s0%b6b4b6W=X15O4b4P8P<P9P:C<eW<W>XA7W@W?W;o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true true) 40) []).
Definition srX1f := Eval vm_compute in (s_regs (fst (fst rX1f))).
Definition cX1f := Eval vm_compute in (carry (s_log (fst (fst rX1f))) (ax_kn true true) []).
Definition knX1f := Eval vm_compute in (fst (fst cX1f)).
(* [comment removed for export] *)
Definition srX2if := Eval vm_compute in (sr_upd (sr_upd srX1f (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x711588) 4 (sr_get srX1f 12)] knX1f []).
Definition knX2if := Eval vm_compute in (fst (fst cX2if)).
(* [comment removed for export] *)
Definition rX2f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x1912a0 srX2if [] knX2if 40) []).
Definition srX2f := Eval vm_compute in (s_regs (fst (fst rX2f))).
Definition cX2f := Eval vm_compute in (carry (s_log (fst (fst rX2f))) knX2if []).
Definition knX2f := Eval vm_compute in (fst (fst cX2f)).
(* [comment removed for export] *)
Definition srX3if := Eval vm_compute in (sr_upd (sr_upd srX2f (ridx 13) (sr_get srX2f 12)) (ridx 15) (ELit 0)).
Definition cX3if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1baa30) 8 (sr_get srX2f 14)] knX2f []).
Definition knX3if := Eval vm_compute in (fst (fst cX3if)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x3_extra_addr : ltac2:(zQ "20!s5!h9>1a$1$0") := ltac2:(zQ "50!h9!qa!r1!kle!jv5\1a$0@3$3$0@1$4^1@3$1$0+hrmuk8@3$1$0+hrmul8@3$1$0+hrmum8@3$1$0+hrmun0@3$1$0+hrmuo8@3$1$0+muvnt4@3$1$0+nhhjn0@3$1$0+nhhjp0@3$1$0+nhhkp0@1$2$0").
Definition x3_core : ltac2:(zQ "20!s5!hgb>1K$1$0") := ltac2:(zQ "d0!ikd!j4!il4!h9!s5!ilb!ip1!ipa!hgb!im3!jud!iqa!kne\1K$8M8\1K$8$4^1\2a0$5\1w$1\1v$0M5\2a0$5$4^3\6a_base$0\1a$3M0\6a_base$0$4^2\1z$3M3\1z$3$4^1@1$b@1$c^2\1p$9$2\1p$9$2\1n$1$2\2op$6\2a1$0\1b$0$2\2op$6\2a1$0\1b$0$2\2op$7\2a1$0\1b$0$2\2op$7\2a1$0\1b$0$2\2sx$4\2lo$1\1n$1\1e$0$2\2sx$4\1k$1\1i$3\1n$1$2\1a$5\1n$0$2\1a$5\1n$0\1k$1$2\2lo$3\2hi$3$2\1e$0\1m$3$2\1e$0\2lo$3\2hi$3M0\1e$0$4^3\1z$3$2\1n$1M1\1n$1$4^1$2\2n0$1M1\2n0$1$4^1$2\2n1$1M1\2n1$1$4^1$2\2n2$1M1\2n2$1$4^1$2\2n3$1M1\2n3$1$4^1$a\2n4$1$2\2op$6\1a$0\1b$0$2\2op$6\1a$0\1b$0$2\2op$7\1a$0\1b$0$2\2op$7\1a$0\1b$0$2\2sx$4\3lo0$1\1n$1\2e0$0$2\2sx$4\1k$1\1i$3\1n$1$2\1a$5\1n$3$2\2a1$5\2n1$3\2a2$5\2n2$3$2").
Definition knX3g := Eval vm_compute in (List.filter x3_core knX3if).
(* [comment removed for export] *)
Definition x3_fact : ltac2:(zQ "20!s5!hgb>1K$1$0") := ltac2:(zQ "80!h9!ilb!jud!ikd!il4!hgb!j4!s5\1K$5M5\1K$5$7^1\1a$1\1w$6\1v$3$2\1a$1\1n$3$2\1a$1\1n$3\1k$6$2\2lo$0\2hi$0$2\1e$3\1m$0$4\1e$3\2lo$0\2hi$0$4\1a$1\1n$0$2\2a1$1\2n1$0\2a2$1\2n2$0$4").
Definition x3_facts := Eval vm_compute in (List.filter x3_fact knX3g).
Definition exX3f := Eval vm_compute in (List.filter (fun K => negb (x3_core K)) knX3if ++ x3_facts).
Definition rX3g := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77b40 srX3if [] knX3g 40) []).
Lemma rX3g_eq : ltac2:(zQ "h50!kof!q3!kpa!r7!ijd!kq6!kqc!r1!re!kr4!il4!kk9!kra!ks3!ksd!kt6!kte!ku8!kud!kv6!jp6@3$b@2$3@2$3$2@1$1$0$4@7$h3$h4$c$a$d$f@5$h1+nnrk0$h0@1$7$h2$eNi8@1$7$0@4$8@2$3$2@1$1$0$4@4$8$2@1$1$0@3$5$2@1$1$0@3$5@2$3$2@1$1$0$4$6@3$9$2@1$1$0@3$5@2$3$2@1$1$0$4$6@3$9@2$3$2@1$1$0$4$6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##'#p;1p;2p;5p;7p;3p;4g0028j1>Tg00^Gj28Tg00S]j2;!s8$gj10Tg0000j11Tg00_Lj1<!s/$jj17Tg00`Jj5:Tg00aVj79Tg00b_j34Tg00c<j36!s/$Yj45Tg00:_j3=Tg00d9j12Tf0#2!s$1p=3g00dXR0g00edR1#>R2'8R3g00foR4'8R5g00h9R6';g00>mg00i?g00<bg00jFg00kNg00>H#0#0#1!s+$!s0,1!s&$!s$,<g00lTg00m\#7g00neg00ol#3!s$'D:%71F9P3P4P0P2A4346R19402A6021C5A6346C55=5do"). Qed.
Definition srX3f := Eval vm_compute in (s_regs (fst (fst rX3g))).
Definition cX3g := Eval vm_compute in (carry_keep keep_nonshadow (s_log (fst (fst rX3g))) knX3g []).
Lemma cX3g_eq : ltac2:(zQ "h21!q3!kof!hgb!r7!s5!kq6!lg1!re!kr4!kpa!r1!kk9!lka!it7!ksd!kqc!ll8!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$b@2$3@2$3@1$0$2@1$0$1@1$0$4@4$c$d@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$a$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Gj22Tg00S]j25Tg00b_j30Tg010Kj19Tg00_jj18Tg011Qj47Tg00c<j33Tg00cYj44Tg00:_j36Tg00;9#1R0g00ed#1R1'2R2g00<BR3#1R4'2R5g012^R6'5g007dg00dXR71271g00fog00h930701#9g00ne%83C7P2P4P0P1A0246R39001A3013C4A3246C4565do"). Qed.
Definition cX3xf := Eval vm_compute in (carry_keep (fun _ => false) (s_log (fst (fst rX3g))) exX3f []).
Lemma cX3xf_eq : ltac2:(zQ "h21!q3!kof!hgb!r7!s5!kq6!lm0!re!kr4!kpa!jud!r1!kk9!lka!lm9!kqc!ll8!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$c@2$3@2$3@1$0$2@1$0$1@1$0$4@4$d\0$2$a@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$b$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Gj22Tg00S]j25Tg00b_j30Tg010Kj19Tg00_jj18Tg011Qj47Tg00c<j33Tg00cYj44Tg00:_j36Tg00;9R0#1R1g00ed#1R2'2R3g00<BR4#1R5'2R6g013dR7'5g00V:V0g00dXR01202g00fog00h930702#9g014k%84C7P3P5P1P2A0357R49012A3124C4A3357C4566do"). Qed.
Definition knX3f := Eval vm_compute in (kn_drop_shadow (fst (fst cX3g)) ++ fst (fst cX3xf)).
Lemma x3_facts_f : ltac2:(zQ "h00!q3!kof!s5!kk9!il4!ln2!ln9!kn4!hgb!kq6!r1!r7!kr4!lm0!lm9!ksd@2$5@3$3$2@2$7$f$6$4@2$5@3$3$2@2$7$e$6$4@3$3@1$0$1@3$c@1$0$8@1$0$1@3$9@2$b@1$0$8@1$0$1@1$0$2$d@1$a$1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;3p;1p;2p;4g00:_j30Tg0028j12Tg00_jj19Tg006kj21Tg00S]j25Tg0162j44Tg00Z3j23Tg00^Gj28Tg00b_j37Tg00c<j36Tg00<BR0g00<bR1;01R2g00edR3#2R4%93R3;03R5,121501R6P2P5P61543C4C4g00neg016MR6'3=001g014k/36=001g00;9#2R11814%20g013d37764=043'1'1do"). Qed.
(* [comment removed for export] *)
Definition srX4if := Eval vm_compute in (sr_upd (sr_upd srX3f (ridx 6) (sr_get srX3f 10)) (ridx 7) (ELit 0)).
Definition cX4if := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1baa30) 8 (sr_get srX3f 5)] knX3f []).
Definition knX4if := Eval vm_compute in (fst (fst cX4if)).
(* [comment removed for export] *)
Definition rX4f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77eb0 srX4if [] knX4if 40) []).
Definition srX4f := Eval vm_compute in (s_regs (fst (fst rX4f))).
Definition cX4f := Eval vm_compute in (carry (s_log (fst (fst rX4f))) knX4if []).
Definition knX4f := Eval vm_compute in (fst (fst cX4f)).
(* [comment removed for export] *)
Definition x_scf : stdio_res := Eval vm_compute in
  (match stdio_call 40 srX4f knX4f with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
Definition rX5f := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS (sc_ret x_scf) (sc_sr x_scf) [] (sc_kn x_scf) 72) []).
Definition cX5f := Eval vm_compute in (carry (s_log (fst (fst rX5f))) (sc_kn x_scf) []).

Lemma x_itinerary_flush : ltac2:(zQ "j10!q3!kof!kq6!kk9!ln2!kpa!r7!hgb!r1!kr4!ijd!s5!ikd!h9!lo3!loa!jsc!jg6!hh9!lsc!jp6!lt5!lta!lu2!kqc!lua!lv2!mjb!mk8!ml1!ml7!mlf!mme!mn6!mne!lg1!mo7!mp0!mp8!mq1!mq9!mr2!mrb!ms4!msd!mt6!mtf!mu8!mv1@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h6+hphip4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h6@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i0@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i2@1$8$1@2$4@3$3@1$h0$c@5$h3$h4$i8@1$h2Z+nhhlo8N4@2$f$c@1$h2Z@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h7+nnrj4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h7@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i1@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i4@1$8$1@2$4@3$3@1$h0$c@5$h3$h4$i9@1$h2Z+hrqqj0N8@2$f$c@2$hc$ic@3$hd@1$h1#5+cKv$h5@2$he@1$h1#5+c@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h8+nnuq4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h8@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i3@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i6@1$8$1@2$4@3$3@1$h0$c@5$h3$h4$ia@1$h2Z+hrqqj0N8@2$f$c@2$hc$id@3$hd@1$h1#5+aKv$h5@2$he@1$h1#5+a@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h9+hporm0@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h9@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i5@1$8$1@2$4@3$3@1$h0$hb@3$j0Ni8$ie$ib@2$f$hb$if@2$4@3$3$d@1$e@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$ha$hf@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$ha@1$8$1@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i7@1$8$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##U}p%0p&0p;1p;3p;2p;4p;<p;5g00^gj11Tg0000j10Tg0028j1nTg00_jj1lTg00:_j3GTg001Vj1sTg017Uj1BTg018\j2X!sS$Lj15Tg00d9j12Tg019>j17Tg01:Ej1b!s/$cj3zTg01;jj2>Tg01=2k403Tg00Lok202Tg00N8j3pTg00Kfj2eTg01>9l<~Tg006kj2!sT$S]j2JTg0162j4oTg00^Gj2wTg00b_j3CTg01?Gj1^Tg01@Lj5m!uY$Uj1}Tg01ANj2vTg01B1j3u!s/$Tj2tTg01C[j3|Tg00c<j3kTg01Dhj3=Tg00A1j3OTg00OAj2{Tf0R0#!s$$p=P%00#0#1#0p=[%1!s:$8%00#5p=dg00W6R1f1R2;G0p=I%10#1#1p=i%0!s0$#0p=`!s2$p=4!sq%!si$<!s2$p=@!s:+!s$'p=E%50#Bp=K!st%!s:$N!sN'5p=;!s>$p=6!t]$!sF%:!tH&#1p=S!s2'0p=c!sJ&p=W!sT'1p=U%20#2p=r!s-$#2#2p=M!t0%5#Bp=Rg00X3R3%72;=0p=af2R4#7%72==305=3p=QA=3209=34p=T%b0,>2p=q!ul%0p>04%5!s:%y!s:&#0p=g!t2&!s?$f!u%+!s$'p=_f3R5/>4?O20p=x%10#5p>01g00;9R6?=20p>00A=6209=64p=Zf4R7%55'>?O42==60p=9%05!vm&5,>7!s?,A%1!s?9?f6R8f5R9;O7AO5!s=%5=6p=Y1{!sK'L%b!s\1D!s7%%02!vW%7O4!s?%HP8P9P7P5P4P2P0CoCop=FAk542=G70p=]AC4209k75p=VAG897AG542/30'3p=\1320,34p=h!s='p=jg00>HR0#1R5#0R4#0R2#1R9#PR8#1#[S00#1R7#[#8#dR:/I:g00edR;#nR<%l;R;;G;R=%s3R>g01EH#BR?,X3R@;G@RA%15!s~$B#1RC#iRD#`#`!sq$E/IES01%1D#8RD#1#4#[#dRF/IFS02%00RG#0RH#0RI#0RJ#0RK#0#<RL#@#<RM#<#E!s$'RN#K,X3RO=G>OS03%19R9#@RP#4#`#N#;RQ/IQS04g01EfRR#sRS%14R4#1RT#0RU#1RV#1RW#0#6RX#8RY#0RZ#0R[#0R\#1S!xg$;R]%50R0%:P#S#c#dRP%@BRB#W#4R^#1R_#4#US06#NS07#0#KR`g00olRa#2Rb#2Rc#2Rd#2Re#7S08P`%KLS09P?P?g01G4%7aRL%bKRf#B3zRg%2eRh#2Ri#2Rj#2Rk#2Rl#rRm#2#MRn#2Ro#2#M#MRp#2Rq#2Rr#2Rs#2Rt#2Ru#2Rv#2Rw#2Rx#2Ry!s\$z%BP%1TRT#8RP#0R{#0#UR|#W#`#R%2z#MR}#7%2}R}!s'%B]%7o%M}!s=2!s'77uS0:%7vS0;%7wS0<%7xS0=%7yRy%2}#r!tz$!sn3%l3'a3Q3T3T3T,at9Qrs9Qpq3Q3Q3Q5T?3T3Q3T,am7Tg'aP?%1[R[#1RgPk%6_#U#6#;R_#BP?PgPkP`P?%1Z!x,$g#0PkP`1>LfPk%7c%02Rc,qLPk%17#:#R%0TRT#0#6#4R7#4Rf#:#;Rm,>?S0>PkP?!vI$$04Rq#:#6Rp#0#;S0?,>?RsPkP?PL%1HRr#1Rt#:Pk%0N#KRNPL%PtRt#0Pk%0f#:PL%0rRr!sH$!{w$PRf#8#6#:#4#K!sD'PPk%KGPL%1IR}!sR$B0RxPL%<}PkPNPL%:JPk%`D#8P?%iTRT#:!u0$D#0RN#1R}#0Rw#1PbP?%0NRN#0Rv#0,y?Ru!s:$1D!sQ$o#0R~!s>$PbP?P?%0w!s/&1!s[$!s3'!sT%!sw&P?%1oRo!s3,~!s/'}R}!s<,N!s/'v!s/&8D!t330o!s/'}!s/$L%04R4#@R}!vN$6rRr#@#6#<!vV$@UPk%1PRP#6#U!}`$o!tc$@PLP8Pk%WoPL%PcPk%8wPL%PCRCPk%1GRG!u2%Rc!uh$8!w,%fPk%0q#6Rq#1#NPL!wT&Pk%8pPL!~+$Pk%WW!tK&1GRW#1Rp#PPkPyPL%<WPkQ0=PL%@oPkQ0<PL%<wPkQ0;PLPtPkQ0:%W7#g,f?R7PbPx%0^R^#0#6Rt#4Ro#1RW#4Ry#0,f?RfPbPxP?%1WS0:!z,$8^R^#1#8RW#0#4#;S0;,>?RDPeg00<bPaPe%7bRaH031qLJPk%7nPLPIPk%7l%5JRJ-02LRl%65#_R5#0#S#c!#6&%;!ud%i#S#_Rn#1Rv!s2&N#55pLR~%08R8,qL%58%5n9pa0Rn%5M%89#E#;'e%14#g!so$<VRV#0R4#@#<!s@$4\#;/e]%1YRY#S#;/emP?%@|#c#;PePaCxP?%4oPk%7dP?%4XRX#0Rd#8Ro!xd$7hRh!yy$PkPhP?%4dRd!s?%iRiP?%1dPkPiP?Q05Pk%7jRjP?%0[PkPj%5KRK%5HQ0>%5IRI%05R5#:#E,f?%0B#N#<#;1>?]%5CP?%8W#8#6!zA&WyPe!s/%!}e$Ry!~2$?PyPkQ00#@#:#RRyP?%g!x4$Pk%1c#:#N#4#6#RP?%1rRr#1#<#[!|p$64#<#;R4,>?Pk%B4%U{#6#4#6,f?!xZ&4U!s/&@P#4#4#6Pk%<5#E!su$0q#4Pe!sE$6V!~a$U}#c#:!sC%r!sr$[Pk%1N#_#_#KP?Q06#0!u+%%8X#8#NPe%KvRvP?%@YRY!{N$ePvP?Q0:Pe%BKQ08Q07$01;p_P?%6g#;Pk%BQ!wi$!#67$!#6D'PkQ09P?%0Y!td&1t!{p$?%1^Pk%1p#8#N#6#U!to$4T#S#4#g!v%$l6-00n9Zl~D9DADAD?DAD?3ZDAD9!s8&!s<%?FY!s-%!s@%3L3L9LuJ9LsI3L9L705LD5Lf!sh'!s$%3Z!s$$L3ZDDFY!sj$!s#,H!s$$!s-'H!t>$!s$6FYD9!sN$!s\'DFYFY!tX%M<~,XRRf;GfRD%18#S!xG$8/I8R713==R0'3RI'3Rs,3=RJ,3=Ru'3R~'3Rl,3=Rn,3=Rb,3=RT'3Rp,3AR^,3=Ry,3=Rt,3=Rx'3RY'3RZ,3=R`,3=Rg'31J1:P=Pg1J<;RgP=P`PgP=PZPgPAPY1J>@RYQ01Px1J1EP=Pt!sE$y!s+$^!sK$pPYQ02PT1J1FP=Pb!sA$n!s+$lPgQ03P~1J>OQ04Pu1J1QP=PJ!sD$sPgPDPI1JSfP7P01J18P=P=PgPgCoF!s#6g00dXRg1wg<R=g00foR8g01G`3CR07C<#^/I:P<PgP<P0P;D]P<%n6R6P<1w6<R0g00<B#nR:g01HfDVP;P<P6!sS$:g01Il!s9$>g00>mR7g01K3P?Q0;PeDmP@g01L:9C=8R@9Cg!t;$E!t;&@!t;%!sr-M@!t,4NF!t,%P7g01OMP?Q0?PkDmg01PT%}GRG%52R2g00VZR@1vG2d3u't,X3g00h9!tH$2!tH'F!tH&2!tH42^!tH4Q[!tH-Rb!tH/Si%5wRwP@1vGwd5uG!t?&1U0!t?$3!t?'Q!t?&3!t?4V6!t+$Sg01W<g01XC5|zg01YJ,XRP1g01ZQ!sr$8!sr%g01[WP<Akg<8!tw'g01\d9C0:P;D]F\F\3hCj!s+3do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn false false) 40) []).
Definition srX1c := Eval vm_compute in (s_regs (fst (fst rX1c))).
Definition cX1c := Eval vm_compute in (carry (s_log (fst (fst rX1c))) (ax_kn false false) []).
Definition knX1c := Eval vm_compute in (fst (fst cX1c)).
(* [comment removed for export] *)
Definition srX2ic := Eval vm_compute in (sr_upd (sr_upd srX1c (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x711588) 4 (sr_get srX1c 12)] knX1c []).
Definition knX2ic := Eval vm_compute in (fst (fst cX2ic)).
(* [comment removed for export] *)
Definition rX2c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x1912a0 srX2ic [] knX2ic 40) []).
Definition srX2c := Eval vm_compute in (s_regs (fst (fst rX2c))).
Definition cX2c := Eval vm_compute in (carry (s_log (fst (fst rX2c))) knX2ic []).
Definition knX2c := Eval vm_compute in (fst (fst cX2c)).
(* [comment removed for export] *)
Definition srX3ic := Eval vm_compute in (sr_upd (sr_upd srX2c (ridx 13) (sr_get srX2c 12)) (ridx 15) (ELit 0)).
Definition cX3ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1baa30) 8 (sr_get srX2c 14)] knX2c []).
Definition knX3ic := Eval vm_compute in (fst (fst cX3ic)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exX3c := Eval vm_compute in (List.filter (fun K => negb (x3_core K)) knX3ic ++ x3_facts).
Definition srX3c := srX3f.
Definition cX3xc := Eval vm_compute in (carry_keep (fun _ => false) (s_log (fst (fst rX3g))) exX3c []).
Lemma cX3xc_eq : ltac2:(zQ "h21!q3!kof!hgb!r7!s5!kq6!mvf!re!kr4!kpa!jud!r1!kk9!lka!ng8!kqc!ll8!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$c@2$3@2$3@1$0$2@1$0$1@1$0$4@4$d\0$2$a@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$b$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Gj22Tg00S]j25Tg00b_j30Tg010Kj19Tg00_jj18Tg011Qj47Tg00c<j33Tg00cYj44Tg00:_j36Tg00;9R0#1R1g00ed#1R2'2R3g00<BR4#1R5'2R6g01]jR7'5g00V:V0g00dXR01202g00fog00h930702#9g01_1%84C7P3P5P1P2A0357R49012A3124C4A3357C4566do"). Qed.
Definition knX3c := Eval vm_compute in (kn_drop_shadow (fst (fst cX3g)) ++ fst (fst cX3xc)).
Lemma x3_facts_c : ltac2:(zQ "h00!q3!kof!s5!kk9!il4!ln2!nh1!kn4!hgb!kq6!r1!r7!kr4!mvf!ng8!ksd@2$5@3$3$2@2$7$f$6$4@2$5@3$3$2@2$7$e$6$4@3$3@1$0$1@3$c@1$0$8@1$0$1@3$9@2$b@1$0$8@1$0$1@1$0$2$d@1$a$1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;3p;1p;2p;4g00:_j30Tg0028j12Tg00_jj19Tg006kj21Tg00S]j25Tg0162j44Tg00Z3j23Tg00^Gj28Tg00b_j37Tg00c<j36Tg00<BR0g00<bR1;01R2g00edR3#2R4%93R3;03R5,121501R6P2P5P61543C4C4g00neg01`8R6'3=001g01_1/36=001g00;9#2R11814%20g01]j37764=043'1'1do"). Qed.
(* [comment removed for export] *)
Definition srX4ic := Eval vm_compute in (sr_upd (sr_upd srX3c (ridx 6) (sr_get srX3c 10)) (ridx 7) (ELit 0)).
Definition cX4ic := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1baa30) 8 (sr_get srX3c 5)] knX3c []).
Definition knX4ic := Eval vm_compute in (fst (fst cX4ic)).
(* [comment removed for export] *)
Definition rX4c := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77eb0 srX4ic [] knX4ic 40) []).
Definition srX4c := Eval vm_compute in (s_regs (fst (fst rX4c))).
Definition cX4c := Eval vm_compute in (carry (s_log (fst (fst rX4c))) knX4ic []).
Definition knX4c := Eval vm_compute in (fst (fst cX4c)).

Lemma x_itinerary_clean : ltac2:(zQ "ia0!q3!kof!kq6!kk9!ln2!kpa!r7!hgb!r1!kr4!ijd!s5!ikd!jg6!h9!hh9!lo3!loa!jsc!lsc!jp6!lt5!nhb!ni3!kqc!nib!mk8!ml1!ml7!mlf!nj3!njb!nk3!lg1!nkc!nl5!nld!nm6!nmf!nn8!no1!noa@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h6+hphip4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h6@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$he@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i0@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i5@1$fZ+nhhlo8N4@2$h1$c@1$fZ@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h7+nnrj4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h7@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$hf@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i2@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i6@1$fZ+hrqqj0N8@2$h1$c@2$ha$i8@3$hb@1$d#5+cKv$h5@2$hc@1$d#5+c@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h8+nnuq4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h8@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i1@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i4@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i7@1$fZ+hrqqj0N8@2$h1$c@2$ha$i9@3$hb@1$d#5+aKv$h5@2$hc@1$d#5+a@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h9$hd@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h9@1$8$1@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i3@1$8$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##5ap;1p;3p;2p;4p;5g00^gj1<Tg0000j11Tg0028j1GTg00_jj1QTg00:_j36Tg001Vj1OTg017Uj1ITg018\j2@Tg006kj20Tg00S]j2=Tg0162j4HTg00^Gj2NTg00b_j32Tg01?Gj1CTg00c<j38Tg00d9j1:Tg01@Lj5F!t^$Uj1P!tU$Lj1MTg01ANj2LTg01B1j3K!s/$Tj2JTf0R0#<#1p=3%10#1p=5%10#<p=4%10#Mp=9g00W6R1f1R2;60p=;%<!sG$?!sW$!s$/p=>!s:+p=Rf6R3f5R4f4R5f3R6f2R7P2P0CHCHp=7A8672=650p=BA6672/00p=EA6345!s6''0p=A1020,07p=Dg00>HR7#<R2#1R0#1R6#3#5R5#3#4#4#5#3#3#9R4/;4g00edR3#GR8%Q3R3;63R9g00X3R:#OR;g01EH#IR<,@:R=;6=R>%32R2#?#?R?#4!sy$!su%@/;@RA%??!t3+9R?/;?RB%17R7#5#>!s$09#I,@:RC=6;CRD%45#?#?#5#R#9R5/;5RE1099RF'0RG'0RH,09RI,09RJ,09RK'0RL,0>RM,09RN,09RO,09RP'0RQ'0RR,09RS,09RT'01=14P9PT1=83RTP9PSPTP9PRPTP>PQ1=;=RQPAPP1=1@P9PO!sD$N!s+$M!sJ$LPQPBPK1=1?P9PJ!s@$I!s+$HPTPDPG1=;CPEPF1=15P9P9PTPTCHF7!s$1g00dXRT1NT8!w+$foR5g01a@32RF728#C/;4P8PTP8PFP3DBP8g00;9#GRF1NF8R4g00<B#GREg01bF32788P3P8g01cL924E98F8P3P;g00>mRCg01dSP<%52#3!xf&?#5!we$9g00ol#:!s$%R2DFP=g01eZ9295R=92T!t]$@!t]&=!t]'1f`!t7-8g01gf!tH/PCg01hmP<%<0#!xz%4!tA$3#5#9R0%:2!tA,g01j4%<7R7#PR=%M6R6g00VZR@1L=6d3K'J,@:g00h9!te$6!te'?!te&6!te+2^!te2k;!te4lBP<P0P!tG%mI%97R7P@1L=7d5K=!t:$P1g01nP!t<$5!t<%g01[WP8A8T85P3!wa$8g01oV924EP3DBCEFAFA3DCE!s+,do"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1n := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn true false) 40) []).
Definition srX1n := Eval vm_compute in (s_regs (fst (fst rX1n))).
Definition cX1n := Eval vm_compute in (carry (s_log (fst (fst rX1n))) (ax_kn true false) []).
Definition knX1n := Eval vm_compute in (fst (fst cX1n)).
(* [comment removed for export] *)
Definition srX2in := Eval vm_compute in (sr_upd (sr_upd srX1n (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2in := Eval vm_compute in (carry [SE (SA (ELit 0) 0x711588) 4 (sr_get srX1n 12)] knX1n []).
Definition knX2in := Eval vm_compute in (fst (fst cX2in)).
(* [comment removed for export] *)
Definition rX2n := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x1912a0 srX2in [] knX2in 40) []).
Definition srX2n := Eval vm_compute in (s_regs (fst (fst rX2n))).
Definition cX2n := Eval vm_compute in (carry (s_log (fst (fst rX2n))) knX2in []).
Definition knX2n := Eval vm_compute in (fst (fst cX2n)).
(* [comment removed for export] *)
Definition srX3in := Eval vm_compute in (sr_upd (sr_upd srX2n (ridx 13) (sr_get srX2n 12)) (ridx 15) (ELit 0)).
Definition cX3in := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1baa30) 8 (sr_get srX2n 14)] knX2n []).
Definition knX3in := Eval vm_compute in (fst (fst cX3in)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exX3n := Eval vm_compute in (List.filter (fun K => negb (x3_core K)) knX3in ++ x3_facts).
Definition srX3n := srX3f.
Definition cX3xn := Eval vm_compute in (carry_keep (fun _ => false) (s_log (fst (fst rX3g))) exX3n []).
Lemma cX3xn_eq : ltac2:(zQ "h21!q3!kof!hgb!r7!s5!kq6!np3!re!kr4!kpa!jud!r1!kk9!lka!npc!kqc!ll8!ijd&@3$5@2$3@1$0$2@1$0$1@1$0$4$6@3$c@2$3@2$3@1$0$2@1$0$1@1$0$4@4$d\0$2$a@1$h0@3$5$9@1$0$1@3$5@2$3$9@1$0$1$h1$f$e@1$b$4@4$7@2$3@1$0$2@1$0$1@1$0$4@4$7@1$0$2@1$0$1@3$5@1$0$2@1$0$1~0@3$8@1$0$2@1$0$1~0@3$8@2$3@1$0$2@1$0$1@1$0$4$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;1p;2p;3p;4g0028j11Tg00^Gj22Tg00S]j25Tg00b_j30Tg010Kj19Tg00_jj18Tg011Qj47Tg00c<j33Tg00cYj44Tg00:_j36Tg00;9R0#1R1g00ed#1R2'2R3g00<BR4#1R5'2R6g020\R7'5g00V:V0g00dXR01202g00fog00h930702#9g021c%84C7P3P5P1P2A0357R49012A3124C4A3357C4566do"). Qed.
Definition knX3n := Eval vm_compute in (kn_drop_shadow (fst (fst cX3g)) ++ fst (fst cX3xn)).
Lemma x3_facts_n : ltac2:(zQ "h00!q3!kof!s5!kk9!il4!ln2!nq5!kn4!hgb!kq6!r1!r7!kr4!np3!npc!ksd@2$5@3$3$2@2$7$f$6$4@2$5@3$3$2@2$7$e$6$4@3$3@1$0$1@3$c@1$0$8@1$0$1@3$9@2$b@1$0$8@1$0$1@1$0$2$d@1$a$1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsExitDefs ()) ["FPX1"] "p;3p;1p;2p;4g00:_j30Tg0028j12Tg00_jj19Tg006kj21Tg00S]j25Tg0162j44Tg00Z3j23Tg00^Gj28Tg00b_j37Tg00c<j36Tg00<BR0g00<bR1;01R2g00edR3#2R4%93R3;03R5,121501R6P2P5P61543C4C4g00neg022jR6'3=001g021c/36=001g00;9#2R11814%20g020\37764=043'1'1do"). Qed.
(* [comment removed for export] *)
Definition srX4in := Eval vm_compute in (sr_upd (sr_upd srX3n (ridx 6) (sr_get srX3n 10)) (ridx 7) (ELit 0)).
Definition cX4in := Eval vm_compute in (carry [SE (SA (ELit 0) 0x1baa30) 8 (sr_get srX3n 5)] knX3n []).
Definition knX4in := Eval vm_compute in (fst (fst cX4in)).
(* [comment removed for export] *)
Definition rX4n := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x77eb0 srX4in [] knX4in 40) []).
Definition srX4n := Eval vm_compute in (s_regs (fst (fst rX4n))).
Definition cX4n := Eval vm_compute in (carry (s_log (fst (fst rX4n))) knX4in []).
Definition knX4n := Eval vm_compute in (fst (fst cX4n)).

Lemma x_itinerary_clean2 : ltac2:(zQ "ia0!q3!kof!kq6!kk9!ln2!kpa!r7!hgb!r1!kr4!ijd!s5!ikd!jg6!h9!hh9!lo3!loa!jsc!lsc!jp6!lt5!nqf!nr7!kqc!nrf!mk8!ml1!ml7!mlf!ns7!nsf!nt8!lg1!nu0!nu9!nv2!nva!og3!ogc!oh5!ohe@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h6+hphip4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h6@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$he@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$hf@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i5@1$fZ+nhhlo8N4@2$h1$c@1$fZ@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h7+nnrj4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h7@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i0@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i2@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i6@1$fZ+hrqqj0N8@2$h1$c@2$ha$i8@3$hb@1$d#5+cKv$h5@2$hc@1$d#5+c@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h8+nnuq4@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h8@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i1@1$8$1@2$4@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i3@1$8$1@2$4@3$3@1$h2$c@5$h3$h4$i7@1$fZ+hrqqj0N8@2$h1$c@2$ha$i9@3$hb@1$d#5+aKv$h5@2$hc@1$d#5+a@2$4@3$3$e@1$h0@3$2$5@1$0$1@3$2@2$6$5@1$0$1$a$h9$hd@2$4@3$3@1$0$1@3$9$5@1$0$1@3$2@2$6$5@1$0$1$a$h9@1$8$1@3$3@1$0$1@3$9@1$0$7@1$0$1@3$2@2$6@1$0$7@1$0$1@1$0$b$i4@1$8$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsExitDefs ()) ["FPX1"] "##5ap;1p;3p;2p;4p;5g00^gj1<Tg0000j11Tg0028j1GTg00_jj1QTg00:_j36Tg001Vj1OTg017Uj1ITg018\j2@Tg006kj20Tg00S]j2=Tg0162j4HTg00^Gj2NTg00b_j32Tg01?Gj1CTg00c<j38Tg00d9j1:Tg01@Lj5F!t^$Uj1P!tU$Lj1MTg01ANj2LTg01B1j3K!s/$Tj2JTf0R0#<#1p=3%10#1p=5%10#<p=4%10#Mp=9g00W6R1f1R2;60p=;%<!sG$?!sW$!s$/p=>!s:+p=Rf6R3f5R4f4R5f3R6f2R7P2P0CHCHp=7A8672=650p=BA6672/00p=EA6345!s6''0p=A1020,07p=Dg00>HR7#<R2#1R0#1R6#3#5R5#3#4#4#5#3#3#9R4/;4g00edR3#GR8%Q3R3;63R9g00X3R:#OR;g01EH#IR<,@:R=;6=R>%32R2#?#?R?#4!sy$!su%@/;@RA%??!t3+9R?/;?RB%17R7#5#>!s$09#I,@:RC=6;CRD%45#?#?#5#R#9R5/;5RE1099RF'0RG'0RH,09RI,09RJ,09RK'0RL,0>RM,09RN,09RO,09RP'0RQ'0RR,09RS,09RT'01=14P9PT1=83RTP9PSPTP9PRPTP>PQ1=;=RQPAPP1=1@P9PO!sD$N!s+$M!sJ$LPQPBPK1=1?P9PJ!s@$I!s+$HPTPDPG1=;CPEPF1=15P9P9PTPTCHF7!s$1g00dXRT1NT8!w+$foR5g024232RF728#C/;4P8PTP8PFP3DBP8g00;9#GRF1NF8R4g00<B#GREg025832788P3P8g026>924E98F8P3P;g00>mRCg027EP<%52#3!xf&?#5!we$9g00ol#:!s$%R2DFP=g028L9295R=92T!t]$@!t]&=!t]'29R!t7-8g02:X!tH/PCg02;_P<%<0#!xz%4!tA$3#5#9R0%:2!tA,g02<f%<7R7#PR=%M6R6g00VZR@1L=6d3K'J,@:g00h9!te$6!te'?!te&6!te'12^!te2=m!te4?4P<P0P!tG%@;%97R7P@1L=7d5K=!t:$P1g02AB!t<$5!t<%g01[WP8A8T85P3!wa$8g02BH924EP3DBCEFAFA3DCE!s+,do"). Qed.
End FPX1.
(* [comment removed for export] *)
