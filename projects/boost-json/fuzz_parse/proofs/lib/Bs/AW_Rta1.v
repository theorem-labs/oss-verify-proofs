(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_Efs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AllocPerfKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AW_Rta1 () := KReplay.lz_vm "#$vFC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib6MState5Wrd64C13~~~C4ELinuxProcessSemantics5Riscv7Prelude4tget!sQKs!sQK5bvmapC47Corelib4Init5Logic8eq_ind_rK!sD+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00!vhT4TacX2wz!vc%!tN>Z02C56Stdlib6ZArith6BinInt1Z3pow!sC=mul!sC=add!v8G1c!uOO2Bs7AW_Rta1=rta_head_post!yA&!vCS5Frame3mkR!z&'!wO?7Z_to_bvK!x~19Datatypes6op!sO#02!tWT8PropExec7seg_rom!t^GDbv_unsigned_in_range!sYA;!sY-!sPA:bv_modulusC!wiR8AsShadow;aceil_facts!whV!sq/5!sq$!sk&!z3;2le!sB<6!uC$oC7!tON8HeapCeil5h!tLHtI!#3063and00I!yK;4prod00!|X=sub!z0<4list01!sFB2!|#Z:munch_refl!|o`5!sn$!si`:wmono!tY-K!#8:Iree!v>/!#5U53!#:DZ2MS!#6\2!xe-2eq01I!#31B0!#:RIsext!#3\\8alu_addi!wJZ8StepFast8sf_congT!uo8!uU,3nat!#9N=6of_nat!#<G8iff!xV%!sd;>pow_pos_nonneg!sN<:!sN#!sJ&4!sJ&9micromega9SatDivModCZ_mod!sP&!s,&I!|`A0K!sw56VarMap1t!xe#!sD>0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr02!sIE4!ut65Tauto8B!t8&!sH6:Z!t^+=Z!sT$CheckerC!uS<4find!sqAC!sq0_sound!~qZ9stk_carve!zK%I!}<9x00K!t/TCells4cell01!#:XX<AllocPerfKit4park!snf6!sn#ed!}3&!uL_2!~hZ3Mem2wa!sd^3le8!#@l&!#5Q8?!s<2>!#5a#!sE+<write_to_mem!#5j\9b_add!#6V#!uCY4StepD!#B_'!#DK%!s{#!#>gA9add_assoc!#7/\=sf!t8#r_ztobv!#7}b7sf!#=|-!|W+5Lists7!s+#Def6firstn!sE;5skipn!zT`5!#>bZ!sj$5csize!si`6cbyte!#F'Y9!}a$TacX;regio!#H`#k!src9!sr&lb!spkub!#6/?q00!#7j5;ZifyClasses6eq_iff!sLB9and_morph!sOB7rew!sv#!#:hD1!spB;!sp&_rev!stE7C!#B|;length!#56W:!sb%_!#5=+!zIT!#:}#6inside!sj`;!#I7$!#6/#!~:'!#O[>6!#4n%!yyR!#:B0un!#;4+!yy9or!#@h7!#A;05Psatz07!sOK5!sOK2K!tc;1!w,Z=disjoint_f!#Ti+!sqYBrw_cells_transpor!#X&`Fstk!sq,_!tw'!x{GD!#:p&obliga!s:#_1!#:s;7add_0_r!#^k;!tS$!u<T!#N%%=!tZ'plus0!u4G9bv_!#X6%!#;]S!#>a&6v!#MK-!#@<I6BvBase@le_!#9B#!u/#wor!#YeEextrac!#byI9!#by#_set!#>5\6!#?'#4!ywZ!sm+?sf_install_load!sv[!w=-sll!w='!#PR;shiftl!#SFIz!#SF_5!#C]-!slS!#DV#F!#DV6_r!vIc7!#U/%!sn%!#Xb@5Instr5!wp#r0:!vv34Znat5Nat2Z9i!#Sa'!#3{X!#NX#!#9k-!w?`n!#GvB4l!sJ#!ur@3Sem5alu64!w2cn!w2U5!zbI6!~a#qb!#?{;4negb!}\]<sf_branch_pc!~Qc!#[N&1!waB3!uG$!sC&4Bool!s'$=!uA#_true!#Dv$!#9%55proj1!sA83not!#9~<eqb_neq!s`89False_!#WL-!tc,>!tc$f!sH%ff!#4#<!t0#eq!y_]4v_or!vWClor!#6@]!zi#!t2D7di!#lR#!tS=div!sC<=mo!#q2#_b!#Zb#!sM@neg!sM25!#Bp#8PreO!s/#1Z;!t[#0_r_ext!sL>!st#!sL&!#IW=3Pol01!#D?J4K!#]I?;!uH%!wG$03!#r[C1!#W}Y>ms_svc_pendingI!sl[achine_result!#h-<!snB4step!#5:MDK!#6~C4core!v==!sO-exec!#DXZ;interp_eff0!#5<Y!sp'lift!vf&!#8B@!wZR3!snj2!xJZ=ov_read!#Ev$!skZ8store_ok!xgE3!wR#6!sNJ1!sNJ7!xET3Mem8load_u64!#CR^=wa_of!#CO&!sp&!#9e66eq_sym!t4Y@!#Op'!wr$a!#Nr'!v=C;amo_al!#}z%!sTC9!sT#!xw%!tuO!#\G#sAtom!yA#!t@-_li!txB!yoB:fetch!#MI%!zYYis_ecal!#J:BDecodeC:d!s-$_any!#31Z8step_gen!#3-&!#@D6and!#8kL!#PT%!#RV$!#PY&!#76ME!|UJ8C3!#QM$7tac!sF#<f_equal_help!{<<i!#qlU!#jN$!{<+!#3F&!{@,!#?%:8eqb!#hm$!tAXA!tA4!~[_>!st+!#LO,!#\@;2!#c7A8or!#dQ%!#HY[!#Ts$1!#;2ct!#QH#!}t+!z&N3!u3]7sf_btgt!#KVb:sf!#\O$MR!sqZ2Nd:ex_introF9!y8[!$&K#evt_done!skdstep!|&B?!#XT$_mul_pow2!xo[<!#WF'!#7f+!u/X3evt!{{8!$4`2!#eCZ5!$2$#!t1'!$A/B1!{-N8!$2rN2!#CKi!#o9B3inj!sIB5mkapp!#qjB!sK$2!sqErel!$-[?2!sD@3!#q,D3!#NVC!$-~'!#O%6!$-8%G!sJ'4!sJF8!z&Z3st!#8{_8!#8{&!#6RS7!#;2bcb_sp!#Bj,!#:?57!#>%%!#6u\@sf!#<C$8_direc!#7nc@!#gq,!t#$!swZ!#}d$;!u{'!#>2\!so%8!vl2!wbX!#>x+!#XY$!t__:!#@_%!$$~b7!sn#!#B`+!uNXDmem_inv!#B=%!$%x[3!#Nb%7!sv&!wxb!uO#up!#f+'!#3&C3!sJF5!#3NY;!$ET$!#D`/!#5ZA!#]2%6!#]2M!$=aE5!#41M6!}}]?sf!#rh#!~uc!$EV/!#rr+!u;N9!}bcf!x-#!y[L7!sJF!vvU7CodeTab;!#DC&_!vqX2Bs5ASegs5aseg!#:2'!#8h&!$LI5!$KF,!sD60!wNHaluop!sp#!wzL0!#d&Y=!#B9&state!$4478Zify!t:#7Inj_Z_Z!$Hv;!$KH#0!$Fx;5eKind!$I\<uni!$I\8!se%4kind!#hpE3Op2!#hB=!t5%!$P4<4bool!tU#!sF@1I!#6bX!$<b$0!#5#I!uA$!#H]Hmsize04I!#WiC!#gy$0!#T,74True!w%K5!$3o75!#s5#!x58!#7&:!$Ny6!sR;0I!u-=0!#`HD2w!$fTT!#OT%6w0!#U@-!{i?1!~CN3!z#B2!#4]X7ct!#DC#!#4_B!$g<+3!#6a[8ct_entry!#6^X!$Ac+=!$Ac%tabl!$N0'!#6L<N!w/P:!sRG;!#~+%cond!#Qe<!t+69!sRG6awidth02!}\E!#bG#0I!us?!sD>!xD,!{zH1!v9T1!xSS8!xS$Rep5AINST!y@Y6AW_Efs;kWriterLoc!#Ki&!$h0N>Asan!t]$Model@kFreeArrayOffse!|A&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsk4dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeob5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~r93mem37Corelib4Init9Datatypesvd4cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hhc4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hm02wzhhc2C837Corelib4Init5Logichq72ex46Stdlib6ZArith6BinInt1Zhs13addhq73and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hu75asegshfbbv_unsignedhs13powvd3nilvd4prodvd4listvd6optionvd4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~im45AINST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iqb8rw_cellshs13subhf7Z_to_bvvd4Nonehq72eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6AW_Efs~~~~~~jh0bkWriterLockhhc2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jm13mkRjm15munchjm13stkjm15wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jrd2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kg07mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kk57seg_romr95aceilhs12le69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~kpdbkNumClasseshs12ltr96AHI_LOhs16modulohhc2C4" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac name_junk_pieces ::= idtac.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition rta_head_post : ltac2:(zQ "60!h9!jc!k1!nb!r1!v7>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$5>2lo$2>1R$2>4rbeg$2>3FAB$2>1c$2>2CH$2>2nf$2>1n$2>0$3P") := ltac2:(zQ "i41!h9!jc!hh5!k1!hl8!hpb!hq1!hrb!ht9!hu0!ii2!iib!ij9!ik0!ik6!ikd!il4!ild!nb!iq2!iu6!iv2!iv9!jg3!jga!r1!jkc!v7!jlb!jpd!jq4!jqd!jr4!jva!kja!ko4&>0@1$1@1$0#k0@1$h0@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2a1@1$1@1$0#k0\2a2@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2t3@1$1@1$0#k0\2t4@1$1@1$0#k0\2t5@1$1@1$0#k0\2t6@1$1@1$0#k0\1F@2$h9@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$hb\2lo$3\1R$3\4rbeg$3\3FAB$3\1c$3\2CH$3\2nf$3\1n$3\3ms'$h2@2$7@1$1@1$0#k0\2t0@1$1@1$0#k0@2$7@1$1@1$0#k0\2t1@1$1@1$0#k0@2$7@1$1@1$0#k0\2t2@1$1@1$0#k0@2$7@1$1@1$0#k0\2a4@1$1@1$0#k0@2$7@1$1@1$0#k0\2a5@1$1@1$0#k0@2$7@1$1@1$0#k0\2a6@1$1@1$0#k0@2$7@1$1@1$0#k0\2a7@1$1@1$0#k0@2$7~0\2m'~0@2$7@1$f@1$1@1$0#8\3j16@1$f@1$1@1$0#8@2$9@3$h8$h2^a@7$i1@hf$hd@1$5+mrttc@2$h6@1$0#k0@2$8@2$b@1$0#k0^ia-o0^i9^i8^9^8^7@1$5^h1@1$5^c@1$5$h3@1$5^h1@1$5^h0@1$5@2$8^c^b^6^5^4^3@1$5^e^i5@1$5$h3@1$5^b@1$5^d@1$5@2$8^c^b@1$5@2$c+2+jd@1$5^f@1$5@2$h5@2$8@2$c+2+jc@2$c+2+h4+1@1$5@2$c+2+jc^h9^h8^h7^h6^h5@2$h6@1$0#k0+mrvq0^h4@1$h7@1$1@1$0#k0^2@1$i3$a@2$9@3$he@3$2@2$e$3$3@4$h1$3$3@2$h5@2$b@1$0#k0^ia+o0@2$b@1$0#k0^ia@3$2@2$e$3$3@4$h1$3$3^h1@2$8^h1+8@1$d@2$e$3$3^h3^2@2$9@3$i0$a^h3^2@2$9@2$i2$a^2@2$9@4$hf$a^2^h2@2$8@2$b@1$0#k0^ia-o0@2$9@4$h4$a^2@2$8@2$b@1$0#k0^ia-o0@3$2$4@2$hcNh0^1@3$2$4@1$6@1$5@2$8^h1+8@3$2$4@1$6^ha@3$2$4@1$6^hb@3$2$4@1$6^hc@3$2$4@1$6^hd@3$2$4@1$6^he@3$2$4@1$6^hf@3$2$4@1$6^i0@3$2$4@1$6^i1@3$2$4@1$6^i2@3$2$4@1$6^i3@3$2$4@1$6^i6@3$2$4@1$6^i7@3$2$4@1$6^ib@1$d$4@4$h4$a^2^h1@3$2$4@1$6@1$5$ha@1$d$4").

Section Head.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo SB ARI c CH nf n : Z).
  Let R := ARI + REGIONINFO_SIZE * c.
  Hypothesis MI : ltac2:(zQ "20!ii2!kja@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "40!h9!ii2!jqd!iib@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis LO : ltac2:(zQ "20!kof!kp7@2$1@1$0?5HCEIL?2lo").  Hypothesis HI : ltac2:(zQ "40!h9!ht9!kp7!iib@2$2@2$1?2lo+o0@2$3@1$0#k0?2sp").
  Hypothesis Ha3 : ltac2:(zQ "40!jga!h9!hpb!jc@3$0@1$3@1$1#k0?2a3@1$2?1c"). Hypothesis Ha4 : ltac2:(zQ "40!jga!h9!hpb!jc@3$0@1$3@1$1#k0?2a4@1$2?2CH"). Hypothesis Ha5 : ltac2:(zQ "40!jga!h9!hpb!jc@3$0@1$3@1$1#k0?2a5@1$2?1n").
  Hypothesis CR : ltac2:(zQ "40!hu0!kte!kp7!kud@2$0@2$2+1?1c@2$3?1c$1"). Hypothesis NFR : 0 <= nf /\ nf + n < 2^32. Hypothesis NNR : 0 <= n. Hypothesis CHR : 0 <= CH < 2^64.
  Hypothesis ARIR : ltac2:(zQ "80!hu0!kp7!jga!k1!kv3!kof!ht9!kvc@2$0@2$1$4?3ARI@2$0@2$1@2$6?3ARI+hgg0@1$5?5HCEIL@3$2$3@2$7?3ARI+hgg0Z").
  Hypothesis SBR : ltac2:(zQ "90!hu0!kp7!jga!k1!kv3!kof!ht9!kvc!ij9@2$0@2$1$4?2SB@2$0@2$1@2$6?2SB@2$8+2+i5@1$5?5HCEIL@3$2$3@2$7?2SB+hgg0Z").
  Hypothesis ISB : ltac2:(zQ "a0!hl8!hh5!hpb!lg6!ik0!ii2!iq2!hq1!iu6!ht9@4$8$5?1m@2$9$6+i0@3$1$0@1$7@1$2?2SB@3$1$0@1$3@1$2+vvvvvvvf@3$1$0@1$3@1$2Z@1$4$0").   (* [comment removed for export] *)
  Hypothesis IRI : ltac2:(zQ "90!hl8!hh5!ik0!ii2!iq2!hq1!iu6!hpb!ht9@4$6$3?1m@2$8$4+j0@3$1$0@1$5@1$7?3ARI@1$2$0").
  Hypothesis RI0 : rw_cells asegs m R [C8 (wz 0)].
  Hypothesis RNF : rw_cells asegs m (R + 16) [C8 (wz nf)].

  Theorem rta_head :
    evt asegs (rta_head_post ra sp gp tp s0 s1 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo R (SB + c * 2^32) (SB + c * 2^32 + kFreeArrayOffset) c CH nf n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz AINST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6bc78) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO, kNumClasses, REGIONINFO_SIZE, AINST, kFreeArrayOffset in *. subst a3 a4 a5.
    change (1809176 + 32) with 1809208 in ISB. change (1809176 + 48) with 1809224 in IRI.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (ARI + 128 * c, ARI + 128 * c + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 128%nat ST. spill_frame ltac:(do 13 step).
    (* [comment removed for export] *)
    do 22 step.
    rewrite (unsigned_lit c) by (clear - CR; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 7), (Z.shiftl_mul_pow2 c 32) by (clear; lia).
    change (2^7) with 128. replace (ARI + c * 128) with R by (subst R; clear; lia).
    (* [comment removed for export] *)
    step. step. st1. do 6 step.
    if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    assert (AL8 : R mod 8 = 0) by (subst R; clear - ARIR; try acb; Z.div_mod_to_equations; lia).
    assert (ALR : 0 <= R < 2^64) by (subst R; clear - ARIR CR; try acb; lia).
    astep.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    astep. fix_lit_store.
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    apply evt_done. unfold rta_head_post. do 9 eexists.
    split. { change (2^61) with 2305843009213693952. change (2^60 + 2^20 - 1) with 1152921504607895551. change (2^60) with 1152921504606846976. reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. unfold kWriterLock, wz. change (2^60) with 1152921504606846976. eassumption.
  Qed.
End Head.

End HCW2.

