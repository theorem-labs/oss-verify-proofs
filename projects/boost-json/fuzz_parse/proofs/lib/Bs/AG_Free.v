(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AS_Free1 AS_Free2 AS_Free3 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_MallocCold AG_MallocTop
     AG_FreeModel AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free5 AG_Free6 AG_Free7 AG_Free8 AG_Free9 SecLazy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_Free () := KReplay.lz_vm "#$-pC79OSSVerify6Proofs:boost_json:fuzz_parse3lib>AsanAllocModel7qc_listC13~~~I47Corelib4Init9Datatypes4!sJ#00K!sF15Logic2eq01I!s@;!sZ3!sz31K!u4^6qbatch01!u5%!v#_8qb_coun!v$&C56Stdlib6ZArith6BinInt1Z3lebC!uc73not!s\<2lt!v@83and00!sv86eq_ind!sB89False!sE#!v|B2!t`<6leb_gtK!td<1C8!vlN2Bs<AG_Free!vm%need_new!vm&4!tU&5Lists4!s+#4lastI!xlf0!z{Cbool!zG?!sF$2!tYacache!tY'!t9B1!zg_;kB!ul#C!zj,!t<,7Numbers7BinNums1Z!}P/!sD60!zT84True!sB:5!z9$!~i:!s_%!yPT8!uT$Rep8agree_on!yL&!snO3Lib5Frame5wmono!v:C8positive02!v_@!|Q=3add!t-G1!~u>e!vJS9!vJ'X:flagsx_rep!vMZ4TacX2wz!vI&!w4TCells4cell!#7$'!tQTStep8rw_!sl#s!{6DN02I45stdpp9bitvector;definitions2bv!zw:2ex00!vAZb8!vAf4!~zB3na!#7W?of_nat!#6H'9micromega;ZifyClasses!#9+#ff!#9+78iff_refl!sjB3inj!sIB9and_morph!sOB7rew!t_#K!sM56VarMap1t!xB#!sD>0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr!~K/!wF26op!yY#02!uI65Tauto8B!t7&!sH6:Z!t]+=Z!sT$CheckerC!uR<4f!#=v#!sq?C!sq0_soundC!zCY:!|p$_size!}bV!#7L-E!}e'_transport_pt!{D8!}1,1!u,T2Nd:!y}#elimF5!#?-1!z+95mkapp!|1C!sK$2!sqErel!yfE1K!z\L!sQ7!yo&G!sJ'4!t@E3!smF5!sJF8!sJF!t:G7I!#5l^0!zKY5ASegs5asegs!shY!#<7+9ASSPGUARD!#DwA!#7H#0!~}<5eKind!#E]<unit!#4Q7!se%4kind!yfF3Op2!w_#!t5@!smJ5!~cUsShadow3mem!#BAL3!xNY8AIMG_TOP!#4`a7AIAINIT!smhST!z/eLIBCPGSZ!spc8AGOT_SS!v?eCFLAGS!#@1F1!{g68ZifyInst7Inj_Z_Z!#=J5!#:u,;!#@j$!tp$!#BsQ!u+/4AREP!}jB4prod!#?&,!#Q7,5NoDup!~/-!sB-2In!te\3alb!#:M&!#;T53!#B~:5proj!#MS\6ast_ok!xxb8inst!#JrY!sn/9!#Kd#!sof:thread!spf7sec!smf6ia!uMgregion!spgpclas!w1gA!tb&s!#80#!swf?!sw&junk!suf4a_!#c0&!#Y8^:ch!t^#!#c}+!{K]!sp%!uP,!td^5as_tq!t_b;!#^P#es!tamgq!sne;kNum!#G~%!st%!#_R^5!w;$!#DgZ!x&,placed!#60[7!so$Wf2WF!sg&!#7z;2C!#Q&;length!#l0`b_addr!wme4zlen!sme7ch_used!yNf!sp%r_beg!#3Aeb!sjb5a_ctx!sketh!ws'!#[214Znat5Nat2Z9is_nonnegC!#^-?;bv_unsigne!#VI69SatDivModCZ_mod!sz&!t%'!#\Z;modulo!sF<>pow_pos!snC3pow!sC<:!sk#!sg%!#[d?!#jLglas!#b<'!t:4!#Sg17!t?_BkQuarantineMaxS!#Ye[:AsDepotInv4d_nb!yI9!w1,mul!|+]disj!tug!|rd4a_pa!#3@d6as_sec!soe:sc_map!#40,!zK_!ss&!#_j^!#T,%4aapp!sjb5aceil!{|<!#V,05Psatz02!sOK6K!#OhL2!~^@3!}hE!#WmP!#b;%;!#b;'13!xJe9kPage!~M-!z3_kSpac!ssj@kPtrArrayReserv!sy&!#{4_s!#Ba/!xXN!#R<U!$#;$75ZH_l!#w{%".
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~06qbatch37Corelib4Init9Datatypesk93nil37Corelib4Init5Logicm72eq07qc_listk94boolk95falsek94listm73andm73not37Corelib7Numbers7BinNumsqb1Z0bkBatchCount04mkQB08qb_count06qcache79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAG_FreeModel~~~~~~ud8need_new36Stdlib5Lists4Listhja4last46Stdlib6ZArith6BinInt1Zhl52lthl52le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~hn97AIAINIThn97AIAINST79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~hsdaflagsx_rep79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~iha3memhl53add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~im68AIMG_TOPim65asegshn98agree_on79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~is25wmono" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
  (* [comment removed for export] *)

Lemma need_new_false_inv : ltac2:(zQ "h10!k1!m1!nb!o0!o9!p0!p8!pf!q5!s4!s8!t5!tb!u5!hif!hkd!hmd>1t$d>0@3$2$4@1$e^1$5@2$7@1$8@3$2@1$6$0@1$3^2@1$1$0@2$h0@1$c@3$f$0@1$3^2@4$bZZZ@1$1$9$a").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_Free ()) ["HCW"] "##0Mp'0h01Eh11Hh22H0h31eh41xi001xh51yh62H1h71bi011bh81li021lh91qi031qh:1tp;1p;2p;3p;4p;6g0000j15Tg001:R0j1C!s1$Zj2=Tg0024j30!s/$Nj1<!s/$nj4BTg0049j12Tg005Dj27!s/$aj16Tg006:j21!s/$VR1j29Tg0071j6;!s/$Mj2:!s/$lj38Tg008Lj2A!s/$lj4@Tg009Gj1?Tg00:Sj3>!s/$lR2f1R3f0R43>p=3g00<7R5g00<WR6704p=4g00=7%54%C2R71=74%53R8=074P0P2f3R9#5!s4'P5P3g00>BR:g00>bR;g00@0R<P<P<g00@NR<#<CBR=,39#2'7n10110000020020103102#4f2R>%<2R?507#613>=#2/1;'9[]0P3%5>=07?A05:6P5P:P5p-0R:P4g00@lR@g00AHRAn01101!t%%00X35g00AeR5P6P4E;PAA07??#613?!t+'/:4b2W1W0f6#5A8234507A82>3/3=#2,7;#4A829>R6=07?RB#6RC136!sf%P7f4=829R6!v%$:P4PAP@!uX%2!uX'!s#%X37P5P?!tV%1:A4b6X2BPCeP11734#4113>[R1114317>3#4RC[11>9\C1A34P3n20!uQ$0001!s{+5<X4<P1^5<^4<P4P;!ti%R6P3O3116;P4b1b2C@W1W0X97X72P3P4O2!tr2!wL%P4O1b0b8%?4#4A078!vJ$8!wP+eW:o"). Qed.

(* [comment removed for export] *)
Lemma flagsx_transport : ltac2:(zQ "e0!pf!hn3!hmd!q5!s4!hr7!hs2!igc!il8!ilf!iq1!iqd!ir6!ive>1P>0$4P>2ma$8>2mb$8>0@3$c^3^2^1>0@3$d$b^3^2>0>1a$4>0@2$0@2$1+hggg0^1@2$2^1$a>0@1$3@2$0@2$1$5^2@2$2^2@2$9$5+4>0@1$3@2$0@2$1$6^3@2$2^3@2$9$6+ohgj0>0@1$3@2$0@2$1+ipvgl8^4@2$2^4+mpvgn0>0@1$3@2$0@2$1+iovgk8^5@2$2^5+iovgm4@1^b^6>0@1$7^5@1$7^5").
Proof.
Ltac trz AG WM H ZT := eapply (rw_cells_transport_pt _ _ _ AG WM); [exact H|];
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Z.mul length];
    let Ha := fresh in intros ? Ha; apply ZT; clear - Ha; lia.
ltac2:(KReplay.run1z (kr_t_AG_Free ()) ["HCW"] "##c?p'0h04__x1h14__p1h24__p2h32H0h47__arithh54__ffh68__varmaph75__with81ah91Hh:1bh;1gh<1xi001xh=2AGh>2FXh?3FXah@3FXbhA3FXchB3FXdhC3FXehD1PhE2WMhF2ZThG2bbhH1mhI2mahJ2mbhK1nhL1yp%0p&0p;3p;1p;2p;4p;6p;9p;8p;<p;Bp;7g00BAk301Tg00CIk300Tg00DLj13Tg006:R0j2!sD$E1j1M!s/$OR1j2!sN$5aj1W!s:$lj1;Tg00FQj26!s`$Vj24!s8$mj1[Tg00H8j1\Tg00I7j1NTg002Nj1^Tg00J;j4PTg00K@j1b!s/$^j1fTg00LAR2j2L!s1$[j1iTg00MZj1XTg00N^j1GTg00O=R3j1HTg001Zj2K!t+$4j3J!sC$]j3OTg00PCj1h!s/$aj4~Tg00QDj6U!s/$mj4S!se$:j1}Tg00RTj2|Tg00S2j1z!s/$Pj1yTg00T;j2x!s/$^j1wTg00U@j2v!s/$bj2uTg00VNj3t!s/$mj4qTg00W_j1QTg00Xgl9RTg00Z<j4eTg008lj4Y!s8$Vj8pTg007lj3oTg00[[l<nTg00\@lBr!s/$fl<sTg00]Kj2m!s/$nj4`Tg00^Yj7cTg00_=j3l!s/$`j7dTg00`Dj8k!s/$hj6jTg00aLj6{Tf0R4#3#3p=C%3!s0$#3p=F!s2'Mp=>f2R5f1R6'6/44p=D%;4#3p=8%34#;p=:%;!s-$9%34#Mp=ag00b0R7?o64p=@g00c4R8P6g00d6R9P4CPp=ZP8P5P6!s3%<!sx$!tH%]1164,45p=5g00@NR:/K4p=Bg00e@R;P:!s$$3P3f5R3f4R<f3R=!sq%M<np=g!sH&!s$%1P4P6P5P1P=P<P3f6R1f7R>f8R?f9R@MBrp=V!sP$0P>P0P1P3P<P!sv+sp=T1m:4p=7P5g00e_R0g00f>RAPAg00f^RBP:!uQ$g>P4C`g00geRCFcp=AAl:64p=EP5P0PAPAP!sQ'hEP4C`P!sL$?!sD-6P4Fdp==P=!s9+!tV$Gkp=2P6!s;+4Ejp=_!sL0!si0E{p=Ip-0R0\:g00hlS00Q00B01564B00856g00ioRC#3RD#3RE#3RF#3#CRG#C#FRH#3#>RIg00jT,147D4g00kYRJ%MERK,0J,167D6#Wg00l`RJ%8G#F#:#8#>RL!sE$57D5#W%;D#CRD#9#9#8#F#8#9#>RJ/6=S01%;CRM#:RN#C!sG+9!si$O,1=RP'4#W%3!sc%F#:RD#3#:#>RQ!s|$#8#aRD,1<7D<#Wf:RRP3O1[[[[[^8:%[<RSP8P3g00mg%MH#\#N%^7R7'@RHCPS02!sD&o1RT%\9#N/@7R9CP%bG#fRG%N4/@7RU,Z1X;G'Lg010:RV%;NRN#3RW#9#MRX'0RY%MCRZ#i#X/@7R[5<3%bF#fR\%;MRM#8!tv$],0VRV%X!sz$^5<1X:\'LPSQ!tU$1PTP9CP1Z?UX;G,LGP2PG1Z@UX;GA<@Y[f;R@?<V^X:\,L\%[R[[P41Z@Uf<RR?<Y[f>RY!sG,P2P\f?R2!s8&%[YP4fA!sH%%CM#:#CRM#3#8RV!wX$!w\%9=<YH%:W#]#]!w-$W%:V!u6$9#>RV#\!vA%T5<YS03fBR8?<VUX;GS04,LGS05%;E#C#9RE#;!xz$:!s$$>RU/0XRS=<Y[S0610U]R_=<8^X:\S07,L\S08'4S09'4S0:'4fCR^P8PYf@R`P2P9PHPR1694RRg011A#GRa#G!s$/Rb#HRc,09Rd754P`P61696Re116dRf'4%MFRF,09Rg95e6RhPePfPeP4X<:RfPFO1Ri,09Rj,161K0eAJ0eee9OeePf1164#hXL:X<:ReP6P6%B6RkPdPjPf!s$$:P:g011`1064C~#BXH:XK:RjP9P9%B9PcPiPfPf%H4#BX<;S0;PbPF%BFEgRbM:VGTEUP4CSR;Phg012DRd#^Rl%}dRd1|:6Rm%z:Rn%y:Ro%79Rp1x:CRC5AoRq%7FRr,Ep9?oC5=o%wARA%7I=AoC%;M!|_$F#>RM#7!sH&RpC21voBRBP4P5g00<7Rsg00>BRt'K1u45=Jstdg00@0=t:6CqRtb5b6b7X0:A5R4g116M9DI6RI[^0:P4P=P6O2RMb4b3P;PhPlPdPmPnPo1_o=Rs9=oqRqPAPo!s8$<R<%3E!y4$F!y2$E#7Ru%7K'E9?oCCIRvC2PBP!tD,X10X2014R6Rw10EKRK95=6g00AHRx[Ry[^0:^10^20P416E=Rz11=gRg!tg$4!te5P!t[&P<%;N#9#C#:#9!vE$N#7R{%7L!tY+|!tY90NLRL95=6Px[R}\w!tO0N=R~P!tKG7O!t4%S0<!t58A5=6OPx[S0=!t10Q01!t-ID!u<&q!t,<DPx[Rh!u72Q=Rw!t//O6W9X8:%QH#H,0995R4fEP6O1RR[^8:eM9RQ03Q0:P!}k$P`P2PWPTP@16W4R@10WcR9!}M+W6RH1169Rg'410WFR;95H6ROPHPgPH10WiRg!}=%HAJ0HHe9OHH!}d$6P6PkP9Pg!}-&jPWPW%BW!|o$!|W0gPO!v0,%7WR9=AoC1E9r9?oCR95=oPAPp!v52114;R;,4@P!{@%!{8%!sr0A=os9R9!w%%AAouCP<CI!zn:6;R;ADE6=Px[!zb01=K16W=RK!x3-!t50P!t0,{!t0=ADN!t&$\;!t'1LP!t#D%7J=Ao!t%$RL!t':J!t'$RJ!t,0PP!t'GQ!t'+!{@:DQ!t'%x!u23DRD!t//!z9+T#H,0W95@4P!z3-5Q09PGQ04P>!z:-V%N>/@7P116V4R110VcR>!z>+V6R@116>RW'410VFRF95@6RTP@PWP@10ViRW!z>%@AJ0@@e9O@@!z>->PW!z>+VPV%BV!z>5bPT!z>/VRi=AoCRc1Ei!z@$!z>9A514F!z:0!sn0A=ocsRcPAP!#5w:16RiP!#5e/Pz11=FRF!wy-!sz0PcPAP!#5;8P}\i!sp/~P!sl@Q!#4s9Q0=!sn0Q01!soAP!#4\8Ph!t]1w!sl/!y='N?/@7#Q#H,0V951!yB-CeQ06Q08!y=-SP[P316S4R3%HaR1,0SRV!y=+S6R?116VRF'410SZRw95?6RiP?PFP?PfPZO1RF,0SRh!yD%?AJ0??e9O??!yD-VPh!yD+SPS%BSAJ:SSeP1PFPfPfQ0;PaPZ%BZEgRa!yZ/hPi!yZ/URU%7X'ERX!ya$V%7ZR?,EX9?oCRX!#5#;wRq,43!yk0!t#0A=oVsRV!yk>36Rc!yk6wRw!x4-!sz0PV!yk?c!yk1!sl<A=osXRXPAPL!th:6qRqPJ!th0P16S=!th>XPAP!zf9Px\q!sp/D!th/!yv'Q[#H,0S953!yq-P\Q07P6!yp-_%X6/@7P416_4R210_1R8!yp+_6R`1168R^'410_ZRZ95`6R3P`P^P`10_FR^!yi%`AJ0``e9O``!yi-8P^!yi+_P_%B_AJ:__!yi%!yY0aP3!yY/],EURU!yU$]1EU?!yQ$C!yQ<ZRp,42!yQ0!sw0A=o]sR]!yQ>26Rv!yQ6ZRZ!wg-!sz0P]!yQ?v!yQ1!sl<A=osCRC!yQ?pRp!yQ5_=RP!th<C!yQ?p!yQ1P!yQ5X5!#4I'_952!#4I/CY!s$%%[YeWCXG\P6P4O2n20010!s#$121!s0%W9WBWAX;G!sI@@W?P4GpW>WFWEW=WJWIWDo"). Qed.

Section FreeGlue.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  Let lcount := qb_count lb.
  Let c := kBatchClass.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x090c40 (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).   (* [comment removed for export] *)
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 32768).
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  (* [comment removed for export] *)
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.
  (* [comment removed for export] *)
  Hypothesis QSZ : size <= kQuarantineMaxSize.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.
  (* [comment removed for export] *)
  Hypothesis PROOM : pusage st + COLD_COST <= B_PRIM.   (* [comment removed for export] *)
  Hypothesis ROOM : rg_mapped_user (get_region st c) + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x090b08) fc None m (seg_rom asegs).

  (* [comment removed for export] *)

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OKs : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OKs). Qed.
  Let WFs : WF st. Proof. exact (proj2 OKs). Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Let HC24 : 0 <= c < kNumClasses. Proof. unfold c, kBatchClass, kNumClasses. lia. Qed.
  Let QSZ2 : size <= kQuarantineMaxSize /\ size < 2^32.
  Proof. split; [exact QSZ|]. unfold kQuarantineMaxSize in QSZ. clear - QSZ. lia. Qed.
  Let DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Proof. npose DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & G12 & G13). clear - G11 G13 LO. lia. Qed.
  (* [comment removed for export] *)
  Let ZHs : forall a, 65536 <= a < AIMG_TOP -> ~ (AIAINIT <= a < AIAINIT + 4) -> ~ (AIAINST <= a < AIAINST + 0x81030) ->
                      ~ (2748504 <= a < 6942832) -> ~ (2682952 <= a < 2682980) -> outside (free_head_W lo (bv_unsigned sp) TH U size d) a.
  Proof. intros a Ha N1 N2 N3 N4. apply (ZH_lo s m d lo (bv_unsigned sp) ch R CHIN UHI DPL LO QSZ2 a); [clear - Ha; lia| assumption| assumption| assumption| assumption]. Qed.

End FreeGlue.
End HCW.
(* [comment removed for export] *)
