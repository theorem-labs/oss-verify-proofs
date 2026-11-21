(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, lemmas added for the revision. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import LazyRestrict LazyLedger AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require LazyMadvise.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX AsDepotInv AW_DepotFrame
     AllocWalkKit SecLazy SecLazy2 AS_SecRecycle1 AS_SecRecycle2 AG_Malloc AG_Malloc2 AG_MallocModel AG_WFHit AG_FreeModel AG_WFFree
     AG_RepQ AG_RepQFacts AG_RepQFacts2 AG_RepQFrame2 AG_RecycleModel AG_WriteSet AG_RecycleDefs AG_RecycleSecModel AG_RecycleSec1.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_RecycleSec2 () := KReplay.lz_vm "#%$OK47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!sg+4Init9Datatypes4prod!sF?list00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib:LazyLedger9nooverlapC13~~~C46Stdlib5Lists4!s+#2In!tM25Logic2eq!tG]2hi!t@&!sg[lo!sg%K!v9A1!sFB2C5!ui&6ZArith6BinInt1Z2le!un9or00K!v0;1K!sZ;1C!s@76eq_ind!s\<2C!u6;8!u6#!sb1!za=3!uA85False!yu4!sC%3an!z8$!v=&7Sorting;Permuta!z{#!s2/00C8!x9N2As6SecGap4zsum!x:'!t;&9micromega6VarMap1t01I!sD?0!sD6=RingM!s4'7Formula!x'#!sQ47Env!sT#5PExp!wr$!sI45Tauto8B!sm&!sH6:Z!t;+=Z!sT$CheckerC!u0<4find!sqAC!sq0_sou!xa?1Z03!uV>3Pol!{z>3nat02K!viC5Psatz!sOM4!sOK6K!v%@;!}Y%!yr$!tL8!x~,!sDA3!xqE2!|eG!vh=6op!{|$2!t8E3!#41;3ad!y3,!}77?!s2-!~i%!w-B!{k+1K!{H<G!sJ'4!sJF8I!zI?0!t_D3Op2!|}>5eKind!#;E<unit!t48!se%4kind!#8R>!sf$!#3`6!z4;0!}1@1!tx=bool!#9-3!sF3!}PB1!|,N1!#75R7AG_RepQ<AREPQ_placed!#=;U>AsanAllocModel6as_sec!#?F<<nth_error_InI!t8_schunk00!t:&!uvR>!uv$cycleSec16rs_bnd!srh8!sr#ands!sth7rs_pnew!ssll1in!xWe:sc_map_beg!x['!#?<6not!s?85proj!zsT8!tN$Rep6AMODEL!v2Y9!sl'X7akernel!snd!t]%X!snc9depot_cov!spY!v>+?amaps_in_l!#Gf#!sudshadow_visible!sub7ABUDGET!smb4a_st!{0e7as!{0#s!spfmp_ki!#3L&K!sp^5m!#:i#3!spl4!uTibas!xk'!#RE?7Z_to_bv!t>csiz!t>&!#<9<!#S:#1C4ELinuxProcessSemantics?!s<25State8m_vm!xc$!s]P7vm!yA$!#>T?!#Pr<3pow!#Sc9x00!vpA;bv_unsigned!u'Q;vm_noac!s;#!|z\3a_L!yYV<LazyRestrict:in_rangesb!zLe;!#9v%!y8,!#VZZ>entries_nowr!#Xi'!#<VSS_Sec!#<Y%28rs_m!tu#!stY7Sec!to#:nonvm_sam!#6qV3Lib4TacX2wz!}k'!yOO:!v~#remove!z0Ureserv!zjS8vm_limit!s]Q<!}N#!#?t#as!tzR6vm_brk!t>Ustart!saU=!#=/#subtract!|[^eager_used!#<5ZsS!#=k#5acei!zgZ:AsDepotInv4d_n!~6'!#5W;mul!t1a!#3A'!ud[2sh!tsCdiv!#5~[5a_fs!u}C6modulo!#`z;6length!#G_2Peano2ltI!tkR<!tk$WalkKit6hidden!#MM'!z{P9a!sp#_top!zwP8HeapCeil5h!z%]!w%/thr!skectx!skb4a!zN^!sj,pa!yFB2lt!t-\2RB!tpeZ!w5Z!#LH+4hcnt!ske!#VY+!#>y]4zlen!tZe!sk,!#;cPregion_free!tM]@sh_!|Z#ing!#B2$!#5ma;!#8S#_fact!#Lw%!#nb7!#m<#1!wC_=as_n!#>\+!#6#Aof_na!#V@88iff_refl!#b+5;ZifyClasses!#q%#ff!sLB9and_morph!sOB7rew!sv$!u&24Znat5Nat2Z9is_nonneg!sr69SatDivModCZ_mod!sP&!sWJdiv!sW2!vY;>pow_pos!sNC:!sN#!sJB7compare!#iSD7!z?P3Lib6M!#B0$!#LJ&_lit!y+B7!u|#mod!sG<=!vv#!ur#boun!sMB!vi#!sM15!uO$8PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL&!#ogJ7!sOK5!#g1M3!#?>;3snd!#Pt@D!#Pt,_!#Nm&!sYA:b!wS$ulusc!#4+Q!#b{02?!$$,'!tI#!#c''!#gk56filt!#vg,!sA-9!sA%_In!u}=fs!#J~;5Riscv7Prelude6bv_eqb!sp<4negb!#Dw<!sa$!sC&4Bool!s'$=!s[#_true!#3N6!{L,eqb_neq!|`T7ZBridge8!u3%_Z!vf'!#6C6!$#v$_r!#SCZ5zcov!#T}V!sj-@!#Un+_!suf:!sj$!w#$!#:h=2ex!#t7,!yW-7ex!s2#b!sB7>!sB&_!s-%!xh=le!yK>and!y-8!s>#!y-E6leb_le!v<P9!v<#Nodes?map_contains!|3#!#>uT!yz#9LiaTuning9zify_done!#Bwd;ch_user!#mk,!st^<ch_!#s%#!suZ!yi-4zin!zTbC!zT%!#UT0!{Nbinb_fals!#D'Y!#]J14rs_!#p`c6ak_l!#Si'!smbl!#4h=9!$4;#_ind!v^[D!wR0!#a40!sy[!#:`+!#^z,!sy`I!#b|0!s~a!#wj2get_!#KU$!sse>rg!tk#ped!}z$!xpY!#h>-S!sib4a_A!#i&c;pages_total!t^dP!$@UW!w{3as!wz&s!t_b<!t_#!srj4disj!sjY!#ic&?!#ic+_atop!~[>8eq_trans!#8n_as_space!#9eh:!#U-%!ss,!vjXKit=!sp,_eq!ss&!#>M;eq_dec!#s]16Specif7sum!$3P$!sf<;lt_ge_case!#@^=sub!#OcD4!yT\9!$3E$_ok!vY[!#Wm%4aapp!{1b5akobj!skd_!{%,!sk^bot!skb8!v1#_en!$,%V3Lib2Nd:and_elimF5!t[YB!#OO/!|=$9secdel_l1!syl>!sy+_perm!vV[G_WFHitB!$Ac-!#P~%!sxU4!}?#4KInv3e!#8L'!taR!#AM,schig!#B<&!}G'!$Cq6!u40!#me$!#TLa9zsum!vw/!#Lk<tb!#L+=tb_!#iET!uy,Bhcnt!#A<,!#U~+!sy^len!sy8!#aA@3inj!sIB5mkrel!udn!$6:Z!ud>le!~xg!$3q%!#<0O;LazyMadviseI!#j5,!#M<7!tl`6!sk];!sk+10!slh8!uGg9!z`'!$$EO!#US-!#B7+!#X/$7!s+#Def3map!$O0E3!sJF5!sJF7!#?>D!smG6!#5d?!$RW/map!}lEap!sKC6!sK$2!$KI^7mapping!#|{&!$OUA2!x\QBtarget_!#}J$!$/|$!#3<[4AHC!tt&!$Qk;!$Q'#!#E@3!#p#,6inj_lt!$U<H3!sMI5!#=wT!#AO&AFS_SIZE!#:n8!u--8!u-#succ!x[_!$B#%!xY'!spe2!spl6!spl8!#:<X5ASegs8AIMG_TOP!#9AU!t]29kPageS!$=rX!#O?2kSpac!ssj@kPtrArrayR!#{I$!vOY!#L_'6AHI_LO!tge;kNum!#51%!stgR!#=e#!vS-!uX[9ALOWSH!u[,!yrX7!yr$!sj[!#5^/L0!skc7ASECMAX!t[fSB!t[eHSB!#Vf'!$J}74True!$yM=:!#~^$ison!$uB9!sh%!$M{Q9page!$Ho#!$`v_!#E/$!$:O+!#9L38ZifyInst7Inj_Z_Z!vk]:ak_sec!$Ue+!#N3a7keep_r!}H'!vy7!$^H#2!u%S;AG_WriteSet4avm!$:i%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14prod37Corelib4Init5Logicm02or69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~n92hin92lo36Stdlib5Lists4Lists02In46Stdlib6ZArith6BinInt1Zt82lek14listm02eqn99nooverlap01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6SecGap~~~~~~hh04zsum36Stdlib7SortingbPermutationhl4bPermutationk14boolk15false69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hoeach_primary79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash2AG_RecycleSecModel~~~~~~htdbsec_map_beghoeasc_map_beg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~ik3cdepot_placed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~ip35aceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~ita7AMODELXita9depot_cov79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~jj13a_Ln9eentries_nowrap" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Lemma nooverlap_in_in : ltac2:(zQ "b1!h9!jc!l9!n4!r6!rb!t3!v0!v5!vc!hg1&@2$2@1$1@1$0#k0@1$1@1$0#k0>1X@1$8~0>2e1~0>2e2~0>0@1$a^3>0@3$6~0^3^4>0@3$6~0^3^5@2$3@3$9~0^5^4@2$3@2$7@1$4^5@1$5^4@2$7@1$4^4@1$5^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec2 ()) ["HCW"] "##4'h02e2h12H2h22e1h31Hh42H1h52NOh61Xh71Lh82e'h91Dh:2IHh;1eh<1op;1p;2p;3p;6p;5g0000j17Tg000Uj1DTg0013j1@!s/$Vj2?Tg0026j1C!s/$Vj18Tg003^j34Tg0045j33!s/$Oj10Tg005Pj11Tg006Qj1>Tg0071j39!s/$Qj22!s/$mR0j26Tg008Gj2B!s/$aj3=Tg009;j6;!s/$Wj3:Tg00:1j5ATf4R1f3R2f2R3'2f1R4f0R5'2'6'6p=51234/65p=<g00:S#7!s$-D#@R6/?6R6#CR7P6%83A4632A4631A3612%01R8%12%02%11R9D5[[[^06^26R:X67%>6R;#8A463;R;g00;8f5R<=361%0<P9P8%1<D5R8P4n010!s#%X1;W4W5X06X26A9612#8A96<19463f6R2=96<9463g00;Uf79465f9R;#0R9%14R=%04R>%1;R?'23<[^86%82P8P3A465;f;R8#0R@%18RA,2>7<=!sI%;P0f8R=9368f:R>946=A36;=P9%1=%0=P?D5P<f<R?=36;P6f=R=A365>%05R9%1>RB%0>RC%15RDD5X26P0A36=;REA46;?RFf>RG=36>RH%0GRIPBPC%1GRGD5P2P6f?RJf@RK=365%0KRLPDP9%1KRKD5X06A36JJ%0JRM%1JRN'2RO/6O1B6J3=P8P5E;X3HP5O1A46>=ROA36J812@N9<MAP<P8P5O23:W1P5O1n20!w6'2!s-$!s'$P>P5E;W3!sl&;8P0PEPFA368>P@PBPCPA!tz%PJA36=5%0=R2!tu%=R9!tu'?J%0?/2NRJ%1?,2MRD'6P<P?P3O216DJP012L9122KfAR2#1,2IRI%02/2GRG'6P5fB!s=%MRM!s=$NRN;:5X7G!tg$=MN5X7I!u==b<3:!v00P=P?P8P1P3P5O5X1O!sb41!sb'W4!sB91000W5W9P4P5O2!sF-1!tG%00W1!zt,X::X67X;6P5DAW6o"). Qed.
  Lemma zsum_perm : ltac2:(zQ "50!hgd!v5!hkc!vc!hn0>1l@1$1$0>2l'@1$1$0>0@3$4$0^2^1@3$3$0@1$2^3@1$2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecycleSec2 ()) ["HCW"] "##5,h04__x1h14__x2h24__x3h31lh47__arithh54__ffh68__varmaph75__with82l'h91Ph:1xh;3IHPh<4IHP1h=4IHP2h>2P1h?2P2h@3l''hA1yp;1p;3p;2p;4p;9p;7p;8g0026j1CTg00<0j3<!s/$[j11Tg006Qj1BTg00=]j1TTg00>;j1M!s/$Yj1KTg00?Dj2J!s/$gj2FTg008Gj2DTg00@Ij2VTg0045j3>Tg00A5j3U!s/$Tj4STg00BFj1O!s/$dj2NTg00CEj1A!s/$dj2=Tg00DMj3?Tg00E6j37!s/$_j2;Tg0071j38Tg00FKj2@!s/$ij4ITg0000j1HTg00GGj2:!s/$jj1GTg00HOj1LTg00I1j35!s/$Tj26Tg00J1l9E!s/$^j4PTg00KIj7Q!s/$mj8RTg00LQR0f1R1f0R23>p=0P0P1g00LoP2CPp=3!s4$MVR3g00N5R4P4g00NUR5P2g00O5FQp=2f3R6P3P4P4P5f2R3P1P2GRp=9A8012p=4%C0R7A<012R8P0%11R9%12'0X87X37g00OUR:#BR;%C:R<%T0%M0R=%K0R>g00PAR?,J0R@/3@'21F>5R5P2P3g00P_R@g00Q?RA'D1V23=>@AdAU0?1CSRAb5b6b7A>0??P2b4%B0#1R?/0?e%13R?/09g00:SR@#O,N0RBg00Q_RC#ARD,=0RE5?01=0CRC570RFg00R>RG';=8:;P<P01@03P11@06CIRHP=P>%H@,:0RI%G!s-$J'3,2>%L4R41:0@R@=50IA50@JRK!sA$C9P5P!tu&X00X10X2010131613RL1616'0[^00^10^20P2%16RMf4RN#1ROf5RPP1O4b414N6#114N3#1'0eW;X98!v{%X:0P;P<PHP=A50IJ950@A50I!tN%!tL762L1623,61'0!tH-P9P6P3O3b41432,41#11412,4!tA%X37XA0X:0A<03110M?A<06310OM%A!vl$D9?0B=70F/;GA70EC970D/;G=8:;58:!tr%P>13JI,2>P4P>13@J!s1$13@I!vL$!vN:3110161036[!vK/f6#1R0%1Pf7#1P1P6O5b4100OeW=W?W<W>X@7!vE%P!zs$M9EW9X87W3o"). Qed.

  (* LPS revision repair (75d69e00, checker 2c6b6db8).  At the revision rs_model's vm_maps
     conjunct is maps_subtract (As/AS_SecRecycle2.v:62), and under nooverlap that list is
     List.filter (nz_at (a + msz)) (map_remove ...) — LazyLedger.maps_subtract_rm_nz, :541.  The
     hsec counts therefore need the sublist bound that the map_remove forms already have.
     These two are the general case of As/AllocRepX.v:95-104 (hcnt_map_remove_le and
     hlen_map_remove_le are their f = negb (fst _ =? a) instance) and are proved the same way. *)
  Lemma hcnt_filter_le : forall (f : word * word -> bool) (E : list (word * word)), hcnt (List.filter f E) <= hcnt E.
  Proof.
    intros f E. induction E as [|e E IH]; [cbn [List.filter]; lia|]. cbn [List.filter].
    destruct (f e); [rewrite !hcnt_cons; destruct (ehigh e); lia| pose proof (hcnt_cons_ge e E); lia].
  Qed.
  Lemma hlen_filter_le : forall (f : word * word -> bool) (E : list (word * word)), hlen (List.filter f E) <= hlen E.
  Proof.
    intros f E. induction E as [|e E IH]; [cbn [List.filter]; lia|]. cbn [List.filter].
    destruct (f e); [rewrite !hlen_cons; destruct (ehigh e); lia| pose proof (hlen_cons_ge e E); lia].
  Qed.

Section RSModel.
  Variables (s : ast) (m0 : mem) (XC XB : list Z) (ch : chunk) (idx : nat) (h lsth : schunk) (d : depot) (lo : Z).
  Let st := a_st s.
  Let T := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let pa := a_pa s.
  Let nch := zlen (as_sec st).
  Let nres := as_n_reserved st.
  Let mch := ch_chunk_beg ch.
  Let U := ch_user_beg ch.
  Let a := sc_map_beg h.
  Let msz := sc_map_size h.
  Let lst := sc_map_beg lsth.
  Let l1 := secdel_l1 (as_sec st) idx.
  Let st2 := remove_map (set_sec (del_state st ch) nres l1) a.
  Let L2 := rs_L (a_L s) a msz.
  Let s2 := mkAst st2 T CTX (a_fsb s) L2 (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).

  Hypothesis RQ : AREPQ s (mch :: XC) XB m0.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis SEC : ltac2:(zQ "40!hnf!ho6!vc!hsf@3$2$0@1$3?2ch$1").
  Hypothesis QUAR : ch_state ch = CQuarantine.
  Hypothesis HIDX : nth_error (as_sec st) idx = Some h.
  Hypothesis HMAP : ltac2:(zQ "40!vc!hgd!ii6!ij5@3$0$1@1$3?1h@1$2?2ch").
  Hypothesis HLAST : nth_error (as_sec st) (length (as_sec st) - 1)%nat = Some lsth.
  Hypothesis DPL : ltac2:(zQ "10!io3@3$0?5HCEIL?1s?1d").
  Hypothesis LO : ltac2:(zQ "20!it1!v0@2$1@1$0?5HCEIL?2lo").

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let HIN : In h (as_sec st). Proof. eapply nth_error_In. exact HIDX. Qed.
  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SECP & SEC2 & TCX).


  Let BND : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 7430144 <= CTX /\ CTX + 160 <= aceil /\ 7430144 <= pa /\ pa + 8388608 <= aceil
            /\ 7430144 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7430144 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
            /\ 7430144 <= a /\ a + msz <= aceil /\ 8192 <= msz /\ 2148314624 <= sh a /\ sh a + msz / 8 <= sh aceil
            /\ 1 <= nch <= nres /\ nres <= 1032192 (* [comment removed for export] *) /\ 7430144 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil
            /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ (idx < length (as_sec st))%nat /\ 7430144 <= lst /\ lst + 8192 <= aceil /\ lst mod 4096 = 0.
  Proof. eapply rs_bnd; eassumption. Qed.
  Let BANDS : hidden ((T + 4096 <= 65536 \/ (7430144 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa)
                   /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                   /\ (d_sb d + 8 * 32768 <= 2147446784 \/ 17594333495296 <= d_sb d)
                   /\ (a + msz <= 2147446784 \/ 17594333495296 <= a)
                   /\ (sh a + msz / 8 <= 2415881728 \/ 2201439137792 <= sh a)
                   /\ (a_fsb s + AFS_SIZE <= 2147446784 \/ 17594333495296 <= a_fsb s)
                   /\ (lst + 8192 <= 2147446784 \/ 17594333495296 <= lst)).
  Proof. eapply rs_bands; eassumption. Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).
  Let PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz T kPageSize /\ disj a msz CTX 160
            /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 32768)
            /\ (forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> disj a msz (sc_map_beg sc) (sc_map_size sc)).
  Proof. eapply rs_pnew; eassumption. Qed.
  Let L1IN : forall y, In y l1 <-> In y (as_sec st) /\ sc_map_beg y <> a.
  Proof. eapply rs_l1in; eassumption. Qed.
  Let SUB1 : forall y, In y l1 -> In y (as_sec st). Proof. intros y Hy. exact (proj1 (proj1 (L1IN y) Hy)). Qed.


  Section Model.
    Variables (mo mo2 : Model).
    Hypothesis AMX : ltac2:(zQ "10!jh9@3$0?5HCEIL?1s?2mo").
    Hypothesis DCOV : ltac2:(zQ "10!ji4@2$0?1d?2mo").
    Hypothesis MO : rs_model mo a msz mo2.
    Hypothesis NWL : ltac2:(zQ "20!jmf!jn6@1$1@1$0?1s").          (* [comment removed for export] *)
    Let hh := m_vmmaps mo.
    Let h2 := m_vmmaps mo2.
    Let L1 := a_L s.   (* [comment removed for export] *)

    (* LPS revision repair (75d69e00, checker 2c6b6db8).  The three proofs below were replays
       whose first error was 'Illegal application: the term and_elimF9': they destructured
       rs_model's OLD vm_maps conjunct (map_remove) and then used it.  They are now plain text,
       STRUCTURED after the plain-text proofs of
       a donor tree:projects/openssl/echconfiglist_parser/proofs/lib/As/AG_RecycleSec2.v
       (294 lines, 0 replays), with every VM2 step RE-PROVED against maps_subtract: that tree's
       own rs_model is still the stale map_remove one, so its VM2 steps are not transportable.
       The bridge is LazyLedger.maps_subtract_rm_nz (:541): under nooverlap, with (wz a, wz msz)
       in the ledger and 0 < msz, maps_subtract X a (a + msz) is
       List.filter (nz_at (a + msz)) (map_remove X (wz a)) -- the old list minus the zero-size
       entries based at a + msz.  So RM gains the hypothesis 0 < bv_unsigned (snd r) (every
       caller has it: a covering entry, a positive-length containment, a placed section map),
       nooverlap/entries_nowrap go through filter_sublist_nooverlap (:297) and
       entries_nowrap_filter (:564), and the hsec counts gain hcnt_filter_le / hlen_filter_le.
       No statement of this file changes.  The one literal, 2201439137792, is this tree's own:
       it is the bound in BANDS above (sh a's high band), and the step that produces it is
       AHSB_eq, not a transposed number. *)
    Theorem amodelx_after_rs : AMODELX s2 mo2 /\ depot_cov d mo2.
    Proof.
      destruct AMX as [AM AK]. destruct AM as (AIL & ASV & AB). destruct AIL as (A1 & A2 & A3 & NOV & NW & NWA).
      pose proof MO as M; unfold rs_model in M; cbv beta iota zeta in M. destruct M as (NV & VM2 & VR2 & VL2 & VB2 & VK2 & VS2 & VA2 & EAG2).
      fold hh h2 in VM2, VR2, VL2, VB2, VK2, VS2, VA2.
      pose proof BND as B. bands_as (BT & _ & BP & _ & _ & BA & BS & BF & _).
      pose proof AK as AK'. destruct AK' as ((K1 & (K2a & K2c) & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11) & AKR). fold hh in K1, K2a, K2c, K3, K4a, K4b, K4c, K6a, K6b, K7, K8a, K8b, K9, K10, K11.
      assert (SHLO : sh AHI_LO = 2201439137792) by (rewrite <- AHSB_eq; reflexivity). pose proof sh_ceiling_range as SCV.
      assert (WA : bv_unsigned (wz a) = a) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      assert (WM : bv_unsigned (wz msz) = msz) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      (* The donor asserts SHB here and never uses it (its own proof reads BA, B, SHLO and SCV
         directly), and its right disjunct does not follow from this tree's BANDS, so it is
         dropped rather than re-keyed: nothing below refers to it. *)
      assert (E0IN : In (wz a, wz msz) (vm_maps hh)) by exact (K7 h HIN).
      (* The revision's maps_subtract, as a filter of the pre-revision map_remove. *)
      pose proof (maps_subtract_rm_nz (vm_maps hh) (wz a) (wz msz) ltac:(rewrite WM; clear - B; try acb; lia) NOV E0IN) as MSEQ.
      rewrite WA, WM in MSEQ.
      assert (VM2' : vm_maps h2 = List.filter (nz_at (a + msz)) (map_remove (vm_maps hh) (wz a))) by (rewrite VM2; exact MSEQ).
      (* [comment removed for export] *)
      assert (BASED : forall r, In r (vm_maps hh) -> bv_unsigned (fst r) = a -> r = (wz a, wz msz) \/ bv_unsigned (snd r) = 0).
      { intros r Hr Hb. pose proof (bv_unsigned_in_range _ (snd r)) as RR.
        destruct (nooverlap_in_in _ _ _ NOV Hr E0IN) as [E|[D|D]]; [left; exact E| right| right];
          unfold LazyLedger.lo, LazyLedger.hi in D; cbn [fst snd] in D; rewrite ?WA, ?WM in D; clear - D Hb B RR; try acb; lia. }
      (* [comment removed for export] *)
      assert (RM : forall r, In r (vm_maps hh) -> bv_unsigned (fst r) <> a -> 0 < bv_unsigned (snd r) -> In r (vm_maps h2)).
      { intros r Hr NE NZ. unfold h2 in VM2' |- *. rewrite VM2'. apply filter_In. split.
        - unfold map_remove. apply filter_In. split; [exact Hr|]. rewrite bv_eqb_Z, WA. apply negb_true_iff. apply Z.eqb_neq. exact NE.
        - unfold nz_at. apply negb_true_iff. apply andb_false_iff. left. apply Z.eqb_neq. clear - NZ. lia. }
      assert (KEEP : forall x : word, in_rangesb x (vm_maps hh) = true -> ~ (a <= bv_unsigned x < a + msz) -> in_rangesb x (vm_maps h2) = true).
      { intros x Hx NI. rewrite in_rangesb_zcovb in Hx |- *. apply zcovb_true in Hx as (r & Hr & R). apply zcovb_true. exists r. split; [| exact R].
        apply RM; [exact Hr| |].
        - intros Eb. destruct (BASED r Hr Eb) as [->|Z0].
          + unfold LazyLedger.lo, LazyLedger.hi in R. cbn [fst snd] in R. rewrite WA, WM in R. exact (NI R).
          + unfold LazyLedger.lo, LazyLedger.hi in R. rewrite Eb, Z0 in R. clear - R. lia.
        - unfold LazyLedger.lo, LazyLedger.hi in R. clear - R. lia. }
      assert (MC0 : forall xa xn y : word, bv_unsigned xn = 0 -> in_rangesb y (vm_maps h2) = true ->
                (bv_unsigned y = bv_unsigned xa \/ bv_unsigned y + 1 = bv_unsigned xa) -> map_contains (vm_maps h2) xa xn = true).
      { intros xa xn y Z0 Hy EY. rewrite in_rangesb_zcovb in Hy. apply zcovb_true in Hy as (r & Hr & R). unfold LazyLedger.lo, LazyLedger.hi in R.
        unfold map_contains. apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; apply Z.leb_le; clear - R EY Z0; lia. }
      assert (MCKEEP : forall xa xn : word, map_contains (vm_maps hh) xa xn = true -> 0 < bv_unsigned xn ->
                (bv_unsigned xa + bv_unsigned xn <= a \/ a + msz <= bv_unsigned xa) -> map_contains (vm_maps h2) xa xn = true).
      { intros xa xn MC POS D. apply LazyNodes.map_contains_In in MC as (r & Hr & R1 & R2). unfold LazyLedger.lo, LazyLedger.hi in R1, R2.
        unfold map_contains. apply existsb_exists. exists r. split.
        - apply RM; [exact Hr| |].
          + intros Eb. destruct (BASED r Hr Eb) as [->|Z0].
            * cbn [fst snd] in R1, R2. rewrite WA in R1. rewrite WA, WM in R2. clear - R1 R2 POS D B; try acb. lia.
            * rewrite Z0 in R2. clear - R1 R2 POS Eb. lia.
          + clear - R1 R2 POS. lia.
        - apply andb_true_iff. split; apply Z.leb_le; lia. }
      (* [comment removed for export] *)
      assert (NWL1 : entries_nowrap L1) by exact NWL.
      assert (SUBL1 : forall x : word, in_rangesb x L1 = true -> in_rangesb x (a_L s) = true) by (intros x Hx; exact Hx).
      assert (SUBL : forall x : word, in_rangesb x L2 = true -> in_rangesb x (a_L s) = true).
      { intros x Hx. apply SUBL1. subst L2. unfold rs_L in Hx. fold L1 in Hx. rewrite in_rangesb_zcovb in Hx |- *.
        rewrite zcovb_maps_subtract in Hx; [apply andb_true_iff in Hx; exact (proj1 Hx)| exact NWL1| |]; clear - B; try acb; lia. }
      assert (INL2 : forall x : word, in_rangesb x (a_L s) = true -> ~ (a <= bv_unsigned x < a + msz) -> in_rangesb x L2 = true).
      { intros x Hx N1. subst L2. unfold rs_L. fold L1. rewrite in_rangesb_zcovb in Hx |- *.
        rewrite zcovb_maps_subtract; [| exact NWL1| clear - B; try acb; lia| clear - B; try acb; lia]. apply andb_true_iff. split; [| apply negb_true_iff; apply zinb_false; exact N1].
        exact Hx. }
      assert (BANDL : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L2 = true).
      { intros x Hx. apply INL2; [exact (ak_lsh s mo AK x Hx)|]. clear - Hx BA B SHLO SCV; try acb. lia. }
      assert (BANDL2 : forall x : word, sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO -> in_rangesb x L2 = true).
      { intros x Hx. apply INL2; [exact (ak_lsl s mo AK x Hx)|]. unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO in Hx. clear - Hx BA B; try acb. lia. }
      (* [comment removed for export] *)
      assert (NWA1 : entries_nowrap (vm_noaccess hh)) by exact NWA.
      assert (NASUP : forall x : word, in_rangesb x (vm_noaccess h2) = true -> in_rangesb x (vm_noaccess hh) = true /\ ~ (a <= bv_unsigned x < a + msz)).
      { intros x Hx. rewrite VA2 in Hx. rewrite in_rangesb_zcovb in Hx |- *.
        rewrite zcovb_maps_subtract in Hx; [| exact NWA1| clear - B; try acb; lia| clear - B; try acb; lia]. apply andb_true_iff in Hx. destruct Hx as [Hx Hn].
        apply negb_true_iff in Hn. apply zinb_false in Hn. split; [| exact Hn]. exact Hx. }
      assert (NASUB : forall x : word, in_rangesb x (vm_noaccess hh) = false -> in_rangesb x (vm_noaccess h2) = false).
      { intros x Hx. destruct (in_rangesb x (vm_noaccess h2)) eqn:E; [| reflexivity]. rewrite (proj1 (NASUP x E)) in Hx. discriminate Hx. }
      assert (NWA2 : entries_nowrap (vm_noaccess h2)).
      { rewrite VA2. apply maps_subtract_nowrap; [exact NWA1| |]; clear - B; try acb; lia. }
      split.
      2:{ (* [comment removed for export] *)
        intros x Hx. apply KEEP; [exact (DCOV x Hx)|]. destruct DPL as (_ & _ & _ & _ & _ & _ & _ & _ & G9 & _). destruct (G9 h HIN) as [E1 E2].
        fold a msz in E1, E2. unfold disj in E1, E2. clear - Hx E1 E2. lia. }
      split.
      { (* [comment removed for export] *)
        split.
        { (* [comment removed for export] *)
          unfold amaps_in_ledger. change (m_vmmaps mo2) with h2. change (a_st s2) with st2. change (a_L s2) with L2.
          change (as_maps st2) with (List.filter (fun mp => negb (mp_base mp =? a)) (as_maps st)). change (as_sec st2) with l1.
          split.
          { intros mp Hin K1' K2' K3' K4'. apply filter_In in Hin. destruct Hin as [Hin NB]. apply negb_true_iff in NB. apply Z.eqb_neq in NB.
            destruct (A1 mp Hin K1' K2' K3' K4') as [INV RANGE].      (* [comment removed for export] *)
            (* The restated first conjunct (As//Bs AllocRep.v) asks ledger membership only of an
               entry whose ledger-word size is non-zero, which is exactly the entry maps_subtract
               keeps: nz_at drops the zero-size entry based at a + msz and nothing else.  So the
               guard the goal hands us is literally the third premise of RM, and the same guard
               is what the pre-state's A1 is applied to. *)
            split; [| exact RANGE]. intros POS. apply RM; [exact (INV POS)| |].
            - cbn [fst]. rewrite unsigned_lit by exact RANGE. exact NB.
            - cbn [snd]. exact POS. }
          split.
          { intros mp Hin KK x Hx. apply filter_In in Hin. destruct Hin as [Hin _]. destruct (A2 mp Hin KK x Hx) as [Q1 Q2]. split; [exact (NASUB x Q1)|].
            destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q2. discriminate Q2. }
          split.
          { intros sc x Hin Hx. pose proof (A3 sc x (SUB1 sc Hin) Hx) as Q. destruct (in_rangesb x L2) eqn:E; [| reflexivity]. rewrite (SUBL x E) in Q. discriminate Q. }
          unfold h2 in VM2' |- *. rewrite VM2'. split; [apply filter_sublist_nooverlap; apply nooverlap_map_remove; exact NOV|].
          split; [apply entries_nowrap_filter; apply entries_nowrap_map_remove; exact NW| exact NWA2]. }
        split.
        { (* [comment removed for export] *)
          destruct ASV as [V1 V2]. unfold ashadow_visible. change (a_st s2) with st2. change (a_S s2) with (a_S s). change (as_sec st2) with l1.
          split; [intros c x Hc Hx; apply (V1 c x Hc); exact Hx| intros sc x Hin Hx; exact (V2 sc x (SUB1 sc Hin) Hx)]. }
        (* [comment removed for export] *)
        destruct AB as [AB0 AB1]. unfold ABUDGET. change (a_AL s2) with (a_AL s). change (a_S s2) with (a_S s). change (m_vmmaps mo2) with h2. rewrite VL2.
        rewrite (aPhi_regions s s2) by reflexivity. split; [exact AB0|]. fold hh in AB1. clear - AB1 EAG2 B; try acb. lia. }
      (* [comment removed for export] *)
      unfold akernel. split.
      2:{ (* LPS 727298f3: [akernel_resx].  The ledger is unchanged ([VR2]), so the same intervals
             witness it; the section's munmap cuts the mappings ([VM2]), and every piece left
             lies inside an entry that was apart from the ledger ([apart_maps_subtract]). *)
          unfold akernel_resx in AKR |- *. cbv zeta in AKR |- *. change (m_vmmaps mo2) with h2.
          destruct AKR as [rx [Hrx [Hok [Hcnt [Hsz HD]]]]]. exists rx. rewrite VR2, VM2.
          split; [exact Hrx|]. split; [exact Hok|]. split; [exact Hcnt|]. split; [exact Hsz|].
          assert (HHI : a + msz <= 2 ^ 64)
            by (pose proof BND as B0; destruct B0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX & _); clear - HX; try acb; lia).
          exact (apart_maps_subtract (vm_maps hh) (vm_reserved hh) a (a + msz) NW HHI HD). }
      change (m_vmmaps mo2) with h2. change (a_thr s2) with T. change (a_ctx s2) with CTX. change (a_sb s2) with sb.
      change (a_pa s2) with pa. change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L2. change (a_st s2) with st2. change (as_sec st2) with l1.
      fold T CTX sb pa in K3, K4b, K5a, K5b. destruct PNEW as (N1 & N2 & N3 & N4 & N5 & _). unfold disj in N1, N2, N3, N4, N5.
      rewrite VR2, VL2.
      split; [exact K1|]. split; [exact (conj K2a (eq_trans (nonvm_same_atop _ _ NV) K2c))|].
      split.
      { intros x Hx. apply KEEP; [exact (K3 x Hx)|]. unfold kPageSize, kSpaceSize, kPtrArrayReserve, AFS_SIZE, AHI_LO in *.
        destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]; [clear - Hx N3| clear - Hx N4| clear - Hx N1| clear - Hx N2| clear - Hx N5| clear - Hx BA B SHLO; try acb]; lia. }
      split.
      { intros xa xn c Hc H1 H2. change (RB s2 c) with (RB s c) in H1, H2.
        assert (SP : sb <= RB s c /\ RB s c + kRegionSize <= sb + kSpaceSize).
        { unfold RB, sb, a_sb. rewrite region_beg_eq. unfold kRegionSize, kSpaceSize, kNumClasses in *. clear - Hc. lia. }
        destruct (Z.eq_dec (bv_unsigned xn) 0) as [Z0|NZ].
        - apply (MC0 xa xn xa); [exact Z0| | left; reflexivity]. apply KEEP; [apply K3; do 2 right; left| ]; unfold kRegionSize, kSpaceSize, kPageSize in *; clear - H1 H2 Z0 SP N1; lia.
        - apply MCKEEP; [exact (K4a xa xn c Hc H1 H2)| pose proof (bv_unsigned_in_range _ xn); clear - NZ H; lia|].
          unfold kRegionSize, kSpaceSize, kPageSize in *; clear - H1 H2 SP N1; lia. }
      split.
      { intros xa xn H1 H2. destruct (Z.eq_dec (bv_unsigned xn) 0) as [Z0|NZ].
        - (* [comment removed for export] *)
          destruct (Z.lt_ge_cases (bv_unsigned xa) (pa + kPtrArrayReserve)) as [XL|XG].
          + apply (MC0 xa xn xa); [exact Z0| | left; reflexivity]. apply KEEP; [apply K3; do 3 right; left| ]; unfold kPtrArrayReserve in *; clear - H1 XL N2; lia.
          + pose proof (bv_unsigned_in_range _ xa) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
            assert (WY : bv_unsigned (wz (bv_unsigned xa - 1)) = bv_unsigned xa - 1) by (unfold wz; apply unsigned_lit; clear - H1 XR B; try acb; lia).
            apply (MC0 xa xn (wz (bv_unsigned xa - 1))); [exact Z0| | rewrite WY; right; lia].
            apply KEEP; [apply K3; do 3 right; left| ]; rewrite WY; unfold kPtrArrayReserve in *; clear - H1 H2 Z0 XG N2 B; try acb; lia.
        - apply MCKEEP; [exact (K4b xa xn H1 H2)| pose proof (bv_unsigned_in_range _ xn); clear - NZ H; lia|]. unfold kPtrArrayReserve in *; clear - H1 H2 N2; lia. }
      split.
      { intros xa xn H1 H2 H3. apply MCKEEP; [exact (K4c xa xn H1 H2 H3)| exact H2|]. clear - H1 H3 BA B SHLO SCV; try acb. unfold AHI_LO in *. lia. }
      split; [exact K5a|]. split; [exact K5b|].
      split; [intros x Hx; split; [exact (proj1 (K5c x Hx))| exact (BANDL x Hx)]|].
      split.
      { (* [comment removed for export] *) intros x Hx. destruct (NASUP x Hx) as [Hx' NI]. exact (KEEP x (K6a x Hx') NI). }
      split.
      { (* [comment removed for export] *) intros sc x Hin Hx. apply NASUB. exact (K6b sc x (SUB1 sc Hin) Hx). }
      split.
      { (* [comment removed for export] *)
        intros sc Hin. pose proof (proj1 (L1IN sc) Hin) as [Hin0 NE].
        placed. pose proof (SECP sc Hin0) as (_ & Q2 & Q3 & Q4 & _). apply aapp_env in Q2; [| unfold kPageSize in Q4; clear - Q4; lia].
        assert (WSC : bv_unsigned (wz (sc_map_size sc)) = sc_map_size sc).
        { first [ (unfold wz; apply unsigned_lit; clear - Q2 Q3 Q4; try acb; unfold kPageSize in *; lia)
                | fail ]. }
        apply RM; [exact (K7 sc Hin0)| |].
        - cbn [fst]. unfold wz. rewrite unsigned_lit by (clear - Q2 Q3 Q4; try acb; unfold kPageSize in *; lia). exact NE.
        - cbn [snd]. rewrite WSC. unfold kPageSize in Q4. clear - Q4. lia. }
      split.
      { intros x Hx. apply KEEP; [exact (K8a x Hx)|]. unfold ALOWSH_LO, AHI_LO in Hx. clear - Hx BA B; try acb. lia. }
      split.
      { intros xa xn H1 H2 H3. apply MCKEEP; [exact (K8b xa xn H1 H2 H3)| exact H2|]. unfold sh, ASHADOW_BASE, AIMG_TOP, ALOWSH_LO in H1, H3. clear - H1 H3 BA B; try acb. lia. }
      split; [intros x Hx; split; [exact (proj1 (K8c x Hx))| exact (BANDL2 x Hx)]|].
      split; [exact K9|].
      split.
      2:{ (* [comment removed for export] *)
          intros xa xn HB. rewrite VA2. apply LazyMadvise.region_free_maps_subtract; [exact NWA| exact (K11 xa xn HB)]. }
      (* [comment removed for export] *)
      destruct K10 as (C1 & C2 & C3). unfold hsec in *. change (as_sec st2) with l1. change (as_sec (a_st s)) with (as_sec st) in C1, C2, C3.
      pose proof (Permutation_filter schigh _ _ (secdel_l1_perm _ _ _ HIDX)) as PF. fold l1 in PF. cbn [List.filter] in PF.
      assert (EHI : KInv.ehi (wz a, wz msz) = a + msz) by (unfold KInv.ehi; cbn [fst snd]; rewrite WA, WM; reflexivity).
      unfold h2 in VM2' |- *. rewrite VM2'.
      pose proof (hcnt_filter_le (nz_at (a + msz)) (map_remove (vm_maps hh) (wz a))) as HCF.
      pose proof (hlen_filter_le (nz_at (a + msz)) (map_remove (vm_maps hh) (wz a))) as HLF.
      destruct (schigh h) eqn:SH; rewrite ?SH in PF; cbv iota in PF;
        pose proof (Permutation_length PF) as PL0; pose proof (zsum_perm _ _ (Permutation_map sc_map_size PF)) as PS;
        cbn [length] in PL0; cbn [map SecGap.zsum] in PS; fold msz in PS; unfold zlen in *; rewrite <- PL0 in C1; rewrite <- PS in C2.
      - (* [comment removed for export] *)
        unfold schigh in SH. apply Z.ltb_lt in SH. fold a msz in SH. rewrite <- EHI in SH.
        pose proof (hcnt_map_remove_in _ _ E0IN SH) as HC. pose proof (hlen_map_remove_in _ _ E0IN SH) as HL. cbn [fst snd] in HC, HL. rewrite WM in HL.
        split; [clear - HC HCF C1; lia|]. split; [clear - HL HLF C2; lia|]. intros sc Hin. exact (C3 sc (SUB1 sc Hin)).
      - pose proof (hcnt_map_remove_le (vm_maps hh) (wz a)) as HC. pose proof (hlen_map_remove_le (vm_maps hh) (wz a)) as HL.
        split; [clear - HC HCF C1; lia|]. split; [clear - HL HLF C2; lia|]. intros sc Hin. exact (C3 sc (SUB1 sc Hin)).
    Qed.

    (* [comment removed for export] *)
    Lemma keep_rs : forall x : word, in_rangesb x (vm_maps hh) = true -> ~ (a <= bv_unsigned x < a + msz) -> in_rangesb x (vm_maps h2) = true.
    Proof.
      destruct AMX as [AM AK]. destruct AM as (AIL & _ & _). destruct AIL as (_ & _ & _ & NOV & _ & _).
      pose proof MO as M; unfold rs_model in M; cbv beta iota zeta in M. destruct M as (_ & VM2 & _). fold hh h2 in VM2.
      pose proof BND as B.
      assert (WA : bv_unsigned (wz a) = a) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      assert (WM : bv_unsigned (wz msz) = msz) by (unfold wz; apply unsigned_lit; clear - B; try acb; lia).
      assert (E0IN : In (wz a, wz msz) (vm_maps hh)) by exact (ak_secmaps s mo AK h HIN).
      pose proof (maps_subtract_rm_nz (vm_maps hh) (wz a) (wz msz) ltac:(rewrite WM; clear - B; try acb; lia) NOV E0IN) as MSEQ.
      rewrite WA, WM in MSEQ.
      assert (VM2' : vm_maps h2 = List.filter (nz_at (a + msz)) (map_remove (vm_maps hh) (wz a))) by (rewrite VM2; exact MSEQ).
      intros x Hx NI. rewrite in_rangesb_zcovb in Hx |- *. apply zcovb_true in Hx as (r & Hr & R). apply zcovb_true. exists r. split; [| exact R].
      unfold LazyLedger.lo, LazyLedger.hi in R.
      unfold h2 in VM2' |- *. rewrite VM2'. apply filter_In. split.
      2:{ unfold nz_at. apply negb_true_iff. apply andb_false_iff. left. apply Z.eqb_neq. clear - R. lia. }
      unfold map_remove. apply filter_In. split; [exact Hr|]. rewrite bv_eqb_Z, WA. apply negb_true_iff. apply Z.eqb_neq.
      intros Eb. pose proof (bv_unsigned_in_range _ (snd r)) as RR.
      destruct (nooverlap_in_in _ _ _ NOV Hr E0IN) as [E|[D|D]].
      - subst r. cbn [fst snd] in R. rewrite WA, WM in R. exact (NI R).
      - unfold LazyLedger.lo, LazyLedger.hi in D; cbn [fst snd] in D; rewrite ?WA, ?WM in D. clear - D Eb R B RR; try acb; lia.
      - unfold LazyLedger.lo, LazyLedger.hi in D; cbn [fst snd] in D; rewrite ?WA, ?WM in D. clear - D Eb R B RR; try acb; lia.
    Qed.
    Lemma avmx_after_rs : avmx s s2 mo mo2.
    Proof.
      intros x Hx. split.
      - destruct (Z.lt_ge_cases (bv_unsigned x) a) as [LT|GE]; [left; apply keep_rs; [exact Hx| clear - LT; lia]|].
        destruct (Z.lt_ge_cases (bv_unsigned x) (a + msz)) as [LT2|GE2]; [| left; apply keep_rs; [exact Hx| clear - GE2; lia]].
        right. exists h. split; [exact HIN|]. split; [| exact (conj GE LT2)].
        intros Hin. change (as_sec (a_st s2)) with l1 in Hin. exact (proj2 (proj1 (L1IN h) Hin) eq_refl).
      - intros sc Hin NIn. exfalso. apply NIn. change (as_sec (a_st s2)) with l1 in Hin. exact (SUB1 sc Hin).
    Qed.
  End Model.
End RSModel.
End HCW.
