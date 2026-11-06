(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJRep BJFrame HeapMF_iface BJHeap BJIface BJEhTabs BJKitW BJKitVS BJKitIn BJKitRV W_pesc0.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_W_pstr0 () := KReplay.lz_vm "##G8C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02!sK=1Z02!t,>tI!s`+4Init5Logic3and00!s]<3pow!sC<6modulo!s~82eq!s}>>pow_pos_nonneg!sN<:!sN#!sJB7compar!v\-!tU21!s@29Datatypes4list01I!sFA0K4!tI&9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr!u@#!sIC2K!t?L!v6=6option!z'@N!t98!t\27!sI65Tauto8G!tU'8C!sJ<B!sJ&!sH6:Z!uG+=Z!sT$CheckerC!wU<4find!sqAC!sq0_sound!z7<9mod_small!sI<4ones!sD=land!ys@1!tK=!sb#_!t,$!{^78eq_ind_r!wGF4!sJF5!wk<5eKind!|Q=uni!|Q9!se%4kind!}Y?!sf$!}Y-!#5L50!#5j?1!#6UF3!#4s74True!}z#!tk::!#4%$ison!~H8!yp-;!x-%Proof!v,8!}[13Op203!sMI5!wC=bool!v=/!sF8!v?H!zH=3sub!wG@3!sa=mu!|J=3add!#3hD5!sIE3!sIE!{iG7!#9x<!~g#add!}@86!}@%!x9I1!zE85False!#<==6shift!vi=?!sF%_mul_pow!#>d<3oppC45stdpp9bitvector;definitions8bv_swrap!vsE6!spA?bv_half_!#?+#us!sTA>!tF'!#6p%!sS@7Z_to_bv!sLA9!sy#igned!tIB!st&!sSH;bv_un!sP&!w,<ltb!u8Bbv_!ud#!si<8ltb_spec!~[<8BoolSpec!#6|=!{D,3!t^A@!uz'!uR+89OSSVerify6!#5+#s:boost_json:fuzz_parse3lib3Lib7ZBridge9zb!vg'13~~~".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJKitRV~~~~~~k42rv37Corelib4Init5Logico62eqo63andhf7Z_to_bvk43ra7k43rrak43rs1k44rs10k44rs11k43rs2k43rs3k43rs4k43rs5k43rs6k43rs7k43rs8k43rs9k43rspk43rt0k43rt1k43rt2k43rt3k43rt4k43rt5k43rt646Stdlib6ZArith6BinInt1Zhif3addhfbbv_unsigned37Corelib4Init9Datatypeshlc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hnc3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hsd4cellhlc4conshsd2C8hlc3nilhsd2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~iic8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~in35rsegshif4landhif2lehif2lthif3subhif3mulhif6shiftlhif3powhif3opphf9bv_signed" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs; try transport_cond_ro segs m a bs.
(* [comment removed for export] *)
Local Ltac addr_diff E A ::=
  lazymatch A with
  | E => constr:(0%Z)
  | _ =>
    match E with
    | Z.add ?X ?c1 =>
        let c1 := zlit c1 in
        lazymatch A with
        | Z.add X ?c2 => let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end
  end.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

  (* [comment removed for export] *)
  Definition sconsts : ltac2:(zQ "40!h9!jc!k1!o1>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "he0!h9!jc!pa!pf!q5!k1!qf!r5!rb!s1!s8!sf!t5!tb!u1!u7!ud!v3!v9!vf!hg5!hgb!hh1!hh7!hhd!hi3!hi9!o1!hk7!hke\1r$hb\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5@2$3@3$2@1$1@1$0#k0@1$h3^4^3@2$3@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0-kgg1@2$3@3$2@1$1@1$0#k0@1$h4^4@2$4@1$0#k0+sgugg0@2$3@3$2@1$1@1$0#k0@1$h5^4@2$4@1$0#k0+ogqgg0@2$3@3$2@1$1@1$0#k0@1$h6^4@2$4@1$0#k0+sgsgg0@2$3@3$2@1$1@1$0#k0@1$b^4@2$4@1$0#k0+ivg1@2$3@3$2@1$1@1$0#k0@1$c^4@2$4@1$0#k0+nvvvvvve@2$3@3$2@1$1@1$0#k0@1$d^4@2$4@1$0#k0@2$hc@2$hd@1$0#k0^2+1@2$3@3$2@1$1@1$0#k0@1$e^4@2$4@1$0#k0+i2@2$3@3$2@1$1@1$0#k0@1$f^4@2$4@1$0#k0+lc@2$3@3$2@1$1@1$0#k0@1$h0^4@2$4@1$0#k0+i0@2$3@3$2@1$1@1$0#k0@1$h1^4@2$4@1$0#k0+6@2$3@3$2@1$1@1$0#k0@1$h2^4@2$4@1$0#k0+hknm0@2$3@3$2@1$1@1$0#k0@1$9^4@2$4@1$0#k0+hmmm0@2$3@3$2@1$1@1$0#k0@1$a^4@2$4@1$0#k0-jvjvghg0@2$3@3$2@1$1@1$0#k0@1$h7^4@2$4@1$0#k0+ogogg0@2$3@3$2@1$1@1$0#k0@1$h8^4@2$4@1$0#k0+nvnvngg0@2$3@3$2@1$1@1$0#k0@1$h9^4@2$4@1$0#k0-jvjvkgg0@2$3@3$2@1$1@1$0#k0@1$ha^4@2$4@1$0#k0-nvnvogg0@3$2@1$1@1$0#k0@1$6^4@2$4@1$0#k0-jvjvhgg0").
  (* [comment removed for export] *)
  Definition ssregs : ltac2:(zQ "40!h9!jc!k1!o1>1r$3>3sp'@1$1@1$0#k0>2pa@1$1@1$0#k0>1e$2P") := ltac2:(zQ "h50!h9!jc!pa!pf!q5!k1!rb!s1!s8!sf!t5!tb!u1!u7!ud!v3!v9!vf!o1!hk7!hke\1r$h2\3sp'@1$1@1$0#k0\2pa@1$1@1$0#k0\1e$5@2$3@3$2@1$1@1$0#k0@1$h1^4^3@2$3@3$2@1$1@1$0#k0@1$6^4@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$9^4@2$4@1$0#k0+ivg1@2$3@3$2@1$1@1$0#k0@1$a^4@2$4@1$0#k0+nvvvvvve@2$3@3$2@1$1@1$0#k0@1$b^4@2$4@1$0#k0@2$h3@2$h4@1$0#k0^2+1@2$3@3$2@1$1@1$0#k0@1$c^4@2$4@1$0#k0+i2@2$3@3$2@1$1@1$0#k0@1$d^4@2$4@1$0#k0+lc@2$3@3$2@1$1@1$0#k0@1$e^4@2$4@1$0#k0+i0@2$3@3$2@1$1@1$0#k0@1$f^4@2$4@1$0#k0+6@2$3@3$2@1$1@1$0#k0@1$h0^4@2$4@1$0#k0+hknm0@2$3@3$2@1$1@1$0#k0@1$7^4@2$4@1$0#k0+hmmm0@3$2@1$1@1$0#k0@1$8^4@2$4@1$0#k0-jvjvghg0").
  Ltac open_sconsts SC := box_post; destruct SC as (?C1 & ?C2 & ?C3 & ?C4 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C10 & ?C11 & ?C12 & ?C13 & ?C14 & ?C15 & ?C16 & ?C17 & ?C18 & ?C19 & ?C20 & ?C21).
  Ltac open_ssregs SS := box_post; destruct SS as (?S1 & ?S2 & ?S3 & ?S4 & ?S5 & ?S6 & ?S7 & ?S8 & ?S9 & ?S10 & ?S11 & ?S12).
  (* [comment removed for export] *)
  Definition sframe : ltac2:(zQ "50!h9!jc!hn4!k1!hs6>1m$4>3sp'@1$1@1$0#k0>2j8@1$2@1$1@1$0#8>3ras@1$1@1$0#k0>3a5s@1$1@1$0#k0>3a0s@1$1@1$0#k0>3tot$3P") := ltac2:(zQ "e0!h9!ig9!ih1!jc!ih9!hn4!ihf!k1!ii6!im7!hs6!iqf!q5!hke\1m$a\3sp'@1$3@1$0#k0\2j8@1$5@1$3@1$0#8\3ras@1$3@1$0#k0\3a5s@1$3@1$0#k0\3a0s@1$3@1$0#k0\3tot$7@4$9$b^7@2$d@1$0#k0^6@3$2$1@2$8N8^5@3$2$1@1$4^4@3$2$1@1$4^3@3$2$1@1$4^2@3$2$1@1$4@2$c@1$0#k0^1@1$6$1").
  Ltac sseg_begin r :=
    intro_rv r; subst; unfold sframe in *; unfold seg_post, sconsts, ssregs, sframe, pcells; hide_post;
    lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ ?a0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
      pose proof (bv_unsigned_in_range _ a0) as RA0; unfold bv_modulus in RA0; cbn in RA0 end;
    hcb.
  Ltac seg_unfold ::=
    lazymatch goal with
    | |- pconsts _ _ _ _ => unfold pconsts
    | |- pcore _ _ _ _ => unfold pcore
    | |- psregs _ _ _ => unfold psregs
    | |- pframe _ _ _ _ _ _ _ _ _ => unfold pframe
    | |- psize _ _ _ => unfold psize
    | |- pcells _ _ _ _ _ _ _ _ => unfold pcells
    | |- sconsts _ _ _ _ => unfold sconsts
    | |- ssregs _ _ _ _ => unfold ssregs
    | |- sframe _ _ _ _ _ _ _ => unfold sframe
    end.
  (* [comment removed for export] *)
  Definition sctx {HCEIL : HeapCeil} (sp' pa : word) (lo e : Z) : Prop :=
    hceil <= lo /\ lo + 48 <= bv_unsigned sp' /\ bv_unsigned sp' + 280 <= bv_unsigned pa /\ bv_unsigned pa + 280 <= 2^64 /\ e <= hceil.
  Ltac open_sctx SX := box_post; destruct SX as (CEIL & ROOM & SPA & A0HI & EHCL).
  (* [comment removed for export] *)
  Lemma land255_small : ltac2:(zQ "60!k1!pf!pa!ir8!is0!is6>1x$0>0@2$1@2$4Z^1@2$5^1+hg0@3$2$0@2$3^2+vf^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_pstr0 ()) [] "##1Ah02Hah17__arithh24__ffh36__sat1h48__varmaph55__with64__x1h72Hxh8!sN%0h91xh:1zp;2p;1p;3p;4p;8p;6p;7g0000j21Tg000Lj10Tg0011j16!s/$Oj24!s/$kj2:Tg002Fj2O!s/$cj2CTg003Cj38!s/$]j2@Tg004Ej3?!s/$ij2>Tg005Jj29!s/$dj1;Tg006Dj1U!s/$dj2TTg007Bj1S!s/$`j1NTg008Kj25!s/$nj2KTg009Qj43Tg00:<j1B!s/$^j1ATg00;<j3D!s/$_j8ETg00<Cj2F!s/$ej2GTg00=Qj3HTg00>0j4I!s/$bj3JTg00?Ej1=!s/$cj2LTg00@Aj1M!s/$_j3<Tg00ABj6P!s/$`j7QTg00BDj7RTf1R0g00BhR1g00CGR2P2g00CgR3f0R4g00DGFQp=2f2R5P1P2P2P3P0P4FRp=7g00DgR6g00EER7/14g00EcR8#0R9#0#0R:#0!s$+6R;,44':R<P6%69R9%6:R='OR>,C0A8645X:61@9=1479R?117=R@147>[RA[1179RBg00FHRCA?9=0UW0117>\C^0BP0g00Fd1>79'9P?eO1PAg00GJRA#;R?%UARA1T60%S6RB%N6RC!uA+61567!us$H6RD1K68R8C3,2CREP6P8g00H]RF156;!s<$57C%B2P6P8PF1569%A:5D6!sA$97CEGE1FC3R3P4P5g00IDREg00IdR:'91G45=8E:dAH670CIR:b2b4b5X661170140>':\<^66P4f5f4O2b1b3b8b39J0>%==,L0P?PA%M6PBP6P1PD156=!tJ$P3P!st&P@P4b19<0=EPW7W9o"). Qed.
  Lemma land127_hi : ltac2:(zQ "70!k1!pf!pa!ir8!is0!is6!isc>1x$0>0@2$1@2$4+o0^1@2$5^1+hg0@3$2$0@2$3^2+nf@2$6^2+o0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_pstr0 ()) [] "##3$h07__arithh14__ffh28__varmaph35__with44__x1h52Hxh61xh71zp;1p;2p;3p;4p;8p;6p;7g000Lj10Tg0011j15Tg0000j28!s8$Oj29!s/$kj2?Tg00JDj1<Tg002Fj2L!s/$cj27!sA$ij2;Tg003Cj34Tg00KFj1C!s/$dj2ATg00LAj2>Tg005dj1\Tg006Dj1V!s/$dj2UTg007Bj1R!s/$`j1QTg008nj2O!s/$Kj23!sn$^j3KTg00MAj3J!s/$dj3FTg009Qj42Tg00<Cj2E!t:$Jj2G!s8$ej2HTg00=Qj3DTg00>0j4ITg00:<j1BTg00;_j8M!sA$bj3NTg00ABj6:Tg00@Aj1PTg00NGj6@!s/$kj4STg00OLj6TTg00?Ej1[!s/$cj2Z!s\$_j3Y!sn$`j7WTg00BDj7XTf1R0g00BhR1g00CGR2P2g00CgR3f0R4g00DGFWp=1g00DgR5P0g00H6P4C2p=6f2R6P1P2P2P3P0P4FXp==g00EcR7#0R8#0!s$,R9#5R:/84%09#5R9,94'?R;P5%58%<7#<#5R8'L,701;6:9454X75R<P5%C7R=/A:R>,>0R?/7:R@P<P5P?P<g00GJR<#\RA%V<R<1U50RB%R5RC%Q5RDP51O57R7135=135:RE5K55J5RFg00OhRGAF57EC2'11ED3RHP4P6g00IDRIg00IdRJ'G1H46=4IJdg00EERJ=D50CIRIb1b2b3X451>4>1;4:545^45P4P6O1b0P@PAP<PBPCPD!vB'16E7,1DP5P7g00H]!tg$9C2,1D5=D%B2135JR9/6F!sL%FP7PE!sE'GMPHP!tD-8J?19?:'?\;!tE&P0O2b09N?:E:170:P0P=P:PAP<%P5R=!tX/P5PEPGP!tJ%E@!t$,A45:Jg00PO[P4b0CSET%[8,Z0!uD$=PC1358,69,1D!s[,18J8P4b09Y08E:W5X65o"). Qed.
  Lemma land127_lo : ltac2:(zQ "60!k1!pf!pa!ir8!is0!is6>1x$0>0@2$1@2$4Z^1@2$5^1+o0@3$2$0@2$3^2+nf^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_pstr0 ()) [] "##1Lh02Hah17__arithh24__ffh36__sat1h48__varmaph55__with64__x1h72Hxh8!sN%0h91xh:1zp;2p;1p;3p;4p;8p;6p;7g0000j21Tg000Lj10Tg0011j16!s/$Oj22!s/$kj2;Tg00JDj19Tg002Fj2F!s/$cj2CTg003Cj37!s/$]j2@Tg004Ej3?!s/$ij2=Tg005Jj2:!s/$dj1VTg006Dj1U!s/$dj2TTg007Bj1R!s/$`j1QTg008Kj24!s/$nj2ETg009Qj43Tg00:<j1B!s/$^j1DTg00;<j3A!s/$_j8GTg00<Cj2H!s/$ej2ITg00=Qj3JTg00>0j4K!s/$bj3>Tg00?Ej1L!s/$cj2MTg00@Aj1N!s/$_j3OTg00ABj6P!s/$`j7<Tg00BDj7STf1R0g00BhR1g00CGR2P2g00CgR3f0R4g00DGF<p=5f2R5P1P2P2P3P0P4FSp=8g00DgR6g00EER7/14g00EcR8#0R9#0!s$-6R:,24';R;P6%69R9%98#9R<#6R='FR>,C0A7645X:61@9=1279R?117=R@127>[RA[1179RBg00FHRCA?9=0UW0117>\C^0BP0g00Fd1=79':P?eO1PAg00GJRA#VR?%UARA1T60%R6RB%Q6RC!uC+61467!uu$H6RD1E68R8C3,5CREP6P8g00H]RF146:!s<$58C%B2P6P8PF1469%D<5A6!sA$98CEGG1HC3R3P4P5g00IDREg00IdR<':1I45=7E<dAJ670CKR<b2b4b5X661170120>';\;^66P4f5f4O2b1b3b8b39>0>%L=,M0P?PA%N6PBP6P1PD146=!tJ$P3P!st&P@P4b19O0=EPW7W9o"). Qed.
  Lemma shiftl1_mul : ltac2:(zQ "40!k1!pa!it3!ita>1x$0@3$1$0@2$3^1+1@2$2^1+2").
Proof.
ltac2:(KReplay.run1 (kr_t_W_pstr0 ()) [] "h07__arithh14__ffh28__varmaph35__with41xh51zp;1p;2p;3p;4p;7p;6g000Lj1ETg0011j12Tg002Fj2:Tg00Kdj20Tg003Cj34Tg005Jj21Tg00Plj2;Tg005dj19Tg006Dj17Tg00@Aj16Tg007Bj15Tg007`j18Tg008Kj23Tg009Qj4DTg00A`j7CTg00<Cj2BTg00<ej2<Tg00=Qj3=Tg00>0j4>Tg0000j2?Tg00QLj3@Tg00ABj6ATg00DgR0P0f0R1g00EcR2#E#2R3%22R2':'0f1R4/039401X501013,101;12g00GJR3#9%73%60%50%80R3g00Bhg00CGR5P5g00CgR5P0g00EER6,30g00H61302CDg00DGFC1B35P1f2R5g00IDR3g00IdR7'11<15=437dA=064C>b1b2b31?62P1b09@12EAW4o"). Qed.
  Lemma shiftl56_mul : ltac2:(zQ "40!k1!pa!it3!ita>1x$0@3$1$0@2$3^1+j8@2$2^1+hggggggggggggg0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_pstr0 ()) [] "##,1h07__arithh14__ffh28__varmaph35__with41xh51zp;1p;2p;3p;4p;7p;6g000Lj10Tg0011j13Tg00JDj17Tg002Fj2ITg00Kdj22Tg003Cj38Tg005Jj25Tg00Plj2;!s8$dj1:Tg006Dj19Tg00@Aj1HTg007Bj1G!s/$`j1FTg008Kj26Tg009Qj4DTg00A`j7CTg00<Cj2@!s/$ej2ATg00=Qj3BTg00>0j4>Tg0000j2=Tg00QLj3E!se$Bj6<Tf0R0#0#0p=4%0!s0$#0p=?!s2+!s$'p=1g00DgR1P1g00EcR2#0R3#3%72#7#0#4#3R2'I,20f1R4%03#4#?#1!s$-3R3'29810X511203,511;02g00GJR3#:%93%H1%G1%F1R3g00Bhg00CGR5P5g00CgR5!tJ%ER6,61g00H61612CDg00DGFC1@35P0f2R5g00ID!sj$IdR7'51A05=837dAB164C>b1b2b31=62P0b09E02E<W4o"). Qed.
  Ltac norm_lits :=
    repeat match goal with
    | |- context [Z_to_bv 64 (Z.land ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.land a' b') in
        change (Z_to_bv 64 (Z.land a b)) with (Z_to_bv 64 v)
    | |- context [Z_to_bv 64 (Z.lor ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.lor a' b') in
        change (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 v)
    | |- context [Z_to_bv 64 (Z.shiftl ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.shiftl a' b') in
        change (Z_to_bv 64 (Z.shiftl a b)) with (Z_to_bv 64 v)
    | |- context [Z_to_bv 64 (Z.shiftr ?a ?b)] =>
        let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.shiftr a' b') in
        change (Z_to_bv 64 (Z.shiftr a b)) with (Z_to_bv 64 v)
    | |- context [Z.land ?a 255] => rewrite (land255_small a) by lia
    | |- context [Z.land ?a 127] => first [ rewrite (land127_hi a) by lia | rewrite (land127_lo a) by lia ]
    | |- context [Z.shiftl ?a 1] => rewrite (shiftl1_mul a)
    | |- context [Z.shiftl ?a 56] => rewrite (shiftl56_mul a)
    | |- evt _ _ (MS ?R _ _ _ _ _ _) => match R with context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia end
    end.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => first [ st1b | arm_inputs; st1b ]; norm_lits; gen_data
                end
            end).
  Lemma signed_lit : ltac2:(zQ "a0!h9!k1!iu4!pf!pa!is0!is6!iub!q5!iv2>1z$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
Proof.
ltac2:(KReplay.run1 (kr_t_W_pstr0 ()) [] "h02Hah16__sat1h24__x1h31zh42Hzh57__arithh64__ffh76__sat0h88__varmaph95__witp;1p;2p;3p;4p;7p;8p;6g000Lj10Tg0011j15Tg00JDj13Tg002Fj2?Tg00R5j1;Tg0000j21Tg001Oj22Tg001kj24Tg00:^j16Tg00RRj2@Tg003Cj39Tg003]j2=Tg004Ej3<Tg004ij2WTg005Jj2:Tg005dj1VTg006Dj1UTg006dj2TTg007Bj1KTg007`j1FTg008Kj2ETg00;<j3DTg00S9j2CTg008nj2BTg009Qj48Tg00BDj7ATg00:<j1GTg00;_j8HTg00<Cj2ITg00<ej2JTg00=Qj3>Tg00>0j4LTg00S\j1MTg00TJj3NTg00U7j2OTg00U]j2PTg00VEj2QTg00ABj6RTg00A`j7STf1R0g00BhR1g00CGR2P2g00CgR3f0R4g00DGFSp=7g00DgR5g00EcR6#0R7#5R8%36#3#3#3#3R9#5R:'?R;#;R</14124;'4R=P5%07#0#0#0#0#6R7/@0f2R>9954X351=8:g00EER?/28R@11?:12?;[RA[11?8RBg00FHRCA<8:0UW011?;\C^0BP0g00Fd1W?8':P@eO1PAg00GJRA#V%UA1T50%K5%F5RAP1P2P2P3PAP1P2P2P3P51E58%695D5R9,C5g00H61B56R6C8,7AP5P6g00H]P9C8,7AFAR9%G2P9GH1IA3P4P>g00IDRAg00IdR3':1J4>=9A3dA>5?0CLb6b8b9X2511<0120;'4\=^25P4f5f4O2b5b1b7b1%M7R4#;/101204'4e9N701O70,P71Q70ERW4W3o"). Qed.
  Lemma signed_hi : ltac2:(zQ "a0!iu4!h9!k1!pf!pa!is0!is6!isc!q5!iv2>1z$2>0@2$3@2$5@2$0+2+jf^1@2$6^1@2$0+2+k0@3$4$2@2$9@1$1#k0@2$8@1$1#k0^2@2$7^2@2$0+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_pstr0 ()) [] "##9Up'0h06__sat1h1!s/%3h24__x1h32Hah47__arithh54__ffh6!sL%0h7!s/%2h88__varmaph95__with:1zh;1Hh<4__p1h=2Hzh>1bi001bh?2b0p;1p;2p;3p;4p;6p;7p;8g000Lj13Tg0011j1>Tg00JDj18Tg002Fj2ATg0000j29!sJ$Oj20!s/$kj2;Tg00:^j1BTg00U7j2NTg00W2j2K!s/$\j27!sw$ij25Tg00X9j2a!s/$_j2]Tg00YAR0j3WTg003]j2FTg004Ej3E!s/$ij2UTg005Jj2D!s/$dj1TTg006Dj1Q!s/$dj2PTg007Bj1O!s/$`j1MTg008nj2L!s/$Kj2?Tg00;<j3@Tg009Qj41!u5$<j1J!tW$ej6ITg00Mdj3HTg00<Cj2R!s/$ej2G!tp$Cj3CTg00=Qj3STg00>0j4`!vI$cj2_!s8$bj3^Tg00ABj6=Tg00ZIj2\!v@$]j2XTg00[8j1Y!sJ$`j7ZTg00BDj7[!tp$_j8VTg00DgR1f1R2f0R33Cp=4g00EER4/93p=2P2g00BhR5g00CGR6P6g00CgR7P3g00DGFZp=6f2R8P5P6P6P7P2P3F[p=:f3R9!s;+8P2P3GVp=<g00EcR:#3R;#>R<%8:#8!s$%R=#>R>'AR?/93%3;#3!s$%!sO$@,A<RA,03';RBP1g00IDRCP1%B;R;1N;2RD'KRE/7?PE15EAn010!s#$20000158ARF,43X:1P11a;2RGPCP1173?P3153ARH!sX1/4FX:1RIP1P2PI1]2?102?19?2RI172?3W178?PCP0109?19?9PCP1P2f5R0150AR0!sv30P2f4R0/0?1F<>RJ104<RK%2>104?[RL[RM%2<RNg00FHROAE<>2UW3R>%2?\O^3NRP1F<@RQ%2@104A[RR\KRSAE<@2VOX3NR@%2A!sP%N!w}$Fd1U4<'DPKeRKO1ROPRP0PKO1RKPLp-0!z2$GJRU#TRV%QURU1P12RW%O1RX%M1RYP11L1:R:g00H]RZ1?1<R<%B=5@1R=C1,6Y%J6R[PYP1P=g00H6R=P:!s?$R\PY!xm+9EI5:YP[P1P:g00OhR9A@1<;R<9H1:R6!sX$C<C<1RY7R7P3P8g00IdR5,DC1G38=CC5dAS142C`R5b5b8b9X21W<103?1;I8148F[[^21^<TP3f<RT/0APTf7RFf;O4b4b1b0b6b0b7b1W;P3O119?0PJPMP>PPPQPSP@PNPOPRPKPLPVPUPWPXP1P6P9P!to%P7P!tI,14HH^21P3PTO1!t,7n2002!xq&00211000!s'$b?b>1_2A!tJDYP1P:PZP<!vo%<9:Y\P[P11?14P!w-'=:Y<C<!ti0%22102A';\B!tp$f8PFO2!tr19^2AE=!{j%G?PG15G!|B42A'4ePE1\;2E=1X;D%YDE=W=X:1o"). Qed.
  (* [comment removed for export] *)
  Ltac box_ugly K ::=
    try (rewrite !signed_lit in K by lia); try (rewrite !signed_hi in K by lia);
    lazymatch type of K with
    | context [Z.lor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.land _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftl _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftr _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.modulo _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | _ => idtac
    end.
  (* [comment removed for export] *)
  Ltac fin_atom ::=
    first [ eassumption
          | reflexivity
          | lazymatch goal with
            | |- @eq Z _ _ => rv_cbv; fin_arith
            | |- (_ <= _)%Z => rv_cbv; fin_arith
            | |- (_ < _)%Z => rv_cbv; fin_arith
            | |- not _ => rv_cbv; fin_arith
            | |- @eq _ _ _ => rv_cbv; first [ reflexivity | eassumption | f_equal; lia | apply bv_eq; rewrite ?unsigned_lit by lia; lia
                                             | apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity ]
            | |- _ => rv_cbv; first [ reflexivity | eassumption ]
            end ].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
(* [comment removed for export] *)
