(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep F_malloc_free MallocTree MallocFacts_B MallocKit_B MallocModel_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export MallocFacts_AM.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_am_A F_am_K F_am_C F_am_D F_am_E F_am_G.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_F_am_P () := KReplay.lz_vm "##ZDC35stdpp4base6Lookupc89OSSVerify6Proofs:boost_json:fuzz_parse3lib5Agent6F_am_P7am_bodyC13~~~C!snO4Spec6Malloc1M!sgb:bad_answer!spb!uH#take!smb<am_after_brk!srb4apt!uM&I!sjT5STree5stree00!sl&!xr&9countable9C!s0'00!y80;RelDecision!s?04fmap!uI]o!uI+C47Core!sG#Init5Logic8eq_ind_r!y$]!s+$_meta!uk14gma!s'%00C!{_[E:am_init_st!t,%K!u=72eq01I!u9[6mstat!w|+!v%\8am_carv!{:W!uk/K8!sl$!ui+!{7^add!vU37Numbers7BinNums8positive01!sKG2!sK=1Z02!uk\A!~o$ook!xU89Datatypes6option01!wm]AREA_HDR!v8M3!t;\5s_ctx!x6bGc_avail!|t$_area_!#3X#!~7>3not!t>\B!t>4s!~:&!}3;0C56Stdlib6ZArith6BinInt1Z6modulo!sF<3mul!sC=addK!u<[2ev02!w@b7upd!x/f;live_ranges!sqb>mmap!#<q%_!|<'C!|<;4negb!t:\6is_err!}HJ2!#9:\new_region!v<bBc!zr&!#:3#shif!|3'!yy<subI!v]<prod!#:]Q!t]/Dset!|Y:!sz\I!sz6!~m0!t{`!v\Seq!yu]4conc!x_cmprotect!{yL3orb!#3Z_6!v2B7eqb_neq!#7>75proj!|8]3!#4:+!uV<snd!#74<!xC$lK!{WA1!v>`4!#36%!sjT!#Gi/2!#9h2!#?T50!#?r?1!sb>N00I!uZ_!#DYb4PGSZ!sjb7PROT_RW!vG&!tY\mctx!#Kx'!y/<bool!w7/!sF8!{?]9!uC$NONE!v4b;MAP_PRIVAT!sqc8!sq#ANON!{7[!sn&5rkind!{85!#<69!#9e\5TWO64!ulb6ENOSYS!ujb<undef_reason03!{Qcset!#U7+!{Q\8brk!#OQ/".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04mctx37Corelib4Init5Logick42eqk43and37Corelib7Numbers7BinNumsm31Z04optr25stdpp9countableo6bZ_countable25stdpp4gmapq54gmap35stdpp7numbers1Zr86eq_dec08c_active0cc_avail_meta0h2c_avail_meta_count09c_bounces0h0c_free_meta_head0h0c_meta_area_head0h0c_meta_area_tail0ec_mmap_counter05c_seq0bc_unmap_seq07c_usage04aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_K~~~~~~hn68carve_st06mstate0h9set_avail_meta_area_count07set_brk07upd_ctx08brkstate0h4set_avail_meta_areas" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition am_body {R} (st : mstate) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  match c_free_meta_head (ctx st) with
  | Some m => k (dequeue LFree m st) (Some m)
  | None =>
    if negb (c_avail_meta_count (ctx st) =? 0) then am_take st k bail else
    let brk_dead := match c_brk (ctx st) with BrkDead => true | _ => false end in
    if (c_avail_meta_area_count (ctx st) =? 0) && negb brk_dead then
      match c_brk (ctx st) with
      | BrkUntried =>
        SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
            else if negb (brk_pages_ok st base (2 * PGSZ)) then bad_answer bail
            else
              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) st in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))
      | BrkLive rid off =>
        let old := conc st (rid, off) in
        let new := old + PGSZ in
        SVis (EBrk new) (fun r =>
          if negb (brk_answer_ok old new r) then bad_answer bail else
          if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
          else if negb (brk_pages_ok st old PGSZ) then bad_answer bail
          else
            let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st in
            let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                          (set_avail_meta_areas (Some (rid, off))
                                          (set_brk (BrkLive rid (off + PGSZ)) c))) st1 in
            am_after_brk st2 false k bail)
      | BrkDead => am_after_brk st true k bail
      end
    else am_after_brk st true k bail
  end.

Lemma alloc_meta_eq {R} st (k : mstate -> optr -> M R) bail : alloc_meta st k bail = am_body (am_init_st st) k bail.
Proof.
ltac2:(KReplay.run1z (kr_t_F_am_P ()) ["HCW"] "##+;h01Rh14bailh21kh32stp;1p;4p;2p-1R0p10000R1p4p710p8P0P!s2$210p8g000DR1p6081000R0g001LR2!sS%R3p8P!sg$2M!se,p1003W!s614^!s6'p1005jp4p70R4p1006n!sQ+!s6$84!t'&5!s8+RR6!s:&7p8P4P6!tn&R6!sI+kp4p73110R4!u+$9=R8!t3$p100:A!t1+5P7!s+$6p8p200R9P0p8P9P3p8P9!sR$_!tx/;i!u`'P5p8P3!sd$3P6!s+$4p8P2j10Tg00<=j13TP1j42Tg00=Hj21!s/$bR1f3R2#0R4\8\1R8f2R3#0R6P2%33f1R7f0R5C2,14X16X28X31X09P2P3P7P5O4W1W2W3X09o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctx_core_eq : ltac2:(zQ "10!je>1c$0>2c'$0P") := ltac2:(zQ "h40!l8!ld!nc!o0!p7!r1!s9!t2!tc!ua!vf!hga!hhd!hj0!hk3!hl3!hla!hm7!je!hn0\1c$h2\2c'$h2@2$1@3$0$2@1$e^1@1$e^2@2$1@3$0$3@1$b^1@1$b^2@2$1@3$0$3@1$8^1@1$8^2@2$1@3$0$2@1$9^1@1$9^2@2$1@3$0$3@1$c^1@1$c^2@2$1@3$0$3@1$d^1@1$d^2@2$1@3$0@4$5$2$6$4$h3@1$7^1@1$7^2@2$1@3$0@4$5$2$6$4$2@1$h1^1@1$h1^2@2$1@3$0@4$5$2$6$4$2@1$h0^1@1$h0^2@2$1@3$0@4$5$2$6$4$2@1$a^1@1$a^2@3$0$2@1$f^1@1$f^2").

Record AMI (st stX : mstate) : Prop := mkAMI {
  ami_ctx : ctx_core_eq (ctx st) (ctx stX);
  ami_secretr : 0 <= c_secret (ctx stX) < 2^64;
  ami_metas : s_metas stX = s_metas st;
  ami_areas : s_areas stX = s_areas st;
  ami_groups : s_groups stX = s_groups st;
  ami_slots : s_slots stX = s_slots st;
  ami_shadow : s_shadow stX = s_shadow st;
  ami_tick : s_tick stX = s_tick st;
  ami_reserved : s_reserved stX = s_reserved st;
  ami_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions stX) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  ami_new : forall rid r', (s_regions stX) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  ami_next : (s_next_rid st <= s_next_rid stX)%N;
  ami_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P st -> ptrs_in P stX;
  ami_fresh : forall rid, (s_next_rid stX <= rid)%N -> (s_regions stX) !! rid = None /\ (s_shadow stX) !! rid = None;
  ami_rpos : forall q rq, (s_regions stX) !! q = Some rq -> 0 < r_len rq
}.

Section PURE.
Variable st : mstate.
Hypothesis AMP : AMpre st.
End PURE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_carve_took {R} stZ p (k : mstate -> optr -> M R) bail :
  am_carve stZ p k bail = k (am_took (carve_st stZ p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_P ()) ["HCW"] "h01Rh14bailh21kh31ph43stZp;1p;2p;3p200R0g001LR1p4p710p8P0p100>jp4p710p8P1j12Tg00@2j28Tg00A;j23Tg00B?j11Tg00Bdj10Tg00CIj17Tg00Cgj36Tg00Doj24Tg00=Hj25Tg00=bR1g005jR2g009=f4R3#2R4[\1R5f3R6#2R7f1R8f2R9,86g00EQ,39R:g00FY#1#0#0#1#0#0#736142:O2,54X17X25X32X41X00P3P6P9P8f0O5W1W2W3W4X00o"). Qed.

Lemma am_after_brk_false_eq {R} stB f p (k : mstate -> optr -> M R) bail :
  c_avail_meta_area_count (f (s_ctx stB)) <> 0 -> c_avail_meta_areas (f (s_ctx stB)) = Some p -> snd p mod PGSZ = 0 ->
  am_after_brk (upd_ctx f stB) false k bail = am_carve (upd_ctx f stB) p k bail.
Proof.
ltac2:(KReplay.run1z (kr_t_F_am_P ()) ["HCW"] "##B_p'0h01rh11ch21Rh34bailh41fh51kh61pi001ph73stBh82H1h92H2h:2H3h;1bh<1oh=1xi011xh>1zi02>need_unprotecti033ridi043st1p;1p;2p;3p;4p;5p;6p200R0g001LR1p4p710p8P0g00>jR2!s704^R3!s7+1j15Tg00G>j14Tg00HCj1ETg00IZj1LTg00J3j1=Tg00Doj2<Tg00KEj36!s/$_j2HTg00Bdj1VTg00CIj1NTg00L?j2D!s/$\j2KTg00M9j4RTg00N=j20Tg00ODj1QTg00POj3PTg00Q]j1@Tg002Mj2?Tg00R;j1YTg00SAj1X!s/$cj4OTg00Tmj1JTg00V?j27!s/$\R1j2WTg00W<j2GTg00XPj2;Tg00Yij28Tg00[=j29!s/$Zj2BTg00\^j1UTg00^0j2TTP2j51!s5$Mj1STg00=Hj2cTg00:Aj6MTg00_Qj2bTg00`2j4a!s/$Mj1:TP3j5`Tg00aPj3^!s/$mj2]Tg006nj3\Tg00bMj4[!s/$mj3ZTg00d1j5_Tg00e7R3f0R2g00eUR436p=Cg00f3R5?^32p=If1R6%J2']p=3g00fQR7?\32p=AP5P3P2g00gUR8C[p=Fg00hY9Z28p=>P7P3f2R7P6P2D_p=2g00=bR9g00i`R:P:]=R;g005jR<g009=R=f5R>#5[\9R?f4R@#5RAf3RB%4@O1#E#C#LP@%4>O1#=1<<B56=%I@/H8#Cg00jfRCg00kFRDf9RE#5RFPCf:RG#5RHP2P4g00FYRI#V#NRJf7RKf8RL#4O1RM'3/D8g00kfRNg00log00n:'KROCRPCf;RP#ARQ10LERR#QPL%4EO1,3J/D8RS;P2#@1?G>RTPCPQ%Y2RUf6RVPR%X<RWO2RXP1P9P5PQg00oBRYP2PSPRCOg010IRSP<f=RZ#5R[%46R\#J%NIRI'KPG%4P!t6%7I1W53R]%F2'</G\';'8#=PCf>R\#5PCPC%I2/H8/94#@PDPDn010!s#$20000R^%J2/KIR_f<R`%4Z!s|'%F7,<]/G2Ra';'8X1:/07Rb/B2#>PCf?#ARc%U2#@Rd1?\EPCPc1924Rcg010kg0120'7,92'TReP\PZ%4\!t%,B!t%&f';,8_!t&$BRgP6PGPED1PGPgPWO2!tx1!s41X0352ZPZPbP2PEPLD1n011!sB$!sF$g0136#SRbPLV352`n1011!sh$2!s,%0n20!s9'121104103!t201!s41!t@$EPSP<PH%=MPC%5PP^1BR!v/$%A`RgPd1?PVPCPgPePP10EG!uK$KPVD1PK!uKJGPGPRP2PVP>!uK3RgP>V392EbRh!uG6!sr,100PE10KLRiPVP>P@D1Rj36X;CP=1<<>!u<%P2PgP!so6=6FjX<=P3P4PCPH!yZ$@c!yR51BiV#>PCPQPdP!{H$Pe!u3$K!u3%PX!ucDEPj!uY1!tJ$>3%5LRjPL10VKRcP>P@PBD1R='c%I>/H8P2EMPV%4KO1Rh#=P6EM%EhRh/94RgA6CgD%EMRM#C#L[%Ch#L19M4=6CD[1bh4P7CaEMPCPF%:cRh#E/94P413Jh/D8PNP!~9$%AGRO%Qi%:i!~,&8!~,&E@PCPOPUP>PiPWO2!}y&OPYP2P8PiCOPSP<%5`10GP#:!{Z'6!{Z%!{X,6#:#=PCP[P^10P`!sP'/;a!sH'7Ra!|~&%A\R\Pd1?ZLPCP\PePZ10`Z!sZ,f!|V,:P6!{x%PEP:!z1H`P`PaP2PLPK!z13PKV392Pb!|NjL!z8$F%=h!yp$^1Bi2!yY86!yYNEPiP2!{L%!u32@V392Lb!|:C=6j=ePLPcPD!z$$`!s7$W:W9W8X3AX5?X6<X4;X79X20!zM%P7P6P2O6W3W5W6W4W7X20o"). Qed.

(* [comment removed for export] *)
Lemma carve_st_brk_irrel : ltac2:(zQ "c0!hr5!je!hs1!hs9!hu5!hue!l8!nc!hn0!hv7!o0!ig1>3stB$2>2c1$7>1a$a>1b$9>1p$8@3$6$2@2$0@2$5\1c$1@2$3^5@2$b^4@2$4^3^1^5^1@2$0@2$5\1c$1@2$3^5@2$4^3^1^5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_P ()) ["HCW"] "h01ah11bh21ch32c1h41ph53stBp;2g014Dj24Tg00XPj23Tg00N=j20Tg00@2j21Tg00=Hj22Tg00=bR0g00e7g009=g015Kg005jg00i`f4R1f2f0R2'4'3W2/01/12,20W4W1W0W3W5o"). Qed.

End HCW.

