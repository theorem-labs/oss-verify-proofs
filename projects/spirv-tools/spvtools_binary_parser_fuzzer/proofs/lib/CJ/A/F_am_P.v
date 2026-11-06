(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocKit_A2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocRep F_malloc_free MallocTree MallocFacts_B MallocKit_B MallocModel_B.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Export MallocFacts_AM.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_am_A F_am_K F_am_C F_am_D F_am_E F_am_G.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_am_P () := "C35stdpp4base6LookupC69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapc69OSSVerify5KrLib2CJ1A6F_am_P7am_bodyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A6F_am_E:am_init_stC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A6F_am_K8carve_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2CJ1A6F_am_A7am_tookC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2CJ4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2CJ4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib2CJ4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK69OSSVerify5KrLib2CJ4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2CJ4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib2CJ4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2CJ4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib2CJ4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK69OSSVerify5KrLib2CJ4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2C69OSSVerify5KrLib2CJ4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6shiftlK47Corelib4Init9Datatypes4prod01K69OSSVerify5KrLib2CJ4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I69OSSVerify5KrLib2CJ4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2CJ4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2CJ4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

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
ltac2:(KReplay.run1 (kr_t_F_am_P ()) ["AC_1"] "h01Rh14bailh21kh32stp;1p;4p;2p-1R0p10000R1p4p710p8P0P1p4p7210p8p1000Dp4p70R1p1001<p4p710p8P1p10026p4p710p8P1p1002TR0p4p710p8P1P0p4p7210p8P1p1002mp4p73110p8g003?R1p60621000R0g0047R2p4p710R3p8P0p1004lp4p710p8P0p1005jp4p710p8P0p1006ep4p7210p8g007eR4p4p70p1008]p4p710p8p200R5P0p8P5P3p8P5p1009;p4p7210p8P2j10Tg00:9j13TP1j42Tg00;4j21Tg00;NR1f3R2#0R3\4\1f2R1#0P2%31f1f0C2,13W1W2W3X05o"). Qed.

Definition ctx_core_eq (c c' : mctx) : Prop :=
  c_mmap_counter c' = c_mmap_counter c /\ c_free_meta_head c' = c_free_meta_head c /\ c_avail_meta c' = c_avail_meta c
  /\ c_avail_meta_count c' = c_avail_meta_count c /\ c_meta_area_head c' = c_meta_area_head c /\ c_meta_area_tail c' = c_meta_area_tail c
  /\ c_active c' = c_active c /\ c_usage c' = c_usage c /\ c_unmap_seq c' = c_unmap_seq c /\ c_bounces c' = c_bounces c /\ c_seq c' = c_seq c.

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

Lemma am_carve_took {R} stZ p (k : mstate -> optr -> M R) bail :
  am_carve stZ p k bail = k (am_took (carve_st stZ p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_P ()) ["AC_1"] "h01Rh14bailh21kh31ph43stZp;1p;2p;3p200R0g0047R1p4p710p8P0p100<Jp4p710p8P1j12Tg00=Fj28Tg00>?j23Tg00?7j11Tg00?\j10Tg00@Aj17Tg00@_j36Tg00AWj24Tg00;4j25Tg00;NR1g000DR2g007ef4#2R3[\1f3R1#2f1f2R4,81g00B9,34R4g00C5#1#0#0#1#0#0#7361424O2,53W1W2W3W4X00o"). Qed.

Lemma am_after_brk_false_eq {R} stB f p (k : mstate -> optr -> M R) bail :
  c_avail_meta_area_count (f (s_ctx stB)) <> 0 -> c_avail_meta_areas (f (s_ctx stB)) = Some p -> snd p mod PGSZ = 0 ->
  am_after_brk (upd_ctx f stB) false k bail = am_carve (upd_ctx f stB) p k bail.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_P ()) ["AC_1"] "p'0h01rh11ch22H1h32H2h42H3h51Rh61bh74bailh81fh91kh:1oh;1pi001ph<3stBh=1xi011xh>1zi02>need_unprotecti033ridi043st1p;1p;2p;3p;4p;5p;6p200R0g0047R1p4p710p8P0g00<JR2p4p710p8P0g006eR3p4p7210p8P1j15Tg00CZj14Tg00DSj1ETg00E^j1LTg00F7j1=Tg00AWj2<Tg00G=j36Tg00GWj2HTg00?\j1VTg00@Aj1NTg00H7j2DTg00HTj2KTg00I1j4RTg00Iij20Tg00Jdj1QTg00Kcj4PTg00Lej1@Tg004lj2?Tg00MCj1YTg00N=j1XTg00N_j4OTg00O]j1JTg00Pcj27Tg00Q@R1j2WTg00Q`j2GTg00Rhj2;Tg00T5j28Tg00U=j29Tg00UZj2BTg00VRj1UTg00WXj2TTP2j51Tg00X5j1STg00;4j2cTg008]j6MTg00Xmj2bTg00YNj4aTg00Yij1:TP3j6`Tg00Z`j3^Tg00[=j2]Tg001<j3\Tg00[]j4[Tg00\=j3ZTg00]5j5_Tg00]oR3f0R2g00^MR436p=Cg00^kR5?^32p=If1R6%J2']p=3g00_IR7?\32p=AP5P3P2g00`AR8C[p=Fg00a99Z28p=>P7P3f2R7P6P2D_p=2g00;NR9g00b4R:P:]=g000DR;g007eR<f5R=#5[\9f4R>#5f3R?%4>O1#E#C#LP>%4=O1#=1<;?56<%I>/H8#Cg00bnR@g00cNRAf9RB#5RCP@f:RD#5REP2P4g00C5RF#V#NRGf7RHf8RI#4O1RJ'3/D8g00cnRKg00dkg00ej'KRLCRP@f;RM#ARNp,5ACEILRO10IBRP#QPI%4BO1,3G/D8RQP2CP#@1?D=RRP@PN%Y2RSf6RTPP%X;RUO2RVP1P9P5PNg00ffRWP2PQPPCOg00gaRQP;f=RX#5RY%46RZ#J%NFRF'KPD%4MO1,3G/7F1W53R[%F2'</GZ';'8#=P@f>RZ#5P@P@%I2/H8/94#@PAPAn0100000020000R\%J2/KFR]f<R^%4XO1,3G/7F%F7,<[/G2R_';'8X1:/07R`/B2#>P@f?#ARa%U2#@Rb1?ZBP@Pa1924Rag00hCg00i<'7,92'TRcPZPX%4ZO1,3G/7F%F?,<[/G2Rd';,8]X1:/0?ReP6PDPBD1PDPePUO2n0100000020000n0100000020000X0352XPXP`P2PBPID1n0110200020000g00j6#SR`PIV352^n10110100021010000n2001101000121104103n0100000020001n0100000020001X0352BPQP;PE%=JP@%5MP\1BP2#>P@%A^RePb1?MTP@PePcPM10BDReP6PHPTD1PHPePUO2n0100000020000n0100000020000X0352DPDPPP2PTP=D1n0110200020000ReP=V392B`Rfn10110100021010000n0100000020100PB10HIRgPTP=P>D1Rh36X6@P<1<;=PQP;PEP2PePfn10110100021010000=6ChX:<P3P4P@PEP@P@%@aPAPAn01000000200001BgT#>P@PNPbPRP@PNPcPDPPPHPTP=D1PVn0100000020000n0100000020000X0352BPhn0110200020000=6ChX>3%5IRhPI10THRaP=P>P?D1R<'c%I=/H8P2EMPT%4HO1Rf#=P6EM%EfRf/94ReA6@eA%EJRJ#C#L[%Cf#L19J4=6@A[1bf4P7CaEMP@PC%:aRf#E/94P413Gf/D8PKPLCRP@%ADRLPO%Qg%:g,3G/D8R8P2CP#@1?B>P@PLPSP=PgPUO2P1P9P5PLPWP2P8PgCOPQP;%5^10DM#:,3G/7F%F6,<[/G2';,8]X1:/06#:#=P@PYP\10M^#:,3G/7F/;_,8]X1:/07R7/B2#>P@%AZRZPb1?XIP@PZPcPX10^X#:,3G/7F/;d,8]X1:/0?R:P6PBPID1PBP:PUO2n0100000020000n0100000020000X0352^P^P7P2PIPHD1n0110200020000PHV392M`n10110100021010000n2001101000121104103n0100000020001n0100000020001X0352IPQP;PC%=fP@PEP\1Bg2#>P@PNPbPRP@PNPcPDPPP6PTP=D1PVn0100000020000n0100000020000X0352BPBPgP2P=P>D1n0110200020000P>V392I`n10110100021010000n0100000020100=6h<ePOPIPaPAP>P?E`=6h<eW4W3W2W7W9W;W8W<X50o"). Qed.

Lemma carve_st_brk_irrel stB c1 a b p :
  carve_st (upd_ctx (fun c => set_avail_meta_area_count c1 (set_avail_meta_areas a (set_brk b c))) stB) p
  = carve_st (upd_ctx (fun c => set_avail_meta_area_count c1 (set_brk b c)) stB) p.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_P ()) ["AC_1"] "h01ah11bh21ch32c1h41ph53stBp;2g00k8j24Tg00Rhj23Tg00Iij20Tg00=Fj21Tg00;4j22Tg00;NR0g00]og007eg00l3g000Dg00b4f4R1f2f0R2'4'3W2/01/12,20W4W1W0W3W5o"). Qed.

End AC_1.
