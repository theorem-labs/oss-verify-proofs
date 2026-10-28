(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ARep ALayout AHeapP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARefill_iface () := "I35stdpp9countable9Countable00C35stdpp4base;RelDecisionc5ARocqVerifyHarness?AgentSubmission5BothW=ARefill_ifaceAcache_refill_treeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl2AMC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7aundef_C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrlCpopulate_free_arrayC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;cache_allocI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7get_clsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7c_countC56Stdlib6ZArith6BinInt1Z3ltbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=cls_set_countC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7put_clsK47Corelib4Init5Logic2eq01I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01c5ARocqVerifyHarness?AgentSubmission5BothW=ARefill_ifaceBcache_alloc_unfoldC35stdpp4base6insertC35stdpp8fin_maps@insert_insert_eqC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_ptr_arrayC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nresC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nsecC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7a_cinitC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5a_clsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nextC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_qlocC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<a_qloc_bytesC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7a_qglobK5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=a_qglob_bytesI47Corelib4Init9Datatypes4list00C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp7tactics<f_equal_helpI47Corelib4Init5Logic2eq00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6aclass00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00C35stdpp4base6lookupI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7aclass0C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;c_num_freedC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrlAcls_set_num_freedc5ARocqVerifyHarness?AgentSubmission5BothW=ARefill_iface?put_cls_put_clsc5ARocqVerifyHarness?AgentSubmission5BothW=ARefill_iface?get_cls_put_clsc5ARocqVerifyHarness?AgentSubmission5BothW=ARefill_iface4apop".
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition cache_refill_tree {R} (st : astate) (c : Z) (k : astate -> bool -> AM R) : AM R :=
  let st1 := init_cache st in
  let n := max_count st1 c / 2 in
  let r1 := get_cls st1 c in
  let take (st2 : astate) : AM R :=
    let r2 := get_cls st2 c in
    if c_num_freed r2 <? n then aundef_ (UCheck 229) (k st2 false)
    else k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed r2 - n) r2)) st2) true in
  if n <=? c_num_freed r1 then take st1
  else populate_free_array st1 c (n - c_num_freed r1) (fun st2 ok => if ok then take st2 else k st2 false).

Lemma cache_alloc_unfold : forall {R} st c (k : astate -> bool -> AM R),
  cache_alloc st c k =
    (if 0 <? c_count (get_cls st c) then k (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) true
     else cache_refill_tree st c k).
Proof.
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01Rh11ch21kh32stp;1p;2p;3p;4p10000p4p710R0p1000NR1p4p710R2p8P0P1p4p7210R1p8g000gR3p6051000R4g0021R5p4p710R6p8P4p1002fp4p710p8P4p1003`p4p710p8p200R7P4p8P7P6p8P7p1004fp4p710p8p1005dR6p4p73101R4p1006>R8p4p73110p8P4p1006WR9p4p73110p8P4p10073p4p710p8P4p1007FR:p4p7201p8P4p1007Xp4p7201p8P4p1007jR;p4p73110p8P4p1008>R<p4p73110p8P4p1008RR=p4p73110p8P4p1008lp4p7201p8P6p4p710R4P8p4p710p8P4P9p4p710p8P4P2p8P4P1p8P4P;p4p710p8P4P<p4p710p8P4P=p4p710p8p1009?R=p4p710R4P0p8P4P2p8P4P1p8P4p1009Sp4p73110p8P=p4p741110R=p1009ep4p73101p8p100:Ap4p7<111111111110p100:cp4p710p8p100;Ap4p741110R4P6p4p7511100R1p8P1P4p8p100;Zp4p741110R4P6p4p76111100R1p8P1P4p8p100<2p4p741110R4P6p4p771111100R1p8P1P4p8p100<Rp4p741110R4P6p4p7:1111111100R6p8P6P4p8P:p4p7200R:P=p8P=P:p8P5j10Tg00<ij29Tg00=cj12Tg00>]j21Tg00?:j18Tg00?Xj27Tg00@5j23Tg00A5j34TP3j45Tg00Aoj26Tg00BIR3g00CDg00CbR5f4#0R:[\3f3R3#0P5P:g00DBf2R:f1R5'9R=#2R4'1f0R6g00D`#8,74/3==45:g00EEO2P3P:P5P6C5n0100000020000'6W2W1W3X07o"). Qed.

(* [comment removed for export] *)
Definition apop (c : Z) (st : astate) : astate :=
  put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st.

Lemma put_cls_put_cls : forall c r1 r2 st, put_cls c r2 (put_cls c r1 st) = put_cls c r2 st.
Proof.
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01ch12r1h22r2h32stp;1p;4p;;p;:p;9p;8p;7p;6p;5p;2p;3p;@p;<p10000p4p710R0p1000NR1p4p710R2p8P0P1p4p7210R1p8p1000gp6051000R3p10021p4p710R4p8P3p1002fp4p710p8P3p1003`p4p710p8p100Eep6051000R5P3p8P5P4p8P5p1004fp4p710p8p1005dR5p4p73101R4p1006>R3p4p73110p8P4g006WR6p4p73110p8P4p10073p4p710p8P4p1007Fp4p7201p8P4p1007Xp4p7201p8P4p1007jR7p4p73110p8P4g00G0R8p4p73110p8P4p1008RR9p4p73110p8P4p1008lp4p7201p8P5p4p710R5P3p4p710p8P5P6p4p710p8P5P2p8P5P1p8P5P7p4p710p8P5P8p4p710p8P5P9p4p710p8g009?R9p4p710R5P0p8P5P2p8P5P1p8P5p1009Sp4p73110p8P9p4p741110R5g00GDR1p4p73101p8p100:Ap4p7<111111111110p100:cp4p710p8g00;AR2p4p741110R0P1p4p7511100R7p8P7P0p8g00;ZR0p4p741110R7P1p4p76111100R3p8P3P7p8g00<2R7p4p741110R3P1p4p771111100R4p8P4P3p8g00<RR3p4p741110R4P1p4p7:1111111100R:p8P:P4p8P1p4p73100R4P5p8P5P4p8g00Gfj1;Tg00Hdj1<Tg00Ibj19Tg00J[j1CTg00KTj1HTP9j4>j3STP7j4Vj3OTP6j4UTg00LNj18Tg00MFj15Tg00N?j16Tg00O8j1FTg00P1j1GTg00Q0j1ETg00Qjl;Dl:?l9@j8Aj7Bj6:j5Tl<3Tg00Rej1=Tg00Sej1WTg00Aoj21Tg00TEj3RTP2j3QTP0j3PTg00T\j3NTg00U3j3LTP3j3KTg00UKj3MTP1l@JTg00Udj80Tg00VAj37Tg00A5j34TP8j7ITg00CDR8g00V[R1f4f3R3f2R0f1R2f0R6FIp=2g00BIR7P8P7%;6R9%<6R4%96R5%C6R:%H6R;P8g00WVR<g00WoR=P1C>R>P8P1P>P8P<P=P1CVCUR?P3P2P>P?P3P0%86R@D2RAD2RB%56RC%66RD%F6RE%G6RF%E6RGM;DP9P4P5P:P;P>P?P3P2P@D2RHPCPDPEPFPGM;D%=6RIPIg00XM#WRJP7\8RKP9P4P5P:P;PBPCPDPEPFM:?P9P4P5P:P;PHPCPDPEPFM:?PGPGP8PK\JRKP9P4P5P:P;PBPCPDPEM9@P9P4P5P:P;PHPCPDPEM9@PFPFPJPK\8RKP9P4P5P:P;PBPCPDGAP9P4P5P:P;PHPCPDGAPEPEg00YHRLPK\JRKP9P4P5P:P;PBPCFBP9P4P5P:P;PHPCFBPDPDPLg00Yfg00Z?g00Z]C>RMPK\LRKP9P4P5P:P;PBE:P9P4P5P:P;PHE:PCPCP>PK\MRKP9P4P5P:P;DTRNPNPBPHPK\>/1NP8AS8<=AR8<=AQ8<=AP8<=AO8<=AN8<=AL8<=AK8<=P<AM8<=P1P@P3P2P0M@JG011MCG011LDG011JEG0118FG011JGG0118IG0P9P4P5P:P;PAPCPDPEPFPGPIM<3RA#;%<A%9A%CA%HAP>P?P3P2%8AD2%5A%6A%FA%GA%EA%=AM<3P9P4P5P:P;PHPCPDPEPFPGPIM<3577eA43069432A4326577eW3X21X11X08o"). Qed.
Lemma get_cls_put_cls : forall c r st, get_cls (put_cls c r st) c = r.
Proof.
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01ch11oh21rh32stp;1p;2p;3p;4p;7p;6p;?p;<p;5p10000p4p710R0p1000NR1p4p710R2p8P0P1p4p7210R1p8p1000gp6051000R3p10021p4p710R4p8P3p1002fp4p710p8P3p1003`p4p710p8p100Eep6051000R5P3p8P5P4p8P5p1004fp4p710p8p1005dR5p4p73101R4p1006>R3p4p73110p8P4g006WR6p4p73110p8P4p10073p4p710p8P4p1007Fp4p7201p8P4p1007Xp4p7201p8P4g00[XR7p4p73110p8P4g00G0R8p4p73110p8P4p1008RR9p4p73110p8P4p1008lp4p7201p8P5p4p710R5P3p4p710p8P5P6p4p710p8P5P2p8P5P1p8P5P7p4p710p8P5P8p4p710p8P5P9p4p710p8g009?R9p4p710R5P0p8P5P2p8P5P1p8P5p1009Sp4p73110p8P9p4p741110R5g00:AR1p4p73101p8P1p4p7<111111111110g00:cR2p4p710p8g00;AR0p4p741110R3P1p4p7511100R4p8P4P3p8g00;ZR3p4p741110R4P1p4p76111100R:p8P:P4p8g00<2R4p4p741110R:P1p4p771111100R;p8P;P:p8g00<RR:p4p741110R;P1p4p7:1111111100R<p8P<P;p8P1p4p73100R;P5p8P5P;p8g00[lj1VTg00\Nj2UTg00]0j1;Tg00VAj30Tg00Aoj2LTP9j4<j3TTP0j4:j3QTP4j45j3=TP6j46Tg00LNj12TP8j78TP7j63Tg00TEj3STP3j3KTg00T\j3>Tg00U3j3?TP:j3@Tg00UKj3ATP1l?BTP2j6CTg00Gfj1DTg00Hdj1ETg00Ibj1FTg00J[j1GTg00KTj1HTg00MFj1ITg00N?j1JTg00O8j14Tg00P1j17Tg00Q0j1MTg00Rej1NTg00Qjl<OTg00A5j3PTg00<ij29Tg00]Lj5RTg00V[R2P2f1R1g00]gf0R:DRp=1g00CDR3g00BI%V2R71U21%;2R8/1:f2R6502X171L21P3P2P3g00WVR7g00WoR4P2C<R0P3P7P4P2C:R9P6P3P2P0P3P2P0P3P7P4P2C5C6P6P1%2:R;F8R5E3P3AT374AS374AQ374AK374A=374A>374A?374A@374P7AA374P2P;P6P1M?BECP3P2P0P9P6%D:%E:%F:%G:%H:P5%I:%J:%4:%7:%M:%N:M<O#2E3,18=021eAP61:/96=021eW3X22W0o"). Qed.

(* [comment removed for export] *)
Lemma take_is_apop : forall c n st2,
  put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
  = apop c (put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2).
Proof.
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01ah11ch21nh33st2p;2p;1p;3p;4p;6p10000p4p710R0p1000NR1p4p710R2p8P0P1p4p7210R1p8p1000gp6051000R3p10021p4p710R4p8P3p1002fp4p710p8P3p1003`p4p710p8p100Eep6051000R5P3p8P5P4p8P5p1004fp4p710p8p1005dR5p4p73101R4p1006>R3p4p73110p8P4p1006WR6p4p73110p8P4p10073p4p710p8P4p1007FR7p4p7201p8P4p1007Xp4p7201p8P4p1007jR8p4p73110p8P4p1008>R9p4p73110p8P4p1008RR:p4p73110p8P4p1008lp4p7201p8P5p4p710R4P3p4p710p8P4P6p4p710p8P4P2p8P4P1p8P4P8p4p710p8P4P9p4p710p8P4P:p4p710p8p1009?R:p4p710R4P0p8P4P2p8P4P1p8P4p1009Sp4p73110p8P:p4p741110R:p1009ep4p73101p8p100:Ap4p7<111111111110g00:cR4p4p710p8p100;Ap4p741110R1P5p4p7511100R2p8P2P1p8p100;Zp4p741110R1P5p4p76111100R2p8P2P1p8p100<2p4p741110R1P5p4p771111100R2p8P2P1p8p100<Rp4p741110R1P5p4p7:1111111100R5p8P5P1p8P7p4p7200R7P:p8P:P7p8g00<ij24Tg00^aj18Tg00?Xj21Tg00__j25Tg00@5j22Tg00?:j1<Tg00A5j30Tg00=cj17Tg00VAj33Tg00Aoj2;Tg00`cj49TP4j66Tg00akj3:Tg00c3j2=Tg00CDR4g00BIR7g00V[R:f1R1f0R5f2R2'4R0#8/11/50R0'2R9f3R8g00D`#<R6,121418R3#8/12/53R3'2;01R;%75/16/251223=081508537X0:P7%79/16/29R:=025R8A37;5X071;78A0295R8902:P2P9P:P5C9E61482A:295E61116/20=0251=28537eW3X24W1o"). Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation AREFILL_STACK := 1536 (only parsing).
Notation arefill_W L st c sp :=
  ([(sp - AREFILL_STACK, sp);
    (al_t L + 208, al_t L + 3168);   (* [comment removed for export] *)
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition refill_ret (H : aholes) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    (* [comment removed for export] *)
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c').

Definition refill_stmt (H : aholes) : Prop :=
  forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st_r X' RNG' ms', refill_ret H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x36498) fc None m (seg_rom bsegs)).
End CANSEC2.
