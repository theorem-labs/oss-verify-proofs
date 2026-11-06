(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARefill_iface () := "c59OSSVerify5KrLib5AsanW=ARefill_ifaceAcache_refill_treeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCpopulate_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;cache_allocC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeC35stdpp4base;RelDecisionI35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6astate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps@insert_insert_eqC35stdpp7tactics<f_equal_helpI47Corelib4Init5Logic2eq00C35stdpp4base6insertI59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes2idC35stdpp4base6lookupC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlAcls_set_num_freedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW=ARefill_iface?put_cls_put_clsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW=ARefill_iface?get_cls_put_clsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW=ARefill_iface4apopC1?~~~~~~~~~~~~~~~".
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
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01Rh11ch21kh32stp;1p;2p;3p;4g0000R0p6051000R1g001:R2p4p710R3p8P1p1001op4p710p8P1p1002ip4p710p8p200R4P1p8P4P3p8P4p1003op4p710p8p1004mR3p4p73101R1p1005GR5p4p73110p8P1p1005`R6p4p73110p8P1p1006<p4p710p8P1p1006OR7p4p7201p8P1p1006ap4p7201p8P1p10073R8p4p73110p8P1p1007GR9p4p73110p8P1p1007[R:p4p73110p8P1p10085p4p7201p8P3p4p710R1P5p4p710p8P1P6p4p710p8P1p1008HR6p4p710R5p8P1P6p4p7210R6p8P1P8p4p710p8P1P9p4p710p8P1P:p4p710p8p1008aR:p4p710R1p10095p4p710p8P1P5p8P1P6p8P1p1009Sp4p73110p8P:p4p741110R:p1009ep4p73101p8p100:Ap4p7<111111111110p100:cp4p710p8p100;Ap4p741110R1P3p4p7511100R6p8P6P1p8p100;Zp4p741110R1P3p4p76111100R6p8P6P1p8p100<2p4p741110R1P3p4p771111100R6p8P6P1p8p100<Rp4p741110R1P3p4p7:1111111100R3p8P3P1p8P7p4p7200R7P:p8P:P7p8P2j10Tg00<ij29Tg00=cj12Tg00>]j21Tg00?:j18Tg00?Xj27Tg00@5j23Tg00A5j34TP0j45Tg00Aoj26Tg00BIR0g00CDg00CbR2f4#0R7[\0f3R0#0P2P7g00DBf2R7f1R2'9R:#2R1'1f0R3g00D`#8,71/3:=427g00EEO2P0P7P2P3C5n0100000020000'6W2W1W3X04o"). Qed.

(* [comment removed for export] *)
Definition apop (c : Z) (st : astate) : astate :=
  put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st.

Lemma put_cls_put_cls : forall c r1 r2 st, put_cls c r2 (put_cls c r1 st) = put_cls c r2 st.
Proof.
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01ch12r1h22r2h32stp;1p;4p;;p;:p;9p;8p;7p;6p;5p;2p;3p;@p;<g00Eej1;Tg00Fcj1<Tg00Gaj19Tg00HZj1CTg00ISj1HTg008aj4>j3STg00<2j4Vj3OTg005`j4UTg00JMj18Tg00KEj15Tg00L>j16Tg00M7j1FTg00N0j1GTg00Noj1ETg00Oil;Dl:?l9@j8Aj7Bj6:j5Tl<3Tg00Pdj1=Tg00Qdj1WTg00Aoj21Tg00RDj3RTg00;Aj3QTg00;Zj3PTg00R[j3NTg00S2j3LTg00<Rj3KTg00SJj3MTg00Scl@JTg00TEj80Tg00Tbj37Tg00A5j34Tg00U<j7ITg00CDR0g00UPR1f4f3R2f2R3f1R4f0R5FIp=2g00BIR6P0P6%;5R7%<5R8%95R9%C5R:%H5R;P0g00VKR<g00VdR=P1C>R>P0P1P>P0P<P=P1CVCUR?P2P4P>P?P2P3%85R@D2RAD2RB%55RC%65RD%F5RE%G5RF%E5RGM;DP7P8P9P:P;P>P?P2P4P@D2RHPCPDPEPFPGM;D%=5RIPIg00WB#WRJP6\0RKP7P8P9P:P;PBPCPDPEPFM:?P7P8P9P:P;PHPCPDPEPFM:?PGPGP0PK\JRKP7P8P9P:P;PBPCPDPEM9@P7P8P9P:P;PHPCPDPEM9@PFPFPJPK\0RKP7P8P9P:P;PBPCPDGAP7P8P9P:P;PHPCPDGAPEPEg00X=RLPK\JRKP7P8P9P:P;PBPCFBP7P8P9P:P;PHPCFBPDPDPLg00X[g00Y4g00YRC>RMPK\LRKP7P8P9P:P;PBE:P7P8P9P:P;PHE:PCPCP>PK\MRKP7P8P9P:P;DTRNPNPBPHPK\>/1NP0AS0<=AR0<=AQ0<=AP0<=AO0<=AN0<=AL0<=AK0<=P<AM0<=P1P@P2P4P3M@JG011MCG011LDG011JEG0110FG011JGG0110IG0P7P8P9P:P;PAPCPDPEPFPGPIM<3RA#;%<A%9A%CA%HAP>P?P2P4%8AD2%5A%6A%FA%GA%EA%=AM<3P7P8P9P:P;PHPCPDPEPFPGPIM<3576eA42359424A4245576eW3X21X11X00o"). Qed.
Lemma get_cls_put_cls : forall c r st, get_cls (put_cls c r st) c = r.
Proof.
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01ch11oh21rh32stp;1p;2p;3p;4p;7p;6p;?p;<p;5g00ZMj1VTg00Zoj2UTg00[Qj1;Tg00Tbj30Tg00Aoj2LTg008aj4<j3TTg00;Aj4:j3QTg00<2j45j3=Tg005`j46Tg00JMj12Tg00U<j78Tg00[mj63Tg00RDj3STg00;Zj3KTg00R[j3>Tg00S2j3?Tg00<Rj3@Tg00SJj3ATg00:Al?BTg00:cj6CTg00Eej1DTg00Fcj1ETg00Gaj1FTg00HZj1GTg00ISj1HTg00KEj1ITg00L>j1JTg00M7j14Tg00N0j17Tg00Noj1MTg00Pdj1NTg00Oil<OTg00A5j3PTg00<ij29Tg00\Aj5RTg00UPR0P0f1R1g00\\f0R2DRp=1g00CDR3g00BI%V0R41U01%;0R5/12f2R6500X141L01P3P0P3g00VKR4g00VdR7P0C<R8P3P4P7P0C:R9P6P3P0P8P3P0P8P3P4P7P0C5C6P6P1%22R:F8R;E3P3AT347AS347AQ347AK347A=347A>347A?347A@347P4AA347P0P:P6P1M?BECP3P0P8P9P6%D2%E2%F2%G2%H2P;%I2%J2%42%72%M2%N2M<O#2E3,15=001eAP612/96=001eW3X20W0o"). Qed.

(* [comment removed for export] *)
Lemma take_is_apop : forall c n st2,
  put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
  = apop c (put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2).
Proof.
ltac2:(KReplay.run1 (kr_t_ARefill_iface ()) ["CANSEC1"] "h01ah11ch21nh33st2p;2p;1p;3p;4p;6g00<ij24Tg00]Vj18Tg00?Xj21Tg00^Tj25Tg00@5j22Tg00?:j1<Tg00A5j30Tg00=cj17Tg00Tbj33Tg00Aoj2;Tg00_Xj49Tg00:cj66Tg00``j3:Tg00ahj2=Tg00CDR0g00BIR1g00UPR2f1R3f0R4f2R5'4R6#8/13/56R6'2R7f3R8g00D`#<R9,151438R:#8/15/5:R:'2;03R;%74/19/24125:=083508531X02P1%77/19/27R2=054R8A31;4X011;18A0574R89052P5P7P2P4C9E61485A:574E61139/26=0541=58531eW3X20W1o"). Qed.

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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
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
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st_r X' RNG' ms', refill_ret H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x364d4) fc None m (seg_rom asegs)).
End CANSEC2.
