(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W3 ASlot_W14.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RASlot_W2 RASlot_W4.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof.
intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. Local Ltac2 Set LiaHints.tbl := fun () => "0010=11607865080.4000001S".
rewrite Z.mod_mod by lia.
f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
Local Ltac2 Set LiaHints.tbl := fun () => "0010<2587196448.2000001S".
rewrite (mod_mod_pow2 _ 32 64) by lia.
rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma unsigned_mod32_swrap_add_not a b :
bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). Local Ltac2 Set LiaHints.tbl := fun () => "0040=20913760734.42587078841.3 38715876989.439165928090.4000001002003007SSSS2RB".
rewrite (mod_mod_pow2 _ 32 64) by lia.
pose proof (sxv_range b) as RB.
rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia.
unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
clearbody x y. Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof.
intros Hx. Local Ltac2 Set LiaHints.tbl := fun () => "0020=14880337059.363368323942.3000004005S2HxS".
rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
(r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.
Definition rtailW : list (Z * Z) :=
[(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.
#[using="r AV FR SC CNT AI ML MST REC Hr Hk P0 P16 PEND GNONE NOGRP OLD12 UR ACT TK"] Lemma rtail_walk :
forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
rmrep stT mC -> mem_inv usegs mC ->
evt usegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16854) fc None m' (seg_rom usegs)
/\ munch rtailW mC m' /\ wmono usegs mC m' /\ mem_inv usegs m'
/\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x166fc) fc None mC (seg_rom usegs)).
Proof.
intros until mC. intros MR MI.
pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl usegs mC) as WM. unfold rtailW in MU.
pose proof (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
pose proof (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). atop_facts.
assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
pose proof (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.
destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
unfold RCTX, RMLOCK in *. atop_facts.
pose proof (rmrep_usage_read (stA stT p) mC sc (wa (324152 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
change (usage (stA stT p) sc) with (usage stT sc) in RDU.
Local Ltac2 Set LiaHints.tbl := fun () => "01j0?10248308338.11110250732959.11110423411451.11112578249668.88 12578657236.99 12812525531.12512942117097.11113733556894.11114285882357.11115272293356.10815272293356.11217212679867.11117684931484.10417687372726.10317699624332.78 17723711466.80 17723711466.86 18490123812.78 19704384439.11121010089708.10821010089708.11222067004187.11123989202659.11223989216365.10725381642938.88 2589713875.111 26794244518.1032740098216.112 28900772779.10828900772779.1122912153760.104 29317317366.10329321854076.10829330713501.99 2939895369.108 2950332137.107 29749124343.10729749137657.77 30163643147.18130267903917.84 31220622482.84 32152749536.11133178051695.11138480705517.11941061482954.12542333700063.10442360909120.88 43523888347.11243835677707.11144732114796.10844744366566.10345083264315.11145249807107.12545249807107.12645249807107.12745249807107.91 45249807107.95 45249807107.97 45952365940.10746495093594.11147037017337.11248052304414.11148817211143.11149234157850.12549234157850.12649234157850.12749234157850.91 49234157850.95 49234157850.97 49437953845.12549437953845.12649437953845.12749437953845.91 49437953845.95 49437953845.97 49702840724.10949702840724.79 49962465963.11151271146707.10351860072732.88 52530479858.11852564885613.10952564885613.79 52565067731.12552565067731.12652565067731.12752565067731.91 52565067731.95 52565067731.97 52567164907.10852567164907.11253779279450.10856284736507.84 56284884342.10356286811819.11156945583962.86 57225978214.12557225978214.12657225978214.12757862605606.10358011231069.11258639763035.12758915522346.86 59148686920.10359310614929.11259314873579.12259314938599.12159314938599.12459879375120.79 60246374218.10762148669186.79 62149010433.77 62149029531.77 6231855609.116 63353258869.10463363773797.78 63964887643.11164792434089.12564792434089.12768319910160.1097442899475.111 8927523831.111 00000900B00N00U00`00f00l01601?01C01G01M01U01]01e01f01g01h02502G02Y02_02e02k03403:03;03D03H03L03T03U03V03c03h03m04604:04m04n05305905B05I05W05[06C06D06N06V06^06d07207@07N07W07`07i07o08508908H08Q08Z08c08l09009409809A09J09S09W09[09_09h09l0:50:90::0:;0:A0:B0:K0:T0:]0:a0:e0:i0:m0;10;50;:0;?0;I0;N0;Z0;f0<20<70<80<90<>0<B0<g0=90=S0>C0>G0>M0>N0>O0>P0>W0>_0>g0>m0?30?90?B0?K0?XS2SC4LACTS2SC4LACTS2ML4LACT2EWS2P02CPS2P02CP3LHBS4LACTS4LACTS3AVR4LACTS2SC4LACTS2HBS2HBS4LACTS3CNT2AIS3CNT2AIS3CNT2AISSSS2SC3CNT4LACTS2P04PEND2CP2GX2HBS2P04PEND2CP2GX2HBS4LACTS4LACTS4LACTS4PEND2CPS4LACTSS2P04PENDS2HBS2HBS2Y83L8RSSS4PEND2CP3LHBS3W8RS3W8RS2SC4LACTS2SCS2P04PEND2GI3RI13RI23AVR4AV1R2GX4LACT1H2H02H42H52H9SS3CNTS4LACTS2ML4LACTS2CP2HaS4Gpos4LACT2HBS2Y8S2P03P164PEND4Gpos2R43RAL3RI13RI22CP3AVRSS3CNT4LACTS3CNT2AIS3CNT2AIS4LACTS4Gpos4LACT2HBS4Gpos4LACT2HBS4Gpos4LACT2HBS4Gpos2HBS4Gpos2HBS4Gpos2HBS4LACTS4LACTS2HBS3AVR4AV1R4LACTS2ML4LACTS4LACT2HBS4LACT2HBS4LACT2HBS2HBS2HBS2HBS4LACT2HBS4LACT2HBS4LACT2HBS2HBS2HBS2HBS2SC4LACTS2SCS2ML4LACTS2Y8SSS4LACTSS4LACT2HBS4LACT2HBS4LACT2HBS2HBS2HBS2HBS2HBS2HBS2HBS3CNTS3CNTS3CNT4LACTS3FRRS2GI4LACT2HBS2GI4LACT2HBS2GI4LACT2HBS3CNTSFS3AVRS2Y8S2P04PEND3RI22CP2Ha2X12X22X32X42X52X6S2CP2Ha2Rb2Cb2EQ1HS2P02CP2Ha2Rq3LRr1D4PEND1HS2P02CP2Ha3Rak3LRr2Ca3Sa11D4PEND1H2Rb2Cb3Sb13Sb0S2SCS4LACTSSSS2CP2HaS3CNT2AIS3CNT2AIS4LACTS4LACTS4LACTS2SC4LACTS2SC4LACTS2SC3CNT4LACT".
replace (wa (324152 + 464 + 8 * sc)) with (Z_to_bv 64 (324144 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
step. clear RDU.
step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.
pose proof MRA as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok usegs _ _ (usages (stA stT p)) sc (wa (324152 + 464 + 8 * sc)) USG
ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
replace (wa (324152 + 464 + 8 * sc)) with (Z_to_bv 64 (324144 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
rraw_store_finish0 (324152 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRA TKA.
step. rewrite ?(unsigned_lit ai) by lia. rewrite ASlot_W14.sllw2_word by lia.
step.
set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
rmeta_open G MUa WMa.
step. step.
assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
{ subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
rewrite (sx32_congr v3 AV V3).
step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite ASlot_W14.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
step. step.
set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
{ subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
step. step.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
| clear MUa WMa; rename H into CH1 ] end.
assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear MRB TKB MSTB.
pose proof MRC as (WFC & _ & _ & _ & _ & SHC). pose proof WFC as (_ & _ & DJ & _ & WG).
destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) end.
destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (HDR : rw_cells usegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
[ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
| clear HB LHB ] end.
pose proof (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl usegs mX) as WMb end.
step.
step.
pose proof (byte_range y8) as Y8.
step. unfold zxb.
step. rewrite ?(unsigned_lit ai) by lia.
replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
step.
pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
rewrite (land224_m32 (bv_unsigned y8)) by lia.
pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].
set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.
lazymatch goal with H : rw_cells usegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
rename H into HDR2;
assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
| assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
[ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
[ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
| rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
| ] ] end.
{
intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
- unfold RCTX in X1. lia.
- unfold RMLOCK in X2. lia.
- unfold RNEED_LOCKS in X3. lia.
- unfold RPAGE_SIZE in X4. lia.
- change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
destruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
- change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
destruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
+ rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
+ pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
- change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
destruct (N.eq_dec q (fst p)) as [->|NE].
+ rewrite Hr in Hq. inversion Hq; subst rq.
destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
+ pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
- unfold RGOT_SSP in X5. lia.
- unfold RSSP_GUARD in X6. lia. }
clear MRC MRC2 MUb WMb HDR2.
assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
clear TKC MSTC.
pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
rmchunk MRD MSTD CH.
change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
rmeta_open G MUc WMc.
step. step. step. step. step.
rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
rewrite (unsigned_lit W), EW, land_pg_mask by lia.
step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
step. rewrite ?unsigned_lit by lia.
step. step. step. step.
rewrite ?(unsigned_lit (mask_upto ai)) by lia.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
lazymatch goal with H : u64arr usegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_read usegs mX (324152 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (324152 + 80 + 8 * sc)) H
(actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
replace (wa (324152 + 80 + 8 * sc)) with (Z_to_bv 64 (324232 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
step. clear RDA.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. step.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
[ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]
| clear MUc WMc; rename H into CH3 ] end.
{ unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
unfold wz. rewrite !app_nil_r.
rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
fold AV. Z.div_mod_to_equations. lia. }
do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
{ reflexivity. }
{ cbn. tauto. }
assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
clear MRD TKD MSTD.
clear CH3.
lazymatch goal with H : u64arr usegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (u64arr_store_ok usegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (324152 + 80 + 8 * sc)) H
ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
replace (wa (324152 + 80 + 8 * sc)) with (Z_to_bv 64 (324232 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
st1.
replace (Z_to_bv 64 (324232 + 8 * sc + 0)) with (Z_to_bv 64 (324232 + 8 * sc)) in SOK by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
rraw_store_finish0 (324152 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.
step.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [exact MRF| exact TKE].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End TAIL.
End CANSEC1.
