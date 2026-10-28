(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_ntf_C MallocKit_B MallocKit_B3 F_am_A F_am_D.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_ntf_C RF_am_A.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ctx_cells_cbn :=
cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
rmrep st m -> mem_inv usegs m ->
c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15a60) fc None m (seg_rom usegs)).
Proof.
intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _).
pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _).
pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite FMH in C1.
unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (324152, 324152 + 928)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
st1. st1.
Local Ltac2 Set LiaHints.tbl := fun () => "00i0?11803370145.91 11803370145.96 11805467289.85 11805467289.94 12804833496.77 12804833496.89 14088807311.96 16578951632.91 16578951632.96 17993216811.77 17993216811.87 28522121551.10928522121551.99 31093012116.73 35259131608.77 35259131608.89 35587154027.85 35587154027.94 38045062865.77 38045062865.87 44321886545.88 44321886545.94 44440941251.74 45793870753.73 45799703203.74 46231211805.10946231211805.99 49702956586.91 49702956586.96 50701188381.77 50701188381.89 51163085556.85 51163085556.94 52565067731.91 52565067731.96 52567164907.85 52567164907.94 53518944813.73 5438383832.77  5438383832.89  57391599064.77 57391599064.89 59715610898.85 59715610898.94 62049120331.91 62049120331.96 63021423832.77 63021423832.89 65715393699.91 6572136593.96  6916085439.109 6916085439.99  6987929670.109 6987929670.99  8831611568.96  8832910886.109 8832910886.99  00000400800900:00;00<00=00E00M00Q00U00Y00]00b00c00d01301B01H01N01O01P01_01n02=02A02E02I02M02N02O02P02Q02U02Y02Z02[02\02]02^02_02`02a02b03203B03C03D03L03M03Q03U03Y03]03e03n047S2HBS2HBSSSSSS3PB22HBS3NB22HBS2LOS2LOS2HxS2HxS3HB0SSS2LO4LOLE5ATOPRS2LO4LOLE5ATOPRS4LOLES4LOLESSS3NB03NB15ATOPRS3HB03HB15ATOPRS3HB03HB15ATOPRS2HxS2HxS2HBS2HBSSSSS2HBS2HBSSSSSSSSSS2LO4LOLE3PB12HBS2LO4LOLE3NB12HBSSS3PB02HBSS2HxS2HxS2HxS2HxS3NB02HBS4LOLE2HxS4LOLE2Hx".
assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.
st1. if_cases K; zify_cond K.
-
assert (Enx : nx = h).
{ rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold rctx_head_cells, rsecw, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells usegs ?mX 324152 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 324000) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
[exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | atop_facts; lia | lia].
- lazymatch goal with H : mem_inv usegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk usegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
-
assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).
rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. st1. clear CH.
rmeta_open (conc st nx) MUn WMn.
rmeta_chunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
st1. st1.
rewrite bv_eqb_refl. cbn [negb]. cbv iota.
rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
rewrite HN, HP in CH. cbn [oconc] in CH.
st1. clear CH.
clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold rctx_head_cells, rsecw, RCTX in C1.
replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
{ eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold rctx_head_cells, rsecw, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
unfold pw. unfold wz at 4.
lazymatch goal with H : rw_cells usegs ?mX 324152 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
st1.
assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
{ rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
rewrite EQ.
change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 324000) with (Z_to_bv 64 RSSP_GUARD).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
[exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | atop_facts; lia | lia].
- lazymatch goal with H : mem_inv usegs ?mX |- _ => exact H end.
- lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
- lazymatch goal with H : stk usegs ?mX lo _ |- _ => exact H end. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. repeat split; intros x Hx.
+ apply ram_fp_stack. lia.
+ eapply ram_fp_meta; [exact MR | exact MSh | lia].
+ eapply ram_fp_meta; [exact MR | exact MSp | lia].
+ eapply ram_fp_meta; [exact MR | exact MSn | lia].
+ apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv usegs m ->
c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
c_avail_meta (ctx st) = Some q -> meta_slot st q ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
(am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15a60) fc None m (seg_rom usegs)).
Proof.
intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _).
pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite FMH, AVM in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
st1. st1.
rewrite bv_eqb_refl. cbv iota.
st1. st1.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>16086156136.6117995379242.6119613635584.6138038706128.6153504623920.619217695454.61 00000400800@00F00G00HS2CRS2LOS3CNT2CRS4LOLESS".
assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
rewrite CF; clear CF.
st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
change (Z_to_bv 64 324000) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 324144) with (Z_to_bv 64 RMLOCK).
eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
[exact MR | exact MI | exact MSq | lia | exact FR | exact ST | atop_facts; lia | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15ab4) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15a60) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR FMH CNT.
pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite FMH, CNT in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
st1. st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.
End CANSEC1.
