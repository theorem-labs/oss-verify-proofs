(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RF_fse_iface_m RF_fse_h_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Section CANSEC1. Context {rc : runConstT}.
Section FuzzMalloc.
Hypothesis MALLOC : rmalloc_stmt.
#[using="MALLOC"] Theorem fuzz_malloc_proof : fuzz_malloc_stmt.
Proof.
unfold fuzz_malloc_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP A0 Hn.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
unfold FUZZ_MALLOC_STACK, RMALLOC_STACK in LOS. atop_facts.
subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
unfold Harness.fuzz_malloc.
apply implM_from_evt.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "00V0>15333948891.5717986829365.5717993511084.5517997477515.5918661941992.6120433961190.5722346159760.8622706553108.5822706553108.9122706661829.6222706661829.952431198685.57 28811795261.8731399144472.5531401241662.8831723364983.5934061680638.863525496340.86 3538291509.59 36656704145.593828097560.56 3830243106.89 42030722078.5943059266230.5545914037331.6149528435466.8849705053714.615187842268.59 54164510851.6154164510851.6354164510851.9659308628433.8961927706159.5764295316298.5864297265517.5567081926311.6167541566890.618838919089.59 00000600;00@00E00W00X00Y00g01A01L01W01]01l01m01n01o02002C02V02Z02_02d02i02n03203303;03@03A03B03C03K03O03X03a03b03j03kS2Hn1KS3LOAS3LOAS3LOAS3LOA3LOS5ATOPR2HBSSS2Hc3LOA5ATOPRS2Hc3LOA2Hn5ATOPR1K3BR12K2S3LOA2H12R4S3LOA2H02R4S2Hn1KS2Hn5ATOPR1K2BRSSFSS3LOA3LOS3RSP5ATOPRS3LOA3LOS3RSP5ATOPRS2HnS3LOSS3LOSS3LOSS3LOSS2HBSS3RSP2HBS3SPBSSSS3BR12K2S2HnS3SPB3LOAS3SPB3LOASS3LOS2HBS".
carve_frame 16%nat ST.
subst a0. unfold PFUZZ_MALLOC. zstep. zstep. zstep.
if_cases K; zify_cond K.
-
assert (n = 0) by lia. subst n. cbn [Z.ltb Z.compare].
zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
apply evt_done. apply implM_ret. apply evt_done.
unfold fuzz_malloc_post.
do 15 eexists. exists m0, errv. split; [reflexivity|].
split; [exact MI|]. split; [exact ST|]. split; [rewrite errno_lit; exact ERR|].
split; [eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]|].
split; [eapply rheap_pres_of_munch; [exact MU| exact WM|]; intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|];
pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _); destruct Hr; atop_facts; lia|].
split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]].
-
replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
zstep. apply evt_done.
assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
assert (AUX1 : rauxv_ok m0 B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
eapply implM_bind.
{ unfold rmalloc_stmt in MALLOC.
eapply MALLOC with (lo := lo) (B := B); try reflexivity; unfold RATP, RMALLOC_STACK; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (192304 + -164) with 192140; exact ERR]. }
cbv beta. intros r s' ms1 PO.
destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 83708)) with (Z_to_bv 64 83708) by (symmetry; rpc).
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [CB 8 (take 8 junk); C8 ra])
by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
clear FR ST MI ERR AUX1.
destruct r as [p|].
+
destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & _).
assert (RA : 0 <= A < 2^64) by (unfold rblock_range in BR; lia).
apply implM_ret. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
zstep. zstep. zstep.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold fuzz_malloc_post.
do 15 eexists. exists m2, errv1. split; [reflexivity|].
split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX2|].
split; [eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]] | eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]]|].
{ pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
split; [exact FAE|]. split; [exact SOE|]. exists A, junk2. split; [reflexivity|]. split; [exact BR|]. split; [exact HP2|]. split; [exact BLK| exact HEXP].
+
unfold new_handler. apply implM_unr.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FuzzMalloc.
Section Create.
Hypothesis FMALLOC : fuzz_malloc_stmt.
#[using="FMALLOC"] Theorem prod_create_proof : prod_create_stmt.
Proof.
unfold prod_create_stmt. intros until errv. intros HP AUX SPB ST LOA LOS ERR MI TP.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
unfold PROD_CREATE_STACK, FUZZ_MALLOC_STACK, RMALLOC_STACK in LOS. atop_facts.
subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
apply implM_from_evt.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "00d0?10301016579.57 1429396990.84  17329002384.84 17993200554.55 17997477515.57 18661941992.61 18661941992.64 19006120615.64 22706553108.98 22706661829.10225566553219.10525566553219.64 28811795257.89 31723364983.57 33683134761.10533683134761.97 34272850783.97 34290115814.54 34374917116.10534374917116.97 35765334355.61 35765334355.64 37196084401.57 38806986883.10338806986883.61 39937556005.96 40577385243.93 41562522430.95 41940620810.95 42757277271.10542757277271.97 43059266230.52 45426444089.97 49705053714.61 49705053714.64 54618151079.64 55104759171.10555104759171.64 56793047152.10556793047152.97 56965461077.79 6166287527.61  62405693620.97 64295316298.56 67541566890.61 67541566890.64 7186771765.57  7190718996.84  788664796.57   7917304984.93  8041752945.105 8838919089.57  00000500600700<00A00S00e00f01801C01D01E01X01Y01a02102202302702;02?02C02D02E02F02K02X02Y02Z02^02b02g02h03003803903:03;03S03k03o04004804A04I04Q04d05705<05=05E05FS3LOSSSS3LOAS3LOAS3LOA3LOS5ATOPR2HBS3LOA3LOS5ATOPR2HBSS2Hc3LOA5ATOPR3BR1S3LOA2H02R4SSS5ATOPR3BR13BR33BR4FS3BR22HBS3BR23BR33BR52HBSSS2HBS2HBS2HBS2HBSSSS3LOSS3SPB3LOA3LOSSSS2HBS2HBS3LOSSS3RSP2HBS3RSP2HBSSSS3LOA3LOS3BR13BR33BR42HBS3LOA3LOS3BR13BR33BR42HBS2RRSS3BR12HBS3SPB3LOAS3LOS2HBS3LOS2HBS3LOA3LOS3RSP5ATOPRS3LOA3LOS3RSP5ATOPRS3SPBSS3BR12HBS".
carve_frame 32%nat ST.
unfold PPROD_CREATE. do 4 zstep. zstep. zstep. zstep. zstep. apply evt_done.
assert (HP1 : RHEAP s LB m0) by (eapply RHEAP_stack_frame; [exact HP| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
assert (AUX1 : rauxv_ok m0 B) by (eapply rauxv_ok_stack_frame; [exact AUX| exact MU| exact WM| constructor; [cbn; atop_facts; lia| constructor]]).
eapply implM_post_evt.
{ unfold fuzz_malloc_stmt in FMALLOC.
eapply FMALLOC with (lo := lo) (B := B) (n := PRODUCER_SIZE); try reflexivity; unfold RATP, FUZZ_MALLOC_STACK, RMALLOC_STACK, PRODUCER_SIZE; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact AUX1 | exact ST | exact MI | lia | change (192304 + -164) with 192140; exact ERR]. }
cbv beta. intros r s' ms1 PO.
destruct PO as (u0 & u1 & u2 & ra0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv1 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
replace (ret_pc (Z_to_bv 64 83280)) with (Z_to_bv 64 83280) by (symmetry; rpc).
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 (take 8 (take 16 (take 24 junk))); C8 s1; C8 s0; C8 ra])
by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
clear FR ST MI ERR AUX1.
destruct r as [p|]; [| destruct RR as (RR & _); unfold PRODUCER_SIZE in RR; lia].
destruct RR as (A & junk2 & -> & BR & HP2 & BLK & HEXP). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
assert (RA : 0 <= A < 2^64) by (atop_facts; lia).
unfold PRODUCER_SIZE in BLK. change (Z.to_nat 16) with 16%nat in BLK.
apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8]%nat) in BLK; [| reflexivity]. cbn [mk_CB_cells app] in BLK.
pose proof (munch_refl [(A, A + 16)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
zstep. if_cases CK1; zify_cond CK1; [exfalso; lia|].
zstep. assert (A7 : Z.land A 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
rewrite A7. zstep. if_false.
zstep. zstep.
destruct (fh_transport s' [(p, A, PRODUCER_SIZE)] LB m2 m3 _ B (bv_unsigned sp + -32) HP2 MU2 WM2
ltac:(constructor; [right; exists (p, A, PRODUCER_SIZE); split; [left; reflexivity| unfold PRODUCER_SIZE; cbn; lia] | constructor]) ltac:(atop_facts; lia))
as (HP3 & AUX3 & _ & HPR23).
specialize (AUX3 AUX2).
zstep. zstep. zstep. zstep. zstep.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold prod_create_post.
do 15 eexists. exists m3, errv1. split; [reflexivity|].
split; [exact MI2|]. split; [exact ST2|]. split; [rewrite errno_lit; exact ERR2|]. split; [exact AUX3|].
split.
{ eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|]]|].
{ pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]|].
eapply rheap_pres_weaken; [exact HPR23| lia| intros b Hb; exact Hb]. }
split; [exact FAE|]. split; [exact SOE|]. exists p, A. split; [reflexivity|]. split; [reflexivity|]. split; [exact BR|].
split; [exact HP3|]. split; [exact BLK| exact HEXP].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Create.
Section Free.
Hypothesis FREE : rfree_stmt.
#[using="FREE"] Theorem prod_free_proof : prod_free_stmt.
Proof.
unfold prod_free_stmt. intros until errv. intros HP IN AUX SPB ST LOA LOS ERR MI TP A0.
unfold PPROD_FREE. apply implM_from_evt. zstep. apply evt_done.
unfold rfree_stmt in FREE. eapply FREE; eassumption || reflexivity.
Qed.
End Free.
End CANSEC1.
