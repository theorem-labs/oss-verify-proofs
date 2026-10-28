(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free MallocModel_B F_ntf_B.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 48 junk; C8 CAN; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End CANSEC1.
Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl usegs mX) as WMq end.
Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUq WMq CH end.
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma rntf_ret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (raw s0o s1o s2o s3o : word) st st' (lo : Z),
rmrep st' m -> mem_inv usegs m ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
munch ((bv_unsigned sp - 96, bv_unsigned sp) :: W) m0 m -> wmono usegs m0 m ->
ivs_covered (rfree_fp st lo (bv_unsigned sp)) W ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st' a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1597c) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
unfold RSSP_GUARD, rntf_frame in *. atop_facts. subst s1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl usegs m) as WMs.
st1. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>2124193155.68 32127996803.675114850435.69 59192637571.6760513468962.5862302209411.6865704383697.6167800019075.688832910886.59 945059608.57  00000100200300400:00;00D00E00N00OSSSSS4LOLESS2LO4LOLESS4LOLE2HxS".
st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rntf_aor : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (i lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
a1 = wz (sxv (2 ^ i)) -> 0 <= i < 32 ->
s1 = Z_to_bv 64 RSSP_GUARD ->
0 <= m_freed (get_meta_rec st g) < 2^32 ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (aor_st st g i) (wz 0) (wz 0))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15954) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & _). pose proof MSL as MS0. destruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
destruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
unfold NSLOTS in *. atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "00E0?11805467289.83 15380552744.83 16073575531.82 16075476085.83 1748580572.84  17990988689.82 18598711923.83 25071629079.83 30653525686.83 36030390537.82 41415908849.83 43143351063.83 44015250961.83 49705053714.83 58152820913.78 59560234164.83 62132444267.82 63397145987.82 63399046557.83 66149329551.1049538426821.83  00000400800?00C00G00K00m01101801<01=01A01B01F01j02J02P02Q02R02l02mS2HBS2HIS2RF2RSS2RFS2HxS2LOS2LO4LOLE3Hk03Ca04Sa014RBC03HGA2HBS2HBS2GB2HBS2HFSS2HFSS2HBS2LO3Hk03Ca04Sa004Sa014RB004RBC03HGAS3Hk03Ca04Sa014RBC03HGA5ATOPR2GBS4LOLESSS2HI4SaL05RBAL01H2H02H42H9S".
assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
set (mr := get_meta_rec st g) in *.
pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
{ apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. lia. }
subst a1.
st1. rewrite sx32_wz_sxv by lia. st1.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep (aor_st st g i) mX) end.
{ unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
- reflexivity.
- cbn. tauto. }
clear MUg MM.
st1. st1.
eapply rntf_ret; [exact MR' | assumption | exact S1 | exact FR | exact ST | atop_facts; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [exact MR | exact MSL | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rntf_frame_remerge : forall m A (j0 : list byte) (z1 z2 z3 z4 z5 : word) rest,
rw_cells usegs m A (CB 8 j0 :: C8 z1 :: C8 z2 :: C8 z3 :: C8 z4 :: C8 z5 :: rest) ->
rw_cells usegs m A (CB 48 (j0 ++ le8 z1 ++ le8 z2 ++ le8 z3 ++ le8 z4 ++ le8 z5) :: rest).
Proof.
intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
eapply rw_cells_congr; [| | | exact H].
- cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
- reflexivity.
- split; [| destruct WFr as (_ & _ & _ & _ & _ & X); exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.
#[using="Type"] Lemma rntf_fm : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (lo : Z),
rmrep st m -> mem_inv usegs m -> meta_slot st g ->
fm_facts st g ->
s1 = Z_to_bv 64 RSSP_GUARD ->
rw_cells usegs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -96) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 ->
evt usegs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x158b8) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR MI MSL FMF S1 FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
unfold RCTX, rntf_frame in *. atop_facts.
rmeta_chunk MR MSL CH.
pose proof MR as (_ & (C1 & _) & _). unfold rctx_head_cells, rsecw, RCTX in C1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.
Local Ltac2 Set LiaHints.tbl := fun () => "01_0>11803370145.6411803370145.6711803370145.7511803370145.7611803370145.7711803370145.7811803370145.8911803370145.9511803370145.9611803370145.9711805467289.7812326863311.9712602660183.7612602660183.7712602660183.7812602660183.9512804833496.7015270429157.7615270429157.7715270429157.9516578951632.6416578951632.6716578951632.7516578951632.7616578951632.7716578951632.7816578951632.8916578951632.9516578951632.9616578951632.971748580572.71 1748580572.90 17990988685.6917990988685.8818600809035.7518600809035.7618600809035.7718600809035.7818600809035.8918600809035.9518600809035.9618600809035.9719092398759.6420163737475.6720163737475.7326492550416.6426492550416.6726492550416.7526492550416.7626492550416.7726492550416.7826492550416.8926492550416.9526494647592.7828370640551.6728680052209.8928680052209.9730655622798.7530655622798.7630655622798.7830655622798.8935205357699.6735205357699.7335209714819.6435209714819.7335259131608.7035851768520.6435851768520.6739084537573.7639084537573.7739084537573.9540150930599.6741272171651.6741272171651.7346231211805.9048188050435.9049702956586.6449702956586.6749702956586.7549702956586.7649702956586.7749702956586.7849702956586.8949702956586.9549702956586.9649702956586.9750131542183.6750701188381.7051163085556.7852565067731.9652565067731.975438383832.70 57391599064.7059314923118.6659314923118.7559715610898.7859759152700.9760872868459.7862132444279.6962132444279.8863021423832.7063854226795.6463854226795.6764698649075.7564772824451.6764772824451.7265704383697.6065715393699.966987929670.71 6987929670.90 7486304935.67 00000400800<00@00D00H00M00R00W00\00]00^00_00`00a00b00c00d00e00f01801J01Q01X01_01f01n02602>02F02J02N02R02V02k03@03U03j04@04V04l05B05C05D05E05I05M05Q05U05Y05]05b05g05h05i05j05k05o06306706<06=06>06?06@06A06V06k06o07307807907:07;07?07C07K07S07W07[07_07c07h07m08208708808908:08?08D08E08F08L08R08S08X08g08m09309409809<09O09P09Q09Z09_09c09g09hS2HBS2HBS2HBS2HBS2HBS2HBS3HB0S3HB0S3HB0S3HB0SSSSSSSSSSS2LO4LOLE5ATOPR2HBS2LO4LOLE5ATOPR2HBS2GB2HBS2GB2HBS2GB2HBS2GB2HBS2GB3HB0S2GB3HB0S2PB3HB0S2HB3HB0S2HxS2HxS2LOS2LOS2LO4LOLE2GB5ATOPR2HBS2LO4LOLE2GB5ATOPR2HBS2LO4LOLE2GB5ATOPR2HBS2LO4LOLE2GB5ATOPR2HBS2LO4LOLE2GB5ATOPR3HB0S2LO4LOLE2GB5ATOPR3HB0S2LO4LOLE5ATOPR2PB3HB0S2LO4LOLE5ATOPR2HB3HB0SSSS2HBS2HBS2HBS2HBS2HBS2HBS3HB0S3HB0SSSSS2HBS2HBS2HBS3HB0SSSSSS2LO4LOLE2GB5ATOPR2HBS2LO4LOLE2GB5ATOPR2HBS2HBS2HBS3HB0SSSS2HxS2HxS3SPR2HBS3SPR2HBS2HBS2HBS2HBS2HBS3HB0S3HB0S3HB0S3HB0SSSS3HB0S3HB0SSS2LJ1KS2HB1KSS3HB0S2LO4LOLE5ATOPRS4LOLES4LOLESS2HBS2HBS2GB2LJ5ATOPR2HB2PBSSS2LO4LOLES3HB0S2HxS2HxS".
st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRf : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
clear MUs.
rmeta_open (conc st g) MUg WMg.
st1. st1.
st1. st1.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
assert (CH' : rw_cells usegs mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; tauto]);
clear CH; rename CH' into CH
end end.
st1. st1.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
assert (CH' : rw_cells usegs mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
by (eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear CH; rename CH' into CH
end end.
rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
set (st0 := put_meta g meta0 st) in MR0.
assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; exact MSL).
rmeta_chunk MR0 MSL0 CH0.
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
clear CH0 K1 K2.
st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
-
destruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by exact NEh.
unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1.
clear CHh.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH.
st1.
rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; exact MSp).
munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
st1.
rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
st1. clear CH.
rmeta_open (conc st head) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
rewrite get_meta_rec_put_same.
rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
st1.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | atop_facts; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSh | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSp | lia].
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
-
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1. st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.
clear C1. pose proof MRb as (_ & (C1 & _) & _). unfold rctx_head_cells, rsecw, RCTX in C1. rewrite FMH in C1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
{ eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. unfold wz at 4. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.
st1.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [exact MR3 | assumption | exact S1 | exact FR' | exact ST | atop_facts; lia | lia | exact MU | exact WM |].
cbn [ivs_covered]. unfold RCTX. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [exact MR | exact MSL | lia].
+ apply rfree_fp_ctx. unfold RCTX. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
