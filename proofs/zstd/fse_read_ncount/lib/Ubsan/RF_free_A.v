(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; lia.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. Local Ltac2 Set LiaHints.tbl := fun () => "0020=12853367178.35738539914.3 000003006S1HS1H".
rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
intros (LI & FB & SCR & ML).
assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
Local Ltac2 Set LiaHints.tbl := fun () => "00=0=16307678836.722701701582.729311237449.735560185155.739539102563.746611986243.752257470722.752335558569.761162877165.765101109554.76757834505.7 68575966226.79982888524.7 00000100200300400500600700800900=00>00B00JSSSSSSSSSS2FBSS2LIS2FB3SCR".
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof.
intros (LI & FB & SCR & ML). unfold meta_word.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=12500182983.618926670024.657504004860.668257150872.600000;00<00=00>S2LI2FB3SCRSSS".
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
fun ms' => exists x1 x5 x6 x7 junk m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 0x4f3f8) x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x153fc) fc None m' (seg_rom usegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rmrep st1 m'.
#[using="Type"] Lemma rfree_head3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (b3 lo8 hi E rsv : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
rmrep st m0 -> mem_inv usegs m0 -> ticks_ok st ->
stk usegs m0 lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells usegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono usegs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 ->
r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
0 <= rsv <= E - (r_base r + po) -> bytes_at usegs m0 (E - rsv) [b8 0] -> bytes_at usegs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 E) a3 (wz rsv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x153ac) fc None m0 (seg_rom usegs)).
Proof.
intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). Local Ltac2 Set LiaHints.tbl := fun () => "00f0?10052459652.12211284053051.11811803471779.11611803471780.11813776223718.11413794057816.11614946198807.11415045343677.10815047392320.10915450407813.11716407571081.1171730476540.116 17680713856.1182061316626.116 25316211135.11829319558748.99 30163642374.15431706190871.11633021745617.11133246259908.11734213079687.11534219699462.10434308191119.12035193784488.11635193784495.11836032650285.11336940382882.10936942432095.1083864950422.116 39832083051.11940599920750.11341246720063.11644282350701.11145710826623.11147430410825.11647430410830.11849702855464.11649702855471.11849712579895.11351845331698.11452461394096.11652461394103.11854854631278.11556756951631.11757020048649.11257020048776.11157979857178.11659308628304.11163070133766.11463160699423.1006437622708.115 66752045130.1146959603832.142 8929152679.113 00000700;00<00=00B00F00G00H00I00N00O00S00[00_00c00d00e00m01F01K01Z01i02002502:02;02<02=02B02C02H02L02M02i03803G03U03c03h03l04104604704C04D04E04J04U04c04n05705<05U05cS3Hfb1HS2HPSSS3P16S2HPFSSS3P16SS2HPS3P162B0S2HPS2HPSFS3P162B0S3P163EHI3RSV2B02BC5ATOPRS3PHIS5ATOPR3GB03GB1S5ATOPR3GB03GB1S3Hfb1HS3ELOS3ELOFSSS3P16FS3IDXS2HxSS2HP3P163ELO3EHI2B02BC5ATOPRS2LO3SLO3PHI2BCS2LO3SLO3PHI2BCS3PHI2BC5ATOPRS3PHI2BC5ATOPRS3IDXS2HPS3RSVS3RSVSS3P163PHI2E1SSS3PHIS2HP3RSV2K1S2LI3FBL2SC2MLS3P162B32B0S3P163PHIS3PHIS3P163PHI2LI3DR13DR21H2H0S2LI3FBL2SC2ML".
rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
unfold UNIT, IB in *. atop_facts.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
pose proof (bytes_at_read usegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
pose proof (bytes_at_read usegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
change (Z_to_bv 64 E) with (wa E).
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
st1. st1. st1. st1. st1. st1.
rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).
pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (SOK3 : store_ok usegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok usegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
st1.
pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
cbn [aadd snd] in MR2. fold po in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
store_done.
pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
assert (SOK2 : store_ok usegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok usegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
st1.
pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
by (f_equal; unfold wa; f_equal; lia) end.
store_done. clear MR2 TK2 HWr HWr2.
st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
st1.
apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|exact I].
intros x Hx. right. right. exists (fst p), r.
assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
apply evt_done. unfold rfhead_post.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
do 6 eexists.
split; [reflexivity|].
split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m0 -> mem_inv usegs m0 -> ticks_ok st ->
stk usegs m0 lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells usegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono usegs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 -> idx <= m_last_idx mr ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at usegs m0 (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at usegs m0 (E - rsv) [b8 0] -> bytes_at usegs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15364) fc None m0 (seg_rom usegs)).
Proof.
intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). Local Ltac2 Set LiaHints.tbl := fun () => "00i0?11114081108.12411114102463.12312249741094.12314243942656.11514258790949.13115047392262.12915047393029.12817991118401.12417991118401.13318575860103.11518643397249.13022019219413.11224377480565.13425274333651.12929319558748.11129319558748.11229524243131.12429524243131.13330317230969.12430317230969.13330496653699.12430496653699.13332050077487.12333474526376.12433474526376.13333779087833.11433781014569.12434217503677.12136940382948.12938140572854.12438140572854.13344012953868.11244420404170.12444420404170.13346304757610.12547938239946.12447938239946.13349089635664.11449712544523.12351220585756.12451220585756.1335632717941.131 57020049165.13257702632612.13259308628820.13159308628949.13259591509826.12961108963232.11263160699423.11263730766366.12463730766366.13365158813098.12465158813098.13366120358059.12466120358059.13368058897448.1288528073404.115 00000700>00B00I00Q00U00V00]00d00l01001701@01D01H01L01T01\01d01l02302:02]02e02m03303:03L03P03W03^03b03i04004904@04G04P04X04g05605<05@05H06006;06?06F06T06\06d06l07407C07R07S07[S2FB2B3S2FB2B3S2FBS2FB2H0S2FB3R32S2FBSS2LO2FBS2LO2FBS2FB3S16S2FBS2FB2B3S2FB2Kb1HS2FBS2FBS2FBS3SLO2FBS3SLO2FBS3P162FBS3P162FBS2FB2MLS2FB2MLS2FB3SB03S163EHI2B02BC2HB3SI05ATOPRS3PHI2FBS3PHI2FBS2FB1HS2FB2KbS2FB5ATOPR3GB03GB1S2FBS2FB2B3S2FB2B3S2FBS2FB2SCS2FB2SCS2FB2Kb1HS2FB2LIS2FB2LIS2FB4RSV0S2FB3IDXS2FB5RSVLE4RSVRS2FB5RSVLE4RSVRS4RSV0S2FBS2FB3R32S3P163PHI2FB3BIG2B03DR13DR23GB02Kb2R52K5S2FB3R322K6S2FBS2FB2B3S3P162FB2B32B0S2FB3EHIS2FB3EHIS2FB3FBLS2FB3FBLS2FB5RSVLE4RSVRS2FB5RSVLE4RSVRSS2FB3IDX".
rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
unfold UNIT, IB in *. atop_facts.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
fold rsv0.
st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
-
replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| atop_facts; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
-
destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
pose proof (bytes_at_read usegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
pose proof (bytes_at_read usegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).
st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
st1.
rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[exact MR1| exact MI| exact TK| exact ST| atop_facts; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
| exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo8 + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m -> mem_inv usegs m -> ticks_ok st ->
stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
c_init_done (ctx st) = 1 ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
(m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m (E - 4) (le4 (wz r32)) /\ bytes_at usegs m (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at usegs m (E - rsv) [b8 0] -> bytes_at usegs m E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs)).
Proof.
intros until r32. intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk HID
AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl usegs m) as WM.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). Local Ltac2 Set LiaHints.tbl := fun () => "01I0?1023186998.161 11114070788.15711805467289.14311805467289.14411805467289.14511805467289.14611882686727.16311889055804.16412371985717.14213204087972.16114243942656.13116075441888.16517991465224.1561800609155.145 21595786118.16322019219413.12824638473347.14525604052563.14325604052563.14425604052563.14525604052563.14627823659829.15628212591088.15628227477070.16228372211924.16129315069148.16229319558748.12629319558748.12829524583922.15629713772808.16530317046832.15630496478922.15631378308326.13633474341857.15633773558382.15633779087833.13034217285255.14834705803648.16335191588242.14335191588242.14435191588242.14535191588242.14636028488970.16336032651178.15736032655604.16136032655735.16037855283162.14737861640391.12738140879871.15638142564733.15740281870821.14840825688260.16541361206858.15642048681435.16242296134476.13242875510527.15643059739913.13443988483203.14344012953868.12844279994491.16244420613251.15645848756903.14347937890947.15649089635664.13049649769127.14649705053714.14349705053714.14449705053714.14549705053714.14650586359343.13852105090727.14552459394442.14352459394442.14452459394442.14552459394442.14654243526019.14456368389193.16259308628179.13460858483367.14561108963232.12863160699423.12763305555623.14463624026922.16164997134979.14665158628067.15667509714473.1658832910886.162 8871789335.156 8990858532.150 00000400;00C00K00S00[00g01301701E01I01P01W01[01_01c01g01o02702?02G02O02X02`02n03203303403<03@03H03O03S03[03c03f04804A04W04m05C05Y05a05i06406?06K06T06[06b06i06m07807<07D07L07T07X07Y07d07k07o08608<08@08L08X08d09009;09?09Z0:50:P0:k0:o0;70;H0;L0;P0;X0;\0;f0;j0<20<90<D0<N0<_S2FBS2B32FBS2FB3HB0S2FB3HB0S2FB3HB0S2FB3HB0S2SC4SC482FBS2SC4SC482FBS2FBS2LO3EHI2BC2FBS2H0S2FB2SZS2LO2FBS2FBS2FBS2B3S2FBS2FB3HB0S2FB3HB0S2FB3HB0S2FB3HB0S3EHI2FBS4Hidx2FBS2FB3MWRS2LO3EHI2BC2FBS2FBSSS3SLO2FBS2FBS3P162FBS2ML2FBS2FBS3PHI2FBS3S162FBS1HS2FB5ATOPR3GB03GB1S2FB4MW5RS2LO3SLO3EHI2BC2FB3HB0S2LO3SLO3EHI2BC2FB3HB0S2LO3SLO3EHI2BC2FB3HB0S2LO3SLO3EHI2BC2FB3HB0S2FB3MWRS2FB3MWRS2LI2FB3MWRS2ML2FB3MWRS3P163PHI2FBS3P163PHIS2B32FBS2B32FBS2HP2FBS2FBS2AV2FB3FRDS2FBS3PLO2FBS3ELO2FBS3SLO2FBS2FBSS3SLO2FB2HAS2SC2FBS2FBS2LI2FBS4RSV0S2FBS3SPR2FB3HB0S3SPR2FB3HB0S3SPR2FB3HB0S3SPR2FB3HB0S2LO3SLO2FBS2FBS2LO3SLO3EHI2BC4RSVR2FB3HB0S2LO3SLO3EHI2BC4RSVR2FB3HB0S2LO3SLO3EHI2BC4RSVR2FB3HB0S2LO3SLO3EHI2BC4RSVR2FB3HB0S2FBS2FB3MWRS2HP3P162B02FB2K0S2FBS2B3S3P162B0S2FBS2ML2FB2KmS2FBS3FBL2FBS2FB2SZS3SLO2FB2HxS5RSVLE2FBS2LI3FBL2SC2ML2FB".
rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (FB : fst base = fst p) by reflexivity.
assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).
revert BIG RB0r RE0.
unfold rfree_entry, UNIT, IB in *. atop_facts. intros BIG RB0r RE0.
st1. if_cases K0; zify_cond K0. { exfalso. lia. }
carve_frame 48%nat ST.
st1. st1. st1. st1. st1. st1. st1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; atop_facts; lia) end.
eapply evt_cut.
{ eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
all: try eassumption. all: try lia. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
replace (ret_pc (Z_to_bv 64 0x1531c)) with (Z_to_bv 64 0x1531c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (MW : mw_ok mr) by (unfold mw_ok; lia).
pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (K2 : forall a4v a5v a6v, evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0x1531c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15364) fc None mX (seg_rom usegs))) end.
{ intros a4v a5v a6v.
lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
lazymatch type of MUs with munch ?W m ?mY =>
assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
subst rsv rsv0 E stride mr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
[exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
| exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
| intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
(eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
| ulia
| exact RB0r
| exact RE0
| exact HCLR]. }
st1. st1. st1. st1. fold idx. rewrite MW12.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt usegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 0x1531c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15348) fc None mX (seg_rom usegs))) end.
{ intros a2v a4v COND. specialize (SC48 COND).
assert (STR : stride = 16 * size_class (m_sizeclass mr)).
{ unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
replace (68784 + m_sizeclass mr * 2) with (68784 + 2 * m_sizeclass mr) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (RS' : ov_read_bytes usegs mX (Z_to_bv 64 (68784 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
{ replace (Z_to_bv 64 (68784 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }
pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
rewrite Egw. apply K2. }
st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- apply KS. left. exact Km.
-
st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
+ apply KS. right. exact Kl.
+
st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
rewrite Egw. apply K2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
