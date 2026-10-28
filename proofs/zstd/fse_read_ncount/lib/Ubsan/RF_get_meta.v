(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma land_pow2_testbit a i : 0 <= a -> 0 <= i -> Z.land a (2 ^ i) = 0 <-> Z.testbit a i = false.
Proof.
intros Ha Hi. split.
- intros H. destruct (Z.testbit a i) eqn:E; [|reflexivity]. exfalso.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=10358064710.752401173550.9000004008S2HiS2NE".
assert (T : Z.testbit (Z.land a (2 ^ i)) i = true) by (rewrite Z.land_spec, E, Z.pow2_bits_true by lia; reflexivity).
rewrite H, Z.bits_0 in T. discriminate.
- intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n i) as [->|NE]; [rewrite H; reflexivity|].
rewrite (Z.pow2_bits_false i n) by lia. apply andb_false_r.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sllw1_word' i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof. intros Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0010=63045839500.3000004S2Hi".
rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rget_meta_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw : word) (off16 : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a2 a3 a4 a5,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs).
#[using="Type"] Lemma rget_meta_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc m
(off16 mword maplen : Z),
0 <= off16 < 65536 -> 0 <= mword < 2^64 -> 0 <= maplen < 2^40 -> Z.shiftr mword 12 = maplen ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt usegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 gw off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 gw (wz off16) (wz mword) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x155b8) fc None m (seg_rom usegs)).
Proof.
intros until maplen. intros O16 MW ML MW4 Hml.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>35497698988.4346244227119.4252067444116.4353221464206.4159308628433.4363368267308.4368243864272.4300000100500;00?00L00M00RSS2MLS2ML1KS2MWS2ML3Hml1K2K2SS3O16".
st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
- st1. unfold rget_meta_post. finish.
- st1. st1. st1. if_cases K2; zify_cond K2.
+ st1. unfold rget_meta_post. finish.
+ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rget_meta_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes usegs m (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes usegs m (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes usegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes usegs m (wa B) 8 = Some (le8 (wz G)) ->
rw_cells usegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes usegs m (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes usegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes usegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
evt usegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz G) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x154c4) fc None m (seg_rom usegs)).
Proof.
intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml.
Local Ltac2 Set LiaHints.tbl := fun () => "01I0?11113887407.91 11447729958.12411447729958.13811601594822.10212286795281.98 12413379419.10312500081776.10512502177912.10713743595831.88 16073345020.10116075458812.99 17210514661.10517212610797.1071848929278.94  18926775167.10518928873335.10718975794542.91 19038168386.11021920755834.99 22069180487.10322557358668.10222594001611.11027380898049.97 29142762609.11029315560028.83 29317547131.92 30528594179.1053096926302.107 31278981366.86 31426263356.10231647478602.10132508646054.10534883041389.1053525623219.92  36181693477.10536183789613.10738136276674.86 40599920879.94 40819006291.86 40825300204.87 40928706962.91 41239403044.87 41415942218.94 42167987094.94 42630527239.92 42790217749.10643605390242.10744015211434.94 45081116263.10346609845873.91 49712580022.94 49712984728.1065073687222.94  53221409744.10453221409745.93 53226811716.96 54466369468.1045650221412.101 56862904998.10257022143158.86 58206708432.10559308628433.87 59308628566.92 59308628695.94 59308629082.10359308629336.10659314923118.86 60013227756.10660015712838.10760140672325.10260700203023.86 63152162437.84 63348584395.1026636562324.99  6638938260.101 66688225592.1026755967158.105 67990047766.10767992143902.10568243864272.87 6970102948.87  7441127501.106 7441127886.105 8532563493.97  8534580141.98  8927055265.108 8927110142.82  8929151147.102 9538464382.94  00000400500600700;00?00I00Z00c00h00m00n00o01401501601:01;01@01A01B01C01G01H01I01J01N01S01X01Y01^01e01i02902:02;02?02D02E02F02G02L02M02Q02a02e03903:03;03<03A03F03J03O03T03U03V03Z03[03\03]03e04304<04D04Y04n05205605705805@05G05H05I05U05V05W05X05]05a05e05i05n06306K06X06b06cS2B3FFSS2FRS2SES2LI2FB2K9S2LI2FB2SC3MW22K8S3GLO3GHIS3SXIS3SXISSS3IDXSSS2LIFS3SXASSFS2AVFSSS2K8S3IDXS3O16SS3SXFS2SC2K8S2K8S2HP3PLO3PHI3O16SSS2B3S3IDXSSSS3O16SS2AVS3PLO3PHI2HB3O16S2SZS3PLO3PHI3Hsc3IDX2SZSSSS3IDXS3IDXS2LIS3MWRS3MWRFFS2FRSSSS3GLO2K2S2HP2HB3GLO2K3S4Hidx2K4S3GLO2K7S3GLO2SC5Hsc633IDX2K9S2HP2AL3PLO3GLO3O161KS2SZS2SZSSS3GLO2B3S2LI2FBSSS3GLO3GHI2HGSSSS3O16S2HBS2SCS2SCS3IDXS3IDXS3PLO3PHI3O163Hsc2SZ3IDXS2LI2FB2SC2MLS2LI2FB2SCS".
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.
assert (RG' : ov_read_bytes usegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. exact RG. }
st1.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. rewrite MW2. st1. st1. if_cases K8; zify_cond K8.
- specialize (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
- specialize (RS ltac:(rewrite ?wz_unsigned in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned in K8 by lia; lia)).
st1. st1. st1. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
assert (RS' : ov_read_bytes usegs m (Z_to_bv 64 (68784 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (68784 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. rewrite GW. eapply rget_meta_tail; eauto.
subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rget_meta_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
st (p : aptr) r g gh ar (b3 lo hi : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
rmrep st m -> mem_inv usegs m ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
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
evt usegs (rget_meta_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 a7 (wz (conc st g)) off16 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rget_meta_entry) fc None m (seg_rom usegs)).
Proof.
intros until hi. intros sh po off16 idx base mr MR MI Hr Hk HP AL P16 PLO PHI C4 C3 C2 C1 Hgh Hg MS G0 Hmem Har Hchk HID
AV FR SE LI FB SC ML Hidx Hav Hfr Hsc Hsc63 Hml. pose proof sec_range as SECR.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & _). atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "00J0?10662066343.10011515307516.10311888887009.13216998880622.13118844022393.13118926747947.13018928490433.12919681463867.1311988470344.130 1990406306.129 2442693916.106 24805867756.10628072791123.13131276902392.13135831776013.11236044444300.13137855574625.1013869037841.103 40017915602.10340273374871.1304154889992.131 46234224835.13152527029236.13154785571905.13158797286115.1317243157411.131 00000900>00F00G00a00b00c00k01001501901=01_01f01g01h02102602702802Y02Z02[02i02j02kS3P163PHIS3PHIS2SC3HltFS3P162B02A02HG3RB04RBAL2HmSSS3PLO2B0S3HkkS3HkkS2LOS2HIS3P162B05ATOPR2A02A12HG3RB03RBC2HmS2LO2HISFS3P163PHIS3P16SSS2AL3P162B03BAL2A02HG3RB04RBAL2HmSFS3PHI2BC5ATOPRSS".
destruct (rmrep_shadow_read st m (fst p) r (po - 4) 0 MR Hr Hk ltac:(lia) C4) as [R4 _].
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) C3) as [R3 B3].
destruct (rmrep_shadow_read2 st m (fst p) r (po - 2) lo hi MR Hr Hk ltac:(lia) ltac:(lia) C2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact C1)) as (R2 & LO & HI).
rewrite <- le2_lohi in R2 by lia.
destruct (rmrep_group_read st m base gh MR Hgh) as [RG _]. rewrite Hg in RG. cbn [pw oconc] in RG.
pose proof (rmrep_meta_chunk st m g MR MS) as MM. fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
pose proof (rmrep_area_check_read st m (area_of g) ar MR Har) as RA.
pose proof (rmrep_ctx_secret_read st m MR) as RC. unfold rsecw in RC. rewrite HID, Z.mul_1_r in RC.
destruct (WG base gh Hgh) as (rb & Hrb & _ & Bb0 & _). cbn [base aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
assert (HB : conc st base = (r_base r + po) - 16 * off16 - 16).
{ unfold base. rewrite conc_aadd by (rewrite Hr; eauto). rewrite (conc_region' st p r Hr). unfold po, UNIT. lia. }
destruct MS as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & A0 & A1 & AAL & ANG & _).
assert (HG : conc st g = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
destruct (WR (fst a) rg Hrg) as (RB0 & RBAL & RL0 & RBC & _). atop_facts.
assert (Hm : (r_base rg + snd a + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
{ unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (r_base rg + snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096 + r_base rg / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
{ rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a) _ rg Hrg).
replace ((snd a + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [lia|].
unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (snd a + (24 + 40 * k)) with ((24 + 40 * k) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
unfold rget_meta_entry.
eapply (rget_meta_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(r_base r + po) (conc st g) (conc st base) (conc st (area_of g)) b3 off16 (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) SECRET
(pw st (m_prev mr)) (pw st (m_next mr))); try eassumption; try lia.
- replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
- replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
- replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
- intros Hlt. apply rsize_classes_read; [exact MI | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition runlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom usegs).
#[using="Type"] Lemma runlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
bv_unsigned a0 = RMLOCK ->
rw_cells usegs m (bv_unsigned a0) [C4 (wz 0)] ->
evt usegs (runlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 runlock_entry) fc None m (seg_rom usegs)).
Proof.
intros until m. intros HA LK. unfold runlock_entry.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>20811133800.3953512850223.3859314923118.386636560927.37 000001002005006SSS1KS".
step. rewrite sx32_wz by lia. step. if_cases K; zify_cond K.
{ exfalso. rewrite wz_unsigned in K by lia. lia. }
step. apply evt_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
