(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Lemma land_align_downA : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 ->
Z.land x (2^64 - 2^j) = x - x mod 2^j.
Proof.
intros x j Hx Hj.
replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
2:{ Local Ltac2 Set LiaHints.tbl := fun () => "00:0=14236896541.429138970806.43255672360.4 34427047669.535497642740.445272753470.452665820999.45333442898.4 5744835304.4 8098277724.4 00000400800900<00=00A00E00F00J00KS2HjS2HjSS1HSS2HjS2HjSS2HxS".
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section CANSEC1. Context {rc : runConstT}.
Definition AGOT_SUAR_R : Z := 0x99968.
Definition AGOT_RDPC : Z := 0x9a588.
Section S.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (SP lo : Z).
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis SPT : SP + 16 < KEND.
Hypothesis LOS : lo <= SP - 208 - 4096.
Hypothesis LOC : ATOP <= lo.
Variable RNG : footprint.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RI : rng_aimg RNG.
Definition SPAz : Z := (SP - 192) - (SP - 192) mod 32.
#[using="rc SP16"] Lemma spa_propsA : SP - 208 <= SPAz <= SP - 192 /\ SPAz mod 32 = 0 /\ (SP + -192) - (SP + -192) mod 2^5 = SPAz.
Proof. unfold SPAz. change (2^5) with 32. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>53663102416.5600000LS4SP161H2H02H42H52H93H103H14".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition RFRB : list cell :=
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
#[using="rc SP16 SPT LOS LOC RSTK RI"] Lemma rd_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
stk bsegs m lo SP -> mem_inv bsegs m ->
rt_got m -> rt_shbase m -> rw_cells bsegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xa2540)] -> rw_cells bsegs m 0xa2540 [C4 (Z_to_bv 64 1)] ->
evtF bsegs RNG (fun ms' => exists m' (k0 k8 k16 k24 k32 k40 k48 k64 k80 : list byte),
ms' = MS (mkR (Z_to_bv 64 0x81dd4) (Z_to_bv 64 SPAz) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
(Z_to_bv 64 64) (Z_to_bv 64 0xa2538) (Z_to_bv 64 1) a3 a4 a5 a6 a7
s2 s3 s4 a0 a2 a4 (Z_to_bv 64 2147450880) s9 s10 a3 t3 t4 t5 t6)
F (Z_to_bv 64 0x3d70c) fc None m' (seg_rom bsegs)
/\ munch [(SP - 208, SP)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' (SP + -104) RFRB
/\ rw_cells bsegs m' SPAz [CB 8 k0; CB 8 k8; CB 8 k16; CB 8 k24; CB 8 k32; CB 8 k40; CB 8 k48; C8 a1; CB 16 k64; CB 8 k80]
/\ stk bsegs m' lo SPAz /\ stk bsegs m' (SPAz + 88) (SP + -104))
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x81d54) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ST MI GOT SHB GSU SUA. unfold AGOT_SUAR_R in *.
unfold KEND in SPT. pose proof atop_range as ATR.
pose proof spa_propsA as (SPAB & SPA32 & ESPA').
assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
pose proof (munch_refl [(SP - 208, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
zstep.
Local Ltac2 Set LiaHints.tbl := fun () => "02X0>10098610879.7210262788553.6710287669065.6510287669065.6710287669065.6810287669065.6910287669065.7210521085166.6711712726766.681209240649.68 12685940462.6713285916654.6713641502813.66136972401.67  13758363081.6813960432457.6714033283697.6814809345196.6815008299246.6716776327022.6716953994825.6817098239598.6917264948956.6717305155697.611792056942.68 17939878638.6718090942830.6818752423881.671892362350.68 189732078.68  19622476014.6719821716078.6819961167854.6720709228048.7220836929836.6721155567546.6721901813971.6022163107130.6722426949358.6723174934126.692342125148.67 2355290730.60 24018786414.6924630998586.6724804226798.6724929030857.6725497026414.6725792608750.6726029473774.67261014828.68  26231113562.6426669182065.6726746114263.6726845759404.6827223603310.6828102239214.6728123739863.6828925250064.7229531591534.6829655294843.6329789957596.6729870281326.6830013766257.6830196181434.6831056488905.6131521058898.6531521058898.6831856720366.673199430677.65 32087020145.6932180884106.7132345147607.6732651489978.6832716547054.6732873346092.6733680001082.6734250653712.7234490278001.6734782976605.6634784644311.6835525229038.6735930198638.6836546680269.6536550167516.6737587267666.6537587267666.6838782755822.6738884154028.6839302203090.5639849574766.6840008004846.6840330257262.68422954356.71  42831019478.6542831019478.6843872227804.6744752146798.6844905565996.6744908879575.6845003960669.6645221239098.6745425164105.6846232973498.694641771485.66 46787521756.6746949129329.6747297859287.6747392944934.7247486080659.6548292934228.6548300761460.6148593432558.6749738116823.6749778780654.6749925508974.674996873838.69 50861135698.6550861135698.6850933153196.6851781592413.6652026536339.685217574615.68 52780046574.6754068232029.6654077074143.6854226150513.6854256297073.6754682826094.6754823529033.6955866736855.6956007886318.67563227834.68  56941978156.6757334927063.6757496662641.685771667637.60 57745675194.6859116267735.6859308628179.6259470286470.5859705885297.6760404244496.7260937512265.6862084694894.6862302827721.6762682870638.6862757205152.6562775338994.586290697132.67 62969565356.696398474066.65 6398474066.68 64993435597.6865298667515.7265800495305.6765805175866.6867810302577.6868071416502.6168179576725.686867211502.68 7136133920.68 7408240000.61 7960668270.68 8013425879.67 8583720762.67 8796323372.67 9183949166.68 9193927790.68 00000400500600700800900?00Q00c00d01601H01M01N01O01P01Q01U01g02902:02L02Q02c03503G03Y03Z03l04>04P04b05405F05J05O05a05f06806J06O06P06b06g07907:07L07^08008408908:08;08?08Q08c08d09609H09I09N09`09a09f09g0:90:K0:]0:^0:_0;10;20;70;I0;M0;R0;d0;e0;j0;k0<=0<O0<P0<U0<g0=90=K0=O0=T0=f0>80>J0>K0>P0>U0>Z0>l0?00?10?60?;0?<0?A0?F0?K0?L0?M0?Q0?R0?c0@40@F0@G0@Y0@k0A=0AO0Aa0Ae0Aj0Ak0Al0B>0BC0BH0BI0BJ0B\0B]0B^0C00C50C90C:0C;0C<0CA0CB0CF0CG0CH0CZ0C[0Cm0Cn0D@0DD0DI0DM0DQ0Dc0E50E60E<0E=0EB0EC0EH0EI0E[0E_0E`0F20F30F80F<0FN0F`S2HBSSSSSS4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSSSSSS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3SPTS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOSSS3LOS3LOC3ATR4SPABS3SPTS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOSSSS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOSS3LOS3LOC3ATR4SPABSS3SPTSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSSS3LOS3LOC3ATR4SPABSS3SPTS3LOS3LOC3ATR4SPABS2HBS3SPTS3LOS3LOC3ATR4SPABSS3LOSSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABFS3SPTS3SPTS3LOSS3LOS3LOC3ATR4SPABS2HBSS3LOSS3SPTSS3SPTS3LOSS3LOSSSS2HBSS3SPT3LOS3LOC3ATRS3SPT3LOS3LOC3ATRS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABS2HBS3LOSSSS3LOS3LOC3ATR4SPABS3LOSS3LOSSSS3LOS3LOC3ATR4SPABSSS3LOS3LOC3ATR4SPABS3SPTS2HBSSSS3SPTSS2K0SSS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABSS3LOS3LOC3ATR4SPABS2HBS3LOSS2HBS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPABSS4SPABSS3SPTSS3LOSSS3LOS3LOC3ATR4SPABS2HBSS3LOS3LOC3ATR4SPABSS3SPTS2HBS3LOS3LOC3ATR4SPABS3LOS3LOC3ATR4SPAB".
carve_frame 104%nat ST. carve_frame 88%nat ST.
zstep.
do 13 zstep.
zstep.
zstep.
change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
release_frame FR0 ST (SP + -104).
destruct (stk_split bsegs _ lo (SPAz + 88) (SP + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
destruct (stk_carve bsegs _ lo (SPAz + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
change (Z.of_nat 88) with 88 in STL, FRA. replace (SPAz + 88 - 88) with SPAz in STL, FRA by lia.
pose proof (rw_cells_split_CB bsegs _ SPAz [] 88 jA [] [8; 8; 8; 8; 8; 8; 8; 8; 16; 8]%nat FRA eq_refl) as FRA2.
cbn [app mk_CB_cells] in FRA2. clear FRA.
zstep.
zstep. zstep. zstep.
zstep.
zstep. zstep. zstep. zstep.
clear GOT GSU.
zstep. rewrite (sx32_small 1) by lia.
zstep.
zstep.
zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
zstep. zstep.
apply evtF_done.
do 10 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
split; [exact FR|]. split; [exact FRA2|]. split; [exact STL| exact STG].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition RFFHDR (FF FLG : Z) (junk : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d54); CB 32 junk; C8 (Z_to_bv 64 FLG)].
Definition RFFSH : list cell :=
[C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
C1 (Z_to_bv 8 18446744073709551608); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].
#[using="Type"] Lemma shadow8_c1sA : forall m s, rw_cells bsegs m s [C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m s [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.
#[using="lo SP16 LOS LOC RSTK RI"] Lemma rd_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) m (FF FLG MSVP BUF NC TLP hb : Z)
(j0 j1 j2 : word) (junk : list byte) (k0 k8 k16 k24 k32 k40 k48 k64 k80 : list byte) (Q : machine_state -> Prop),
rw_cells bsegs m SPAz [CB 8 k0; CB 8 k8; CB 8 k16; CB 8 k24; CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; CB 8 k80] ->
rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m AGOT_RDPC [C8 (Z_to_bv 64 0x81d54)] -> mem_inv bsegs m ->
unpoisoned m MSVP (MSVP + 4) -> MSVP mod 4 = 0 -> ablk MSVP (MSVP + 4) -> (MSVP + 4 <= FF \/ FF + 64 <= MSVP) ->
ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 ->
ablk BUF (BUF + hb) -> 0 <= hb ->
rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG (shad MSVP) 1 ->
(forall m' (y10 y11 y12 : word),
munch [(SPAz, SPAz + 88); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m m' ->
wmono bsegs m m' -> mem_inv bsegs m' ->
rw_cells bsegs m' SPAz [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)] ->
rw_cells bsegs m' FF (RFFHDR FF FLG junk) -> rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH ->
Q (MS (mkR (Z_to_bv 64 0x81dd4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
y10 y11 y12 (Z_to_bv 64 18446744073709551603) x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + hb)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
F (Z_to_bv 64 (if 7 <? hb then 0x81f0c else 0x81eb0)) fc None m' (seg_rom bsegs))) ->
evtF bsegs RNG Q
(MS (mkR (Z_to_bv 64 0x81dd4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
(Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
s2 s3 x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
(Z_to_bv 64 2147450880) s9 s10 (Z_to_bv 64 BUF) x28 x29 x30 x31)
F (Z_to_bv 64 0x81dd4) fc None m (seg_rom bsegs)).
Proof.
intros until Q. intros FRA FFC SHF GPC MI UM M4 BM MF FH FC F64 BBK HB0 RF RSF RSM K.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ BM) as (BMa & BMb & BMc & BMd).
pose proof (ablk_lin _ _ BBK) as (BKa & BKb & BKc & BKd). unfold AIMG_HI in *.
unfold AGOT_RDPC in *. pose proof atop_range as ATR. unfold KEND in SPT.
pose proof spa_propsA as (SPAB & SPA32 & _).
apply shadow8_c1sA in SHF. Local Ltac2 Set LiaHints.tbl := fun () => "02]0?10191062042.11610299541350.11110967961352.11011603250610.11112066655206.11513067081226.1151332645506.111 13557852353.11613736921998.11513876056558.11014239244710.11115160347210.11515341314694.11115701870224.11115849985159.11316283555162.11516753464773.11616867429482.11517415683873.14817458367892.11617941155254.11618343703478.11118369228174.11118412700769.11618412700769.11718412700771.12219202614250.11019599858853.11419621011775.11119834408514.11120200392866.11121163621150.11121286029596.11321470349994.11522575207196.11622575207196.11722575207198.12222736837800.14223584418860.11023687287154.11524200872257.11424521592556.11525334232912.11625418808852.11625556167827.11025927005322.11526525165237.11626525165237.11726525165239.12226774769626.11527413605758.15527818666165.1132818573085.116 28897571974.11528987856538.11529181457478.11129197563789.13229388000845.11729417129412.11429581966254.11029784351708.10629790837596.97 29792256213.11329792256213.11629792256213.11729792256215.12229792256218.11029792256218.11730781785835.11030906104780.11131281980400.11631693696482.11532096596784.11132180884101.12232180884103.11632180884103.11732365281766.11032923343604.1143342490946.111 34167244991.11434252541850.11434437547116.11034437547116.11134437547116.11434437547116.11534437547116.11634597926842.11135301401292.111353645442.115  36293873445.11136685953222.11537568097145.11337646148266.11738105256826.11138114226429.10538709023052.11539159981841.11340763182096.11440829096511.14941091132398.11141416008524.10641547508789.1154173552739.116 422954361.116  422954361.117  422954363.122  4238719193.148 42643832943.11642831019478.11142858367508.11443070630379.105443350610.115  44417097546.111449256530.102  45508725130.11146037991009.11346390900177.10546398707289.11646901542423.11647747998098.11048211285674.11148615158610.11148618085652.11449544569934.11150970283838.11151768488898.10551816630506.11151833088772.11451854515243.10951884304678.11453156436688.11453510313881.11653538127893.14953640511348.97 5464662474.111 55060265338.11555241207509.11056329465350.11356804907040.111568661336.107  56883187806.11557533215052.11557866766837.11357866766837.12057866766842.11657875639024.10658116526106.1115812810971.110 58197955214.11558862976443.11059308628179.10259308693840.10559308693969.10659310676438.14959338331354.11159623654526.11561760858756.11162760451890.11163958622316.11164026414714.11064555500442.11165822352186.11066149329538.13466867539939.1146743478006.110 678924122.113  68066155898.11068100572504.12268100572506.11668100572506.1177382020290.107 8369729419.110 8945620178.107 00000=00F00`00i01201?01J02>02G02H02T02a02j03D03^04<05005=06206?06L06j07^07_07`07a08?08`08l09709k0:80:90:F0:G0:H0:I0:d0:m0;a0<U0<^0=<0=Z0=[0>90>:0>;0><0>I0?<0?=0?F0?O0?\0?e0@I0A10A:0AG0AP0AY0Ab0Ak0B40B=0BF0BO0BX0Ba0Bn0Cb0DH0Db0E<0EV0E_0Eh0F\0Fh0G50G>0GG0GP0GY0Gb0H@0HI0I=0I^0Ig0Ih0Ii0JN0K40K=0L30LM0LQ0L^0Lg0M00M=0M>0M?0M@0N00N=0NJ0NW0Nd0O50OB0OS0O`0Oa0PG0Pl0Q50Qi0R60RC0RL0RY0Rf0SG0ST0T50T>0TJ0Th0U10UH0UQ0Uo0VM0VN0VW0V`0Vi0W60W?0WP0Wa0X20XC0XP0XY0Xf0Xo0Y?0YO0Y_0Z60ZC0ZP0[10[e0[n0\;0\Y0\Z0\^0\k0\l0\m0]:0];0]<0]=0]F0]O0]XS3FHb3FHd3BMbS3FHb3BMbS3LOS3LOC3FHb3BMb3ATR4SPABS3FHb3BMbS3FHb3BMbS3FHb3BMb3BSFS3FHb3BMb1BS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BMbFS3FHb3BMb2HBS3FHb3BMb3BSFS3FHb3BMbS3LOS3LOC3FHb3BMb3ATR4SPABS3LOS3LOC3FHb3BMb3ATR4SPABS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BMb3BSFS3LOS3LOC2M43FHa3BMa3BMc3ATR4SPAB3FHu2K02G22H42H53H19S3FHa3FHb3BMbS3FHb3FHd3BMbS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0FFFS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFS3LOS3LOC3FHb3BMb3ATR4SPAB3BSF2HBS3FHb3BMb2HBS3FHb3BMb1BS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BMb3BSFFS3FHb3BMb3BSFFFFS2M43FHa3BMa2K02G21H2H03H14S3FHb3BMbS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BMbS3LOS3LOC3FHb3FHc3BMb3ATR4SPABS3LOS3LOC3FHb3FHc3BMb3ATR4SPABFS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFFFFS3FHb3BMb3BSFS2M42MF3F643FHa3BMa2K02G21H2H02H42H52H93H103H193H24FS3FHb3BMbS3FHb3BMbS3FHb3BMb3BSFS3FHb3BMbS2MF3F643FHa3FHc3BMa3BMc3ATR1H2H02H9S4SP163LOS3LOC2M43FHb3BMb3ATR4SPAB5SPA32S3FHb3BMbS3FHb3BMb3BSFS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHa3FHb3BMbS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3HB03FHb3BMb3BKa3BKc3ATR4SPABS3LOS3LOC3FHb3BMb3ATR4SPABS3LOS3LOC3FHb3BMb3ATR4SPABS3LOS3LOC3FHb3BMb3ATR4SPABS3FHb3BMbS3FHb3BMbS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BMb2HBS3FHb3FHd3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMbS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFS3FHb3BMbS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3LOS3LOC3FHb3BMb3ATR4SPAB3BSF2HBS3FHb3BMbFFS3LOS3LOC3FHb3BMb3BKa3BKd3ATR4SPAB2G1S3LOS3LOC3HB03FHb3BMb3BKa3BKd3ATR4SPABS3FHb3BMbS4SP163LOS3LOC3FHa3FHb3BMa3BMb3ATR4SPAB5SPA322K02G22CKS3LOS3LOC3FHb3BMb3ATR4SPABS2SRS3FHb3BMb3BSFS3FHb3BMbS3FHb3BMbS3FHa3FHb3BMbFFFS2M42MF3FHa3BMa3BMc3ATR3FHu2K02G21H2H02H42H53H19S3FHa3FHb3BMbS3FHb3BMb3BSFS3FHa3FHb3BMbS3FHb3BMb3BKaS3FHa3FHb3FHd3BMbS3FHb3BMb3BSFS3FHa3FHb3FHd3BMbS3FHb3BMb3BSFFS3LOS3LOC3HB03FHb3BMb3BKa3BKc3ATR4SPABS3LOS3LOC3FHb3BMb3BKa3BKc3ATR4SPAB2G1S3FHb3BMbS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BMb3BSFS3FHb3BMb3BSFS3FHb3BMbS3FHb3BMb3BSFS3FHb3BMb3BSFS3LOS3LOC3FHb3BMb3BKa3ATR4SPAB2G1S3FHb3BMb3BSFS3LOS3LOC3FHb3FHc3BMb3ATR4SPAB2HBS3FHb3BMbS3FHb3BMb2HBS3LOS3LOC3FHb3FHc3BMb3ATR4SPABS3FHb3BMbS3FHa3BMa2K02G22CK1G2H0S3FHb3BMbS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFFS3FHb3BMbS3FHb3BMbS3FHb3BMbS3FHb3BMb3BSFS3FHb3BMbS3FHb3BMa3BMb3BMdS3FHb3BMa3BMb3BMdS3FHb3BMa3BMb3BMdS3FHb3BMa3BMb3BMdS3FHb3BMb3BSFS3FHb3BMbS3FHb3BMb3BSFS3FHb3BMbS3FHa3FHb3BMb2K0S3HB03FHb3BMb2G1S3FHb3BMa3BMb2G2S3FHa3BMa2K02G22CK1G2G'S3FHb3BMb3BSFS3FHb3BMb3BSFS3LOS3LOC3FHb3FHc3BMb3ATR4SPAB2HBS4SP163LOS3LOC3FHa3FHb3BMb3ATR4SPAB5SPA323BSF3FHu2K0S3FHb3BMbS3FHb3BMb3BSFS3LOS3LOC3FHb3BMb3ATR4SPAB3BSFFS2M4S3FHa3FHb3BMbFFS3FHb3BMb3BSFFFFS3FHb3BMbS3FHb3BMbS3FHb3BMb".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in SHF, RSF by (unfold shad, ASHOFF; lia).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
pose proof (munch_refl [(SPAz, SPAz + 88); (FF, FF + 24); (Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
zstep.
zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].
zstep.
do 8 zstep.
zstep. zstep. zstep.
zstep. zstep.
replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
zstep. zstep. zstep. zstep.
zstep.
replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
zstep. clear SOK. zstep. zstep. zstep.
zstep.
zstep.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. replace (0 <? BUF) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
zstep. replace (BUF + hb <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
zstep. change (Z.lxor 1 0) with 1.
zstep. if_false.
zstep. zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. zstep. replace (Z.land MSVP 3) with 0
by (change 3 with (2^2 - 1); rewrite land_ones_mod by lia; change (2^2) with 4; symmetry; Z.div_mod_to_equations; lia).
zstep. if_false.
zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with MUx : munch _ m mx |- _ =>
assert (UMx : unpoisoned mx MSVP (MSVP + 4))
by (eapply unpoisoned_munch; [exact UM| exact MUx|]; rewrite !shad_div; cbn [disjoint_from]; rewrite !Z.shiftr_div_pow2 by lia; unfold ASHOFF;
change (2 ^ 3) with 8; refine (conj _ (conj _ (conj _ I))); Z.div_mod_to_equations; lia)
end end.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
destruct (chk1A mx MSVP (MSVP + 4) MSVP 4 UMx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK & SR) end.
zstep. rewrite sxb_sval.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (JOIN : forall (y10 y11 : word),
evtF bsegs RNG Q
(MS (mkR (Z_to_bv 64 0x81dd4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
y10 y11 (Z_to_bv 64 0x81d54) (Z_to_bv 64 18446744073709551603) x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + hb)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
F (Z_to_bv 64 0x81ea8) fc None mx (seg_rom bsegs)))
end.
{ intros y10 y11. clear RDB CK SR.
zstep. zstep.
if_cases B; zify_cond B.
- apply evtF_done. replace (7 <? hb) with true in K by (symmetry; apply Z.ltb_lt; lia).
eapply K; eassumption.
- apply evtF_done. replace (7 <? hb) with false in K by (symmetry; apply Z.ltb_ge; lia).
eapply K; eassumption. }
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN.
- apply JOIN.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation RET mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
(MS (mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None mm (seg_rom bsegs)).
Definition bx (P : Prop) : Prop := P.
#[using="SP16 LOS LOC RSTK"] Lemma rd_epi : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word) m (FF FLG : Z)
(j0 : word) (k0 k32 : list byte),
rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH ->
rw_cells bsegs m FF [C8 j0] -> rw_cells bsegs m (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m (SP + -104) RFRB -> rw_cells bsegs m SPAz [CB 24 k0; C8 (Z_to_bv 64 FF); CB 56 k32] ->
stk bsegs m lo SPAz -> stk bsegs m (SPAz + 88) (SP + -104) -> mem_inv bsegs m ->
ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> ablk FLG (FLG + 1) -> FLG + 1 <= ATOP -> (FLG + 1 <= FF \/ FF + 64 <= FLG) ->
rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG FLG 1 ->
evtF bsegs RNG (fun ms' => exists mp m',
ms' = RET m' x5 x6 x7 x12 (Z_to_bv 64 FF) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
/\ munch [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
/\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
(MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x82548) fc None m (seg_rom bsegs)).
Proof.
intros until k32. intros SHF FF0 FF56 FLC FRB FRA STL STG MI FH FC F64 GH GC GF RF RSF RG.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in *.
unfold RFFSH in SHF. unfold RFRB in FRB.
pose proof atop_range as ATR. unfold KEND in SPT.
pose proof spa_propsA as (SPAB & SPA32 & _).
assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
Local Ltac2 Set LiaHints.tbl := fun () => "02E0?10299541350.10211603250610.10212066655206.10113067081226.10113111200937.10213641502813.104136972401.105  14033283697.10614793220770.10215160347210.10115341314694.10215849985162.10116283555162.10116753464773.10316867429482.10117264948956.10517523863986.10117738602889.10217941155254.10318343703478.10218369228174.10219202614250.10120200392866.10220810893807.99 21470349994.10121899930564.99 22416474134.10022700267513.10123404677272.1062342125148.105 23584418860.10123687287154.10123868465886.99 24521592556.10125071629079.10125071629079.10225071629079.1032521080681.102 25418808852.10325653217698.10625862343643.10625927005322.10126101064249.10126669182065.10526774769626.1012818573085.103 28897571974.10128987856538.10129181457478.10229197563648.11529417129419.10029786624606.87 29789957599.10629792256216.10130013766257.10630781785835.10130906104780.10231693696482.1013199430677.102 32087020145.10732365281766.10132923343611.10033416653251.1063342490946.102 33969101564.10634442460115.10334490278001.10534597926842.10234782976605.10435235452859.10635301401292.102353645442.101  36550167516.10536685953222.10137545354041.10137568097140.10138709023052.10140811138462.10241091132398.10241545411645.10242583353243.10342643832943.10342831019478.10243279913209.10243641966310.10543872227807.10643928696920.10644417097546.102449256530.94   45003960669.10445508725130.10245740938393.10146037991020.1014641771485.104 46787521756.10546901542423.10346924073390.10246949129329.10547747998098.10147936924685.10248046123689.10648162556019.10648211285674.1024861306889.101 48618085659.10051574738409.10151781592413.10451816630506.10251854515243.10052889152969.10153653468790.87 54068232029.10454077074143.10654226150513.10654256297073.1055464662474.102 55060265338.10156392233662.10356482153492.10656804907040.10257466002425.10257496662641.10657533215052.10157622410744.10157871968190.10258116526106.1025812810971.101 58862976443.10159308628179.94 59338331354.10259705885297.10560125984793.10162598956670.10162760451890.10263700058990.10163958622316.10264026414714.10164555500442.10264993435597.10766183421017.10266948228265.10167810302577.107678924119.101  68066155898.1016968827998.101 7342793742.101 7698681169.109 8369729419.101 8715731206.108 00000500:00?00H01?01H01M01R02I02R02W02m03G04704@04I04J05A05J05d06[07507l08108:08P08Y08g09009909>0:50:K0:P0:U0:Z0:_0;90;S0;X0;]0<70<n0=30=<0=A0=F0=O0=T0>10>60>;0>D0>I0>N0>S0>X0?O0?i0?n0@30@80@@0A70An0B30B80BR0B[0Bd0Bi0C`0Ci0Cn0DH0DI0DN0EE0EN0ES0Em0F60F?0G60G;0GD0GL0GU0Gb0Gk0H40HN0HO0HX0Ha0Hf0I]0Ib0JY0KP0KU0Ko0L80LR0LW0MN0MW0M`0Me0N\0Na0Nj0O30O80O=0OW0P10P90PS0PX0Q20Q70Q<0QJ0RA0RJ0RO0RT0R`0Ri0Rn0Se0T\0US0VJ0VO0VX0W20W70WQ0Wk0X00X10X:0Y10Yh0Ym0Z20Z7S3FHbS3FHbS3FHbS3FHb3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3FHbS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3BSFS3FHbS3LOS3LOC3FHb3ATR4SPABS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHb3ATR4SPAB5SPA323BSF3FHu3GHuS3FHb3BSFS3LOS3FHbFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3FHdS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPABS3LOS3FHbS3FHa3FHb2K01HS3FHb3GHaS3LOS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPABS3FHbS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3FHc3ATR4SPABS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHb3BSFS3FHbS3FHbS3FHb3BSFS3FHbS3F643FHa3FHc3GHc3ATR1H2H02H9S3FHbS3FHbS3LOS3FHbS3FHbS3FHbS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHbS3FHbS2GF3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3FHbS3FHb3GHdS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFFS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3BSFS3FHbS3LOS3LOC3FHb3FHc3ATR4SPABS3FHa3FHbS3FHb3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3FHbS2GF3FHbS3FHb3BSFS3FHa3FHb3FHdS3LOS3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFFS3LOS3FHbS3LOS3FHbS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3LOC3FHb3GHc3ATR4SPABS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3LOS3FHbS3FHb3BSFS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3LOS3FHbS3LOS3FHbS3FHbS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS2GF3FHbS3LOS3LOC3FHb3GHc3ATR4SPABS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3FHbS3FHa3FHb2K01HS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHb3BSFS3FHbS3FHbS3FHa3FHb2K0S3FHb3BSFS3FHbS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHb3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbS3LOS3LOC3FHb3ATR4SPAB3BSFS3LOS3LOC3FHb3ATR4SPAB3BSFS3FHbFS3FHb3BSFS4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S4SP163LOS3LOC2GF3FHa3FHb3ATR4SPAB5SPA323BSF3FHu3GHu2K0S3FHbS3FHbS3FHb".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
pose proof GH as GHu. unfold ablk, AIMG_HI, KLS in GHu.
pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] m) as MU1.
pose proof (wmono_refl bsegs m) as WM1.
zstep. zstep. zstep.
zstep.
zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
zstep. replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
zstep. zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SH : rw_cells bsegs mx (Z.shiftr FF 3 + 2147450880) _ |- _ =>
pose proof (rw_cells_store_ok bsegs mx _ _ 0%nat _ 1%nat SH ltac:(cells_cbv; reflexivity) ltac:(reflexivity)) as SOK end end.
zstep. clear SOK. zstep. zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bx (mem_inv bsegs mx)) in MIp end end.
lazymatch type of MU1 with ?T => change T with (bx T) in MU1 end.
lazymatch type of WM1 with ?T => change T with (bx T) in WM1 end.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
zstep.
zstep.
zstep. zstep. zstep.
do 13 zstep. zstep. zstep.
eapply stk_release in FRA; [| exact STL| lia]. cbn [cells_size csize Nat.add] in FRA. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in FRA.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (stk_merge bsegs mx lo (SPAz + 88) (SP + -104) FRA STG ltac:(lia)) as ST2 end.
release_frame FRB ST2 SP.
apply evtF_done. unfold bx in MU1, WM1, MIp.
eexists _, _. split; [reflexivity|].
split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM1|]. split; [exact MIp|].
split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM2|]. split; [eassumption|].
split; [exact ST2| exact FLC].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition RFFSH0 : list cell :=
[C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)].
#[using="rc SP"] Lemma c1z_unpoisoned : forall m A k, rw_cells bsegs m (Z.shiftr A 3 + 2147450880) [C1 (Z_to_bv 8 0)] -> A mod 8 = 0 ->
0 <= A -> 0 <= k <= 8 -> A + 8 <= 2^47 -> unpoisoned m A (A + k).
Proof.
intros m A k H A8 A0 K8 AH. Local Ltac2 Set LiaHints.tbl := fun () => "0060>24931798969.3629784465499.3945622866703.3951442758412.3654760678771.5357168406553.5400000400800<00F00M00]S2A0S2A0S2A0S2A02K82AHS2A02H1S2A82K82H12H22H3".
split; [lia|]. split; [lia|]. intros G H0 H1 H2.
assert (EG : G = A / 8) by (Z.div_mod_to_equations; lia). subst G.
exists (Z_to_bv 8 0). split.
- unfold ASHOFF. rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
apply (rw_C1_high m _ _ H). Z.div_mod_to_equations; lia.
- left. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc SP"] Lemma pad_tailA : forall (z : byte) k, (k <= 8)%nat -> firstn (8 - k) (skipn k (repeat z 8)) = repeat z (8 - k).
Proof. intros z k Hk. do 9 (destruct k as [|k]; [reflexivity|]). Local Ltac2 Set LiaHints.tbl := fun () => "0010=6273517741.31000004S2Hk".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SP16 SPT LOS LOC RSTK RI"] Lemma rd_small1 : forall (x10 x11 x12 x13 x14 x15 x5 x6 x7 x16 x17 x20 x28 x29 x30 x31 : word) m (FF FLG MSVP BUF NC TLP : Z)
(buf : list Z) (junk : list byte) (RLO1 RHI1 : Z) (k0 k8 k16 k32 k40 k48 k64 : list byte) (Q : machine_state -> Prop),
0 <= zlen buf < 8 -> Forall (fun c => 0 <= c < 256) buf ->
bytes_at bsegs m BUF (map (Z_to_bv 8) buf) ->
rw_cells bsegs m FF (RFFHDR FF FLG junk) -> rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH ->
rw_cells bsegs m SPAz [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)] ->
mem_inv bsegs m -> stk bsegs m lo SPAz ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
app_blk BUF (BUF + zlen buf) -> unpoisoned m BUF (BUF + zlen buf) ->
(RLO1 <= BUF /\ BUF + zlen buf <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
wr_at bsegs m (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO1) (shad RHI1 - shad RLO1) ->
ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> (BUF + zlen buf <= FF \/ FF + 64 <= BUF) -> ablk BUF (BUF + zlen buf) ->
rng RNG FF 64 -> rng RNG (shad FF) 8 -> rng RNG BUF (zlen buf) ->
(forall m' rs j16 (y5 y6 y7 y16 y17 y28 y29 y30 y31 : word),
munch [(SPAz - 2224, SPAz); (FF + 24, FF + 56); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m m' ->
wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' lo SPAz ->
rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d54); CB 8 rs;
CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - zlen buf)))); CB 16 j16; C8 (Z_to_bv 64 FLG)] ->
rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH0 ->
rw_cells bsegs m' SPAz [CB 8 k0; CB 8 k8; CB 8 k16; C8 (Z_to_bv 64 FF); CB 8 k32; CB 8 k40; CB 8 k48; C8 (Z_to_bv 64 MSVP); CB 16 k64; C8 (Z_to_bv 64 FF)] ->
bytes_at bsegs m' BUF (map (Z_to_bv 8) buf) ->
evtF bsegs RNG Q
(MS (mkR (Z_to_bv 64 0x81ee8) (Z_to_bv 64 SPAz) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
(Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 8) (Z_to_bv 64 0) y16 y17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 (FF + 32)) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) y28 y29 y30 y31)
F (Z_to_bv 64 0x81d54) fc None m' (seg_rom bsegs))) ->
evtF bsegs RNG Q
(MS (mkR (Z_to_bv 64 0x81dd4) (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
F (Z_to_bv 64 0x81eb0) fc None m (seg_rom bsegs)).
Proof.
intros until Q. intros Hhb FBY HBUF FFC SHF FRA MI ST GOT RIC SHB INI LAY REAL APPS UB HULL1 WR1 RSH1 FH FC F64 SEPB BBK RF RSF RB K.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). pose proof (ablk_lin _ _ BBK) as (BKa & BKb & BKc & BKd). unfold AIMG_HI in *.
pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu. pose proof atop_range as ATR. unfold KEND in SPT.
pose proof spa_propsA as (SPAB & SPA32 & _).
Local Ltac2 Set LiaHints.tbl := fun () => "01N0?10975380398.1171197920647.140 12080092226.13812131124654.11713042424365.1401343968393.118 13511899538.1171517678646.117 1517678646.119 15905069158.1471604143352.171 16212326239.11516214161251.11917216476300.14018412700771.14719075572372.11919201636503.12219202614250.11719632111445.14020512673496.12221728105754.11922311602227.12222851761109.17023584418860.11724519961094.1782917511839.115 29197563776.14429784643818.12029786644186.11529786706908.12129788756444.12229790837596.10229792256215.14730295706099.12231476977057.12232180884101.14732248767751.14032280608180.14132365281766.11732821070484.11934212215190.13834833594177.14037544479623.14038404006830.11740295071388.12240577642234.12241549633781.14741861025198.11742150890820.122422954363.147  42915233120.14744169666283.12244869238027.17145571381294.12245935527747.12246704937776.12247747998098.11748109907701.14748532250936.12248772945147.11550158764462.11750991518280.11951854515243.11652118466567.14053640511348.10253650963650.12053653026804.12154773823056.11955201240583.14056170466456.12257622410744.14158275795604.11958393220756.1196077494932.119 61171916934.16461756361310.14062175718784.11363188123053.14163439143815.14064026414714.1176486633172.138 66062017088.12266149329410.15766340543425.11967437603143.14067437603143.14168066155898.11768100572504.14768151712404.11968221440193.14068239093121.1228171545981.169 8929938862.117 9671089426.114 00000900W01=01F01l02102i02n03303403T03]03f03g03h04104[05;05a05n06706Y07:07?07g08008I08R08W08`08i08n0970:80:V0;80;V0<@0<E0<N0<W0=A0=_0=h0=i0>20>30><0>V0>W0>X0>e0?B0?O0@M0@o0Ag0Ah0BJ0BS0B\0CP0CU0D30D80DA0DJ0Dn0EL0EZ0F^0Fg0G00G90GZ0H@0Hd0If0JD0JM0Jo0Ka0L;0M30N=0Ng0O00O10O:0O;0OH0Oi0P20PRS3FHb3BSFS3LOS3LOC3HU53FHa3FHb3ATR4SPABS3LOS3LOC3Hhb3HU23HU53FHb3BKa3ATR4SPABS3FHb3BSFS3LOS3LOC3HU23HU53FHb3FHc3BKa3ATR4SPABS3FHbS4SP163LOS3LOC5HULL14SEPB3FHb3FHu3ATR4SPAB5SPA323BSF3BBuS3FHbS3FHbFS3LOS3LOC3FHu3ATR4SPAB3BBu2H42H5S3FHa3FHbS3FHa3FHbFFS3FHa3FHbS3LOS3LOC3Hhb3HU23HU53FHb3FHc3BKa3ATR4SPABS3LOS3LOC5HULL13FHb3ATR4SPAB3BSFS3LOS3LOC3Hhb3HU23HU53FHb3BKa3ATR4SPABS3Hhb3HU53FHbS3FHb3FHdS3LOS3LOC3HU23HU53FHb3BKa3ATR4SPABS3F644SEPB3FHu3BBu1H2H02H42H53H14S3FHbS3F644SEPB3FHu3BBu1H2H02H42H52H93H103H19S3Hhb3FHbS3F643BKc3FHu3ATR1H2H02H9S3HU53FHbS3FHbS3HU53FHbS3HU53FHbS3FHbS3HU53FHbS4SP163LOS3LOC3Hhb3HU23HU43HU53F643FHa3FHb3FHd3BKa3ATR4SPAB5SPA32S3SPT3LOS3LOC3HU53FHb3ATR4SPABS3LOS3LOC3HU23HU53FHb3BKa3ATR4SPABS3LOS3LOC3HU53FHa3FHb3ATR4SPABS3LOS3LOC3Hhb3HU23HU53FHb3FHc3BKa3ATR4SPABS3FHbS3FHa3FHbS3HU53FHbS3LOS3LOC3Hhb3HU23HU53FHb3FHc3BKa3ATR4SPABS3LOS3LOC3HU53FHa3FHb3ATR4SPABS3FHb3BSFFS3HU53FHbFS3FHb3BSFS3LOS3LOC3HU53FHb3ATR4SPABFFS3Hhb3HU53FHbS4SEPB3FHu3ATR3BBu1H2H02H42H5S3Hhb3HU53FHbS4SP163LOS3LOC3Hhb3HU23HU43HU54SEPB3FHb3FHu3ATR4SPAB5SPA323BBuS3LOS3LOC3HU23HU53FHb3BKc3ATR4SPABS4SP163LOS3LOC5HULL14SEPB3FHb3FHu3ATR4SPAB5SPA323BSF3BBuFS3LOS3LOC3HU23HU53FHb3BKa3ATR4SPABS3FHb3FHdS3FHb3BSFS4SP163LOS3LOC5HULL14SEPB3FHb3FHu3ATR4SPAB5SPA323BBuS3FHbS3LOS3LOC3HU53FHa3FHb3ATR4SPABS3FHbS3HU53FHbS3HU53FHbS3LOS3LOC5HULL13FHb3FHc3BKa3ATR4SPABS3LOS3LOC3HU53FHa3FHb3ATR4SPABS3HU53FHb4SPABS4SP163LOS3LOC3Hhb3HU23HU43HU54SEPB3FHb3FHu3ATR4SPAB5SPA323BSF3BBu1HS3FHa3FHbS3FHa3FHbS3FHa3FHbS3F644SEPB3FHu3BBu1H2H02H42H53H14S3LOS3LOC3Hhb3HU23HU53FHb3BKa3ATR4SPABS3LOS3LOC3Hhb5HULL13FHb3BKa3ATR4SPABS4SP163LOS3LOC3Hhb3HU23HU43HU54SEPB3FHb3FHu3ATR4SPAB5SPA323BBu3LBSS3LOS3LOC3HU53FHa3FHb3ATR4SPABS3FHb3BSFS3LOS3LOC3HU23HU53FHb3BKa3ATR4SPABS3LOS3LOC3HU13HU23HU33HU43HU53HU63FHb3BKa3ATR4SPABS3F644SEPB3FHu3BBu1H2H02H9S4SP163LOS3LOC5HULL14SEPB3FHb3FHu3ATR4SPAB5SPA323BSF3BBuS3LOS3LOC3Hhb3HU23HU53FHb3FHc3BKa3ATR4SPAB4SP163HU44SEPB3FHu5SPA323BSF3BBuS3LOS3LOC3Hhb3HU23HU53FHb3FHc3BKa3ATR4SPABS3FHb3BSFFS3FHa3FHbFS3Hhb3HU53FHbS3F644SEPB3FHu3BBu1H2H02H42H53H14S3FHb3BSFS3LOS3LOC5HULL13FHb3BKa3ATR4SPAB".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
unfold RFFHDR in FFC. unfold RFFSH in SHF.
pose proof (rw_cells_split_CB bsegs m FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d54)] 32 junk
[C8 (Z_to_bv 64 FLG)] [8%nat; 8%nat; 16%nat] FFC eq_refl) as FF2.
cbn [app mk_CB_cells] in FF2. clear FFC.
pose proof (munch_refl [(SPAz - 2224, SPAz); (FF + 24, FF + 56); (Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
pose proof BBK as BBu. unfold ablk, AIMG_HI, KLS in BBu.
assert (LBS : Z.of_nat (length (map (Z_to_bv 8) buf)) = zlen buf) by (rewrite length_map; reflexivity).
set (hb := zlen buf) in *. set (hbn := Z.to_nat hb).
zstep.
zstep.
zstep.
zstep. zstep. zstep.
zstep.
change [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 72550); C8 (Z_to_bv 64 531796); CB 8 (firstn 8 junk);
C8 (Z_to_bv 64 0); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]
with ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 72550); C8 (Z_to_bv 64 531796); CB 8 (firstn 8 junk)]
++ [C8 (Z_to_bv 64 0)] ++ [CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]) in FF2.
apply rd_rw_cells_appA in FF2. destruct FF2 as [FA FF2]. apply rd_rw_cells_appA in FF2. destruct FF2 as [FB FCc].
cbn [cells_size csize Nat.add] in FB, FCc. change (Z.of_nat 32) with 32 in FB, FCc. change (Z.of_nat 8) with 8 in FCc.
pose proof (rw_cells_merge bsegs _ (FF + 32) [] [C8 (Z_to_bv 64 0)] [] FB) as FM.
cbn [app cells_size cells_bytes csize cbytes Nat.add] in FM. clear FB.
change (le8 (Z_to_bv 64 0) ++ []) with (repeat (Z_to_bv 8 0) 8) in FM.
pose proof (rw_cells_split_CB bsegs _ (FF + 32) [] 8 (repeat (Z_to_bv 8 0) 8) [] [hbn; (8 - hbn)%nat] FM ltac:(cbn [sum_nat]; lia)) as FS.
cbn [app mk_CB_cells] in FS. clear FM.
change [CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8)); CB (8 - hbn) (firstn (8 - hbn) (skipn hbn (repeat (Z_to_bv 8 0) 8)))]
with ([CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8))] ++ [CB (8 - hbn) (firstn (8 - hbn) (skipn hbn (repeat (Z_to_bv 8 0) 8)))]) in FS.
apply rd_rw_cells_appA in FS. destruct FS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
replace (FF + 32 + Z.of_nat (hbn + 0)) with (FF + 32 + hb) in R2 by lia.
assert (UD : unpoisoned m1 (FF + 32) (FF + 32 + hb)).
{ change [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603);
C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]
with ([C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
C1 (Z_to_bv 8 18446744073709551601)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 18446744073709551603);
C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]) in SHF.
pose proof SHF as SH2. apply rd_rw_cells_appA in SH2. destruct SH2 as [_ SH2]. apply rd_rw_cells_appA in SH2. destruct SH2 as [SH4 _].
cbn [cells_size csize Nat.add] in SH4.
apply c1z_unpoisoned; [| Z.div_mod_to_equations; lia| lia| lia| lia].
replace (Z.shiftr (FF + 32) 3 + 2147450880) with (Z.shiftr FF 3 + 2147450880 + Z.of_nat 4); [exact SH4|].
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
destruct HULL1 as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
assert (WR2 : wr_at bsegs m1 (shad FF) (shad (FF + 64) - shad FF)).
{ destruct SHF as [_ W]. cbn [cells_size csize Nat.add] in W. replace (shad FF) with (Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
replace (shad (FF + 64) - (Z.shiftr FF 3 + 2147450880)) with (Z.of_nat 8); [exact W|].
unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
assert (RSF2 : rng RNG (shad FF) (shad (FF + 64) - shad FF)).
{ replace (shad FF) with (Z.shiftr FF 3 + 2147450880) by (unfold shad, ASHOFF; lia).
replace (shad (FF + 64) - (Z.shiftr FF 3 + 2147450880)) with 8; [exact RSF|].
unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
assert (UB1 : unpoisoned m1 BUF (BUF + hb)).
{ eapply unpoisoned_munch; [exact UB| exact MU|]. rewrite !shad_div. cbn [disjoint_from]. unfold ASHOFF.
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. refine (conj _ (conj _ (conj _ I))); Z.div_mod_to_equations; lia. }
clear UB.
eapply evtF_cut; [eapply amemcpy_specZ with (A := FF + 32) (S := BUF) (n := hb) (SPz := SPAz) (RLO1 := RLO1) (RHI1 := RHI1)
(RLO2 := FF) (RHI2 := FF + 64) | post_call bsegs m1 ];
try (lazymatch goal with |- rng _ _ _ => solve_rng end).
all: first [ lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- mem_inv _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- bytes_at _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => first [exact R1 | assumption]
| |- app_blk _ _ => first [exact APPS | apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]]
| |- unpoisoned _ _ _ => first [exact UD | exact UB1]
| |- wr_at _ _ _ _ => eassumption
| |- rng _ _ _ => first [exact RSF2 | eassumption | eapply rng_sub'; [exact RF| lia] | eapply rng_sub'; [exact RSTK| lia]]
| |- length _ = _ => rewrite length_map; lia
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
| |- _ => unfold KHIGH, KEND in *; lia
end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
rewrite (pad_tailA (Z_to_bv 8 0) hbn) in R2 by lia.
lazymatch goal with P : rw_cells bsegs ?mx (FF + 32) [CB (Z.to_nat hb) (map (Z_to_bv 8) buf)] |- _ => rename P into RB1; rename mx into m2 end.
assert (RB8 : rw_cells bsegs m2 (FF + 32) [CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb))))]).
{ replace (FF + 32 + hb) with (FF + 32 + Z.of_nat (cells_size [CB hbn (map (Z_to_bv 8) buf)])) in R2
by (cbn [cells_size csize Nat.add]; lia).
pose proof (proj2 (rd_rw_cells_appA bsegs m2 (FF + 32) [CB hbn (map (Z_to_bv 8) buf)]
[CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))]) (conj RB1 R2)) as RJ.
pose proof (rw_cells_merge bsegs m2 (FF + 32) [] [CB hbn (map (Z_to_bv 8) buf); CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] [] RJ) as RMg.
cbn [app cells_size cells_bytes csize cbytes Nat.add] in RMg. rewrite app_nil_r in RMg.
replace (hbn + (8 - hbn + 0))%nat with 8%nat in RMg by lia.
rewrite map_app, map_repeat. replace (Z.to_nat (8 - hb)) with (8 - hbn)%nat by lia. exact RMg. }
clear RB1 R2.
assert (FRM : rw_cells bsegs m2 FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d54); CB 8 (firstn 8 junk);
CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb)))); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]).
{ change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d54); CB 8 (firstn 8 junk);
CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb)))); CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]
with ([C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d54); CB 8 (firstn 8 junk)]
++ [CB 8 (map (Z_to_bv 8) (buf ++ repeat 0 (Z.to_nat (8 - hb))))] ++ [CB 16 (firstn 16 (skipn 8 (skipn 8 junk))); C8 (Z_to_bv 64 FLG)]).
apply rd_rw_cells_appA. split; [eassumption|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
apply rd_rw_cells_appA. split; [exact RB8|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8. eassumption. }
do 6 zstep.
zstep.
eapply K; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="lo LOS LOC"] Lemma rd_small2 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word) m (FF n hb : Z) (Q : machine_state -> Prop),
rw_cells bsegs m (Z.shiftr FF 3 + 2147450880) RFFSH0 -> mem_inv bsegs m ->
ablk FF (FF + 64) -> FF mod 64 = 0 -> rng RNG (shad FF) 8 ->
0 <= n <= hb -> hb < 8 ->
(forall m' (y10 y11 : word),
munch [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
rw_cells bsegs m' (Z.shiftr FF 3 + 2147450880) RFFSH ->
evtF bsegs RNG Q
(MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
y10 y11 (Z_to_bv 64 n) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 hb) x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x82548) fc None m' (seg_rom bsegs))) ->
evtF bsegs RNG Q
(MS (mkR x1 (Z_to_bv 64 SPAz) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPAz)
(Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 hb) x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0x81ee8) fc None m (seg_rom bsegs)).
Proof.
intros until Q. intros SHF MI FH F64 RSF Hn Hhb K.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu. pose proof atop_range as ATR. unfold KEND in SPT.
Local Ltac2 Set LiaHints.tbl := fun () => "00=0>11805467289.7923584418860.7929197563661.8929786411260.6832110716938.8132365281766.7951854515243.7853653386452.6859314873579.7361937685141.7861937685146.8164026414714.7968066155898.7900000500:00O00T00l01101601;01G01S01_01h021S3FHbS3FHbS3F643FHu3ATR1H2H02H4S3FHbS3LOS3LOC2Hn3Hhb3FHb3ATRS3FHbS3FHbS3FHbS2Hn3FHb1H1BS2Hn3Hhb3FHbS2Hn3Hhb3FHbS3FHb3BSFS3FHb3BSF".
replace (shad FF) with (Z.shiftr FF 3 + 2147450880) in RSF by (unfold shad, ASHOFF; lia).
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
unfold RFFSH0 in SHF.
pose proof (munch_refl [(Z.shiftr FF 3 + 2147450880 + 4, Z.shiftr FF 3 + 2147450880 + 5)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
zstep. zstep. zstep. zstep.
zstep. bcase B; [| exfalso; rewrite ?unsigned_lit in B by lia; destruct (Z.ltb_spec hb n); cbn in B; try lia; rewrite ?Z.land_0_r in B; lia].
zstep. replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
zstep.
zstep.
eapply K; try eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
