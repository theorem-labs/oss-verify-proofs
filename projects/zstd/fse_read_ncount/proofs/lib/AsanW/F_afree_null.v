(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ABytes AQConst ADepot_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AKitQ F_aalloc_s F_aalloc1 F_aalloc3 F_aunwind F_aunwind2 F_afree_s F_aintal F_afree_iseg F_afree_front F_afree_icpt.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rw_cells_of_u64arr' : forall m A ws,
u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof. exact rw_cells_of_u64arr. Qed.
#[using="Type"] Lemma dealloc_null_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv asegs m ->
a0 = Z_to_bv 64 0 ->
rng RNG lo (bv_unsigned sp - lo) ->
evtF asegs RNG (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32160) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> RSTK. atop_facts.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
do 9 step.
step.
Local Ltac2 Set LiaHints.tbl := fun () => "00b0>11805467289.5311805467289.5411805467289.5511805467289.5611912744615.5512367362435.5513021749692.551527479463.53 17646078182.4717776320428.5419049469500.5621918414723.5524630998586.5325314760359.5625878270255.5527923971379.5429545175216.5431081687356.5632651489978.5533039531175.5633680001082.5636115622447.5536425882626.4836993589379.5637107179452.553945979267.55 41809558659.5341809558659.5442831019478.5443060403331.5643061431595.4543987951407.5545221239098.5649345641752.4751425718543.5451481786499.5651678667181.5353767577772.5456228262055.55563227834.55  57745675194.5560025031335.5661917199020.5463235321901.5263235321901.5363694018620.5667800801447.557010956092.53 8583720762.56 985337532.55  00000100200300400500600:00;00<00@00D00E00J00K00O00P00T00X00]00^00c00g00k00l01001101201301801901=01A01F01G01H01I01M01Q01R01W01\01]01a01e01i01m01n02202702;SSSSSSS2HBSSS2LOS2HBSS3SPRSS2LOSS2HBS2HBS3SPRSS3SPRS2LOS2LOSS2HBSSSS3SPRSS2LOS2LOS3SPRSSSS2LOS2LOSS3SPRS3SPRSS2LOS2LOS2LOS2HBSS2HBS3SPRS2HB".
carve_frame 64%nat ST.
do 9 step.
step. if_lit.
do 8 step.
zstep. step.
release_frame FR ST (bv_unsigned sp).
finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition free_null_post (sp : word) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4); (t + 3168, t + 3169)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
/\ rw_cells asegs m' 0x131f08 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk asegs m' 0xa3680 (0xa3680 + 0x81030)
/\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
#[using="Type"] Lemma free_null_spec : forall (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem)
(t ctx lo top bot : Z) (trt : list Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 0 ->
bv_unsigned sp mod 16 = 0 ->
allocA_cells m ctx t ->
rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)] ->
rw_cells asegs m 0xa317c [C4 (Z_to_bv 64 30)] ->
rw_cells asegs m 0x133fca [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m 0x99760 [C8 (Z_to_bv 64 0x131f20)] -> rw_cells asegs m 0x131f20 [C8 (Z_to_bv 64 4096)] ->
rw_cells asegs m 0x131f08 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk asegs m 0xa3680 (0xa3680 + 0x81030) ->
(ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))) ->
rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
afree_unw RNG lo m top sp s0 ra trt ->
bv_unsigned s0 <> bv_unsigned sp + 8 ->
0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
evtF asegs RNG (free_null_post sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
intros until trt.
intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC FL IAS IAM CT8 TT0 SW UW CX0 C0 C1 T0 T1 CT2
UNW S0NE B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT. band_lin.
pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
Local Ltac2 Set LiaHints.tbl := fun () => "01B0?10798321633.17111263527009.17111767339402.13111807744665.17112217537535.12213748778845.15213993462363.12614966552394.96 15819558015.1211744903108.119 17986879152.17118203597971.15419043498592.11919590291912.1202250029779.154 22700267513.17422700267513.17525625845715.15426359334394.15326496924968.11927176698494.12327393365820.12328575982988.12628575982988.17429147777627.12630229009457.1233086677402.96  33688774939.12333824905934.12035844084819.15436166301066.13136166301066.13437245297491.15437592147547.12637592147547.15237592147547.17138242491404.15438377103120.13138377103120.13440585126993.12341024469503.15442877022815.13142877022815.13443229261695.12643886324944.15445208558218.17146173415533.12346173415533.13447117593297.12348486878908.12349921929014.12949921929014.15450486567840.11951085951050.17151234294911.15152041488522.13152041488522.13452450093533.15452569147371.15452569147371.15553618232787.15456759370246.12657818248480.11958422691744.11959310676309.14259310676315.14559972613898.15360356887589.15460657043208.12360864384416.11961789444896.11964949347711.12065285823486.12365285823486.1346562149469.2   6566541509.134 66260016006.15866260016006.1758800126135.155 8800126135.158 8800126135.174 9255215264.119 00000;00F00M00Y00Z00[00\00`00a01;01A01b01m01n02O02a03203S03T04404=04>04O04a04b04c04d04h04i05J05R05Z06;06<06=06>06?06D06I06X06d06e06f06g06h06i07807O07P07Q07a08108<08@08A08B08C08D08P09509V09k0:60:A0:c0;E0;F0;J0;O0;Z0;e0;f0;k0<00<50<:0<A0<H0<Z0=@0=R0=]S4CEIL2LO1HS4CEIL2LO1HS5TOPLES4CEIL2LO2T1SSSS2LOSS4CEIL2LO2T02T14LTRT3SPR1HS4CEILS4CEIL2LO4SP162T04LTRT3LTB4LTB21HS4CEIL2LO1HSS4CEIL2LO4SP162T04LTRT3LTB4LTB21HS4LTRT3LTB4LTB22HqS4CEIL2LO2Hj2Hi1HS4CEIL2LO4SP162T04LTRT3LTB4LTB21HSS4CEIL2LO2C02C12T02T14LTRT3SPR1HS3RA43RARFS4CEIL2LO2GE2Ha1HS4LTRT3LTB4LTB22HqSSSS2BBSS4CEIL2LO4SP162T04LTRT3LTB4LTB21HS2LO3HspS2LO3HspS4CEIL2LO4SP162T04LTRT3LTB4LTB21HSSSSS3HspS3HspS4RANE4LTRT3SPRS4CEIL2LO2T1SSSSSS4SP164LTRT3SPRS4SP163LTR4LTRT3SPR3LTBFFS4CEIL2LO4SP471HS4CEIL2LO4SP471HS4CEIL2LO1HS2LOSSSSS4CEIL2LO2T1S4CEIL2LO2C12T14LTRT3SPR3LTB4LTB21Y1HS4CEIL2LO4SP162T04LTRT3LTB4LTB21HS4CEIL2LO3TOP2GE2Ha1HS4CEIL2LO1HS4CEIL2LO1HS4SP164S0NE4LTRT2LT1H2H12H22H63H11S4SP164S0NE4LTRT2LT1H2H12H22H83H13SS2LOS3S0RS4CEIL2LO1HS4CEIL2LO1HSS3BTXS3BTXS3TOPS3TOPS2Hj2HiS2Hj2HiS4LTRT3LTB4LTB22HqS4CEIL2LO2T04LTRT3SPR3LTB4LTB22Hj2Hi1HS4LTRT3LTB4LTB22HqS4CEIL2LO1H".
pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
word_range sp SPR. word_range s0 S0R. word_range ra RAR.
box CT2.
pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.
eapply evtF_cut.
{ eapply (ficptA_spec 0 ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
all: try lazymatch goal with
| |- rw_cells _ _ AIA_FLAG _ => exact FL
| |- stk _ _ AIA_BASE _ => exact IAS
| |- _ = true -> _ => exact IAM
| |- rng _ _ _ => solve_rng
end.
all: match goal with |- ?G => idtac "REMA" G end. }
cbv beta. intros ms1 PA. unfold ficptA_post in PA.
destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRA & FRt & FRs & FL1 & IAS1 & IAM1).
pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 341008 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
uchain m1 top 341008 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
{ intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 341008 then [] else [bv_unsigned ra]) ++ tr)
by (replace (bv_unsigned ra =? 341008) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
eapply (uc_step m1 top 341008 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
- rewrite Z_to_bv_bv_unsigned. exact BS0.
- rewrite Z_to_bv_bv_unsigned. exact BRA.
- replace (bv_unsigned ra =? 341008) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
+ eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
+ inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
clear BS0 BRA.
xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.
step.
name_sp sp (-2128).
eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 341008 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
{ destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
- eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 341008 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; exact STa
| |- mem_inv _ _ => exact MIa
| |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
| |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
| |- u64arr _ _ _ _ => exact TB
| |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
| |- _ \/ _ => unboxed CT2
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
| |- rw_cells _ _ (_ + 40) _ => exact SW
| |- rw_cells _ _ (_ + 3168) _ => exact UW
end.
all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
all: match goal with |- ?G => idtac "REMU" G end.
- eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 341008 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; exact STa
| |- mem_inv _ _ => exact MIa
| |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
| |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
| |- u64arr _ _ _ _ => exact TB
| |- _ \/ _ => unboxed CT2
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
| |- rw_cells _ _ (_ + 40) _ => exact SW
| |- rw_cells _ _ (_ + 3168) _ => exact UW
end.
all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
all: match goal with |- ?G => idtac "REMU0" G end. }
cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
destruct PU as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & tb2
& -> & MUu & WMu & MIu & STu & SZ2 & TB2 & LTB2 & TRF2 & BP2 & UW2).
unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
replace (ret_pc (Z_to_bv 64 341100)) with (Z_to_bv 64 341100) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
{ eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; lia). xport CT8 MU12 WMu ltac:(ub CT2; lia). xport TT0 MU12 WMu ltac:(lia).
xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
{ intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
clear IAM1.
rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
zstep. zstep. step. step.
step.
name_sp sp (-2128).
eapply evtF_cut.
{ eapply (dealloc_null_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 lo);
[rewrite Hsp; exact STu | exact CEIL | rewrite Hsp; lia | exact MIu | reflexivity | rewrite Hsp; eapply rng_sub; [exact RSTK| lia| lia]]. }
cbv beta. intros ms3 PD.
destruct PD as (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & -> & MUd & WMd & MId & STd).
unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.
replace (ret_pc (Z_to_bv 64 341120)) with (Z_to_bv 64 341120) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
xport UW2 MUd WMd ltac:(lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at asegs m3 (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
{ intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
clear IAM2.
apply rw_cells_of_u64arr' in TB2. rewrite LTB2 in TB2.
eapply evtF_mono.
{ (eapply (ficptD_spec RNG sp gp tp); [exact STd | atop_facts; lia | lia | exact MId
| eexists; split; [exact SS | reflexivity]
| eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB2 | reflexivity]
| exact FRS | exact RIMG | solve_rng ]). }
cbv beta. intros ms4 [-> ST4].
assert (MU : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4); (t + 3168, t + 3169)]%Z m m3).
{ eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
eapply munch_weaken; [| exact MUa].
all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
assert (WM : wmono asegs m m3).
{ eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu| exact WMd]. }
unfold free_null_post. do 15 eexists. exists m3.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact ST4|].
split; [exact UW2|]. split; [exact FL1|]. split; [exact IAS1|]. exact IAM3.
Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
