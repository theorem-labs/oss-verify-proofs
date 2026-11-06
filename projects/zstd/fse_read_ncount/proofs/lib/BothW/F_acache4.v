(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AModelFacts APrimFacts F_acache F_acache2 F_acache3.
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
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma calloc_hit_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
mem_inv bsegs m ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
rw_cells bsegs m 0x9eef8 [C8 (Z_to_bv 64 spacebeg)] ->
rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
rw_cells bsegs m (acache_stats t) [C8 stj] ->
iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
evtF bsegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3681c) fc None m (seg_rom bsegs)).
Proof.
intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ M8 HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
unfold AIMG_HI, AINSTANCE in *.
Local Ltac2 Set LiaHints.tbl := fun () => "03=0?10082350123.86 11531127361.89 11531127361.96 11775166127.87 12506424771.88 12506424771.95 12525554635.88 12525554635.95 14734152553.85 14734152553.92 16008861546.86 16008861546.89 16008861546.96 16015403875.82 16654661901.10516654661901.98 17776320431.10217776320431.85 17776320431.95 1800609155.103 1800609155.86  1800609155.96  18867207222.88 18867207222.95 19030965577.79 19515728436.88 19515728436.95 20262998748.85 20262998748.92 20335463178.85 20335463178.92 20854954799.86 20979536691.86 21651633935.88 21651633935.95 22391638788.84 22954551237.10622954551237.99 23678444659.66 24570100999.10424570100999.97 24638473347.10424638473347.87 24638473347.97 26492550416.10626492550416.84 26492550416.86 26492550416.87 26492550416.89 26492550416.96 26492550416.99 27904923141.88 27904923141.95 28419357060.86 29003366760.88 29003366760.95 29788955507.10629788955507.99 30757180118.87 30863979691.84 31378308326.77 32075992937.84 32075992937.91 32098070984.10332098070984.96 32356862517.10632356862517.99 33677903874.87 34428055044.87 34832712819.82 35214167685.10135214167685.94 35241715170.93 36115622446.10336115622446.86 36115622446.96 37683496382.89 37683496382.96 38446806799.10238446806799.86 38446806799.95 38510784165.89 38510784165.96 40455642244.86 40818989526.86 40818989526.93 41352055893.87 41352055893.94 42240553391.87 42553017460.88 42651412631.79 42828922350.86 42828922350.89 42828922350.96 42858215713.86 43059266230.75 43063227478.86 43987951406.10343987951406.86 43987951406.96 43988483203.10243988483203.84 43988483203.95 44021460374.86 44021460374.88 44021460374.93 44021460374.95 45219141890.87 45848756903.84 46466564356.87 48185458843.86 48320830113.87 48722578991.86 49073433023.10649073433023.99 49242818135.88 49242818135.95 49649769127.87 50669429877.88 50669429877.95 51356649574.88 51356649574.95 51418988165.86 51711223320.87 51711223320.94 52094863241.10552094863241.98 52105090727.86 52624921519.84 52793185963.87 53767577775.10253767577775.85 53767577775.95 54243526019.10354243526019.86 54243526019.96 54267463126.87 55336861633.10255336861633.95 55338958790.10255338958790.95 55345848131.82 55345848131.89 55345848258.83 55345848258.90 565324930.86   56983243656.86 57008552236.87 57008552236.94 57700073633.84 57743577986.86 59171504470.86 59314873579.80 59314873579.81 59314873579.83 59314873579.84 59314873579.88 59314873579.90 59314873579.91 59314873579.95 60858483367.87 61408636886.84 61523295858.89 61523295858.96 61917199020.10161917199020.94 61917199023.85 6280285958.104 6280285958.105 6280285958.97  6280285958.98  63164784673.86 63235321900.10163235321900.83 63235321900.94 63305555623.86 63314293035.86 64371235530.10664371235530.99 64997134979.10464997134979.87 64997134979.97 65093347183.10565093347183.10665093347183.98 65093347183.99 65098632094.88 65106454549.80 65106454676.81 65108530606.79 65658293242.79 66149329537.11666149329537.12366165977419.10666165977419.99 67033309574.88 67033309574.95 67388853175.86 6946516564.106 6946516564.99  8581623554.84  9272504225.87  9581476779.87  9869190602.88  9869190602.95  00000<00G00R00e00n01701@01I01J01K01T01d02402802A02J02N02V02Z02[02`02a02b02c02g02h02i02j02k02l02m03@03E03N03W03[03\03]03a03f03k03l04104204304404504604704804904=04A04E04J04O04S04W04`04l05105505905H05W05[05_05d05h05o06006106506906A06E06I06M06N06S06T06`06l07007107207;07D07W07X07\07a07e07i08808@08I08M08U08Y08Z08_08`08a08b08c08d08i08n09209E09T09g0:60:E0:F0:G0:L0:M0:N0;60;^0;m0;n0;o0<30<70<<0<O0<[0<_0<g0<k0<l0=10=20=;0=?0=C0=G0=K0=O0=S0=W0=[0=`0=d0=m0>60>E0>J0>S0>^0>i0?40??0?K0?V0?a0?m0@20@;0@?0@C0@G0@K0@S0@W0@[0@_0@c0A20A60A>0AB0AG0AS0AW0A[0A\0Aa0Ab0Ac0Ad0Ae0Af0An0B20B60B:0B>0B_0C@0CE0CJ0CO0CT0C`0D60DL0DQ0D`0Dl0Dm0DnS4CEIL2LO2T1S2HR3LCH2RBS2HR3LCH2RBS4CEIL2LO3LCH2T12C1S3LCH3CNTS3LCH3CNTS3LCH3CNTS3LCH3CNTFFS4CEIL2LOS2SZ3LCH3TAL3CS3S2SZ3LCH3TAL3CS3S2K2S3LCH3CNTS3LCH3CNTS2LOS2LO3LCHS2LOSS3LCHSSSS2SZSSFFFFS4CEIL2LO3LCH2T12C1S3LCHS3LCH3IXSS3LCH3IXSS2HBSSS2SZS3LCHS3LCHSS3LCHSSSSSSSSS2LOS2LOS2HBS3LCHS3LCHS2HBS2HBS4CEIL2LOS4CEIL2LO2T1S3LCHS2C1S2C1S2HR3LCH3CNT2RBS2HR3LCH3CNT2RBS2RBS2RBS3SPRS2HBS2SZ2K2FFS2SZS2LOS2LO3LCHS2LOS2RBS2RBSS3LCHSS4CEIL2LO2T1S4CEIL2LO2T1S2HBSSS3LCH3CNTS3LCH3CNTS4CEIL2LO3LCH2T12C1FS2SZS3SPRS2HBS2HBS4CEIL2LO2T12C1S2LO3LCHS4CEIL2LOS2LOS2LO3LCHS2LOSS3LCHSSSSSS3SPRS3LCHS2HBS4CEIL2LO3LCH2T12C1S4CEIL2LO2T12C1S4CEIL2LO3LCH2T12C1S4CEIL2LO2T12RBS4CEIL2LO2T12RBSSS3LCHSSS2SZ3LCH3CNT2T02T13TAL2C13CS32K22K32K51HS2SZ3LCH3CNT2T02T13TAL2C13CS32K22K32K51HS4CEIL2LO2T12C1SSS2RBS2RBS3LCHS4CEIL2LO3LCH2T12C1S4CEIL2LO2T1S2LOS2LO3LCHS2LOSS3LCHSS4CEIL2LOS2C1S2C1S2C1S2C1S2C1S2C1S2C1S2C1S3SPRS2HBS3LCH3CNTS3LCH3CNTS4CEIL2LO2T12C1S3SPRS4CEIL2LOS2SZ3LCH2K0S2SZ3LCH2K1S3LCH2C12K3S3LCH2C12K4S3LCH3CNT2K5S3LCH2C12K3S3LCH2C12K4S3LCH3CNT2K5S3LCHS4CEIL2LOS2HBS2HBS2LOS2LOS2LO3LCHS2RBS2RBS2RBS2RBS4CEIL2LO2T12C1S2LOS2LO3LCHS2LOS3LCHS4CEIL2LO2T1S2HBS2HBSS3LCHSSSSSS2SZ3LCHS2SZS2SZS2SZS2SZS3LCH3CNT3TAL2C12K22K32K51H2H02H9S3LCH3CNT3TAL2C12K22K32K51H2H02H9S3LCHS3LCHS3LCHS3LCHS4CEIL2LO2T1S2SZ2HR3LCH3TAL3CS32RBS2SZ2HR3LCH3TAL3CS32RBS3SPRS4CEIL2LO2T12C1S4CEIL2LO2T1SS".
pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
word_range sp SPR. word_range idxw IXR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 48%nat ST.
do 7 step.
do 3 zstep.
replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
step. if_cases K0; zify_cond K0; [| exfalso; lia].
do 2 step. step. if_lit.
step. step. if_lit.
step. if_cases K1; zify_cond K1. { exfalso. lia. }
step. step. if_cases K2; zify_cond K2.
1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
all: step.
all: if_cases K3; zify_cond K3; [exfalso; lia|].
all: step.
all: step.
all: if_cases K4; zify_cond K4; [exfalso; lia|].
all: step.
all: zstep.
all: zstep.
all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
all: remember (t + 208 + c * 80) as R eqn:HR.
all: lstep.
all: step.
all: if_cases K5; zify_cond K5; [exfalso; lia|].
all: do 3 zstep.
all: step.
all: zstep.
all: step.
all: zstep.
all: zstep.
all: replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
all: pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
all: step.
all: clear RD.
all: rewrite (zx32_small idxw) by lia.
all: assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
all: amo_stepA AMO.
all: step.
all: do 4 zstep.
all: step.
all: step.
all: if_lit.
all: do 8 step.
all: release_frame FR ST (bv_unsigned sp).
all: subst R.
all: setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
all: finish.
all: eexists.
all: exact STS.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma calloc_pre_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
mem_inv bsegs m ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
iclr t 4096 -> t + 4096 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
evtF bsegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3681c) fc None m (seg_rom bsegs)).
Proof.
intros until csz. intros ST CEIL LO MI -> -> -> -> SZ M8 HC CR T0 T1 RIMG RSTK RT. band_lin.
unfold AIMG_HI, AINSTANCE in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0190>11805467289.6911805467289.7111805467289.7216015403875.6717776320431.701800609155.71 19030965577.6420979536691.7122389541692.6923678444659.5224638473347.7228417259964.7131378308326.6232075992937.6932075992937.7633680001082.7234430152252.7234832712819.6735241715170.7836115622446.7138446806799.7140457739452.7142553017460.7342651412631.6442831019478.7142860312857.7143059266230.6043987951406.7143988483203.6945221239098.7245848756903.6946468661564.7248318732953.7249649769127.7251421085373.7152105090727.7153767577775.7054243526019.7155338958790.8055338958790.8755345848131.6755345848131.7455345848258.6855345848258.75563227834.71  56981146544.7157697976473.6957745675194.7159314873579.6559314873579.6659314873579.6859314873579.6959314873579.7559314873579.7660858483367.7261482382924.7261482382924.7961917199023.706280285958.82 6280285958.89 63162687513.7163235321900.6863305555623.7164997134979.7265093347183.8365093347183.9065098632094.7365106454549.6565106454676.6665108530606.6465658293242.648583720762.69 9270407065.72 00000100200300700;00<00@00A00E00I00J00N00O00S00W00\00`00g00k00o01001401501901>01M01Q01U01V01[01\01`01o02002?02@02D02E02I02M02Q02U02Y02]02b02f03503:03A03H03O03V03]03d03e03f03g03k03o04304B04F04G04H04I04J04N04R04V04Z04^04c052SSSS2K2S2LOSS2SZSS2HBS2SZSS2HBSS2C1S2C1S3SPRS2HBS2SZ2K2S2SZS2LOSS2HBFS2SZS3SPRS4CEIL2LO2T12C1S2LOS2LOSS3SPRSS2HBS4CEIL2LO2T12C1SS4CEIL2LO2T12C1SS2LOSS2C1S2C1S2C1S2C1S2C1S2C1S3SPRS2HBS4CEIL2LO2T12C1S3SPRS2SZ2K0S2SZ2K1S2C12K3S2C12K4S2C12K3S2C12K4SSSS2LOS2RBS2RBS4CEIL2LO2T12C1S2LOSSSSS2SZS2SZS2SZS2SZS2SZS3SPRS4CEIL2LO2T12C1".
pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 48%nat ST.
do 7 step.
do 3 zstep.
replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
step. if_cases K0; zify_cond K0; [| exfalso; lia].
do 2 step. step. if_lit.
step. step. if_lit.
step. if_cases K1; zify_cond K1. { exfalso. lia. }
step. step. if_cases K2; zify_cond K2.
1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
all: step.
all: if_cases K3; zify_cond K3; [exfalso; lia|].
all: step.
all: step.
all: if_cases K4; zify_cond K4; [exfalso; lia|].
all: step.
all: zstep.
all: zstep.
all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
all: remember (t + 208 + c * 80) as R eqn:HR.
all: lstep.
all: step.
all: if_cases K5; zify_cond K5; [| exfalso; apply K5; reflexivity].
all: do 7 step.
all: step.
all: subst R.
all: finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma calloc_popj_gen : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(rav s0v s1v s2v s3v s4v rv : word)
(F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
stk bsegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
mem_inv bsegs m ->
bv_unsigned rv <> 0 ->
1 <= c <= 30 ->
rw_cells bsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
rw_cells bsegs m 0x9eef8 [C8 (Z_to_bv 64 spacebeg)] ->
rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
rw_cells bsegs m (acache_stats t) [C8 stj] ->
iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
evtF bsegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
(MS (mkR (Z_to_bv 64 0x36acc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
(Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
rv a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36acc) fc None m (seg_rom bsegs)).
Proof.
intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
unfold AIMG_HI, AINSTANCE in *.
word_range sp SPR. word_range idxw IXR. word_range rv RVR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "00i0>11531127361.8012506424771.7912525554635.7914734152553.7616008861546.8016654661901.8817776320431.861800609155.87 18867207222.7919515728436.7920262998748.7620335463178.7621651633935.7922954551237.9024570100999.8824638473347.8826492550416.8026492550416.9027904923141.7929003366760.7929788955507.9032075992937.7432098070984.8732356862517.9035214167685.8536115622446.8737683496382.8038446806799.8638510784165.8040818989526.7742828922350.8043987951406.8743988483203.8644021460374.7744021460374.7949073433023.9049242818135.7950669429877.7951356649574.7951711223320.7852096960386.9053767577775.8654243526019.8755336861633.8657008552236.7861523295858.8061917199020.856282383117.89 63235321900.8564371235530.9064997134979.8865093347183.9066151427713.9366165977419.9067033309574.796946516564.90 9869190602.79 00000;00D00M00N00W00`00d00e00f00g00h00i01201301801901:01;01?01D01H01L01[01_01`01d01h01i02502602:02>02?02@02A02P02Q02R02m02n03203603703;03D03H03L03P03T03X03Y03Z04504:04?04N04OS2HR3LCH2RBS3LCH3CNTS3LCH3CNTFS3LCH3TALS3LCH3CNTS2LOSSSFFS3LCH3IXSSS3LCHSSSS2LOS3LCHS2HBS2C1S2HR3LCH3CNT2RBS2RBFS2LOS2RBSS4CEIL2LO2T1SS2HBS2LOSSSS4CEIL2LO2T12RBSSS2RV3LCH2T02T13TAL3RVR2K01HSS2RBS2LOSS2C1S3LCH3CNTS2HBS2LOS2RBS2LOS2HBSSS2RV3LCH3TAL3RVR2K01H2H02H4S3LCHS3LCHS2HR3LCH3TAL2RBS".
assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
remember (t + 208 + c * 80) as R eqn:HR.
step. if_cases K0; zify_cond K0. { exfalso. apply RV. exact K0. }
lstep.
do 3 step.
step.
do 3 zstep.
step.
zstep. step. zstep. zstep.
replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
step. clear RD. rewrite (zx32_small idxw) by lia.
assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
amo_stepA AMO.
step.
do 4 zstep.
step. step. if_lit.
do 8 step.
release_frame FR ST (bv_unsigned sp). subst R.
setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
finish. eexists. exact STS.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
