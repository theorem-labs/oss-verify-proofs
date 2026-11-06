(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit F_acache.
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
Definition calloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t c lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x36be0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
(Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
(Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache_rec t c)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x37080) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp - 48)
/\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
#[using="Type"] Lemma calloc_pre_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
mem_inv asegs m ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
iclr t 4096 -> t + 4096 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36930) fc None m (seg_rom asegs)).
Proof.
intros until csz. intros ST CEIL LO MI -> -> -> -> SZ HC CR T0 T1 RIMG RSTK RT. band_lin.
unfold AIMG_HI, AINSTANCE in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0100>11805467289.6311805467289.6511805467289.6617776320431.641800609155.65 19030965577.5820979536691.6522389541692.6324638473347.6624963260777.6328417259964.6529311285958.5131378308326.5633680001082.6634430152252.6635241715170.7236115622446.6538446806799.6540457739452.6542553017460.6742651412631.5842831019478.6542860312857.6543059266230.5443987951406.6543988483203.6345221239098.6645848756903.6346468661564.6648318732953.6649649769127.6650287149751.5851421085373.6552105090727.6553767577775.6454243526019.6555338958790.7455345848131.6155345848258.62563227834.65  56981146544.6557697976473.6357745675194.6559314873579.5959314873579.6059314873579.6159314873579.6259314873579.6360858483367.6661482382924.6661917199023.646280285958.76 63162687513.6563235321900.6263305555623.6564997134979.6665093347183.7765098632094.6765106454549.5965106454676.6065108530606.5865658293242.588583720762.63 9270407065.66 00000100200300700800<00=00A00B00F00J00K00L00Q00U00Y00]00^00b00c00g00l01;01?01C01D01I01J01N01]01^01g02602702;02<02@02D02H02M02Q02`02e02l03303:03A03H03I03J03N03R03a03e03f03g03h03l04004404804<04A04PSSSS2LOSS2SZSS2HBSS2C1S2HBSSS3SPRS2HBS2SZS2LOSS2HBFS2SZS3SPRS4CEIL2LO2T12C1S2LOS2LOSS3SPRSS2HBS4CEIL2LO2T12C1SS2SZ1H2H0S4CEIL2LO2T12C1SS2LOSS2C1S2C1S2C1S3SPRS2HBS4CEIL2LO2T12C1S3SPRS2SZ2K0S2SZ2K1S2SZ2K2S2C12K3S2C12K4SSS2LOS2RBS4CEIL2LO2T12C1S2LOSSSS2SZS2SZS2SZS2SZS2SZS3SPRS4CEIL2LO2T12C1".
assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
do 7 step.
do 3 zstep.
replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
step. if_cases K0; zify_cond K0; [| exfalso; lia].
do 2 step. step. if_lit.
step. step. if_lit.
step. if_cases K1; zify_cond K1. { exfalso. lia. }
step. step. if_cases K2; zify_cond K2. { exfalso. lia. }
do 2 zstep. rewrite HC.
step.
step. if_cases K3; zify_cond K3. { exfalso. lia. }
step. step. if_cases K4; zify_cond K4. { exfalso. lia. }
step. zstep. zstep.
assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
remember (t + 208 + c * 80) as R eqn:HR.
lstep.
step. if_cases K5; zify_cond K5. 2: { exfalso. apply K5. reflexivity. }
do 7 step.
step.
subst R. finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma calloc_popj_spec : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(rav s0v s1v s2v s3v s4v rv : word)
(F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
stk asegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
mem_inv asegs m ->
bv_unsigned rv <> 0 ->
1 <= c <= 16 ->
rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
rw_cells asegs m 0x9ee38 [C8 (Z_to_bv 64 spacebeg)] ->
rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
rw_cells asegs m (acache_stats t) [C8 stj] ->
iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
(MS (mkR (Z_to_bv 64 0x36be0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
(Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
rv a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36be0) fc None m (seg_rom asegs)).
Proof.
intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
unfold AIMG_HI, AINSTANCE in *.
word_range sp SPR. word_range idxw IXR. word_range rv RVR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "00i0>11531127361.8012506424771.7912525554635.7914734152553.7616654661901.8817776320431.861800609155.87 18867207222.7919515728436.7920262998748.7620335463178.7621651633935.7922954551237.9024570100999.8824638473347.8824963260777.7426492550416.8026492550416.9027904923141.7929003366760.7929788955507.9032098070984.8732356862517.9035214167685.8536115622446.8737683496382.8038446806799.8638510784165.8040818989526.7742828922350.8043987951406.8743988483203.8644021460374.7744021460374.7944318756436.9047932942186.8049073433023.9049242818135.7950669429877.7951356649574.7951711223320.7852096960386.9053767577775.8654243526019.8755336861633.8657008552236.7861523295858.8061917199020.856282383117.89 63235321900.8564371235530.9064997134979.8865093347183.9066151427713.9366165977419.9067033309574.799869190602.79 00000;00D00M00N00W00[00\00]00^00_00`00i00j00o01001401501601:01?01C01R01V01W01[01_01`01l01m02102502602702802J02S02b02c02d03?03@03D03H03I03M03V03Z03^03b03f03j03k03l04G04L04Q04RS2HR3LCH2RBS3LCH3CNTS3LCH3CNTFS3LCH3CNTS2LOSSSFFS3LCH3IXSSS3LCHSS2C1SSS2LOS3LCHS2HBS2HR3LCH3CNT2RBS2RBFS2LOS2RBSS4CEIL2LO2T1SS2HBS2LOSSSS2C12HR3LCH3TAL2RBS3LCH3TALS4CEIL2LO2T12RBSSS2RV3LCH2T02T13TAL3RVR2K01HSS2RBS2LOSS2C1S3LCH3CNTS2HBS2LOS2RBS2LOS2HBSSS2RV3LCH3TAL3RVR2K01H2H02H4S3LCHS3LCHS".
assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
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
pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
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
