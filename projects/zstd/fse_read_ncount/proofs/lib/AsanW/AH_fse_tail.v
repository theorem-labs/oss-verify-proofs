(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_iface AH_fse_kit AH_fse_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
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
Lemma upd_app_midA : forall {X} (l1 : list X) (x v : X) (l2 : list X), upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. induction l1 as [|a l1 IH]; intros x v l2; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Section CANSEC1. Context {rc : runConstT}.
Section Tail.
Hypothesis U32R : prod_u32r_stmtA.
Variables (RNG : footprint) (gp tp s0 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (m : amem) (SPA NC P D B : Z) (pl data : list Z) (msv dsz bsz lo : Z).
Variable POST : machine_state -> Prop.
Hypothesis RSPA : 0 <= SPA < 2^64.
Hypothesis LO : lo <= SPA - 16.
Hypothesis LOK : KHIGH <= lo.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis BLO : B + bsz <= lo.
Hypothesis BP : B + bsz <= P \/ P + 16 <= B.
Hypothesis BD : B + bsz <= D \/ D + zlen pl <= B.
Hypothesis DSZ : zlen data = dsz.
Hypothesis DSZR : 0 <= dsz.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis P0 : 0 < P.
Hypothesis P16 : P mod 16 = 0.
Hypothesis D0 : 0 < D.
Hypothesis D8 : D mod 8 = 0.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis BLKD : 0 < zlen pl -> ablk D (D + zlen pl).
Hypothesis BLKB : ablk B (B + bsz).
Hypothesis B16 : B mod 16 = 0.
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (SPA - lo).
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Hypothesis RB : rng RNG B bsz.
Hypothesis RBS : rng RNG (shad B) (nshad bsz).
Hypothesis RT : fse_rt m.
Hypothesis PAY : bytes_at asegs m D (map (Z_to_bv 8) pl).
Hypothesis UNP : unpoisoned m P (P + 16).
Hypothesis UND : unpoisoned m D (D + zlen pl).
Hypothesis UNB : unpoisoned m B (B + bsz).
Notation W := [(P + 8, P + 16); (B, B + bsz); (SPA - 16, SPA)].
Definition TINVA (m1 : amem) (filled : list Z) (rest : list byte) (size : Z) : Prop :=
u8arr asegs m1 B (map (Z_to_bv 8) filled ++ rest)
/\ rw_cells asegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size)]
/\ stk asegs m1 lo SPA
/\ munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1.
#[using="rc data lo RSPA LO LOK PLO DLO DP BLO BP BD P0 P16 D0 D8 BLKP BLKD BLKB B16 RT PAY UNP UND UNB"] Lemma inv_tail : forall m1, munch W m m1 -> wmono asegs m m1 ->
fse_rt m1 /\ bytes_at asegs m1 D (map (Z_to_bv 8) pl)
/\ unpoisoned m1 P (P + 16) /\ unpoisoned m1 D (D + zlen pl) /\ unpoisoned m1 B (B + bsz).
Proof.
intros m1 MU WM. pose proof (ablk_lin _ _ BLKP) as LP. pose proof (ablk_lin _ _ BLKB) as LB.
pose proof (ablk_disj_band _ _ BLKP) as DBP. pose proof (ablk_disj_band _ _ BLKB) as DBB. unfold KHIGH, KLS, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>13126631277.9813126631277.9913126631394.9413449311261.641829929204.63 23492641683.6423492641683.6528752246964.6332813024786.9832813024786.9932813024925.9438879299635.6439543755059.9839543755059.9939543755196.9457487226275.6400000R01<01`01d02?02C02G02[03303a04B04`05L06=06k07=S2LO3LOK3PLO3DLO3P163DBP2H42H53H19S2LO3LOK3PLO2DP3BLO2BP2BD3DBP3DBB2N02H42H5S2LO3LOK3PLO3DLO2DP3DBP2N03DBD2H42H5S2E0S2LO3PLO3DLO2DP2BD2P02D02LBS2N0S2N0S2LO3LOK2P02D02LP2LBS3P163DBP1H2H02H42H53H19S2DP2BP2BD3B162LB3DBP3DBB2N01H2H02H42H52H93H24S2DP2D83DBP2N02LD3DBD1H2H42H53H19S4RSPA2LO3DLO2P02D02LP2LB2E01HS2DP2BP2BD3P162LP3DBP3DBB1H2H02H42H53H193H24S2DP2BP2BD3B162LP2LB3DBP3DBB2N01H2H02H42H52H93H24S2DP2BP2BD2D82LP3DBP3DBB2N02LD3DBD1H2H42H53H19S2P02D02LP2LB2E01H".
split; [eapply fse_rt_munch; [exact RT| exact MU| exact WM| cbn [above]; unfold AIMG_HI; lia]|].
split; [eapply bytes_at_transport; [exact PAY| exact MU|]; rewrite length_map; cbn [disjoint_from]; lia|].
split; [| split; [| ]].
- (eapply unpoisoned_munch; [exact UNP| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- destruct (Z.eq_dec (zlen pl) 0) as [E0|N0].
+ replace (D + zlen pl) with D by lia. apply unpoisoned_nil. change (2^64) with 18446744073709551616 in *. lia.
+ pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. pose proof (ablk_disj_band _ _ (BLKD ltac:(lia))) as DBD. unfold AIMG_HI, KLS in *.
(eapply unpoisoned_munch; [exact UND| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- destruct (Z.eq_dec bsz 0) as [E0|N0].
+ rewrite E0, Z.add_0_r. apply unpoisoned_nil. change (2^64) with 18446744073709551616 in *. lia.
+ (eapply unpoisoned_munch; [exact UNB| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x26 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 s0 (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 2147450880) (Z_to_bv 64 dsz) (Z_to_bv 64 NC) x22 (Z_to_bv 64 bsz) (Z_to_bv 64 P) (Z_to_bv 64 msv)
x26 s11 x28 x29 x30 x31)
FR (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
#[using="rc U32R RSPA LO LOK PLO DLO DP BLO BP BD DSZ PLB P0 P16 D0 D8 BLKP BLKD BLKB B16 RI RSTK RP RPS RD RDS RB RBS RT PAY UNP UND UNB"] Lemma tail_loopA : forall f size acc rest m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
(1 <= f)%nat -> length rest = f -> dsz + zlen acc + Z.of_nat f = bsz -> 0 <= size <= zlen pl ->
TINVA m1 (data ++ acc) rest size ->
(forall m2 junkF remF (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y26 y28 y29 y30 y31 : word),
fseB_tail_loop f pl size acc = (junkF, remF) ->
TINVA m2 (data ++ junkF) [] remF -> 0 <= remF <= size ->
evtF asegs RNG POST (STpc 0x81210 m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y26 y28 y29 y30 y31)) ->
evtF asegs RNG POST (STpc 0x811c8 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.of_nat f)) (Z_to_bv 64 (B + (dsz + zlen acc)))
(Z_to_bv 64 (B + (dsz + zlen acc))) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros size acc rest m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
HF HR HB SZ (BA & PR & ST & MU & WM & MI) K.
{ exfalso. Local Ltac2 Set LiaHints.tbl := fun () => "01D0?11433765066.13111433765066.13212430247196.1191395739812.129 1395739812.130 14266202272.13114266202272.13215706649906.11616012868274.12916012868274.13016750069139.12017205643321.11917982984349.11718107228603.12418820116168.12918820116168.1301948619306.119 19617313304.13119617313304.13220694722321.12821113969864.12921113969864.13022123429781.12122191642204.13122191642204.13225175475380.12025772912818.12426492565650.12926492565650.13029782367974.13530509613568.12531077279272.12931077279272.13031989980671.12034031823111.1203413804470.131 3413804470.132 3522744003.102 3522744003.117 35968369417.10236937113401.12936937113401.13036937113401.1313742331655.129 3742331655.130 38534587673.98 38604560519.12041730628386.12742847939376.10042857743526.13942859840672.13643606267538.12446933480113.15847438200993.13147438200993.13251654974520.13551654974520.13655144173634.11755268463308.15655268463308.15756595472219.13457203912670.12957203912670.13057551420232.12957551420232.13057622410744.12059314873579.13059314923118.86 59568093227.13159568093227.1326059934030.131 6059934030.132 60951274468.12960951274468.13061716034728.12961716034728.13063374621462.12464405586220.13468300224490.99 8619817626.129 8619817626.130 9206490685.130 9206490685.131 9448783279.158 00000Z01O01P01_01n02B02Y02h03>03T04M05A05S06A06a07A07T07U07V08J08j09J0:40:F0:X0:Y0;G0<D0=D0=S0=d0>M0?=0?>0?h0@:0@L0@[0@j0A[0BI0C>0D30DE0DW0E:0Ed0F30Fd0GL0H40HC0HU0IJ0JF0K40Ki0L80M00Mo0N00Nb0OW0Of0P50PF0Q?0QI0QJ0QK0R50Rf0SF0Sf0TT0UI0UX0VQ0W:0WZ0X:0Xk0Y\0Z3S2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1FS2HF2HR2HB4LBA'S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'1G2B3S2HF2HR2HB4LBA'2CK1G2B3S2HF2HR2HB4LBA'S2HB2HR2HF4LBA'3SZ'2B3S2HB2HR2HF4LBA'3SZ'2B3S2LO3PLO3DLO2DP3BLO2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'S2LO3PLO2DP3BLO2BP2BD2P02D02HF2HR2HB2LB3LBA4LBA'3LM1S2HF2HR2HB2SZ4LBA'S2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'3LM1S3DSZ2P02D02HF2HR2HB2LB4LBA'3LM1S3DSZ2P02D02HF2HR2HB2LB4LBA'3LM1S3PLO2HF2HR2HB4LBA'FFS2DP2BP2BD2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM12CKS3DSZ2P02D02HF2HR2HB2LB4LBA'3LM1S3DSZ2P02D02HF2HR2HB2LB4LBA'3LM1S2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'S2HB2HR2HF4LBA'2B3S2HB2HR2HF4LBA'2B3FS2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'3LM1S2LO3PLO2DP3BLO2BP2BD3DSZ2P02D02HF2HR2HB2LB4LENP3LBA4LBA'3LM1S2LO3PLO2DP3BLO2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'1HS2DP2BP2BD2P02D02HF2HR2HB2LB3LBA4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP3LBA4LBA'3LM1FS2LO3PLO3BLO2P02D02HF2HR2HB2LB2LP3LBA4LBA'S2HF2HR2HB4LBA'2B3S2HF2HR2HB4LBA'2B3S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'S2DP2BP2BD2P03P162D02HF2HR2HB2SZ2LB4LENP3LBA4LBA'S2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2HF2HR2HB4LBA'2CRS2HF2HR2HB4LBA'2CRS2DP2BP2BD3DSZ2P02D02HF2HR2HB2SZ2LBS2LO3PLO3BLO2P02D02HF2HR2HB2LB2LP3LBA4LBA'S2HF2HR2HB4LBA'S2DP2BP2BD3DSZ2P02D02HF2HR2HB2SZ2LB4LENP3LBA4LBA'S3DSZ2P02D02HF2HR2HB2LB2LP4LENP4LBA'3LM1S3DSZ2P02D02HF2HR2HB2LB2LP4LENP4LBA'3LM1S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'2SRS2DP2BP2BD2P02D02HF2HR2HB2SZ2LB4LENP3LBA4LBA'3LM13SZ'S2DP2BP2BD3DSZ2P02D02HF2HR2HB2SZ2LB2LP4LENP3LBA4LBA'3LM13SZ'S2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2HF2HR2HB4LBA'S2DP2BP2BD2P02D02HF2HR2HB2SZ2LB4LENP3LBA4LBA'3LM13SZ'2H1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2SZ2LB2LP4LENP3LBA4LBA'3LM13SZ'2H1FS2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB4LENP3LBA4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'1HS2DP2BP2BD2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM12CK1G2G2S2HF2HR2HBFFS2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'S2DP2BP2BD2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2P02D02HF2HR2HB2LB2LP4LENP4LBA'S2P02D02HF2HR2HB2LB2LP4LENP4LBA'S2DP2BP2BD2P02D02HF2HR2HB2LB4LENP3LBA4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2HF2HR2HB4LBA'S2DP2BP2BD3DSZ2P02D03B162HF2HR2HB2LB2LP4LENP3LBA4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB4LENP3LBAS3DSZ2P02D02HF2HR2HB2LB4LBA'3LM1S3DSZ2P02D02HF2HR2HB2LB4LBA'3LM1S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'S2DP2BP2BD3DSZ2P02D02HF2HR2HB2LB2LP4LENP3LBA4LBA'S2HF2HR2HB4LBA'2CK1G2H0".
lia. }
destruct (inv_tail m1 MU WM) as (RT1 & PAY1 & UNP1 & UND1 & UNB1).
pose proof (ablk_lin _ _ BLKB) as LB. pose proof (ablk_lin _ _ BLKP) as LP. unfold AIMG_HI in LB, LP.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
assert (LBA : zlen (map (Z_to_bv 8) (data ++ acc) ++ rest) = bsz).
{ rewrite length_app, length_map, length_app. lia. }
assert (LBA' : length (map (Z_to_bv 8) (data ++ acc) ++ rest) = Z.to_nat bsz) by lia.
assert (LM1 : Z.of_nat (length (map (Z_to_bv 8) (data ++ acc))) = dsz + zlen acc) by (rewrite length_map, length_app; lia).
zstep. zstep. zstep. zstep.
unfold prod_u32r_stmtA, APROD_U32R in U32R.
destruct RT1 as (GOT1 & _ & _ & SHB1 & _).
eapply evtF_cut; [ eapply U32R with (SPV := SPA) (P := P) (D := D) (pl := pl) (size := size) (mn := 0) (mx := 255) (lo := lo)
| post_call asegs m1 ];
[ first [ assumption | split; assumption | reflexivity | lia | (clear - P16; Z.div_mod_to_equations; lia)
| change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia | solve_rng ] .. | ].
try clear PR. rename POST0 into PR. rename PC into ST. rename MI0 into MI. unfold prod_atA in PR.
pose proof (uint32Range_spec pl size 0 255 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as UR.
rewrite fseB_tail_loop_step in K.
destruct (uint32Range pl size 0 255) as [c size'] eqn:EU. cbn [fst snd] in *. destruct UR as (CR & SZ' & _).
destruct rest as [|r0 rest']; [cbn in HR; lia|]. cbn [length] in HR.
destruct (inv_tail _ MU WM) as (_ & _ & _ & _ & UNB2).
destruct (unpoisoned_check_rd asegs _ B (B + bsz) (B + (dsz + zlen acc)) 1 UNB2 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(pose proof (Z.mod_pos_bound (B + (dsz + zlen acc)) 8 ltac:(lia)); lia)) as (sb & RDB & CK).
unfold shad, ASHOFF in RDB. replace (2147450880 + Z.shiftr (B + (dsz + zlen acc)) 3) with (Z.shiftr (B + (dsz + zlen acc)) 3 + 2147450880) in RDB by lia.
pose proof (sval_range sb) as SR.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
-
zstep. rewrite land7_mod. zstep. if_cases G2; [| exfalso; unfold bv_lts in G2; rewrite !signed_lit_small64 in G2 by (Z.div_mod_to_equations; lia); zify_bool G2; lia].
pose proof (u8arr_store_ok asegs _ B _ (dsz + zlen acc) (wa (B + (dsz + zlen acc))) BA ltac:(rewrite LBA; lia) eq_refl) as SOK.
zstep. rewrite ?le1_lit.
pose proof (u8arr_write asegs _ B _ (dsz + zlen acc) (Z_to_bv 8 c) BA ltac:(rewrite LBA; lia)) as BA2.
clear BA. store_done.
replace (Z.to_nat (dsz + zlen acc)) with (length (map (Z_to_bv 8) (data ++ acc))) in BA2 by (rewrite length_map, length_app; lia).
rewrite upd_app_midA in BA2.
replace (map (Z_to_bv 8) (data ++ acc) ++ Z_to_bv 8 c :: rest') with (map (Z_to_bv 8) (data ++ (acc ++ [to_byte c])) ++ rest') in BA2.
2:{ rewrite (app_assoc data acc), map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
unfold to_byte. rewrite (Z.mod_small c 256) by lia. reflexivity. }
zstep. zstep. zstep.
replace (Z.of_nat (S f) + -1) with (Z.of_nat f) by lia.
replace (B + (dsz + zlen acc) + 1) with (B + (dsz + zlen (acc ++ [to_byte c]))) by (rewrite length_app; cbn [length]; lia).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => assert (INV2 : TINVA mx (data ++ (acc ++ [to_byte c])) rest' size') end.
{ split; [exact BA2|]. split; [exact PR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
zstep. if_cases B3; zify_cond B3.
+
eapply (IH size' (acc ++ [to_byte c]) rest'); try lia; [rewrite length_app; cbn [length]; lia| exact INV2|].
intros. eapply K; try eassumption. lia.
+
assert (f = 0%nat) by lia. subst f. destruct rest'; [|cbn in HR; lia].
zstep. eapply K; [reflexivity| exact INV2| lia].
-
pose proof (u8arr_store_ok asegs _ B _ (dsz + zlen acc) (wa (B + (dsz + zlen acc))) BA ltac:(rewrite LBA; lia) eq_refl) as SOK.
zstep. rewrite ?le1_lit.
pose proof (u8arr_write asegs _ B _ (dsz + zlen acc) (Z_to_bv 8 c) BA ltac:(rewrite LBA; lia)) as BA2.
clear BA. store_done.
replace (Z.to_nat (dsz + zlen acc)) with (length (map (Z_to_bv 8) (data ++ acc))) in BA2 by (rewrite length_map, length_app; lia).
rewrite upd_app_midA in BA2.
replace (map (Z_to_bv 8) (data ++ acc) ++ Z_to_bv 8 c :: rest') with (map (Z_to_bv 8) (data ++ (acc ++ [to_byte c])) ++ rest') in BA2.
2:{ rewrite (app_assoc data acc), map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
unfold to_byte. rewrite (Z.mod_small c 256) by lia. reflexivity. }
zstep. zstep. zstep.
replace (Z.of_nat (S f) + -1) with (Z.of_nat f) by lia.
replace (B + (dsz + zlen acc) + 1) with (B + (dsz + zlen (acc ++ [to_byte c]))) by (rewrite length_app; cbn [length]; lia).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => assert (INV2 : TINVA mx (data ++ (acc ++ [to_byte c])) rest' size') end.
{ split; [exact BA2|]. split; [exact PR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
zstep. if_cases B3; zify_cond B3.
+
eapply (IH size' (acc ++ [to_byte c]) rest'); try lia; [rewrite length_app; cbn [length]; lia| exact INV2|].
intros. eapply K; try eassumption. lia.
+
assert (f = 0%nat) by lia. subst f. destruct rest'; [|cbn in HR; lia].
zstep. eapply K; [reflexivity| exact INV2| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Tail.
End CANSEC1.
