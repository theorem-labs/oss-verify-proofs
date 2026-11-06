(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Definition combined_alloc_entry := 0x356c4%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).     (* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
Definition cache_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c cnt idx spacebeg lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * idx)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj']).

#[using="Type"] Lemma combined_alloc_hit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells bsegs m 0x9d9f8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x356c4) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "02;0>10082350123.8011531127361.8311775166127.811234415188.93 12431607254.8112506424771.8212525554635.8214734152553.7914763672662.8016654661901.9217776320431.7917776320431.891800609155.80 1800609155.90 18867207222.8219030965577.7319515728436.8220262998748.7920335463178.7920854954799.8020979536691.8021651633935.8222391638788.7822954551237.9324570100999.9124638473347.8124638473347.9124963260777.7826492550416.7826492550416.8026492550416.8126492550416.8326492550416.9327904923141.8228419357060.8029003366760.8229311285958.6529788955507.9330863979691.7831378308326.7132098070984.9032356862517.9333677903874.8134428055044.8135214167685.8835241715170.8736115622446.8036115622446.9037683496382.8338446806799.8038446806799.8938510784165.8340455642244.8040605904854.7840818989526.8041352055893.8142240553391.8142553017460.8242651412631.7342828922350.8042828922350.8342858215713.8043059266230.6943987951406.8043987951406.9043988483203.7843988483203.8944021460374.8044021460374.8245219141890.8145412913494.8045848756903.7846466564356.8148185458843.8048320830113.8148722578991.8049073433023.9349242818135.8249649769127.8150669429877.8251356649574.8251418988165.8051711223320.8152094863241.9252105090727.8052624921519.7852793185963.8153767577775.7953767577775.8954243526019.8054243526019.9055336861633.8955338958790.8955345848131.7655345848258.7755989853626.8156428783466.8056428783466.83565324930.80  56983243656.8057008552236.8157700073633.7857743577986.8059314873579.7459314873579.7559314873579.7659314873579.7759314873579.7859314873579.8260858483367.8161523295858.8361917199020.8861917199023.796280285958.91 6280285958.92 63164784673.8063235321900.7763235321900.8863305555623.8063314293035.8064371235530.9364997134979.8164997134979.9165093347183.9265093347183.9365098632094.8265106454549.7465106454676.7565108530606.7365658293242.7366165977419.9367033309574.8267103057043.6467388853175.808581623554.78 9272504225.81 9581476779.81 9869190602.82 9954448086.81 00000<00G00Z00l01501>01G01H01Q01Z01b01f01k01l01m02102202302402G02L02U02Y02Z02_02d02e02i02j02k02l02m02n03203603;03<03@03L03Q03`03d03i03m03n04204:04>04B04G04H04T04X04a04b04k05>05?05C05H05L05[05c05k05o06406506606706<06E06J06N06a07007C07R07S07X07Y08708F08G08K08P08c08o09709;09@09A09E09I09M09Q09g0:00:90:>0:B0:K0:Z0:_0:j0;50;@0;K0;V0;b0;g0;k0;o0<70<;0<?0<N0<V0<Z0<_0<k0<o0=40=50=60=70=?0=C0=G0=K0=O0=T0=Y0=a0=m0>20>A0>M0>N0>WS4CEIL2LO2T1S2HR3LCH2RBS4CEIL2LO3LCH2T12C1S2HR3LCH3TAL2C12RBS4CEIL2LOS3LCH3CNTS3LCH3CNTFS4CEIL2LOS3LCH3CNTS2LO3LCHS2LOS3LCHSSS2SZSFFS4CEIL2LO3LCH2T12C1S3LCHS3LCH3IXSS2HBSS3LCHS3LCHSS2C1SSSSSS2LOS2HBS3LCHSS2HBS4CEIL2LO2T1S3LCHS2HR3LCH3CNT2RBS2RBS3SPRS2HBFS2SZS2LO3LCHS2LOS2RBS3LCHSS4CEIL2LO2T1S2HBS4CEIL2LOSS3LCH3CNTS4CEIL2LO3LCH2T12C1FS2SZS3SPRS2HBS4CEIL2LO2T12C1S2LO3LCHS2LO3LCHS2LOS3LCHSSSS3SPRS4CEIL2LOS3LCHS2HBS4CEIL2LO3LCH2T12C1S4CEIL2LO2T12C1S4CEIL2LO3LCH2T12C1S4CEIL2LO2T12RBSS3LCHSS3LCH3CNT2T02T13TAL2C12K32K51HS4CEIL2LO2T12C1SS2RBS3LCHS4CEIL2LO3LCH2T12C1S4CEIL2LO2T1S2LO3LCHS2LOS3LCHSS2C1S2C1S2C1S2C1S3LCH3CNT3TAL2C12K32K5S4CEIL2LOS3LCH3TALS3SPRS2HBS3LCH3CNTS4CEIL2LO2T12C1S3SPRS2SZ3LCH2K0S2SZ3LCH2K1S2SZ3LCH2K2S3LCH2C12K3S3LCH2C12K4S3LCH3CNT2K5S3LCHS2HBS2LOS2LO3LCHS2RBS2RBS4CEIL2LO2T12C1S2LO3LCHS2LOS3LCHS4CEIL2LO2T1S2HBS3LCHSSSS2SZ3LCHS2SZS2SZS2SZS2SZS3LCHS3LCHS2SZ3LCHS4CEIL2LO2T1S3SPRS4CEIL2LO2T12C1S4CEIL2LO2T1SS4CEIL2LO".
assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }   (* [comment removed for export] *)
  do 2 zstep. rewrite HC.                           (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K4; zify_cond K4. { exfalso. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  lstep.                                            (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. lia. }   (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
