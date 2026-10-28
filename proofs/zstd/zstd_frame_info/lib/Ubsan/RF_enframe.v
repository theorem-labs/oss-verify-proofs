(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition renframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P - 3)) [b8 k] in
  let m2 := write_to_mem m1 (wa (P - 2)) (le2 (wz q)) in
  let r := E - P - n in
  let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition ren3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
   (m : word -> option byte) (P E n k q : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 pw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ m' = renframe_tail_mem m P E n k q
    /\ mem_inv usegs m'.

#[using="Type"] Lemma lor_shl5 r k : 0 <= k < 32 -> 0 <= r -> Z.lor (r * 2 ^ 5) k = Z.land k 31 + Z.shiftl r 5.
Proof.
  intros Hk Hr. Local Ltac2 Set LiaHints.tbl := fun () => "0070=29317572540.530212793343.836370612534.644209199684.949280143748.551797253729.98850484027.9 00000100400500900=00C00FSS1HSS2HkS2HkS2Hk1nS1H".
replace (Z.land k 31) with k by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (D : Z.land (r * 2 ^ 5) k = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 5).
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit k i) with false; [apply andb_false_r|]. symmetry.
      destruct (Z.eq_dec k 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End CANSEC1.
Ltac read_k := lazymatch goal with BKc : bytes_at usegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read usegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
(* [comment removed for export] *)
Ltac sok off len addr := lazymatch goal with W : wr_at usegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok usegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma renframe_tail_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw : word) F fc m
    (P0 P E B n k stride : Z),
  bv_unsigned p0w = P0 -> bv_unsigned nw = n -> E = P0 + stride - 4 ->
  mem_inv usegs m ->
  wr_at usegs m (P - 3) (E - P + 3) ->
  E + 1 <= 2^64 -> B + 16 <= P -> P0 <= P -> P + n <= E -> E - P - n < 2^31 -> P - B < 2^31 -> 16 <= P0 -> 0 <= B -> 0 <= n -> 0 <= k < 32 ->
  0 <= stride ->
  evt usegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) F fc m P E n k ((P - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (Z_to_bv 64 P) (Z_to_bv 64 stride) p0w (wz B) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15b54) fc None m (seg_rom usegs)).
Proof.
  intros until stride. intros HP0 HN HE MI WR ETOP BP P0P PNE EP PB P16 B0 N0 HK S0.
  pose proof (bv_unsigned_in_range _ p0w) as PWR. change (bv_modulus 64) with (2^64) in PWR.
  set (r := E - P - n).
  Local Ltac2 Set LiaHints.tbl := fun () => "01W0>10776995384.6110822033626.7111671058801.5712389288094.6114267522680.6915045133701.6615045133701.7015045146400.6315047230593.571546337317.67 1546337317.71 18468461873.6618468461873.7018468466580.6318736134169.57194881816.67  20775746093.6622797752595.6322799854258.5722948535026.6324422594165.6425738052104.6928153383213.6328153396104.6628153396104.7028153514158.5828153514158.6428260588173.6029010565541.6629010569984.632925277044.63 2927369429.57 29311379388.5629317166687.6729317547385.6629317547385.7030532418181.5930534109351.6430534109351.6730534109351.7131675533918.6433965535425.663523526069.57 35391669133.5735393777708.6335473918055.6736942891458.6336942904167.6636942904167.7037832605946.7139922484861.6840130415992.604063019048.64 4063019048.67 4063019048.71 40823203693.5742298116046.6642628430081.574360182696.67 45252236538.7145788509687.6146759293741.6447862893687.7149278734724.5651735249241.695367493339.66 54172198805.6655703722969.7255723328444.6455927799826.5855927799826.6455927799826.6755927799826.7155927819790.6455927819790.6755927819790.7156138132542.6858446107943.7159251261832.6659251261832.7060937265595.6462538202716.5962540680318.6462540680318.6762540680318.7163872929716.6363875038229.5764026078540.7164268586311.6764407792293.5764497643482.6364698003840.6365005348578.5765007441219.6365007445990.6665007445990.7065746174505.6766114380519.696755817987.60 7538996526.61 781211313.63  8120280595.57 9222643068.67 00000100500H00I00Y00Z00[00\00]00d00h00l01001401501?01@01A01B01J01K01U01Y01]01a01e01i01j02202:02M02`02a02b02c02d03103>03K03W03a03i04004804@04D04E04F04G04K04L04T04U04V04W04X04_05205B05F05S05]05^05b05k06006806906:06;06<06=06>06?06@06A06H06L06P06T06X06_06f06m07407G07Z07[07_07c07d07o08708>08F08M08V08Z08[08b08f08m098SS2HES4ETOP2BP3PNE2B02N0SS2HE2BP2B02N02K5SSSSS2BP2KRS2K5S2HKS2HKS2HKSS2HE2N02K5SSSS3PNE2EPSS2HE2N02K5S2HKS2HKS2HKS2HKS2HKSS3PNE2K5S3PNE2EPS4ETOP2BP3PNE2B02N0S4ETOP2BP3PNE2B02N0SSSSS4ETOP3PNE2N0S4ETOP3PNE2N0S4ETOP3PNE2N0S4ETOP2N02K5S4ETOP3PNES3PNE2K5S2BP2PBS3PNE2EPS3PNE2EPS2HESSSS2HESS3PNE2N0FFFSS2N02K5S4ETOP2BP3PNE2B02N0S2HE2BP2B02N02K5S2HKS4ETOP3PNE2N0S2BP2B02N0FS2HKS2HE4ETOPS3PNES3PNE2EPSSSSSSSSSS2N02K5S2K5S2HKS2HKS2N0S2BP2B0S2BP2B0S2BP2B0S2BP2B0S4ETOP2BP3PNE2B02N0S4ETOP2BP3PNE2B02N0FS2K5S2HESS2BP3PNE2KRS3PNE2N0S2N02KRS3PNE2N0S2N02K5S2HE4ETOPS2HESS2BP2B0S2N0S2BP2PBS3PNE2HK2K5".
assert (K31 : Z.land k 31 = k) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit P), (wz_unsigned B), (swrap32_small (P - B)) by lia.
  (* [comment removed for export] *)
  step. rewrite HN.
  (* [comment removed for export] *)
  step. rewrite HP0. replace (P0 + stride + -4) with E by lia.
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit (P - B + -16)), Z.shiftr_div_pow2 by lia.
  change (2 ^ 4) with 16. replace (P - B + -16) with (P - B - 16) by lia.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  sok 0 1%nat (P + -3).
  step. rewrite (le1_wz k) by lia. sdk.
  lazymatch goal with E2 : ?mc = write_to_mem ?mp (wa ?a) [b8 k] |- _ =>
    pose proof (bytes_at_write_same usegs mp a [b8 k] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
    replace a with (P - 3) in BK by lia end.
  (* [comment removed for export] *)
  sok 1 2%nat (P + -2).
  step. change (le2 (Z_to_bv 64 ((P - B - 16) / 16))) with (le2 (wz ((P - B - 16) / 16))). sdk.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    read_k. step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned k), ?K31 by lia. step. step. rewrite ?(unsigned_lit 0), ?(unsigned_lit k) by lia.
    rewrite Z.lor_0_l.
    sok 0 1%nat (P + -3).
    step. change (le1 (Z_to_bv 64 k)) with (le1 (wz k)). rewrite (le1_wz k) by lia. sdk.
    step. step.
    apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
    split; [|assumption].
    unfold renframe_tail_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    rewrite K31. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r.
    repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
    repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      read_k. step. clear RK. rewrite ?zxb_b8 by lia.
      step. rewrite ?(wz_unsigned k), ?K31 by lia.
      step. rewrite (unsigned_lit r), Z.shiftl_mul_pow2 by lia.
      step. rewrite (unsigned_lit (r * 2 ^ 5)), (unsigned_lit k) by lia. rewrite (lor_shl5 r k) by lia.
      sok 0 1%nat (P + -3).
      step. rewrite (le1_wz (Z.land k 31 + Z.shiftl r 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
      step. step.
      apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
      split; [|assumption].
      unfold renframe_tail_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - P - 2) 1%nat (P0 + stride + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (P0 + stride + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      read_k. step. clear RK. rewrite ?zxb_b8 by lia.
      step. rewrite ?(wz_unsigned k), ?K31 by lia.
      step. step. rewrite ?(unsigned_lit 5), (unsigned_lit k) by lia. change (5 ≪ 5) with (5 * 2 ^ 5). rewrite (lor_shl5 5 k) by lia.
      sok 0 1%nat (P + -3).
      step. rewrite (le1_wz (Z.land k 31 + Z.shiftl 5 5)) by (rewrite K31; change (Z.shiftl 5 5) with 160; lia). sdk.
      step. step.
      apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
      split; [|assumption].
      unfold renframe_tail_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition renframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
  if off =? 0 then m
  else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off)))
                    (wa (P0 + 16 * off - 4)) [b8 0].

(* [comment removed for export] *)
#[using="Type"] Lemma renframe_off_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
    (P0 B stride n k off avail freed mword : Z),
  bv_unsigned p0w = P0 -> bv_unsigned nw = n ->
  mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at usegs m (P0 - 4) stride ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 -> P0 + 16 * off - B < 2^31 -> 16 <= P0 -> 0 <= k < 32 ->
  0 <= off -> 16 * off <= stride - 4 - n ->
  evt usegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15b30) fc None m (seg_rom usegs)).
Proof.
  intros until mword. intros HP HN MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OFF0 OFFS.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
  (* [comment removed for export] *)
  step. step. Local Ltac2 Set LiaHints.tbl := fun () => "00c0>10500183861.6212662692441.6414157728925.5914159890590.6714765941800.5917364588512.6718586509700.6718588411271.5918639614516.5920705668160.6724082382131.612474587902.66 26523454504.6227895696130.5931466414420.6432337844796.5934966404843.6235970597666.5937167726282.6740746209785.6140825296207.6140947215360.6341415938799.6345618816738.6546777209680.594699770125.67 47403337021.6747841276241.6247845209988.6750529237564.6750958529839.5952785568338.675320293466.64 55710818555.6755764213932.6656179584482.5957006878397.6657763296224.6458699708685.6760167584771.6760169877504.5960319817908.6762162794107.5965227439451.6665330009231.676755963935.61 67773805936.61713426688.59  7909999988.67 9130291799.65 9760512911.67 00000400K00Q00W00X00^00e00n01301<01I01_02602702;02<02K02O02U02b02c02j02k03103C03D03E03O03P03Y03]03^03m04304404504C04M04N04O04P04T04U04_04h04i05005105505>05?S2HPS2HP4SEPG2N02NS4OFF02KOS4PTOPS4PTOPSS4OFFSS2N02NSS2N04OFFSS3PBSS2BP4OFF0S2BP3PBS4OFF0S4SEPG2N04OFF04OFFS2KOS2HP4SEPG2N02NS4OFF02KOSS2HPSS2HP4PTOP2N02NSS2NSS4OFF0S2BP3PBS4OFF0SS2N02NSSS4OFF0S4PTOP2N03P164OFFSSSS2HP2BP2B0FS2SS4OFF0S2SSFS2HP4PTOP2N02NSS4OFF0SFS4PTOP2N04OFFSS2HP2BP2B0SSSS2HPFS3P164OFF0S4OFF02KOSS2N02NSSS2HPS2N04OFFSF".
if_cases KO; zify_cond KO; rewrite ?(unsigned_lit off) in KO by lia.
  - (* [comment removed for export] *)
    subst off. unfold renframe_off_mem. rewrite Z.eqb_refl.
    replace (P0 + 16 * 0) with P0 by lia.
    replace p0w with (Z_to_bv 64 P0) by (rewrite <- HP; apply Z_to_bv_bv_unsigned).
    eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
    + apply unsigned_lit. lia.
    + eapply wr_at_sub; [exact WR | lia | lia].
  - (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit off), Z.shiftl_mul_pow2, (swrap32_small (off * 2 ^ 4)) by lia.
    step. rewrite HP.
    pose proof (wr_at_store_ok usegs m _ _ 1 1 WR ltac:(lia) ltac:(lia)) as SO1.
    replace (P0 - 4 + 1) with (bv_unsigned p0w + -3) in SO1 by lia.
    change (wa (bv_unsigned p0w + -3)) with (Z_to_bv 64 (bv_unsigned p0w + -3)) in SO1.
    step. rewrite le1_neg32. sdk.
    lazymatch goal with W : wr_at usegs ?mc (P0 - 4) _ |- _ =>
      pose proof (wr_at_store_ok usegs mc _ _ 2 2 W ltac:(lia) ltac:(lia)) as SO2;
      replace (P0 - 4 + 2) with (bv_unsigned p0w + -2) in SO2 by lia;
      change (wa (bv_unsigned p0w + -2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in SO2 end.
    step. change (le2 (Z_to_bv 64 off)) with (le2 (wz off)). sdk.
    lazymatch goal with W : wr_at usegs ?mc (P0 - 4) _ |- _ =>
      pose proof (wr_at_store_ok usegs mc _ _ (16 * off) 1 W ltac:(lia) ltac:(lia)) as SO3;
      replace (P0 - 4 + 16 * off) with (P0 + off * 2 ^ 4 + -4) in SO3 by lia;
      change (wa (P0 + off * 2 ^ 4 + -4)) with (Z_to_bv 64 (P0 + off * 2 ^ 4 + -4)) in SO3 end.
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    step.
    replace (P0 + off * 2 ^ 4) with (P0 + 16 * off) by lia.
    unfold renframe_off_mem. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      replace (write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off))) (wa (P0 + 16 * off - 4)) [b8 0])
        with mc end.
    2:{ repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
        repeat (f_equal; try (unfold wa; f_equal; lia)). }
    eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
    eapply wr_at_sub; [exact WR | lia | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma swrap32_add_2p64 d : -2^31 <= d < 2^31 -> bv_swrap 32 (18446744073709551616 + d) = d.
Proof.
  intros Hd. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=43375938307.345048875388.352225336943.3000004005006S2HdSS".
replace (18446744073709551616 + d + 2147483648) with ((d + 2147483648) + 4294967296 * 4294967296) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma renframe_fold_walk : forall (ra sp gp tp t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
    (P0 B stride n k off0 avail freed mword T0 : Z),
  let slack := (stride - 4 - n) / 16 in
  let off := fold_off off0 slack in
  bv_unsigned p0w = P0 -> bv_unsigned nw = n -> T0 = stride - 4 - n ->
  mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at usegs m (P0 - 4) stride ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
  (forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 16 <= P0 -> 0 <= k < 32 ->
  0 <= off0 < 256 ->
  evt usegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp (Z_to_bv 64 T0) (Z_to_bv 64 slack) t2 s0 s1
               gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15af4) fc None m (seg_rom usegs)).
Proof.
  intros until T0. intros slack off HP HN HT0 MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OF.
  Local Ltac2 Set LiaHints.tbl := fun () => "00k0>1007317331.77 12118773960.7413017035673.7413017398407.6515521291196.7918587220045.7418587338353.6422005796916.6127839860440.6830298370776.6330849675254.6530849675254.7930849675254.8031288095343.7833006402833.7735230748000.7835497483805.7836231842086.8037628337619.7138869306396.6838871413405.6740823609964.7040825300077.6341417924045.6742446486969.7447369967617.6548139118193.6448274710567.7748274710567.7849042613487.6550116072775.7951510776154.8051779417508.6551779417508.7951779417508.8052405666041.7856063338499.6156063517723.7756093753535.7956197538779.785744668161.78 5744684037.77 5744875184.78 5744993178.76 58777926696.5959308628433.7859308628433.7959631524510.7659631529781.6559631851269.7859631906613.6459631906740.7859631906740.7959632463669.6660037177791.7467332360224.7067334468903.716755968317.63 6755968317.64 00000>00C00G00K00Y00]00a00b00f00j00k00l00m01101501601701B01F01K01P01Q01R01S01X01\01g01k01o02702?02C02K02S02^02i02m03103503C03Q03_03m04404;04B04I04T04_04j05505@05K05V05Z05_05d05e05fS2SS3S162RX2GES3RM3S2OFS2OFS2SS3S162LT2FAS2OFS2OFSS2R2S2K1FFFS2LTS2GESSS2FO3S162EOS2R3S3RM1S3RM1SSSS3RM3S2R1S3HT02NS2SSS2K1S2K1S3S162K1S3S162K2S2LTS3S162K1S3S162K2S2FO3S162EOS2SS2SL3S16S2SLS2SLS2RXS2SS3S162LT2FAS2SS3S162RX2FAS2SS3S162RX2GES2SS3S162RX2GES2OF2RXS2N02NSS2GE2K2S2FA2K2S2SS2SL3S16S2SS2SL3S16S2SS2SL3S16S2SS2SL3S16S2SS2SL3S16S2SS2SL3S16S2SS2SL3S16S2OFS3RM2S3RM2SS".
assert (SL : 0 <= slack <= stride) by (subst slack; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (fold_off_le_slack off0 slack OF ltac:(lia)) as FO. fold off in FO.
  assert (S16 : 16 * slack <= stride - 4 - n) by (subst slack; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(unsigned_lit slack), ?(unsigned_lit off0) in K1 by lia.
  - (* [comment removed for export] *)
    assert (EO : off = off0) by (subst off; rewrite fold_off_eq; replace (slack <? off0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    rewrite EO. eapply renframe_off_walk; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try (apply PBS; lia).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit T0), HT0 by lia.
    replace ((stride - 4 - n) ≫ 5) with (slack ≫ 1) by (subst slack; rewrite <- (Z.shiftr_div_pow2 _ 4), Z.shiftr_shiftr by lia; reflexivity).
    pose proof (Z_shiftr_range slack 1 ltac:(lia) ltac:(lia)) as R1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (slack ≫ 1)), (unsigned_lit slack) by lia.
    set (m1 := Z.lor slack (slack ≫ 1)).
    pose proof (Z_lor_range slack (slack ≫ 1) ltac:(lia) R1) as RM1. fold m1 in RM1.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit m1) by lia. pose proof (Z_shiftr_range m1 2 RM1 ltac:(lia)) as R2.
    step. rewrite (unsigned_lit m1), (unsigned_lit (m1 ≫ 2)) by lia. rewrite (Z.lor_comm (m1 ≫ 2) m1).
    set (m2 := Z.lor m1 (m1 ≫ 2)). pose proof (Z_lor_range m1 (m1 ≫ 2) RM1 R2) as RM2. fold m2 in RM2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit m2) by lia. pose proof (Z_shiftr_range m2 4 RM2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit m2), (unsigned_lit (m2 ≫ 4)) by lia. rewrite (Z.lor_comm (m2 ≫ 4) m2).
    set (m3 := Z.lor m2 (m2 ≫ 4)). pose proof (Z_lor_range m2 (m2 ≫ 4) RM2 R3) as RM3. fold m3 in RM3.
    assert (SM : m3 = smear slack) by reflexivity.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit off0), (unsigned_lit m3) by lia.
    set (x := Z.land off0 m3).
    assert (RX : 0 <= x <= off0) by (subst x; split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
    (* [comment removed for export] *)
    step. rewrite v_sltu_b2z, (unsigned_lit slack), (unsigned_lit x) by lia.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit slack) by lia.
    destruct (Z.ltb_spec slack x) as [LT|GE]; cbn [Z.b2z].
    + pose proof (fold_assert_ok off0 slack OF ltac:(lia) ltac:(rewrite <- SM; exact LT)) as FA. rewrite <- SM in FA. fold x in FA.
      step. step. rewrite (zb_lxor_ones slack) by lia. rewrite (unsigned_lit (18446744073709551615 - slack)) by lia.
      change 18446744073709551615 with (Z.ones 64) at 1. rewrite (Z.land_comm (Z.ones 64)), Z.land_ones by lia.
      rewrite (Z.mod_small (18446744073709551615 - slack)) by lia.
      step. rewrite (unsigned_lit (18446744073709551615 - slack)), (unsigned_lit x) by lia.
      replace (18446744073709551615 - slack + x) with (18446744073709551616 + (x - (slack + 1))) by lia.
      rewrite swrap32_add_2p64 by lia.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit (x - (slack + 1))) in K2 by lia; [|exfalso; lia].
      assert (EO : off = x - (slack + 1)).
      { subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
        rewrite <- SM. fold x. replace (slack <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      rewrite EO. eapply renframe_off_walk; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try (apply PBS; lia).
    + step. step. change (Z.land 0 _) with 0.
      step. rewrite (unsigned_lit x), Z.add_0_l, (swrap32_small x) by lia.
      step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit x) in K2 by lia; [|exfalso; lia].
      assert (EO : off = x).
      { subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
        rewrite <- SM. fold x. replace (slack <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite EO. eapply renframe_off_walk; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try (apply PBS; lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma land_m4096 a : 0 <= a < 2^64 -> Z.land a 18446744073709547520 = a - a mod 4096.
Proof.
  intros Ha.
  Local Ltac2 Set LiaHints.tbl := fun () => "00=0=10357883337.611320819982.811431533854.617210503357.317210504373.519457651979.823902346647.726980962951.835497642613.553506897146.363681228783.666340890413.67768763522.6 00000400800900:00;00?00C00I00J00K00N00Q00TS2HiS2HaSSSS2H0S2H0S2Ha1nSSS1HS1HS1H".
replace (a - a mod 4096) with (Z.shiftl (Z.shiftr a 12) 12) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^12) with 4096; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones by lia.
  destruct (Z.lt_ge_cases i 12).
  - rewrite Z.shiftl_spec_low by lia. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (i <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb]. rewrite !andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (i <? 12) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.lt_ge_cases i 64).
    + replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn. rewrite andb_true_r. reflexivity.
    + replace (Z.testbit a i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia|lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma renframe_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw nw prev next : word) F fc m
    (B stride n k ctr avail freed last_idx freeable sc maplen vb3 v16 : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let P0 := B + 16 + stride * k in
  let slack := (stride - 4 - n) / 16 in
  let off0 := (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
  let off := fold_off off0 slack in
  bv_unsigned nw = n ->
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
  ((last_idx =? 0) && negb (maplen =? 0) = false -> sc < 48) ->
  mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at usegs m (P0 - 4) stride ->
  ov_read_bytes usegs m (wa (P0 - 3)) 1 = Some [b8 vb3] ->
  ov_read_bytes usegs m (wa (P0 - 2)) 2 = Some (le2 (wz v16)) ->
  ov_read_bytes usegs m (wa (P0 - 4)) 1 = Some [b8 0] ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
  (forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 0 <= k < 32 ->
  0 <= ctr < 2^32 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  0 <= vb3 < 256 -> 0 <= v16 < 65536 ->
  evt usegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15a78) fc None m (seg_rom usegs)).
Proof.
  intros until v16. intros mword P0 slack off0 off HN HS SC48 MI MM WR R3 R2 R4 PTOP SEPG B0 N0 NS SS PBS HK CT LI FB SC ML VB V16.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
  Local Ltac2 Set LiaHints.tbl := fun () => "01=0>11001303940.8811420635998.8912415402040.9212639332404.9013292368169.8016076623856.8717197832428.8218428768297.8318470534250.8818588543525.8518977788745.7818977788776.7919532568852.8820324561062.8921464901593.912199286046.92 23580900985.9023967613044.942424904036.89 28148992737.8929315071079.9229315560028.7929697015606.8529703215556.8930177719770.9231413455932.8832052216138.8832506553272.9332506565909.9432508665535.8733711176136.883398842305.83 34847673685.8936153507375.893817749923.88 39086535308.7940825298140.8840825706315.9540930850741.7842586640110.8942790203290.9544545114044.794524912096.89 46242130221.9146607661142.7846777173294.8748368836835.7950233000702.815073694350.92 51040918774.8951332251705.9551792513599.8552767353170.8853092224985.8853219017336.9453219412205.9153219412334.9253221361490.8853221409749.8153879069958.8954895990976.8957020046649.8957478373785.8957497915694.8358235876502.8959251261451.8959308628695.8959850840104.8959884575159.8960013242723.9560321931285.8963368245764.8363380833449.8365877549681.8366770214140.928042396058.88 8927262848.77 00000700<00I00M00b00g00h00i00m01401801<01A01E01L01M01R01V01Z01_01`01a01f01g01n02402J02R02Z02f03303403903>03B03F03G03H03I03M03Q03U03Z03^03_04504904N04R04S04Y04]04^04c04h04m05205705<05H05L05M05T05U05[05_05c05g05m06106606706806906@06D06QS2NS2SSS3HP0S2LI2ML2KM2KLS2VBS4SC482NS2LI2FB2SC2MLS3EP0SSS2HKS2N02NSS2LIS2LIS3V16S2SSS2ML2KMSS3V16S2R5S2N0S3BP0SSS3SK0SS2ML2KMS2LI1HS4PTOP2B03SK04ST163EP0S2SC3SC'S2SC3SC'S4SC482LI2SCS2HS2N02NS2MZSS3HP0S3OF0S2VBS2FBSSSS2NSS2SZS2SCS3V16S2MLSS4PTOP2B03SK04ST163EP0S2MLS4SC482NS2LI2FB2SC2MLS2LIFS4HS16S2HKSS3EP0S3MWRS3MWRS3MWRS3MWRS3MWRS2B03SK03EP0S2HNSS2VB2KBSS4SEPGS2HKS2K4S2B0S4PTOPS2SZS3HP0SSSS2LI2KLS2RCS2LI2FB2SC2ML".
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (MW5 : Z.land (Z.shiftr mword 5) 126 = 2 * sc) by (subst mword; apply mword_sc; lia).
  assert (MW12 : Z.land mword 18446744073709547520 = 4096 * maplen).
  { rewrite land_m4096 by lia. subst mword. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (MZ : Z.shiftr mword 12 = maplen).
  { rewrite Z.shiftr_div_pow2 by lia. subst mword. change (2^12) with 4096. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (L255 : Z.land (sxv ctr) 255 = Z.land ctr 255).
  { change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
    rewrite <- (mod_mod_pow2 (sxv ctr) 8 32), sxv_mod32, (mod_mod_pow2 ctr 8 32) by lia. reflexivity. }
  assert (OF0 : 0 <= off0 < 256).
  { subst off0. destruct (vb3 =? 0); (split; [apply Z.land_nonneg; lia|]);
      change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia. }
  assert (SK0 : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
  assert (ST16 : 16 <= stride /\ B + 16 <= P0).
  { split; [| subst P0; lia]. rewrite HS. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
    - apply andb_prop in E. destruct E as [_ E2]. destruct (Z.eqb_spec maplen 0); [discriminate|]. lia.
    - pose proof (size_class_range sc ltac:(specialize (SC48 eq_refl); lia)). lia. }
  destruct ST16 as [ST16 BP0].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. rewrite (wz_unsigned mword), MZ by lia.
  (* [comment removed for export] *)
  assert (JOIN : forall a5',
    evt usegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) (Z_to_bv 64 stride) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15ab8) fc None m (seg_rom usegs))).
  { intros a5'.
    pose proof (sxv_range ctr) as RC.
    assert (Eoff0 : off0 = (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255)) by reflexivity.
    assert (EP0 : P0 = B + 16 + stride * k) by reflexivity.
    assert (Eoff : off = fold_off off0 slack) by reflexivity.
    assert (Esl : slack = (stride - 4 - n) / 16) by reflexivity.
    clearbody off slack off0 P0 mword. clear MW1 MW5 MW12 MZ HS SC48.
    (* [comment removed for export] *)
    step. step. step. rewrite ?(wz_unsigned k), ?(wz_unsigned B), ?(unsigned_lit stride) by lia.
    (* [comment removed for export] *)
    replace (wa (P0 - 3)) with (Z_to_bv 64 (B + stride * k + 13)) in R3 by (unfold wa; f_equal; lia).
    lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
    lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
    step. rewrite ?zxb_b8 by lia. clear R3.
    (* [comment removed for export] *)
    step. rewrite HN. step. step. replace (B + stride * k + 16) with P0 by lia.
    set (p0w := Z_to_bv 64 P0). assert (HP0 : bv_unsigned p0w = P0) by (subst p0w; apply unsigned_lit; lia). clearbody p0w.
    replace (wa (P0 - 2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in R2 by (unfold wa; f_equal; lia).
    replace (wa (P0 - 4)) with (Z_to_bv 64 (bv_unsigned p0w + -4)) in R4 by (unfold wa; f_equal; lia).
    (* [comment removed for export] *)
    step. if_cases KB; zify_cond KB; rewrite ?(wz_unsigned vb3), ?(unsigned_lit vb3) in KB by lia.
    - (* [comment removed for export] *)
      clear R2. unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
      step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
      step. rewrite ?(wz_unsigned (sxv ctr)), ?L255 by lia.
      step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
      replace (Z.land ctr 255) with off0 by (rewrite Eoff0, KB; reflexivity).
      rewrite Eoff, Esl. eapply renframe_fold_walk.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
           | |- mem_inv _ _ => exact MI
           | |- wr_at _ _ _ _ => exact WR
           | |- _ => idtac end.
      all: first [lia | exact PBS].
    - (* [comment removed for export] *)
      unfold frozen in R2.
      step. rewrite ?zx16_wz by lia. clear R2. step. rewrite (wz_unsigned v16) by lia.
      unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
      step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
      step. rewrite ?(unsigned_lit (v16 + 1)) by lia.
      step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
      replace (Z.land (v16 + 1) 255) with off0 by (rewrite Eoff0; replace (vb3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Eoff, Esl. eapply renframe_fold_walk.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
           | |- mem_inv _ _ => exact MI
           | |- wr_at _ _ _ _ => exact WR
           | |- _ => idtac end.
      all: first [lia | exact PBS]. }
  (* [comment removed for export] *)
  assert (JOIN2 : forall a5', stride = 16 * size_class sc -> sc < 48 ->
    evt usegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) (wz mword) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15a9c) fc None m (seg_rom usegs))).
  { intros a5' HS16 SC'.
    lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
    lazymatch type of R3 with ?T => change T with (frozen T) in R3 end.
    lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
    pose proof (Z_shiftr_range mword 5 MWR ltac:(lia)) as R5.
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned mword) by lia. step. step. rewrite (unsigned_lit (mword ≫ 5)), MW5 by lia.
    step. step. rewrite ?(unsigned_lit (2 * sc)) by lia.
    pose proof (rsize_classes_read m sc MI ltac:(lia)) as RS. unfold RSIZE_CLASSES in RS.
    (* [comment removed for export] *)
    step. rewrite ?zx16_wz by lia.
    step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia.
    replace (size_class sc * 2 ^ 4) with stride by lia.
    apply JOIN. }
  (* [comment removed for export] *)
  step. if_cases KM; zify_cond KM; rewrite ?(unsigned_lit maplen) in KM by lia.
  - (* [comment removed for export] *)
    apply JOIN2; [| apply SC48]; rewrite ?HS; replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; lia); rewrite ?andb_false_r; cbn [negb andb]; try reflexivity.
    all: destruct (last_idx =? 0); reflexivity.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned mword), MW1 by lia.
    step. if_cases KL; zify_cond KL; rewrite ?(unsigned_lit last_idx) in KL by lia.
    + (* [comment removed for export] *)
      apply JOIN2; [| apply SC48]; rewrite ?HS; replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity.
    + (* [comment removed for export] *)
      step. step. rewrite (wz_unsigned mword) by lia. rewrite MW12.
      step. replace (4096 * maplen + -16) with stride.
      2:{ rewrite HS. replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
          replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia. }
      step. apply JOIN.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
