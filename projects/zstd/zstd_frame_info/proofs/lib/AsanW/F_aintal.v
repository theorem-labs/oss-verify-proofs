(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AQConst.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF StrwF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AKitQ.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a4 a5 a6 a7 : word) (A n : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3' t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Section IMemset.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis AB : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ 0 < bv_unsigned a2.
  Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 (bv_unsigned a0) (bv_unsigned a2) m).
  Notation ST pc mm x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac with_arr tac :=
    lazymatch goal with
    | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
    end.
  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    unfold imemset_post; finish; subst; assumption.

  (* [comment removed for export] *)
  Lemma imemset_bloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF asegs RNG POST (ST 0x63120 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi x13 ->.
    Local Ltac2 Set LiaHints.tbl := fun () => "0090>11469010974.5812527860964.5519628481055.5531168967626.5835987002189.555120842925.58 67692313067.547739161719.55 8929161887.55 00000=00K00\01201@01K01\01d025S2HK3LEN2Hj1lS2HK2Hi3LEN2KKS2AB2R02HK2Hi3LENS2HK3LEN2Hj1l2AB2Hi2KKS2AB2HK2Hi3LENS2HK3LEN2HiS2AB2R02HK3LEN2HiS2HK3LENS2AB2R02HK2Hi3LEN".
mst i 1%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      eapply (IH (Z.to_nat (n - (i + 1))) ltac:(lia) (i + 1) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia|f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia].
    - zstep. fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; apply HQ; lia| right; lia]).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Lemma imemset_wloop : forall (K : nat) (i : Z) (m1 : amem) (bs : list byte) (Q : Z -> Prop),
    Z.to_nat (n - i) = K ->
    u8arr asegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> (exists q, i = 16 * q) -> (exists q, n = 16 * q) ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF asegs RNG POST (ST 0x63154 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
  Proof using AB RR.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    induction K as [K IH] using lt_wf_ind; intros i m1 bs Q HK ARR FIL LEN MI MU WM HQ Hi [qi Hqi] [qn Hqn] x13 ->.
    Local Ltac2 Set LiaHints.tbl := fun () => "00?0>11469010974.6215334889917.6215524692031.5922522182488.5832466410975.693256324148.63 34339459430.6335987002189.5940132705702.7045230111716.5950278918646.5950432419481.5966492033975.5967694409198.588929161887.59 00000=00S00l01E01[02202?02P02X02f03803J03R03k04DS2HK3LEN2Hj1lS2AB2HK3LEN2Hi3Hqi3HqnS2AB2R02HK2Hi3Hqi3Hqn3LENS2AB2R02HK2Hi3Hqi3Hqn3LENS2AB2HK2Hi3Hqi3Hqn3LENS2HK3LEN2Hj2l02AB2Hi2KKS2HK3LEN1l2l0S2AB2HK2Hi3LEN2KKS2HK3LENS2HK2Hi3LEN2KKS2AB2HK2Hi3Hqi3LENS2AB2HK2Hi3Hqn3LENS2HK3LENS2AB2R02HK3LEN2Hi3Hqi3HqnS2AB2R02HK2Hi3Hqi3Hqn3LEN".
mst i 8%nat ltac:(reflexivity).
    mst (i + 8)%Z 8%nat ltac:(reflexivity).
    zstep. zstep. if_cases KK; zify_cond KK.
    - eapply (IH (Z.to_nat (n - (i + 16))) ltac:(lia) (i + 16) _ _ _ eq_refl ARR FIL LEN MI MU WM); [|lia| exists (qi + 1); lia| exists qn; lia| f_equal; lia].
      intros j Hj. destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|]. destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia].
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j i); [left; left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (i + 8)); [left; right; lia| right; lia]).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Lemma imemset_body : forall junk,
    rw_cells asegs m A [CB (Z.to_nat n) junk] ->
    evtF asegs RNG POST (ST 0x63108 m (Z_to_bv 64 0) a2 a3).
  Proof using AB MI0 RR.
    intros junk DST. pose proof MI0 as MI.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 0) junk) as FIL.
    zstep. zstep.
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>40825300077.5043549202818.4943549254066.5043833420478.5054385497688.5055514599560.5059308586377.5159308586377.5259308628304.4960706498226.4800000500=00E00V00[00i01101901D01IS3LENS2AB3LENS2AB3LENS2AB2R03LEN2Kn2KAS3LENS2AB2R03LEN2HAS3LEN2HjS3LEN2HjS2AB3LEN2K1S3LEN".
if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      do 7 zstep. zstep.
      assert (HA : A mod 16 = 0 /\ n mod 16 = 0).
      { rewrite Z.land_lor_distr_l in K0. apply Z.lor_eq_0_iff in K0. destruct K0 as [Kn KA].
        change 15 with (Z.ones 4) in Kn, KA. rewrite Z.land_ones in Kn, KA by lia. change (2^4) with 16 in Kn, KA. lia. }
      eapply (imemset_wloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| exists 0; lia| exists (n / 16); lia| symmetry; apply Z_to_bv_plus0].
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      zstep. zstep.
      eapply (imemset_bloop (Z.to_nat (n - 0)) 0 m _ _ eq_refl ARR FIL LEN MI MU WM); [intros j Hj; lia| lia| symmetry; apply Z_to_bv_plus0].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End IMemset.

#[using="Type"] Lemma imemset_spec : forall (A n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (junk : list byte),
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 n -> 0 <= A -> 0 < n -> A + n < 2^64 ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  mem_inv asegs m ->
  rng RNG A n ->
  evtF asegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 A n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x63108) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros -> -> -> HA Hn HAn DST MI RR.
  pose proof (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI) as H.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>28807763462.435619512016.43 61927656618.4300000;00C00NS2HA2Hn3HAnS2Hn3HAnS2HA2Hn3HAn".
rewrite !unsigned_lit in H by lia. apply (H ltac:(lia) RR junk DST).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=   (* [comment removed for export] *)
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xa2080) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xa2080, 0xa2080 + 0x81030); (0x130908, 0x130908 + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x130908 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk asegs m' 0xa2080 (0xa2080 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xa2088 + 8 * j) (le8 (Z_to_bv 64 0))).

#[using="Type"] Lemma internal_allocator_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ia : bool) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells asegs m 0x98e18 [C8 (Z_to_bv 64 0x130920)] -> rw_cells asegs m 0x130920 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d608) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI FL IA Z2 PG1 PG2 RIMG RSTK.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "03C0?1029061855.112 10322388026.12210322388026.54 10678428854.68 11382190574.61 11383668557.97 11647286254.61 11716686062.64 11805467289.61 11805467289.62 11805467289.63 11805467289.64 12208768790.10812208768790.98 13313378710.65 13324683698.69 13324683698.83 13373187642.12213981348533.76 14286730093.69 14286730093.70 14286730093.83 15196958054.12215359466822.70 15463508213.83 15463508213.84 16314008053.10016577348149.12216577348149.54 17108665461.99 1733952373.69  1733952373.83  17776320428.61 17776320431.11617776320431.61 1800609155.117 1800609155.62  1800609155.63  1878909846.98  18930958230.70 18930958230.81 1924221764.122 20140320437.12220404037910.11120404037910.56 21537764200.11221921109347.1152200994037.69  2200994037.83  22389541692.61 22503210696.86 22700267513.10122700267513.11322700267513.56 22700267513.57 22700267513.59 22700267513.71 22700267513.85 23309688626.1112356674933.69  2356674933.83  23630880698.12224485175024.12224638473347.11824638473347.62 24638473347.63 24774394966.11824812739566.63 25259226101.11125359426490.76 25882472949.11226196785238.11826389341780.11826494647592.11826494647592.12226494647592.54 26494647592.76 26565674554.12226643078230.11827778003822.63 27907200258.54 27907201564.10927997757027.11228244197298.67 28417259964.63 28554063989.69 28554063989.83 28981197552.76 2993314286.61  29980125965.76 30337625205.99 30603927662.62 31378308326.54 31477130326.11832665237229.99 33680001082.64 33943096374.66 34057641259.11234430152252.64 35015851720.56 36115622446.11736115622447.61 36115622447.62 36151843734.86 36157221978.56 36654913774.64 37218512752.12237218512752.54 37845668334.63 37945682572.82 3805929914.76  38616101306.76 38814555112.1123891106746.76  39110875637.11139224602138.54 39754443706.12239813362070.96 40046767273.11840046767273.1224019174645.99  40457739452.62 40765835058.99 42044441841.11842488118638.63 43059266230.52 43987951406.11743987951406.62 43987951406.63 43988483203.11643988483203.61 44069254645.99 44691966965.99 4509240205.122 4509240205.54  45221239098.63 45266465884.82 45315213813.99 45823321905.12245848756903.61 46468661564.63 47279694931.54 48180355634.87 48240850362.12248339482809.53 48504422806.79 48622336054.85 48962187194.12249190166253.11149649769127.64 49750950894.63 50306151606.83 50682779066.12250935185394.11251711223320.10851711223320.53 51837085242.12252105090727.63 53135533173.11153289116917.11153375371158.86 53375371158.97 53767577775.11653767577775.61 53767577775.62 54055774778.12254055774778.54 54243526019.11754243526019.62 54453305650.1105535658070.118 56138800742.122563227834.62   56426498662.12257022093363.54 57622410744.11757745675194.63 58376559585.11860132729672.70 60176644150.10860858483367.63 60913556319.10060939531615.84 61439603310.62 61482382924.54 62040152470.10762891150694.12263235321900.11563235321900.60 63305555623.62 64031177494.56 64031177494.70 64307395438.63 64650279534.62 64997134979.11864997134979.63 64997134979.64 65256630714.55 65492910130.69 66260016006.11766260016006.59 66397490293.1116656565736.112 66686409032.98 66848280053.11167517576806.12267618838849.12268501319406.64 7876249357.122 8583720762.61  9702425369.55  00000100200300400=00>00G00P00Q00R00S00T00U00V00W00]00c00d00m01601701@01A01B01C01D01E01N01W01X01Y01Z01^01b01f01g01h01i01j01k01l01m02602702802902=02>02?02C02D02G02J02N02R02c02f02i02o03003103203303403503603703@03A03B03C03D03E03F03G03H03I03J03K03T03X03\03]03^03b03c03d03e03n03o04004904:04;04D04I04J04K04O04P04T04X04\04]04a04j04k04l05505905:05;05<05=05>05?05@05A05B05C05D05H05N05W05`05d05h05l06006106206306406506606;06?06@06A06B06F06G06H06I06J06K06L06M06V06W06`06a06b06c06d06e06f06g06h06i06j06k06o07307707807907:07;07<07=07>07C07D07E07L07Q07R07S07T07U07V07W07`07a07b07c07g07k07l07m07n08708@08A08B08C08D08E08L08S08T08U08V08W08X08a08j08k090091FSSSS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSSSSSSS4CEILS4CEILSS4CEIL2LOS4CEIL2LOFS4CEIL2LOSFSFFS4CEIL2LOS4CEIL2LOSSSS2LOS2LOS2LOSSSSSSSS4CEIL2LOSSSS2HjSSS2HBSS1HS1HS2HqS2HqS4CEIL2LO2Hj2Hi1HS1HS1HS4CEILSSSSSSSSS4CEIL2LOSSFSSSSSSSSS4CEIL2LOS2LOS2LOSSS2HBSSSS4CEIL2LOSSS4CEIL2LOSSS4CEIL2LOS3SPRSSS2HBSS2LOS2LOS2LOSS2HjS4CEIL2LOSSS4CEIL2LOS2HjSSSSSSSSSSSS2HBS4CEILS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS2LOSSSSSSS3SPRS2HjSSSS2HBSSSSSSSS4CEIL2LOSS4CEIL2LOSSSSSSSSSSSS2LOS2LOS2LOSSSSSSSS3SPRSSS2Hj2HiS3SPRSSSSFFS4CEIL2LOSSSS2LOS2LOSSSS4CEIL2LOS4CEIL2LOSSSSSS2Hj2HiS2Hj2HiSSSSSS4CEIL2LOS4CEIL2LOSS3SPRS".
carve_frame 48%nat ST.
  do 6 step.                                   (* [comment removed for export] *)
  step. zstep.                                 (* [comment removed for export] *)
  destruct ia.
  - (* [comment removed for export] *)
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold ia_post. finish.
    + eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros q Hq; lia.
    + intros j Hj. pose proof (Z2 eq_refl j ltac:(lia)) as B. eapply bytes_at_agree; [exact B|].
      intros i Hi. apply MU. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
  - (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (0xa2080, 0xa2080 + 0x81030); (0x130908, 0x130908 + 4)]%Z) in MU.
    2:{ unfold sub_fp; cbn [outside]; intros q Hq; lia. }
    clear Z2.
    lstep. step. step. if_lit.                 (* [comment removed for export] *)
    do 8 zstep.                                (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in FL. change (0 + 256 * 0) with 0 in FL.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. zstep. step. if_lit.                (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 0 1 ltac:(lia) ltac:(lia)) in FL.
    lstep. step. if_lit.                       (* [comment removed for export] *)
    step. step. zstep. zstep. zstep. step. step.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 40%nat IA.
    step. call (imemset_spec 0x123088 40); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact FR0| assumption|].
    rename POST into Z1.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xa2080 0xa2088 (663680 + 528392) IA ltac:(lia)) as [IA0 IA1] end.
    clear IA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xa2080 0xa2088 IA0 ltac:(lia)) as [junk1 FR1] end.
    clear IA0. change (Z.to_nat (0xa2088 - 0xa2080)) with 8%nat in FR1.
    step.
    (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xa2088 0xe2088 (663680 + 528392) IA1 ltac:(lia)) as [IA2 IA3] end.
    clear IA1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xa2088 0xe2088 IA2 ltac:(lia)) as [junk2 DST2] end.
    clear IA2. change (0xe2088 - 0xa2088) with 0x40000 in DST2.
    step. call (imemset_spec 0xa2088 0x40000); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST2| assumption|].
    rename POST into Z2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MAP : forall j, 0 <= j < 32768 -> bytes_at asegs mm (0xa2088 + 8 * j) (le8 (Z_to_bv 64 0)))
        by (intros j Hj; apply (cb_zero_le8 _ _ _ _ Z2); lia);
      pose proof (stk_of_cb mm 0xa2088 0x40000 _ Z2 ltac:(lia)) as IA2 end.
    clear Z2. box MAP. snapshot [(0xe20c0, 0x123088); (0x130908, 0x13090c)]%Z MUm WMm.
    (* [comment removed for export] *)
    zstep. zstep. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xe2088 0xe20c0 (663680 + 528392) IA3 ltac:(lia)) as [IAg IA4];
      destruct (stk_split asegs mm 0xe20c0 0xe2e40 (663680 + 528392) IA4 ltac:(lia)) as [IA5 IA6];
      destruct (stk_cb mm 0xe20c0 0xe2e40 IA5 ltac:(lia)) as [junk3 DST3] end.
    clear IA3 IA4 IA5. change (0xe2e40 - 0xe20c0) with 0xd80 in DST3.
    step. call (imemset_spec 0xe20c0 0xd80); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST3| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe20c0 0xd80 _ POST ltac:(lia)) as IA5 end.
    clear POST.
    (* [comment removed for export] *)
    step. zstep. zstep. zstep. step.           (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xe2e40 (663680 + 528392) IA6 ltac:(lia)) as [junk4 DST4] end.
    clear IA6. change (663680 + 528392 - 0xe2e40) with 0x40248 in DST4.
    step. call (imemset_spec 0xe2e40 0x40248); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST4| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe2e40 0x40248 _ POST ltac:(lia)) as IA6 end.
    clear POST.
    (* [comment removed for export] *)
    step. step. step. step. if_lit.            (* [comment removed for export] *)
    zstep. zstep. zstep. step.                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split asegs mm 0xe2e40 0xe2e50 (0xe2e40 + 0x40248) IA6 ltac:(lia)) as [IA7 IA8];
      destruct (stk_cb mm 0xe2e40 0xe2e50 IA7 ltac:(lia)) as [junk5 FR5] end.
    clear IA6 IA7. change (Z.to_nat (0xe2e50 - 0xe2e40)) with 16%nat in FR5.
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_rw_cells asegs mm _ _ FR1) as Q0; cbn [cells_size csize Nat.add] in Q0;
      pose proof (stk_of_rw_cells asegs mm _ _ FR5) as Q5; cbn [cells_size csize Nat.add] in Q5;
      pose proof (stk_of_cb mm _ _ _ Z1 ltac:(lia)) as Q1 end.
    assert (IA : stk asegs m1 0xa2080 (0xa2080 + 0x81030)).
    { eapply stk_merge3; [exact Q0| exact IA2| | lia| lia].
      eapply stk_merge3; [exact IAg| exact IA5| | lia| lia].
      eapply stk_merge3; [exact Q5| exact IA8| exact Q1| lia| lia]. }
    unfold ia_post. finish.
    intros j Hj. unbox MAP. eapply bytes_at_agree; [apply (MAP j); lia|].
    intros i Hi. apply MUm. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
