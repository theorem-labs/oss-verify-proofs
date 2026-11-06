(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AQConst.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF StrwF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AKitQ.
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Section IMemset.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem).
  Hypothesis MI0 : mem_inv bsegs m.
  Hypothesis AB : bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ 0 < bv_unsigned a2.
  Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 (bv_unsigned a0) (bv_unsigned a2) m).
  Notation ST pc mm x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

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
    u8arr bsegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF bsegs RNG POST (ST 0x63124 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
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
    u8arr bsegs m1 A bs -> filled (Z_to_bv 8 0) bs Q -> length bs = Z.to_nat n ->
    mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
    (forall j, 0 <= j < i -> Q j) -> 0 <= i < n -> (exists q, i = 16 * q) -> (exists q, n = 16 * q) ->
    forall x13, x13 = Z_to_bv 64 (A + i) ->
    evtF bsegs RNG POST (ST 0x63158 m1 (Z_to_bv 64 0) (Z_to_bv 64 (A + n)) x13).
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
    rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
    evtF bsegs RNG POST (ST 0x6310c m (Z_to_bv 64 0) a2 a3).
  Proof using AB MI0 RR.
    intros junk DST. pose proof MI0 as MI.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
  rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
  mem_inv bsegs m ->
  rng RNG A n ->
  evtF bsegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a4 a5 a6 a7 A n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6310c) fc None m (seg_rom bsegs)).
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
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xa2240) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xa2240, 0xa2240 + 0x81030); (0x130ac8, 0x130ac8 + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x130ac8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xa2240 (0xa2240 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xa2248 + 8 * j) (le8 (Z_to_bv 64 0))).

#[using="Type"] Lemma internal_allocator_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (ia : bool) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells bsegs m 0x98ff0 [C8 (Z_to_bv 64 0x130ae0)] -> rw_cells bsegs m 0x130ae0 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a7 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d60c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI FL IA Z2 PG1 PG2 RIMG RSTK.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  Local Ltac2 Set LiaHints.tbl := fun () => "03C0?10263081402.12210883545142.10811275736598.65 11486312769.12211805467289.61 11805467289.62 11805467289.63 11805467289.64 12208768790.10812208768790.98 12334040174.62 12389690253.12212389690253.54 12978503270.12213647586421.11114576288537.55 1546421142.98  15752505101.12217141182446.61 17316385814.96 17776320428.61 17776320431.11617776320431.61 1800609155.117 1800609155.62  1800609155.63  18835938280.11218930958230.70 18930958230.81 19627791802.12219735047526.12219861513302.11820347031482.12220404037910.11120404037910.56 21921109347.11522216746262.79 22389541692.61 22700267513.10122700267513.11322700267513.56 22700267513.57 22700267513.59 22700267513.71 22700267513.85 23222060602.12223847006446.64 24344696422.12224559830510.63 24638473347.11824638473347.62 24638473347.63 25358857070.63 25505873970.69 25819751994.12226494647592.11826494647592.12226494647592.54 26494647592.76 26568299189.76 26657728946.69 26657728946.83 26910067829.11127375013365.11127907200258.54 27907201564.10928417259964.63 29181207093.12229181207093.54 29352395194.76 31244730096.12231378308326.54 31390892533.10032188171381.99 32727271093.12233148765780.11833680001082.64 33723367410.11234430152252.64 35730135792.76 3574620722.87  35814319382.10735819387798.86 35999763510.66 36001088598.11836115622446.11736115622447.61 36115622447.62 36157221978.56 36936768494.63 37856381709.76 37945682572.82 38066443117.69 38066443117.70 38066443117.83 38586328150.11839224602138.54 40220501434.76 40333975240.86 40457739452.62 41695308149.11141969794374.70 4233133805.111 4290927915.112 42995994990.63 43059266230.52 43967450992.12243967450992.54 43987951406.11743987951406.62 43987951406.63 43988483203.11643988483203.61 43991364538.76 45221239098.63 45266465884.82 45417131125.99 45848756903.61 46468661564.63 46989140341.99 47245046632.11247279694931.54 48217982522.12248781039854.64 49649769127.64 49749326152.98 49930565050.12250046078310.12250153896121.53 51208713398.83 51711223320.10851711223320.53 51743381590.11852105090727.63 52349812658.67 52427903418.76 52541764959.84 53375371158.86 53375371158.97 53657132744.56 53703771953.12253767577775.11653767577775.61 53767577775.62 54058140533.69 54058140533.83 54243526019.11754243526019.62 54489183221.11154541959413.69 54541959413.83 54648300785.11854680338805.69 54680338805.83 55111905781.11255207105262.64 55560706911.100563227834.62   56427648749.99 57022093363.54 57622410744.11757745675194.63 578361838.61   58244463674.12258244463674.54 5854373046.68  58567281210.12258567281210.54 59028845166.62 59127789045.99 59736440626.11159750501365.99 60390525429.99 60858483367.63 61482382924.54 61492198486.11861756746921.11861756746921.12261874979822.63 62330894390.85 63235321900.11563235321900.60 63305555623.62 63706815254.56 63706815254.70 64997134979.11864997134979.63 64997134979.64 65256630714.55 65322011578.12266257009633.11866260016006.11766260016006.59 66699223528.11267474238453.69 67474238453.83 67770919157.83 67770919157.84 67832995427.11268340832757.11168555252582.1227121518413.97  757710047.112  7720336238.63  8054831726.62  8583720762.61  8690068292.122 8957257522.99  8967238126.61  9182626098.110 9237726024.70  00000100200300<00=00>00?00@00A00B00K00L00M00N00O00P00Q00R00[00\00`00d00h00i00j00k00l00m00n00o01001101201301401801901=01@01C01G01K01\01_01b01c01l01m02602702802902B02C02D02E02F02G02H02Q02W02]02^02_02c02g02k03403=03>03?03@03A03B03K03L03Q03R03V03W03X03Y03Z03[03\03`03d03h03l04504604:04C04D04M04N04O04P04Q04U04V04W04`04a04j04n04o05005405805<05=05>05?05D05H05I05J05N05O05P05Q05R05[05\05]05^05_05`05a05b05c05d05e05f05g05h05i05j05k05l06006406806906:06;06<06=06>06?06H06I06J06K06T06U06Z06c06d06k07007907:07;07<07=07>07G07H07N07O07P07Q07R07S07T07U07^07_07c07g07h07i07j07k07l07m07n07o08008708>08?08@08A08B08C08D08E08F08G08H08Q08Z08_08`08f08o090091SSSS4CEIL2LOSSSSSSS4CEIL2LOSSSSSSSS4CEIL2LOSS2LOS2LOS2LOSSSSSSSSSSSSS2HjSS2HBS1HS1HS2HqS2HqS4CEIL2LO2Hj2Hi1HS1HS1HSS4CEIL2LOSS4CEIL2LOSSSS4CEIL2LOSSSSSSS4CEIL2LOS4CEILS4CEILSSS2LOS2LOS2HBS4CEIL2LOS4CEIL2LOSSSFSS4CEIL2LOSS3SPRSS2HBSSSSSSS2LOS2LOS2LOS2HjS4CEIL2LOSS2HjS4CEIL2LOFS4CEIL2LOSSSSS2HBSFS4CEIL2LOSS4CEIL2LOS2LOSSS2LOS2LOS2LOSSSS3SPRS2HjSSS2HBSSSSS4CEIL2LOSSSSSSSSSSSSFSSSSS2LOS2LOS2LOSSSSSSSS4CEIL2LOSSFS4CEIL2LOFS3SPRS4CEIL2LOSS2Hj2HiS3SPRS4CEIL2LOSSSSSS4CEIL2LOSS4CEILSSSSSSSS4CEIL2LOSS2LOS2LOSSSSSSSSSS2Hj2HiS2Hj2HiSSSSFSSSSFS4CEIL2LOS4CEIL2LOS3SPRSS4CEILS4CEIL2LOSS".
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
    apply (munch_weaken _ [(bv_unsigned sp - 48, bv_unsigned sp); (0xa2240, 0xa2240 + 0x81030); (0x130ac8, 0x130ac8 + 4)]%Z) in MU.
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
    step. call (imemset_spec 0x123248 40); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact FR0| assumption|].
    rename POST into Z1.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0xa2240 0xa2248 (664128 + 528392) IA ltac:(lia)) as [IA0 IA1] end.
    clear IA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xa2240 0xa2248 IA0 ltac:(lia)) as [junk1 FR1] end.
    clear IA0. change (Z.to_nat (0xa2248 - 0xa2240)) with 8%nat in FR1.
    step.
    (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0xa2248 0xe2248 (664128 + 528392) IA1 ltac:(lia)) as [IA2 IA3] end.
    clear IA1.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xa2248 0xe2248 IA2 ltac:(lia)) as [junk2 DST2] end.
    clear IA2. change (0xe2248 - 0xa2248) with 0x40000 in DST2.
    step. call (imemset_spec 0xa2248 0x40000); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST2| assumption|].
    rename POST into Z2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MAP : forall j, 0 <= j < 32768 -> bytes_at bsegs mm (0xa2248 + 8 * j) (le8 (Z_to_bv 64 0)))
        by (intros j Hj; apply (cb_zero_le8 _ _ _ _ Z2); lia);
      pose proof (stk_of_cb mm 0xa2248 0x40000 _ Z2 ltac:(lia)) as IA2 end.
    clear Z2. box MAP. snapshot [(0xe2280, 0x123248); (0x130ac8, 0x130acc)]%Z MUm WMm.
    (* [comment removed for export] *)
    zstep. zstep. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0xe2248 0xe2280 (664128 + 528392) IA3 ltac:(lia)) as [IAg IA4];
      destruct (stk_split bsegs mm 0xe2280 0xe3000 (664128 + 528392) IA4 ltac:(lia)) as [IA5 IA6];
      destruct (stk_cb mm 0xe2280 0xe3000 IA5 ltac:(lia)) as [junk3 DST3] end.
    clear IA3 IA4 IA5. change (0xe3000 - 0xe2280) with 0xd80 in DST3.
    step. call (imemset_spec 0xe2280 0xd80); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST3| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe2280 0xd80 _ POST ltac:(lia)) as IA5 end.
    clear POST.
    (* [comment removed for export] *)
    step. zstep. zstep. zstep. step.           (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cb mm 0xe3000 (664128 + 528392) IA6 ltac:(lia)) as [junk4 DST4] end.
    clear IA6. change (664128 + 528392 - 0xe3000) with 0x40248 in DST4.
    step. call (imemset_spec 0xe3000 0x40248); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact DST4| assumption|].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_of_cb mm 0xe3000 0x40248 _ POST ltac:(lia)) as IA6 end.
    clear POST.
    (* [comment removed for export] *)
    step. step. step. step. if_lit.            (* [comment removed for export] *)
    zstep. zstep. zstep. step.                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm 0xe3000 0xe3010 (0xe3000 + 0x40248) IA6 ltac:(lia)) as [IA7 IA8];
      destruct (stk_cb mm 0xe3000 0xe3010 IA7 ltac:(lia)) as [junk5 FR5] end.
    clear IA6 IA7. change (Z.to_nat (0xe3010 - 0xe3000)) with 16%nat in FR5.
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep.                               (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_of_rw_cells bsegs mm _ _ FR1) as Q0; cbn [cells_size csize Nat.add] in Q0;
      pose proof (stk_of_rw_cells bsegs mm _ _ FR5) as Q5; cbn [cells_size csize Nat.add] in Q5;
      pose proof (stk_of_cb mm _ _ _ Z1 ltac:(lia)) as Q1 end.
    assert (IA : stk bsegs m1 0xa2240 (0xa2240 + 0x81030)).
    { eapply stk_merge3; [exact Q0| exact IA2| | lia| lia].
      eapply stk_merge3; [exact IAg| exact IA5| | lia| lia].
      eapply stk_merge3; [exact Q5| exact IA8| exact Q1| lia| lia]. }
    unfold ia_post. finish.
    intros j Hj. unbox MAP. eapply bytes_at_agree; [apply (MAP j); lia|].
    intros i Hi. apply MUm. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
