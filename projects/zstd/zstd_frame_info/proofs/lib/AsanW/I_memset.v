(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells ShadowTac F_memset F_rip.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition memset_i_entry := 0x51458%Z.

Definition memset_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (junk : list byte) (RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
                  [CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
    /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.

  #[using="m ST LO KLO APPD NSZ R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    Local Ltac2 Set LiaHints.tbl := fun () => "0010>29786661831.66000004S2Rn".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LED AD R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].   (* [comment removed for export] *)
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
  #[using="m ST LO KLO APPD NSZ R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62904913180.6200000:S2LO3NSZ1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1 & UD1 & WR21).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  #[using="ST LO KLO APPD UDST NSZ R2 WR2"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0020>11807744665.7733470593740.7900000600:S2R21BS2H2".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x514ec) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00L0?11799456952.98 11801586693.11011801586693.11114540549476.11414684412918.10716852238724.10717231150308.11417607716380.11519031052389.11522580318183.11322700267513.10125250094364.114260657820.114  27914623132.11431655642334.10635834628839.11335973911964.11537601013348.11438214514495.10644484923210.1105226650179.111 53295060839.11353723688860.11457540799784.97 66283099932.11568577416220.1167850239254.107 8794126823.113 00000=00J00K00L00M00Q00R00S00T00U00X00Y00Z00[00\00]00^00_00`00f00g00h00i00m00n00o010011S4SEPD2R23BL0S4SEPD2R23BL0FSSS2LOSSSSS1HSSSSSSSSS4SEPDFSSS2LOSSSS".
prep IV.
    assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    zstep. zstep. zstep.
    unfold sf_hide in SEPD.
    apply (munch_weaken _ [(bv_unsigned sp + -2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR21.
    call memset_spec; [exact DST1 | exact MI1 |].
    do 11 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x51620) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13708355367.10213732943226.10224120772675.10240339170390.10641502378089.10050781112641.10057540799784.97 59308585478.97 59308627018.1  60888476447.10262863995381.10600000700C00K00V00]00d00k01201601D01ES2Hk2HcS2Hk2Hc2SL1KS3BL02HkS3BL02Hk2HcS2Hk2HcS2Hk2HcS2LO2HkS2Hk2HcS2K'S3BL02Hk2Hc2SLF".
prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
               (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x51604) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?19482125344.10819482125345.10724122881528.99 24991237562.10829782203372.10429784416728.99 30507626521.94 3421727977.99  36004493144.94 37100885899.10443614754995.94 52076332689.10552523015476.10653510313883.10756209684249.98 57540799784.93 59308629082.1  67298533313.98 68646946464.94 00000500:00?00@00A00B00C00G00H00N00O00W00X00Y00Z00^00b00g00kS3CK2S3CK2S3BL0SSSSS2K6SS2N11BSS2N13BL0SSSS2LOS2K7S3CK2S2N1".
prep IV.
    destruct (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma LB : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x51494) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00a0?11447729195.16111801586693.1221606899715.8   16917719815.12221665481682.11123068901782.11823260809484.10223260842252.10024115025142.11024122799997.10029782203372.11129782203372.11230010325480.10031247978648.10031824352466.11131885183527.1033210808038.112 35895327997.12236986663037.12239547979280.10240886601363.11140886601363.11242148837058.10044484923210.12247018790687.10247019085599.10049610168957.12249852543712.10049852904160.10250216114301.12251845486909.98 52076332702.11052733105242.10152733105242.10356172410654.10057540799784.96 57880736640.112585992346.101  5876716948.99  59308628304.98 59308628695.1  60274602806.10462806329641.97 63407398368.10063407889888.10264073056942.1007744853832.103 7848643581.122 9405451517.122 00000100600>00?00@00A00E00I00N00S00T00U00V00[00\00a00b00k01401?01E01K01P01Q01U01Y01b01f01j02302802@02E02J02K02O02P02S02T02\02`02g02l03003403?03@03I03RFS3HspS3BL02K2FSSS2R2S2R2S3BL0S3BL0SSSS3BL0SS3BL0FS3BL03HspS3BL03HspS2R23BL02N1S2N11BS2N11BS3BL0FS2R2S2R2S3BL03HspS2R2S2R2S3BL03HspS3BL0S3BL02N1S3BL0S3BL0SS2LOFS1BFS3BL02K1S2K4S3BL01HS3BL0S2R2S2R2S2R23BL02N1FS3BL03HspS3BL03Hsp".
prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      do 5 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; eassumption.
      + eapply LX; exact IV0.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="junk RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma memset_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x51458) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    Local Ltac2 Set LiaHints.tbl := fun () => "01S0>10499999408.7611712989376.8011799361125.7911799361125.8011799361125.8111799361125.8212371295384.8013177412632.7914540549476.7714971218840.8015300726187.8016390485400.8017231150308.7717607716380.7817748760128.7817793405592.8018472667160.8118486058859.6518542239966.7718795919531.7919031052389.7820264391448.7921179061016.7922537331120.7922580318183.7623342567448.7923766180800.7723781151384.8125250094364.7625624991000.82260657820.77  2644808984.82 27914623132.7728252944920.8128521959216.7829094024344.8029768397120.7930041986200.8030301036312.813091892504.81 31262483992.8132018305688.8132648281752.8032824455704.8134496658584.8034540297392.7834844613528.8035281682200.8135834628839.7635973911964.7836003610136.8237033834392.8037601013348.7738300552235.8038515848600.8040600447536.7740808938648.8041389258667.7942211160088.7943061432073.6743649743150.7743821196696.8045545526552.7946412915608.8046586017712.7848377235864.8148454161048.8150432113816.8052473359256.8052637746480.7752689461784.8153295060839.7553324180011.8153723688860.7755120970136.8156347265304.8156367821504.795695863616.78 57540799784.6459308628179.1 60245500312.8160858764075.8060891612184.8261428698795.7961837739032.8262371084587.7862393598016.7863719325464.8163971998950.6964640737328.7764777566744.816490496664.80 66283099932.786781596952.82 68412599744.7968577416220.798794126823.76 9014990744.80 9454272280.81 00000100500600700800900>00C00D00I00M00R00S00T00X00]00b00f00g00k00l01101601701801=01A01F01G01L01M01R01S01X01Y01^01b01g01l02102602;02@02E02J02K02P02U02V02W02\02a02b02f02k02l03103503:03?03@03E03J03O03P03U03Z03_03d03e03j03k03o04004504:04>04B04F04J04O04S04X04\04a04e04i04n04o05005505:05;05@05D05E05F05K05PSS2HBSSSSS3BL0S3BL0SS3BL0S2HBS3BL0SSS2HBS3BL0S3BL0S2LOSS2HBSS3BL0S3BL0SSS3BL0S2HBS3BL0SS3BL0SS3BL0SS3BL0SS3BL0S2HBS3BL0S3BL0S3BL0S3BL0S3BL0S3BL0S3BL0S3BL0SS3BL0S3BL0SSS3BL0S3BL0SS2HBS3BL0SS3BL0S2HBS3BL0S3BL0SS3BL0S3BL0S3BL0SS3BL0S3BL0S3BL0S3BL0SS3BL0SS2HBSS3BL0S3BL0S2HBS2HBS2LOS2K0S3BL0S2HBS3BL0S2HBS3BL0S2HBS2HBS3BL0SSS3BL0S3BL0SS3BL0S2HBSSS3BL0S3BL0".
assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    change (?P) with (sf_hide P) in DST.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    carve_frame 2144%nat ST0.
    do 11 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    eapply LB. eapply inv_of; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.

#[using="Type"] Lemma memset_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51458) fc None m (seg_rom asegs)).
Proof. intros. eapply memset_i_body; eassumption. Qed.
End CANSEC1.
