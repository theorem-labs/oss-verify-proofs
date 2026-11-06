(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells ShadowTac F_syscalls F_tryinit F_rip.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition read_i_entry := 0x433d4%Z.

(* [comment removed for export] *)
Definition read_i_post (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => RNG' = RNG /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells asegs m' B [CB n junk]
                    /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells asegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z).
  Notation B := (bv_unsigned a1).
  Notation W := [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + count); (errno_addr tp, errno_addr tp + 4)]%Z.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_read m.
  Hypothesis DST : rw_cells asegs m B [CB (Z.to_nat count) junk].
  Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
  Hypothesis A0 : a0 = Z_to_bv 64 fd.
  Hypothesis A2 : a2 = Z_to_bv 64 count.
  Hypothesis FD : (3 <= fd < 2^32)%Z.
  Hypothesis CNT : (1 <= count <= 16777216)%Z.
  (* [comment removed for export] *)
  Hypothesis BHI : (0x5f6000 <= B \/ (0x5c34d0 <= B /\ B + count <= 0x5d34d0 /\ B + count <= errno_addr tp))%Z.
  Hypothesis SEPD : (B + count <= lo)%Z.                  (* [comment removed for export] *)
  Hypothesis SEPE : (0xa2080 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f6000)%Z.   (* [comment removed for export] *)
  Hypothesis TP : (164 <= bv_unsigned tp)%Z.
  Hypothesis APPD : app_blk B (B + count).
  Hypothesis UDST : unpoisoned m B (B + count).
  Hypothesis R2 : (RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RERR : rng RNG (errno_addr tp) 4.
  Hypothesis RD : rng RNG B count.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m).

  (* [comment removed for export] *)
  Definition INV2 (bs : list byte) (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2128)
    /\ munch W m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_read mc
    /\ unpoisoned mc B (B + count)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2)
    /\ rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)]
    /\ rw_cells asegs mc (errno_addr tp) [C4 errv]
    /\ (length bs <= Z.to_nat count)%nat.

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 1 <= count <= 16777216
     /\ 0x5c34d0 <= B /\ (0x5f6000 <= B \/ B + count <= 0x5d34d0 /\ B + count <= errno_addr tp) /\ B + count <= lo /\ B + count + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr B 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= B /\ B + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0
     /\ 0xa2080 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f6000)%Z.

  #[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    Local Ltac2 Set LiaHints.tbl := fun () => "0010>29786661831.75000001S".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
    Z.div_mod_to_equations. nia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac acc_facts Bf ::= pose proof BND_ok as Bf; unfold BND, KHIGH, KEND in Bf.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 1 <= count <= 16777216 /\ 0x5c34d0 <= B /\ (0x5f6000 <= B \/ B + count <= 0x5d34d0 /\ B + count <= errno_addr tp) /\ B + count <= lo
     /\ B + count + 8 <= 2^47 /\ 0 <= Z.shiftr B 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad B /\ shad (B + count - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296
     /\ 0xa2080 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f6000)%Z.
  #[using="m ST LO KLO CNT BHI SEPD SEPE APPD R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62898626424.7200000IS2LO3CNT3BHI4SEPD4SEPE2Bf".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1 & INI1 & LAY1 & REAL1 & UD1 & WR21 & BUF1 & ERR1 & LENB).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let Bl := fresh "BL" in pose proof BL_ok as Bl; unfold BL in Bl;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in ERR; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.

  #[using="ST LO KLO CNT BHI SEPD SEPE APPD UDST R2 WR2"] Lemma inv2_of : forall bs mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2080 jk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2128) ->
    munch W m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_read mc ->
    rw_cells asegs mc B [CB (length bs) bs; CB (Z.to_nat count - length bs) (skipn (length bs) junk)] ->
    rw_cells asegs mc (errno_addr tp) [C4 errv] -> (length bs <= Z.to_nat count)%nat ->
    INV2 bs mc.
  Proof.
    intros bs mc jk FR ST1 MU1 WM1 MI1 G1 G3 G4 G5 G6 BUF1 ERR1 LENB. pose proof BND_ok as Bf. unfold BND, KHIGH, KEND in Bf.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : (shad (B + count - 1) + 1 <= 17594333495296 /\ 2147450880 <= shad B /\
                  (B + count <= shad B \/ shad (B + count - 1) + 1 <= B))%Z).
    { pose proof APPD as [_ AD]. unfold KLOW, KHIGH, KEND in AD. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0020>26494383029.8938821100026.8900000G00[S3CNT3BHI2R24LENB2Bf2SSS3CNT3BHI4LENB2Bf2AD".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. lia. }
    split. { eapply wr_at_transport; eassumption. }
    repeat (split; [assumption|]). assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD SEPE APPD R2 RSTK"] Lemma LX : forall bs mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 (Z.of_nat (length bs))) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x43484) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00@0?15498737820.1181807322596.118 25820099228.11928053229631.11035378896924.11835854634524.1193602932068.118 37031752369.11046703417572.11849475153977.11150221378407.11752415237221.11958390049052.12066138656668.1196922740008.110 7944451815.117 00000600<00B00H00N00T00Z00d00j01401:01@01F01L01U01[S4LENBS4LENBS4LENBS4LENBS4LENBS4LENBS4LENBS3CNT4LENBS4LENBS4LENB3BL0S4LENBS4LENBS4LENBS4LENBS2LO4LENBS4LENB".
prep IV.
    do 9 zstep.
    release_frame FR ST1 (bv_unsigned sp). unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD SEPE APPD R2 RSTK RSH2"] Lemma LSL : forall bs mc (k : nat) (c : Z) x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    Z.to_nat (shad (B + Z.of_nat (length bs) - 1) - c) = k -> (shad B <= c < shad (B + Z.of_nat (length bs) - 1))%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)) (Z_to_bv 64 0) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x435e8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00<0?13708355367.11613732943226.11624120772675.11640339170391.12144092989940.12157132210400.11457930470673.11159308585478.11159308627018.1  60888476447.1166734743638.114 6922740008.110 00000@00]01701R01S01_01o02?02C02Z03503AS3CNT4LENB2Hk2HcS3CNT3BHI4LENB3BL02Hk2Hc2SL1KS3CNT4LENB3BL02SM2Hk2Hc2SLS3CNT3BHI4LENB3BL02SM2Hk2HcFS4LENB2Hk2HcS3CNT4LENB2Hk2HcS3CNT4LENB2Hk2HcS2K'S3CNT4LENB3BL02SM2Hk2HcS3CNT3BHI4LENB2N13BL02Hk2HcS2LO4LENB2Hk".
prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    revert c x14 Hk Hc. induction k as [|k IH]; intros c x14 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (B + Z.of_nat (length bs) - 1) = 2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3)%Z)
      by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc B (B + count) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD SEPE APPD R2 RSTK RSH2"] Lemma LSS : forall bs mc x1 x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc -> (1 <= Z.of_nat (length bs) <= 64)%Z ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               (Z_to_bv 64 (2147450880 + Z.shiftr B 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (B + Z.of_nat (length bs) + -1) 3))
               (Z_to_bv 64 (B + Z.of_nat (length bs) + -1)) x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2120)) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x435cc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00D0?19482125347.12424122881528.11424991237561.12429782203372.12029784416728.11430511807874.1093421727977.114 36641402764.10937100885899.12043610543400.10952076332689.12052523015483.12253364399459.10853510313881.12456209684249.11357930470673.10759308629082.1  59949010196.10967298533313.1136922740008.106 00000I00S00Y00_00e00k01C01M01d01j02?02E02N02T02Z02d02h03103G03PS3CNT3BHI4LENB2N13BL03CK2S4LENB3BL0S4LENBS4LENBS4LENBS4LENBS3CNT3BHI4LENB2N13BL02K6S3CNT4LENBS3CNT3BHI4LENB2N13BL01BS4LENBS3CNT3BHI4LENB2N13BL0S4LENBS4LENB2N1S4LENBS4LENBS3CNT4LENBS2K7S4LENB2N1S3CNT3BHI4LENB3BL03CK2S2LO4LENB".
prep IV.
    pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
    pose proof (shad_mono B (B + Z.of_nat (length bs) - 1) ltac:(lia)) as SM2.
    destruct (unpoisoned_check_rd asegs mc B (B + count) (B + Z.of_nat (length bs) + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((B + Z.of_nat (length bs) + -1) mod 8) (sval b2)) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LSL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="ST LO KLO CNT BHI SEPD SEPE APPD UDST R2 WR2 RI RSTK RSH2"] Lemma LC : forall bs mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    INV2 bs mc ->
    evtF asegs RNG (POST (RdData bs) RNG)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp a1 (Z_to_bv 64 (Z.of_nat (length bs)))
               x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x43424) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "0100?11447729195.17811447729323.19111801586693.13816073429258.11916075443317.11616075584073.11416917719815.13821665481682.12723009804051.11623260809484.11823260842252.11624115025141.12724122799997.11627923658942.11229782203372.12829782203372.1292996087336.121 30010325480.11631824352466.12731885183527.1193210808038.129 35895327997.13836200717662.11236986663037.13838168593942.13438525121917.13839547979280.11839677217177.11640243440868.12840886601363.12840886601363.12941055186995.11341123052556.11642148695032.11643374880621.11244484923210.13846186857798.10946766756607.12 47018790687.11847019085599.11647803503873.11648325108386.11649610168957.13849852543712.11649852904160.11849921929014.12051845486909.11452074235542.12852735198782.11752735198782.11956172530212.11657880736640.12957915647498.1155876716948.115 59308628179.1  59308628304.11459308628695.1  62348280136.11963407398368.11663407889888.11864368761933.11664659114050.1166922740008.108 9405451517.138 00000100e01E01R01_01l01m02302<02E02N02X02b02o03503;03G03M03S03o04004E04K04`04f05;05P05Y05Z06;06O06a07607@07I07J07T07_07h08108;08E08Z08k09<09L09^0:30:=0:G0:M0:N0:W0:X0:\0:m0;10;20;?0;L0;R0;\0;e0<:FS3CNT3BHI4LENB3BL01H2H02H42H52H93H103H143H153H193H20S3CNT2R24LENB3BL03Hsp2LO4SEPD2RrS3CNT4LENB2RrS3CNT4LENB2RrS3CNT4LENB2RrFS4LENBS4LENB2RrS2R24LENBS2R24LENBS4LENB3BL0S4LENB3BL0S3CNT4LENB2RrS4LENBS4LENBS4LENB2KZ2N1S4LENBS4LENBS3CNT3BHI4LENB3BL03R1'2K22SMFS3CNT2R24LENB3BL03HspS4LENBS3CNT2R24LENB3BL03HspS4LENBS3CNT2R24LENB3BL03HspS3CNT3BHI2R24LENB3R1'S4LENB2RrFS3CNT3BHI4LENB3BL02Rr3R1'2K22N11BS3CNT3BHI4LENB3BL01BS3CNT3BHI4LENB3BL0S3CNT3BHI2R24LENB3R1'S4LENB3BL0S4LENB2KZFS3CNT4LENBS3BL02Rr2K2S2R24LENBS2R24LENBS3CNT4LENBS4LENB3BL0S3CNT2R24LENB3BL03HspS3CNT3BHI2R24LENBS3CNT3BHI2R24LENBS3CNT4LENB3BL01HS3CNT3BHI4LENB3BL0S3CNT3BHI4LENB3R1'2K1S4LENB3BL0S4LENB3BL0S4LENBFS4LENB2RrFS2K0S3CNT4LENB3BL02K1S2K4FS3CNT2R24LENBS3CNT2R24LENBS4LENBS3CNT4LENBS2LO4LENBS3CNT2R24LENB3BL03Hsp".
prep IV.
    assert (Rr : (0 <= Z.of_nat (length bs) <= count)%Z) by lia.
    zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    zstep. if_cases KZ; zify_lts KZ.
    { (* [comment removed for export] *) eapply LX; eassumption. }
    assert (R1' : (1 <= Z.of_nat (length bs))%Z) by lia.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      do 4 zstep.
      unfold sf_hide in DST. (* [comment removed for export] *)
      pose proof (shad_mono (B + Z.of_nat (length bs) - 1) (B + count - 1) ltac:(lia)) as SM.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
        | zsimp; eapply app_blk_sub; [exact APPD | lia | lia | lia]
        | zsimp; eapply unpoisoned_sub; [exact UD1 | lia | lia]
        | zsimp; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 3 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv2_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (Z.of_nat (length bs) <= 64)%Z) by (clear - K2 Rr R1' BL0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 B WR21 ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (B + Z.of_nat (length bs) + -1) WR21
                  ltac:(apply no_image_asan; pose proof BND_ok as Bf; unfold BND in Bf; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LSS; [eassumption | lia].
      + eapply LX; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="RLO2 RHI2 MI ST LO KLO GOT SHB INI LAY REAL DST ERR A0 A2 FD CNT BHI SEPD SEPE APPD UDST R2 WR2 RI RSTK RERR RD RSH2"] Lemma read_i_body :
    implA asegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
          (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x433d4) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    Local Ltac2 Set LiaHints.tbl := fun () => "02:0?10561131328.91 11801586693.10412371295384.93 12594912664.93 12973736063.10013879134417.10714971218840.93 15414308376.94 15498737820.12415498737820.90 15642987184.91 162492479.82   16390485400.93 16790697868.12016880578840.1181807322596.89  1807322599.121 18655812081.93 18795919531.92 20589361816.93 21694748720.90 22282192675.11822284289799.10423654922526.10025794325363.93 25820099228.12525820099228.90 26293660097.1182644808984.91  26504917904.11926504917904.12026505308628.91 26505308628.93 26505308628.94 27080381553.94 27490081048.91 27709328113.93 27712824752.88 28055345289.11428252944920.93 28633291712.89 29094024344.93 29337189107.91 30041986200.93 30301036312.93 3091892504.94  3117223615.100 31255036184.11831262483992.94 32648281752.93 32824455704.94 34233151718.81 34235665431.10034496658584.93 34633935168.91 35226064150.10035281682200.93 35378896924.12435378896924.88 35854634524.12535854634524.90 35895327997.1043602932068.89  3602932074.124 36142286193.91 36200717662.11536986663037.10437033834392.93 37033835015.1143812400510.114 38300552235.92 38515848600.93 38525121917.10441389258667.92 42149037413.82 42272313587.93 42497191704.93 43055369225.79 43466714008.11843466714008.12044368527500.10044484923210.10445079670641.93 45261929843.93 4558652864.91  45735046704.90 46703417572.89 46703417578.12448556466190.11949460590346.11549610168957.10449921929014.10149921929014.86 50221378405.12350221378407.87 51077402219.75 51100856984.11851795196848.90 52415237221.90 52415237227.12552473359256.93 53175635037.10053324180011.90 54844324854.10556170256219.10056172315833.82 56280451506.11456347265304.94 57603479822.11557813240112.90 58390049052.12658390049052.91 59222033649.93 59308628179.1  59308633593.1  59430450874.10059525410931.93 60858764075.93 60891612184.91 61233359552.92 61248564120.93 61428698795.92 61837739032.91 62623352644.11464777566744.93 6490496664.93  66138656668.12266138656668.90 67252353088.91 6781596952.91  68211399064.1186922740008.74  7078002290.100 7250900467.94  7944451812.89  7944451813.123 9014990744.93  9405451517.104 00000400L00T00\00b00c00k01301401501601:01B01N01g01h01i02602:02B02C02D02E02I02Q02R02S02T02\02]02m02n02o03003=03E03R03S03T03\03`03h04004804@04H04M04f04n05605>05?05D05L05P05Q05Y05Z05[05\05]05i05j05k06906:06F06N06S06W06[06c06o07307807@07H07M07f08?08W08X08e08m09109209309409E09I09U09k0:A0:B0:C0:G0:`0:a0:b0:c0:k0;<0;@0;A0;B0;C0;D0;L0;M0;N0;O0;P0;]0;a0;e0<10<90<=0<E0<I0<Q0<U0<]0<a0<i0=10=20=30=70=?0=X0=\0=o0>70>80>90>A0>MS2HBS3Hsp2R23BL02LO3CNT4SEPDS2R23BL0S2R23BL0S4SEPESS2R23BL0S2R23BL0SSSS2LOS2R23BL0S2R23BL03HspS3CNT3BHI4SEPE2R23BL03HspSSS2LO3CNT4SEPDS2HBS2R23BL0SFFS2FDS2R23BL0SSFS2R23BL0FS3CNT2R23BL03HspSSSS2LO3CNT4SEPDS2R23BL0S2LO3CNT4SEPDSSS2R23BL0S2HBS2R23BL0S2R23BL0S2R23BL0S2R23BL0S2R23BL0S3BL0S3CNT3BHI4SEPE2R23BL03HspS2R23BL0S2R23BL0S2R23BL0SS3CNTS2R23BL0S2HBSS2R23BL0SSSSS2R23BL03HspSSS3CNT4SEPD3LO'SS2R23BL03HspS2R23BL0S3CNTS2HeS2HBS2R23BL0S2R23BL03HspS2HBS3BL0S2R23BL0S2R23BL0S3LO'S3CNT3BHI4SEPE2R23BL03HspS3CNT3BHI4SEPE2R23BL03HspS2LO3CNT3BHI4SEPD2R23HspFS2LO3CNT4SEPDS2R23BL0S2HBSSSS2LO3CNT4SEPD3HspS2LOS2R23BL03HspS2LO3CNT3BHI4SEPD2R21HS2LO3CNT3BHI4SEPD2R21HSSS2LOS3CNT3BHI4SEPE2R23BL03HspSSSS2R23BL0S3CNT3BHI4SEPE2R2S2HBSSSSS2R23BL0SSSSS2LO3CNT4SEPDS2K0S2KZS2R23BL03HspS2R23BL0S2HBS2R23BL0S2HBS2R23BL0S2HBS2R23BL0S2HeS2R23BL0S2R23BL0SSS2HBS2R23BL0S3CNT3BHI4SEPE2R23BL03HspS2LOS2LO3CNT3BHI2R23HspS2R23BL0SSS2R23BL0S2R23BL03Hsp".
assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2; change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    pose proof DST as DST0. change (?P) with (sf_hide P) in DST. pose proof ERR as ERR0. change (?P) with (sf_hide P) in ERR.
    rewrite A0, A2.
    iprefix.
    carve_frame 2128%nat ST0.
    do 9 zstep. do 3 zstep. zstep.
    call_sp tryinit_spec; [ assumption | exact ST0 | lia | unfold KHIGH; lia | assumption | eapply rng_sub'; [exact RSTK | lia] | ].
    do 6 zstep. zstep.
    name_sp sp (-2128)%Z.
    Local Ltac usp := match goal with H : bv_unsigned _ = (bv_unsigned sp + -2128)%Z |- _ => rewrite H end.
    icallk read_spec;
      [ usp; eassumption | eassumption | eassumption | assumption | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | lia | lia
      | usp; eapply rng_sub'; [exact RSTK | lia] | ].
    ipost asegs. unname_sp.
    lazymatch goal with P : context [match ?a with RdErr _ => _ | RdData _ => _ end] |- _ => rename P into RP end.
    destruct ans as [e|bs]; cbn [read_ret].
    - (* [comment removed for export] *)
      destruct RP as (BUFe & ERRe & He).
      zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
      zstep. if_cases KZ; zify_lts KZ. 2:{ exfalso. clear - KZ. lia. }
      do 9 zstep.
      lazymatch goal with ST2 : stk asegs _ lo _ |- _ => release_frame FR ST2 (bv_unsigned sp) end.
      unfold read_i_post. rewrite (Z2Nat.id count) by lia. finish; lia.
    - (* [comment removed for export] *)
      destruct RP as (BUF1 & ERR1 & LENB).
      eapply LC. eapply inv2_of; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.

#[using="Type"] Lemma read_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fd count : Z) (junk : list byte) (errv : word) (RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_read m ->
  rw_cells asegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells asegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 16777216)%Z ->
  (0x5f6000 <= bv_unsigned a1 \/ (0x5c34d0 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= 0x5d34d0 /\ bv_unsigned a1 + count <= errno_addr tp))%Z -> (bv_unsigned a1 + count <= lo)%Z ->
  (0xa2080 <= errno_addr tp /\ errno_addr tp + 4 <= 0x5f6000)%Z -> (164 <= bv_unsigned tp)%Z ->
  app_blk (bv_unsigned a1) (bv_unsigned a1 + count) ->
  unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + count) ->
  (RLO2 <= bv_unsigned a1 /\ bv_unsigned a1 + count <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (errno_addr tp) 4 -> rng RNG (bv_unsigned a1) count ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  implA asegs RNG (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
        (epostF (read_i_post RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x433d4) fc None m (seg_rom asegs)).
Proof. intros. eapply read_i_body; eassumption. Qed.
End CANSEC1.
