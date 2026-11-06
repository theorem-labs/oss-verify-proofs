(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells ShadowTac F_memcpy F_rip.
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
Definition asan_memcpy_entry := 0x50d7c%Z.

Definition asan_memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at asegs m' (bv_unsigned a1) src.

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
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
  Hypothesis SRC : bytes_at asegs m S src.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.
  Hypothesis SEPS : (S + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= S)%Z.
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPS : app_blk S (S + n).
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis USRC : unpoisoned m S (S + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R1 : (RLO1 <= S /\ S + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1).
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH1 : rng RNG (shad RLO1) (shad RHI1 - shad RLO1).
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m).

  (* [comment removed for export] *)
  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
                  [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
    /\ unpoisoned mc S (S + n) /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO1) (shad RHI1 - shad RLO1) /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).

  (* [comment removed for export] *)
  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= S /\ S + n + 8 <= KEND /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO1 /\ shad RLO1 <= shad S /\ shad (S + n - 1) + 1 <= shad RHI1 /\ shad RHI1 <= KHIGH
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO1 mod 8 = 0 /\ shad RHI1 mod 8 = 0 /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO1 <= S /\ S + n <= RHI1 /\ RLO2 <= D /\ D + n <= RHI2
     /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.

  #[using="m src ST LO KLO LEN APPS APPD NSZ R1 R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPS as [LES AS]. destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R1 as R1'. pose proof R2 as R2'. unfold sf_hide in R1', R2'.
    Local Ltac2 Set LiaHints.tbl := fun () => "0010>29786661831.82000008S3LEN2Rn".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LES AS LED AD R1' R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].   (* [comment removed for export] *)
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  (* [comment removed for export] *)
  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= S /\ S + n + 8 <= 2^47 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr S 3 < 2^44 /\ -1 <= Z.shiftr (S + n + -1) 3 < 2^44 /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO1 /\ shad RLO1 <= shad S /\ shad (S + n - 1) + 1 <= shad RHI1 /\ shad RHI1 <= 17594333495296
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
  #[using="m src ST LO KLO LEN APPS APPD NSZ R1 R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62904913180.7500000>S2LO3LEN3NSZ1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Ltac inv_open H :=
    let jk := fresh "jk" in
    destruct H as ((jk & FR) & ST1 & MU1 & WM1 & MI1 & GOT1 & RIC1 & SHB1 & INI1 & LAY1 & REAL1 & US1 & UD1 & WR11 & WR21).

  (* [comment removed for export] *)
  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in SRC; change (?P) with (sf_hide P) in DST;
    change (?P) with (sf_hide P) in SEP; change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in SEPD;
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  (* [comment removed for export] *)
  #[using="src ST LO KLO LEN SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2072 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0020>11807744665.9033470593740.9200000K00cS3LEN3SEP4SEPS4SEPD2R12R21BS3LEN3SEP4SEPS4SEPD1B2H2".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    split. { eapply unpoisoned_munch; [exact USRC | exact MU1 |]. cbn [disjoint_from]. pose proof (SS S (S + n)%Z). lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    split; eapply wr_at_transport; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x50e6c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00O0?11799456952.11411801535522.11511801586693.12611801586693.12714540549476.13115704552726.12416852238724.12417231150308.13117607716380.13219031052389.13222580318183.13022700267513.11824346829668.13125250094364.131260657820.131  26362266742.12427914623132.13135834628839.13035973911964.13237601013348.13138214514495.12338637523228.13244484923210.12648795194334.1235226650179.127 53295060839.13053723688860.13157540799784.11366283099932.13268577416220.1338794126823.130 00000H00`01=01Z01_01d01l02102602;02@02G02L02Q02V02[02`02e02j02o03403903C03H03I03N03S03[03`03e03jS3LEN3SEP4SEPS2R12R23BL0S3LEN3SEP4SEPD2R12R23BL0S3LEN3SEP4SEPS4SEPD2R12R23BL0S3LEN3SEP4SEPS4SEPD2R12R23BL0S3LENS3LENS2LO3LENS3LENS3LENS3LENS3LENS3LEN1HS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LENS3LEN4SEPDS3LENFS3LENS3LENS2LO3LENS3LENS3LENS3LEN".
prep IV.
    assert (SRC1 : bytes_at asegs mc S src).
    { unfold sf_hide in *. eapply bytes_at_transport; [exact SRC | exact MU1 |]. rewrite LEN. cbn [disjoint_from]. lia. }
    assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    zstep. zstep. zstep.
    unfold sf_hide in SEPD.
    apply (munch_weaken _ [(bv_unsigned sp + -2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR11 WR21.
    call memcpy_spec; [exact SRC1 | exact LEN | exact DST1 | unfold sf_hide in SEP; exact SEP | exact MI1 |].
    do 12 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x1 x5 x6 x7 x9 x16 x17 x18 x21 x23 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 (Z_to_bv 64 (D + n + -1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) x21 (Z_to_bv 64 (n + -65)) x23
               s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x51194) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13708355367.11713732943226.11724120772675.11740339170388.12341502378089.11550781112641.11557540799784.11259308585478.11259308627018.1  60888476447.11762863995383.12300000>00Q00]00o01=01H01S01a01e02:02;S3LEN2N12Hk2HcS3LEN2N12Hk2Hc2SL1KS3LEN3BL02HkS3LEN2N13BL02Hk2HcS3LEN2N12Hk2HcS3LEN2Hk2HcS2LO3LEN2HkS3LEN2N12Hk2HcS2K'S3LEN2N13BL02Hk2Hc2SLF".
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
  #[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD NSZ R1 R2 RI RSTK RS RD RSH2"] Lemma LWS : forall mc x1 x5 x6 x7 x9 x15 x16 x17 x18 x21 x23 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) x15 x16 x17
               x18 (Z_to_bv 64 (D + n + -1)) (Z_to_bv 64 (bv_unsigned sp + -2144)) x21 (Z_to_bv 64 (n + -65)) x23
               s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x51178) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?19482125344.12419482125358.12224122881528.11524991237562.12429782203372.12129784416728.11530507626521.1103421727977.115 36004493144.11037100885899.12143614754995.11052076332703.12352523015476.12253510313876.12256209684249.11457540799784.10959308629082.1  67298533313.11468646946464.11000000<00H00Q00V00[00`00e01001501?01D01P01U01Z01_01g01k02702?S3LEN2N13CK2S3LEN2N13CK2S3LEN3BL0S3LENS3LENS3LENS3LENS3LEN2N12K6S3LENS3LEN2N11BS3LENS3LEN2N13BL0S3LENS3LENS3LENS2LO3LENS2K7S3LEN2N13CK2S3LEN2N1".
prep IV.
    destruct (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; eassumption.
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH2"] Lemma LW : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) x21 (Z_to_bv 64 (n + -65)) x23
               s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x50e24) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00_0?11447729323.18911801586693.1361606899715.11  16917719815.13621665481694.12123260809484.11623260842252.11424115025143.12324122799997.11429782203372.12630010325480.11431247978648.11431824352466.12531885183527.1173210808038.126 35895327997.13636986663037.13639547979280.11640886601363.12642148837058.11444484923210.13647018790687.11647019085599.11449610168957.13649852543712.11449852904160.11650216114301.13651845486909.11252076332689.12152733105242.11552733105242.11756172410654.11457540799784.11057880736640.126585992346.115  5876716948.113 59308628304.11259308628695.1  60274602806.11862806329641.11163407398368.11463407889888.11664073056942.1147744853832.117 7848643581.136 8393561110.132 9405451517.136 00000100600>00?00D00L00T00]00f00k01001901>01G01H01Q01Z01i02302<02=02E02M02V02a02l03503>03J03S03\03a03i03j04104204>04B04M04V04a04l05;05<05E05J05SFS3HspS3BL02K2FS3LENS3LEN2R2S3LEN2R2S3LEN3BL0S3LEN3BL0S3LENS3LENS3LEN3BL0S3LENS3LEN3BL0FS3BL03HspS3BL03HspS3LEN2R23BL02N1S3LEN2N11BS3LEN3BL0FS3LEN2R2S3LEN2R2S3BL03HspS3LEN2R22N1S3LEN2R22N1S3BL03HspS3LEN3BL0S3LEN3BL02N1S3LEN3BL0S3LEN3BL0S3LENS2LO3LENFS3LEN1BFS3LEN3BL02K1S2K4S3LEN3BL01HS3LEN3BL0S3LEN2R22N1S3LEN2R22N1S3LEN2R23BL02N1FS3BL03HspS3LENS3BL03Hsp".
prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ (* [comment removed for export] *) zstep. eapply LX; eassumption. }
      do 5 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      do 10 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; eassumption.
      + eapply LX; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LRL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x23 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (S + n - 1) - c) = k -> (shad S <= c < shad (S + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (n + -65)) x23
               s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x510f0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. Local Ltac2 Set LiaHints.tbl := fun () => "00<0?13708355367.11513732943226.11524120772675.11540339170389.12253037104326.11357132210400.11357540799784.11059308585478.11059308627018.1  60483825568.12260888476447.11562863995382.12200000>00Q00]00^00l01701B01P01T01f02;02<S3LEN2N12Hk2HcS3LEN2N12Hk2Hc2SL1KS3LEN3BL02HkFS3LEN2N12Hk2HcS3LEN2Hk2HcS2LO3LEN2HkS3LEN2N12Hk2HcS2K'S3LEN2N13BL02Hk2HcS3LEN2N13BL02Hk2Hc2SLF".
prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (S + n - 1) = 2147450880 + Z.shiftr (S + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc S (S + n) c US1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LW; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LRS : forall mc x5 x6 x7 x9 x15 x16 x17 x18 x23 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr S 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (S + n + -1) 3)) x15 x16 x17
               x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (n + -65)) x23
               s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x510d4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?19482125344.12219482125358.12024122881528.11324991237562.12229782203372.12029784416728.11330507626521.1083421727977.113 37100885899.12043614754995.10848157833191.10852076332702.12252523015476.12053510313876.12056209684249.11257540799784.10759308629082.1  59961573519.10867298533313.11200000<00H00Q00V00[00`00e01001:01?01D01P01U01Z01_01g01k02302?S3LEN2N13CK2S3LEN2N13CK2S3LEN3BL0S3LENS3LENS3LENS3LENS3LEN2N12K6S3LEN2N11BS3LENS3LENS3LEN2N13BL0S3LENS3LENS3LENS2LO3LENS2K7S3LEN2N1S3LEN2N13CK2".
prep IV.
    destruct (unpoisoned_check_rd asegs mc S (S + n) (S + n + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as (b2 & RD2 & CK2).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((S + n + -1) mod 8) (sval b2)) by (OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    zstep. if_cases K6; zify_cond K6.
    - (* [comment removed for export] *) zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LW; eassumption.
    - eapply LRL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="junk ST LO KLO SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma LR : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (bv_unsigned sp + -2144)) (Z_to_bv 64 (S + n)) x22 x23
               s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x50dd8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. Local Ltac2 Set LiaHints.tbl := fun () => "00`0?11447729323.18811801586693.1351606899715.11  16224732650.11516225027562.11316917719815.13521665481694.12022625362435.11322625395203.11524115025143.12224122799997.11326844494028.11329782203372.12530010325480.11331247978648.11331782320794.11631824352466.12431885183527.1163210808038.125 35895327997.13536986663037.13540886601363.12541067758515.11042148837058.11343042078623.11343042373535.11544484923210.13545198201878.13146415450209.11446415450209.11649610168957.13550216114301.13551845486909.11152076332703.12256172410654.11357540799784.10957880736640.125585992346.114  5876716948.112 59308628304.11159308628695.1  60274602806.11765824578719.11565824677023.1137744853832.116 7848643581.135 9405451517.135 9722591124.115 00000100600>00F00N00O00T00\00d00m01601E01J01O01X01a01f01g01h02102:02D02M02V02a02l02m03203;03D03M03V03_03k04004804904@04A04M04Q04\04g05205305<05E05TFS3HspS3BL02K2S3LEN2R1S3LEN2R1FS3LENS3LEN2R1S3LEN2R1S3LEN3BL0S3LEN3BL0S3LEN2R13BL02N1S3LENS3LENS3LEN3BL0S3LEN3BL0S3LENFFS3BL03HspS3BL03HspS3LEN2N11BS3LEN3BL0S3LEN3BL0S3LEN2R12N1S3LEN2R12N1FS3LENS3LEN3BL0S3LEN3BL0S3BL03HspS3BL03HspS3LEN3BL0S3LEN3BL02N1S3LENS2LO3LENFS3LEN1BFS3LEN3BL02K1S2K4S3LEN3BL01HS3LEN2R12N1S3LEN2R12N1FS3BL03HspS3BL03HspS3LEN2R13BL02N1".
prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ (* [comment removed for export] *) zstep. eapply LW; eassumption. }
      do 6 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPS | exact US1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LW; eapply inv_of; eassumption.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      do 10 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R1.
      destruct (shadow_probe8 asegs mc RLO1 RHI1 S WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO1 RHI1 (S + n + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LRS; eassumption.
      + eapply LW; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="junk RLO1 RHI1 RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL SRC LEN DST SEP SEPS SEPD APPS APPD USRC UDST NSZ R1 R2 WR1 WR2 RI RSTK RS RD RSH1 RSH2"] Lemma asan_memcpy_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x50d7c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    Local Ltac2 Set LiaHints.tbl := fun () => "01a0>10499999408.8911712989376.9311799361125.9211799361125.9311799361125.9411799361125.9512371295384.9313177412632.9214540549476.9014971218840.9315207249688.9415300726187.9316390485400.9317231150308.9017607716380.9117748760128.9117793405592.9318234062872.9418472667160.9418486058859.7818542239966.9018795919531.9219031052389.9120264391448.9221179061016.9222537331120.9222580318183.8923342567448.9223766180800.9023781151384.9424346829668.9025250094364.8925624991000.95260657820.90  2644808984.95 27914623132.9028252944920.9428521959216.9129094024344.9329270719787.9329768397120.9230041986200.9330301036312.943091892504.94 31262483992.9432018305688.9432648281752.9332824455704.9434496658584.9334540297392.9134844613528.9335281682200.9435834628839.8935973911964.9136003610136.9537033834392.9337145596952.9437601013348.9038300552235.9338515848600.9338637523228.9140600447536.9040808938648.9341389258667.9242211160088.9243061432073.8043225798424.9443649743150.9043821196696.9344314892224.9245383013400.9445545526552.9246412915608.9346586017712.9148377235864.9448454161048.9450432113816.9352473359256.9352637746480.9052689461784.9453295060839.8853324180011.9453723688860.9055120970136.9456347265304.9456367821504.925695863616.91 57540799784.7758622399152.9159308628179.1 59308628566.8860245500312.9460858764075.9360891612184.9561428698795.9261837739032.9562371084587.9162393598016.9163719325464.9463971998950.8264640737328.9064777566744.946490496664.93 66283099932.916781596952.95 68412599744.9268577416220.928794126823.89 8929152288.87 8929152679.88 8930218264.94 9014990744.93 9454272280.94 00000500900:00;00<00=00B00G00L00Q00V00Z00_00d00i00m01201701<01D01I01M01R01W01\01a01f01k01o02402902>02C02H02M02R02W02\02a02e02i02n03303803=03B03G03L03Q03V03[03`03e03j03o04404904>04B04G04L04Q04V04Z04_04h04m05205705;05@05E05J05O05T05Y05^05c05h05m06206606;06@06E06I06M06U06Z06^06m07207607;07?07D07H07L07Q07V07[07`07e07j07o08308808=08L08^08c08h08mS3LENS2HBSSSSS3BL0S3BL0S3LENS3BL0S3BL0S2HBS3BL0S3LENS3LENS2HBS3BL0S3BL0S3BL0S2LO3LENS3LENS2HBS3LENS3BL0S3BL0S3LENS3LENS3BL0S2HBS3BL0S3LENS3LENS3BL0S3LENS3BL0S3LENS3BL0S3LENS3BL0S2HBS2HBS3BL0S3BL0S3BL0S3BL0S3BL0S3BL0S3BL0S3BL0S3LENS3BL0S3BL0S3LENS3LENS3BL0S3BL0S3BL0S3LENS2HBS3BL0S3LENS3LENS3BL0S2HBS3BL0S3LEN3BL0S3BL0S3LENS3BL0S2HBS3BL0S3BL0S3BL0S3LENS3BL0S3BL0S3BL0S3BL0S3LENS3BL0S3LENS2HBS3LENS3BL0S3BL0S2HBS2HBS2LO3LENS3LENS2K0S3LEN3SEP2K22K3S3BL0S2HBS3BL0S2HBS3BL0S2HBS2HBS3BL0S3LENS3LENS3BL0S3BL0S3LENS3BL0S2HBS3LENS3LENS3LEN2R12R23BL0S3LEN2R12R23BL02K2S3BL0S3BL0S3BL0".
assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in SEP; change (?P) with (sf_hide P) in SEPS;
    change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    (* [comment removed for export] *)
    change (?P) with (sf_hide P) in SRC; change (?P) with (sf_hide P) in DST.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST.
    change (?P) with (sf_hide P) in WR1; change (?P) with (sf_hide P) in WR2.
    carve_frame 2144%nat ST0.
    do 12 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    do 4 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IV : INV m1) by (eapply inv_of; eassumption) end.
    zstep. if_cases K1; zify_cond K1.
    { eapply LR; exact IV. }
    zstep. if_cases K2; zify_cond K2.
    { eapply LR; exact IV. }
    zstep. if_cases K3; zify_cond K3. { exfalso. unfold sf_hide in SEP. lia. }
    eapply LR; exact IV.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.

#[using="Type"] Lemma asan_memcpy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (src junk : list byte) (RLO1 RHI1 RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO1 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x50d7c) fc None m (seg_rom asegs)).
Proof. intros. eapply asan_memcpy_body; eassumption. Qed.
End CANSEC1.
