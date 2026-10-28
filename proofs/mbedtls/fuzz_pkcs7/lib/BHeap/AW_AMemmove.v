(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_stringA A_rip.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_amem_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemmove.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L16405147374.59L29644601389.59L30095897756.55L35469551417.59L4610065464.50 L48379326627.59L51748475512.50L53520163529.59L53520247005.59L56775215785.59L56775393469.59Q17581378383.58Q35222541774.58Q39502766003.58Q4111067988.58 Q52324771135.5800000C00P00f01902m03704k05I05j06H06i07?07@07P07d08>S1k1q2lo1p2Hk2Hp2NES1k1q1p2Hk2NES1k1q2lo2hi1p2Hk2Hp2HqS1k1q2lo1p2Hk2Hp2EQS2AL2CS1q2ra2sp2gp2tp2t02t12t22s02s12a02a12a22a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo1p2a52a62Hk2HpS1k1q1p2HkS2AL2CS1q2ra2sp2gp2tp2t02t12t22s02s12a02a12a22a72s22s32s42s52s62s72s82s93s103s112t32t42t52t61F2fc1m2lo1p2a52a62Hk2HpS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3HloS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3Hlo2EQS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3HloS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi3Hlo2EQS1k1q2lo2hi1p2Hk2Hp2HqFS1k1q2lo1p2Hk2HpS1k1q2lo1p2Hk2Hp3HloS1k1q2lo2hi1p2Hk2Hp2Hq3Hhi". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma amm_orloop : forall pc k (p q : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo hi : Z),
    (pc = 0x686e0 \/ pc = 0x68784) ->
    q - p <= Z.of_nat k -> lo <= p < q -> q <= hi -> hi < 2^63 -> 0 <= lo ->
    (forall x, lo <= x < hi -> exists b, bytes_at asegs m x [b]) ->
    (forall x, lo <= x < hi -> aok_addr AL CS x) ->
    evtA asegs AL CS
      (fun ms' => exists a5' a6',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 q) (Z_to_bv 64 q) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (pc + 16)) fc None m (seg_rom asegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 p) (Z_to_bv 64 q) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Proof.
    intros pc k. intros until hi. intros PC.
    destruct PC as [-> | ->];
      [ replace (427744 + 16) with 427760 by reflexivity | replace (427908 + 16) with 427924 by reflexivity ]; revert p a5 a6;
      (induction k as [|k IH]; intros p a5 a6 Hk Hp Hq Hhi Hlo RD AOK; [lia|]; al_facts;
       destruct (RD p ltac:(lia)) as [b B]; pose proof (bytes_at_read1 _ _ _ _ B) as RDB;
       zstep; zstep; zstep; zstep;
       destruct (Z.eq_dec (p + 1) q) as [EQ|NE];
       [ if_falseU; rewrite EQ; finish
       | if_trueU; eapply IH; try eassumption; lia ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition mmS_post (sp gp tp s0 s4 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists ra t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + -65)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x6852c) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

  Definition mmD_post (sp gp tp s0 s4 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST SRC n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists ra t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s3 s5 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x68578) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@C17025492443.114C17025492443.89 L11447729190.145L11944109973.89 L13226205188.73 L13230398037.88 L14345069909.70 L18705684095.88 L1918331350.57  L19322770858.88 L19628431903.91 L20966712717.93 L24122754266.93 L24122936649.93 L24124928684.87 L24124928684.88 L24608617390.71 L24982526223.91 L25792253067.69 L27196467039.70 L28083348026.89 L29784464483.92 L29786564236.88 L29971684470.71 L31686803170.93 L3248729870.2   L3421674955.93  L34922678286.2  L36929494798.2  L38150352304.93 L39594679749.88 L41312602363.93 L45607281678.2  L46817748388.73 L47543971773.93 L49899794702.2  L51172192526.2  L52065394884.87 L52514161039.91 L53517158443.70 L53519158063.91 L5549769202.93  L6106346273.0   L61097676998.2  L61932014891.70 L64055233047.93 L64240928084.87 L64596837268.71 L66488557582.2  L7106453518.2   L82129492.73    O14206727921.114O14206727921.89 O15547502833.114O15547502833.89 O17025492443.114O17025492443.89 O23485702385.114O23485702385.89 O32131581681.114O32131581681.89 O38504098033.114O38504098033.89 O4492316913.114 O4492316913.89  O48978854641.114O48978854641.89 O65485481713.114O65485481713.89 P3245129067.114 P3245129067.89  P34917767787.114P34917767787.89 P36941614443.114P36941614443.89 P45611546219.114P45611546219.89 P49904706411.114P49904706411.89 P51184575339.114P51184575339.89 P66501341803.114P66501341803.89 P7102853739.114 P7102853739.89  Q11819106457.89 Q12384979828.88 Q17356333121.88 Q19275945964.88 Q20040127854.88 Q20109487353.88 Q21797814763.88 Q23650890746.92 Q24745328269.92 Q28218390483.92 Q29427030349.88 Q31394395900.88 Q31762069934.92 Q32231604980.88 Q33251509847.88 Q34268098539.88 Q34355500059.89 Q34947676851.88 Q35212026327.88 Q36722057835.88 Q3742509637.88  Q38148316102.88 Q39778974580.88 Q39942779359.88 Q41324687698.92 Q43608312681.89 Q43855177782.88 Q44556843737.92 Q44682733963.92 Q45748806138.92 Q45896845414.88 Q46309744770.92 Q46311840365.88 Q49545476915.88 Q51241282684.88 Q52818999351.88 Q52821082840.92 Q53519998161.88 Q56964988266.88 Q59322611797.88 Q59365683033.88 Q62824840384.88 Q63037122486.88 Q6460837458.88  Q66715486460.88 Q67805910652.88 00000100200300400>00H00O00[00e00l01801F01U01d01e02402=02D02I02P02Q02X02_02k03;03<03O03P03Q03h04704J04K04]04m04n04o05;05B05C05J05T05U05V05[05e06106706806906C06D06E06F06G06R06]06^06_06`06a06b06c06d06e06f06g06h06i07:07E07V07a08208=08N08Y08j09509F09Q09b09m0:>0:I0:U0:V0:W0:e0:f0:g0:h0:i0;<0;G0;H0;O0;P0;Q0;R0;k0<20<30<40<50<60<M0<W0=50=60==0=L0=b0=c0=n0=o0>?0>X0>Y0>`0>a0>b0?20?30?J0?`0@?0@N0@O0@a0A3FFFFS3SRC1n2B0S3SRC1n2B0S1n3BIGS3SRC1n1N2B0S3SRC1n2ARS3SRC1nS3SRC1n1N2B0S3SRC1n2q13Q45S3SRC1n3H8a3H8bS3SRC1n3H8a3H8bFS3SRC1n3H8b3H8aS1n5SMALLS3SRC1nS1n1NS1n3BIGFS3SRC1nS3SRC1nS3SRC1n1N2NZS3SRC1n2q02q12DBFS3SRC1n2q02q12DB2LTFFS3SRC1n2B02q02q12E03Q01S3SRC1n3H8b3H8aS3SRC1n2q02q12DB2GEFS3SRC1n1N5SMALL2NZS3SRC1n2B05SMALLFFS3SRC1n1N2B0S3SRC1nSS3SRC1nS3SRC1n2GESFS1n1NS3SRC1n2LTS3SRC1n1N2B0S1n2N0FFS3SRC1n2B0FFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S2sp3SRC1n2lo3LO0S2sp2lo3LO0S3SRC1n1N2NZFFS3SRC1n2q13Q45FFFFS3SRC1n2B02q02q12DBS3SRC1n3H8bFS3SRC1nFFFS3SRC1n1N2B02q02q13Q012DBS3SRC1nFFFFS3SRC1n2B02q02q12E03Q01S3SRC1n2q0S2AL3SRC1n4IMG'2B02q02q12E12DBFS3SRC1nS2AL3SRC1n4IMG'S2AL3SRC1n4IMG'2B03H8bFS3SRC1n3H8bFS3SRC1n2q02q12DBS3SRC1n1N2B02q02q13Q012DBFS3SRC1nFFS2AL3SRC1n5ALWF'FS3SRC1n2B02q02q13Q452DBS3SRC1n2B02q02q12E12DBS2AL3SRC1n4IMG'2B02q02q12E03Q01S2AL3SRC1n4IMG'FS2AL3SRC1n4IMG'2B0S2AL3SRC1n4IMG'2B0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma amemmove_chkS :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (DST SRC n lo : Z),
    aobj asegs AL CS m SRC n -> 0 <= n < 2^40 -> app_range SRC (SRC + n + 7) ->
    (1 <= n -> crange CS (SRC - SRC mod 64) 64 /\ crange CS (SRC + n - 1 - (SRC + n - 1) mod 64) 64) ->
    (forall c, CS c -> exists b, bytes_at asegs m (shadow_of AL c) [b]) ->
    rip_consts m ->
    stk asegs m lo (bv_unsigned sp) -> HSE < lo -> lo <= bv_unsigned sp - 80 ->
    crange CS lo (bv_unsigned sp - lo) -> mem_inv asegs m -> 0 <= DST < 2^64 ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 SRC -> a2 = Z_to_bv 64 n ->
    evtA asegs AL CS (mmS_post sp gp tp s0 s4 s7 s8 s9 s10 s11 F fc DST SRC n lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x684e4) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI DB0 -> -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < SRC /\ SRC + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    Ltac ripS SRC n lo SCS :=
      zstep; zstep; zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := SRC) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      zstep; zstep; zstep; zstep; zstep;
      unfold mmS_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. (* [comment removed for export] *) zstep. if_trueU. ripS SRC n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold mmS_post; finish. }
    replace ((1 <=? n) && (n <=? 64))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
    if_falseU.
    destruct (HULL ltac:(lia)) as [HULL0 HULL1].
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m SRC n OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    do 11 zstep.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (SRC + n + -1) with (SRC + n - 1) by lia.
    rewrite !Z.mod_small by lia.
    rewrite !land_m8 by lia. rewrite !hull_sh by lia.
    rewrite E0, E1.
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold mmS_post; finish. }
    (* [comment removed for export] *)
    shadow_byte OBJ (SRC + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((SRC + n - 1) / 8) 2147450880) in RDk.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (SRC / 8) ((SRC + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply amm_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [left; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (SRC / 8) with ((SRC + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a5' & a6' & ->)).
    zstep. zstep.
    if_cases Ks.
    2:{ ripS SRC n lo SCS. }
    unfold mmS_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0280@C17025492443.113C17025492443.88 L11447729190.144L11944109973.88 L14345069909.69 L16029456145.72 L16033656128.87 L19628431903.90 L20966712717.92 L23189051853.56 L2394494565.92  L24122754266.92 L24122936649.92 L24124928684.86 L24124928684.87 L24608617390.70 L24982526223.90 L25792253067.68 L27050710447.72 L27196467039.69 L28083348026.88 L29784464483.91 L29786564236.87 L29971684470.70 L31686803170.92 L31723725750.68 L3248729870.2   L3421674955.92  L34922678286.2  L35600352231.68 L35692323376.92 L36929494798.2  L38150352304.92 L39594679749.87 L41794548952.87 L45607281678.2  L46817748388.72 L47543971773.92 L49899794702.2  L51172192526.2  L52065394884.86 L52514161039.90 L53517158443.69 L53519158063.90 L61097676998.2  L61402522944.86 L61402946443.67 L61402946443.68 L61931751947.68 L61932014891.69 L63477229558.87 L6351988974.92  L64596837268.70 L64951446305.0  L66488557582.2  L7106453518.2   O14206727921.113O14206727921.88 O15547502833.113O15547502833.88 O17025492443.113O17025492443.88 O23485702385.113O23485702385.88 O32131581681.113O32131581681.88 O38504098033.113O38504098033.88 O4492316913.113 O4492316913.88  O48978854641.113O48978854641.88 O65485481713.113O65485481713.88 P3245129067.113 P3245129067.88  P34917767787.113P34917767787.88 P36941614443.113P36941614443.88 P45611546219.113P45611546219.88 P49904706411.113P49904706411.88 P51184575339.113P51184575339.88 P66501341803.113P66501341803.88 P7102853739.113 P7102853739.88  Q10652825868.87 Q12854075564.87 Q19275945964.87 Q21797814763.87 Q23650890746.91 Q24745328269.91 Q25930949378.87 Q28218390483.91 Q29427030349.87 Q31394395900.87 Q34268098539.87 Q34947676851.87 Q36722057835.87 Q3742509637.87  Q37735318614.87 Q38148316102.87 Q39778974580.87 Q39942779359.87 Q41324687698.91 Q43608312681.88 Q43855177782.87 Q44556843737.91 Q45129161346.87 Q45748806138.91 Q46309744770.91 Q46311840365.87 Q49545476915.87 Q49598061100.87 Q51241282684.87 Q52818999351.87 Q52821082840.91 Q53519998161.87 Q54929902563.91 Q56964988266.87 Q58952702441.87 Q59322611797.87 Q59365683033.87 Q62824840384.87 Q63037122486.87 Q63979701653.91 Q6460837458.87  Q66715486460.87 Q6693426778.88  Q67304791703.88 Q67805910652.87 Q67834060547.87 00000100200300400;00E00O00[00i01301=01L01[01\01k02402;02@02J02Q02R02Y02`02l03<03F03G03Z03[03g04104204I04X04_04`05205B05C05D05P05W05X05_05`05l06806D06I06N06Z06m07307407507607707807907:07E07P07Q07R07S07T07U07V07W07X07Y07Z07[07\07m08808I08T08e09009A09L09]09h0:90:D0:U0:`0;10;<0;=0;>0;L0;M0;N0;a0;b0;m0;n0<50<N0<O0<P0<Q0<R0<i0=30=Q0=R0=Y0=h0>>0>?0>J0>Z0?30?40?50?<0?=0?>0?N0?O0?P0?Q0?h0@>0@]0@l0@m0@n0A@0AG0AS0Ae0AfFFFFS1n3BIGS3DST1n2B0S3DST1n2B0S3DST1n1N2B0S3DST1n2q13Q45S3DST1n2ARS3DST1n2GES3DST1n3H8a3H8bS3DST1n3H8a3H8bFS3DST1n3H8b3H8aS1n5SMALLS3DST1nS1n1NS3DST1n2B0S1n3BIGFS3DST1nS3DST1nS3DST1n1N2NZS3DST1n2q02q12DBS3DST1n2B0FS3DST1n2q02q12DB2LTFS3DST1n1N2B0S3DST1n2LTFS3DST1n2B02q02q12E03Q01S3DST1n3H8b3H8aS3DST1nFS3DST1n1N5SMALL2NZS3DST1n2B05SMALLFFS3DST1n1N2B0S3DST1nSS3DST1nFS3DST1n1N2B0S3DST1n1N2B0S3DST1n1N2B0S1n1NS1n1NS3DST1n1N2B0S3DST1n2q02q12DB2GES1n2N0SFFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFS2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0S2sp3DST1n2lo3LO0S2sp2lo3LO0FFS3DST1n2q13Q45FFS3DST1n2B02q02q12DBFS3DST1n3H8bFS3DST1nS3DST1n1N2B02q02q13Q012DBFFFFS3DST1n2B02q02q12E03Q01S3DST1n2q0S2AL3DST1n4IMG'2B02q02q12E12DBFS3DST1nS2AL3DST1n4IMG'S2AL3DST1n4IMG'2B03H8bFS3DST1n3H8bS3DST1n2q02q12DBS3DST1n1N2B02q02q13Q012DBFFS3DST1nFFS2AL3DST1n5ALWF'FFFS3DST1n2B02q02q13Q452DBS3DST1n2B02q02q12E12DBS2AL3DST1n4IMG'2B02q02q12E03Q01S2AL3DST1n4IMG'FFS2AL3DST1n4IMG'2B0S3DST1nS3DST1n1N2NZS2AL3DST1n4IMG'2B0F". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma amemmove_chkD :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (DST SRC n lo : Z),
    aobj asegs AL CS m DST n -> 0 <= n < 2^40 -> app_range DST (DST + n + 7) ->
    (1 <= n -> crange CS (DST - DST mod 64) 64 /\ crange CS (DST + n - 1 - (DST + n - 1) mod 64) 64) ->
    (forall c, CS c -> exists b, bytes_at asegs m (shadow_of AL c) [b]) ->
    rip_consts m ->
    stk asegs m lo (bv_unsigned sp) -> HSE < lo -> lo <= bv_unsigned sp - 80 ->
    crange CS lo (bv_unsigned sp - lo) -> mem_inv asegs m -> 0 <= SRC < 2^64 ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 SRC -> a2 = Z_to_bv 64 n -> s3 = Z_to_bv 64 (n + -65) ->
    evtA asegs AL CS (mmD_post sp gp tp s0 s4 s6 s7 s8 s9 s10 s11 F fc DST SRC n lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6852c) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros OBJ N AR HULL SHRD RC ST LO0 SPL SCS MI SB0 -> -> -> ->. al_facts. unfold app_range in AR.
    assert (B0 : 0 < DST /\ DST + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    Ltac ripD DST n lo SCS :=
      zstep; zstep; zstep; zstep; zstep;
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply rip_spec with (CS := CS) (BEG := DST) (n := n) (lo := lo);
               first [ exact IMG | exact ALWF | exact CSOK | exact ASB | exact OBJx | split; assumption | eassumption
                     | reflexivity | unfold app_range; lia | lia ])
      end;
      zstep; zstep; zstep; zstep; zstep;
      unfold mmD_post; finish.
    (* [comment removed for export] *)
    zstep. zstep. rewrite zb_lxor_ones by lia. if_falseU.
    zstep. zstep. rewrite ltu_m65 by lia.
    destruct (Z_lt_le_dec n 65) as [SMALL | BIG].
    2:{ replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
        if_trueU. zstep. if_trueU. ripD DST n lo SCS. }
    destruct (Z.eq_dec n 0) as [N0 | NZ].
    { replace ((1 <=? n) && (n <=? 64))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      if_trueU. subst n. zstep. zstep. unfold mmD_post; finish. }
    replace ((1 <=? n) && (n <=? 64))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
    if_falseU.
    destruct (HULL ltac:(lia)) as [HULL0 HULL1].
    ddestruct (qc_facts AL IMG ALWF CS CSOK ASB m DST n OBJ ltac:(lia) ltac:(lia) ltac:(lia) HULL0 HULL1 SHRD)
      as (q0 & q1 & w0 & w1 & E0 & E1 & Q01 & Q45 & DB & AOKS & RDS & RD0 & RD1 & H8a & H8b).
    do 11 zstep.
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (DST + n + -1) with (DST + n - 1) by lia.
    rewrite !Z.mod_small by lia.
    rewrite !land_m8 by lia. rewrite !hull_sh by lia.
    rewrite E0, E1.
    zstep. zstep. zstep. zstep.
    if_cases Kq.
    2:{ unfold mmD_post; finish. }
    shadow_byte OBJ (DST + n - 1) 1 as k RDk HK.
    rewrite ASB, Z.shiftr_div_pow2 in RDk by lia. change (2^3) with 8 in RDk. rewrite (Z.add_comm ((DST + n - 1) / 8) 2147450880) in RDk.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { destruct (Z_lt_le_dec (DST / 8) ((DST + n - 1) / 8)) as [LT|GE].
      - if_falseU. eapply amm_orloop with (k := 16%nat) (lo := 2147450880 + 8 * q0) (hi := 2147450880 + 8 * q1 + 8); try eassumption; [right; reflexivity | cbn [Z.of_nat]; lia | lia ..].
      - if_trueU. replace (DST / 8) with ((DST + n - 1) / 8) by lia. apply evtA_done. eexists. eexists. reflexivity. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a5' & a6' & ->)).
    zstep. zstep.
    if_cases Ks.
    2:{ ripD DST n lo SCS. }
    unfold mmD_post; finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac shrd_now SHRD MU SCS OBJD name :=
    lazymatch type of MU with munch ?W _ ?mx =>
      assert (name : forall c, CS c -> exists b, bytes_at asegs mx (shadow_of AL c) [b])
        by (eapply (shrd_munch AL CS CSOK W); [ | exact MU | exact SHRD ];
            unfold w_client; apply Forall_cons;
            [ cbn [fst snd]; lazymatch goal with |- crange _ _ (?a + ?k - _) => replace (a + k - a) with k by lia end;
              eapply aobj_crange; exact OBJD
            | apply Forall_cons; [cbn [fst snd]; exact SCS | apply Forall_nil] ])
    end.

  Definition amemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (DST n lo : Z) (ss : list byte) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u8arr asegs m' DST ss /\ stk asegs m' lo (bv_unsigned sp).

  Local Ltac2 Set LiaOrc.tbl := fun () => "05R0@C17025492443.117C17027589631.135C29675049067.141C29675049067.142K21979204025.141K21979204025.142K47064714985.140K47064714985.141K58434789865.140K58434789865.141K61309466857.140K61309466857.141L11123517328.1  L11239731393.4  L11255914340.95 L12283411672.131L12283411672.132L12283411672.88 L13225815175.131L13301871092.88 L13454883133.2  L14106684376.131L14106684376.132L14106684376.87 L14995614230.131L16029064082.131L16852238724.137L16852238724.138L17646078182.91 L17751112592.1  L19006798410.95 L20146841363.2  L2025501661.3   L21992643032.3  L22015551912.3  L23267971501.72 L235161816.136  L235161816.137  L25796462353.113L25796462354.95 L26130624665.4  L2666392125.2   L2716773170.131 L27501889588.95 L27501889591.113L28563140627.2  L29441512509.2  L30284306320.1  L31245493021.95 L31245493022.113L32460099653.2  L33818746643.2  L34035577502.132L34994544387.88 L3513748118.2   L35265264016.1  L35823981161.131L36436139936.136L36436139936.137L36914643987.2  L37819470141.2  L38250533172.95 L38250533175.113L38432703077.93 L39887139444.88 L40294402896.1  L40691620147.2  L41288976216.131L41288976216.132L41288976216.88 L43055353660.89 L43877851624.95 L43877851627.113L44549549206.2  L44866992728.131L44866992728.132L44866992728.88 L45800883475.2  L45898055924.88 L46030209441.0  L46229568912.1  L46638324410.4  L47075365651.2  L48429268312.131L48429268312.132L48429268312.88 L49092413757.2  L49129331261.2  L49356111292.135L49356111292.136L50169871760.1  L5145216728.131 L5145216728.132 L5145216728.88  L51925114228.88 L52499634749.2  L54243326995.2  L54422382992.1  L54668938301.2  L55843909098.3  L57933933556.88 L58119466785.94 L58130246816.112L58423753747.2  L60268184117.113L60268184118.95 L61320439059.2  L61390376978.95 L61935960466.95 L63962036340.87 L64253079557.113L64253079558.88 L64253079558.95 L64319148573.2  L64788204432.1  L65655075046.4  L65868959243.1  L66493423933.2  L67158371251.131L67158371251.132L67158371251.88 L67275561872.1  L68354046352.1  L7274816372.88  L7373312899.91  L8064833853.2   L8722184664.131 L8722184664.132 L8722184664.88  L8830339091.2   L9121157098.3   N44259866089.118N58594013575.136N64040766665.118N6820435427.136 O10240217556.141O10240217556.142O14206727921.117O14208825045.135O15545405653.135O15547502833.117O17025492443.117O17027589631.135O23485702385.117O23487799509.135O28953822661.135O28955919841.117O29675049067.141O29675049067.142O30179188619.140O30179188619.141O30286673803.140O30286673803.141O32129484501.135O32131581681.117O34072225748.141O34072225748.142O3521469857.142 O3521469857.143 O35907574667.140O35907574667.141O38504098033.117O38506195157.135O42849031057.117O42851128245.135O43116495243.140O43116495243.141O4352777611.140 O4352777611.141 O4492316913.117 O4494414037.135 O45584088819.117O45586185943.135O48635945867.140O48635945867.141O48978854641.117O48980951765.135O50651377905.117O50653475029.135O52201094539.140O52201094539.141O54335600011.140O54335600011.141O55436697483.140O55436697483.141O62532530571.140O62532530571.141O65483384533.135O65485481713.117O66103434849.140O66103434849.141O66254176497.117O66256273621.135O7921967435.140 O7921967435.141 P11136886036.97 P11136886036.98 P11225555076.135P11227652256.117P13440002940.135P13442100056.117P17762908436.97 P17762908436.98 P20140522217.140P20140522217.141P2020832220.97  P2020832220.98  P21979204025.141P21979204025.142P22027872681.97 P22027872681.98 P26127147256.117P26129244380.135P2650994812.135 P2653091928.117 P28568546793.140P28568546793.141P29428729432.117P29430826620.135P30297150740.97 P30297150740.98 P33813332713.140P33813332713.141P35252419348.97 P35252419348.98 P36925037033.140P36925037033.141P37830017916.135P37832115032.117P40289946068.97 P40289946068.98 P40697808073.140P40697808073.141P45791156457.140P45791156457.141P46232977172.97 P46232977172.98 P46625147103.140P46625147103.141P49103625084.135P49105722200.117P49133717592.117P49135814780.135P50173804308.97 P50173804308.98 P52510050428.135P52512147544.117P54249710057.140P54249710057.141P54410586900.97 P54410586900.98 P54665076312.117P54667173500.135P55836798992.141P55836798992.142P64312787036.135P64314884216.117P64783223060.97 P64783223060.98 P65658691719.142P65658691719.143P66498474840.117P66500572028.135P67262191892.97 P67262191892.98 P68366891796.97 P68366891796.98 P8059128700.135 P8061225816.117 P8841319913.140 P8841319913.141 P9110442512.141 P9110442512.142 Q13482121755.94 Q15457446739.94 Q15457446739.95 Q15643324129.93 Q15647878503.137Q15647878503.138Q17974635083.94 Q18361895783.137Q18361895783.138Q18363828454.94 Q19120365881.97 Q21877548677.94 Q21892523268.137Q21892523268.138Q24394897947.94 Q25513505925.96 Q25513505925.97 Q27905103109.94 Q27911231108.137Q27911231108.138Q31258583015.137Q31258583015.138Q31269428326.94 Q32653403622.94 Q32659924583.137Q32659924583.138Q33251554080.94 Q33913700356.137Q33913700356.138Q33916158853.94 Q35419777341.142Q36330714342.142Q36423785477.94 Q36438237060.137Q36438237060.138Q36722022172.94 Q38248387216.117Q38250484404.135Q3832524549.94  Q3834260612.137 Q3834260612.138 Q39935065476.137Q39935065476.138Q39941651973.94 Q41139448935.137Q41139448935.138Q41154490342.94 Q43855338817.94 Q43877802600.135Q43879899724.117Q43928033258.95 Q44650941030.94 Q44652743143.137Q44652743143.138Q49598033755.94 Q49698585326.95 Q49698585326.96 Q51000317356.94 Q51223049447.137Q51223049447.138Q51233699686.94 Q51241048331.94 Q53519968678.94 Q57916578385.94 Q59830194919.137Q59830194919.138Q59841040742.94 Q60268184117.113Q60268184118.95 Q62283281657.97 Q62283281657.98 Q64536302640.94 Q66524164229.94 Q66534486788.137Q66534486788.138Q67806143243.94 Q7377275490.96  Q7377275490.97  Q9838812676.137 Q9838812676.138 Q9843367298.93  00000100200300400500600_01H02102Z03G04404504604J04T04^04h05<05F05G05Q05[05e06906M06^06o07907:07i07j07k07l07m08m09709A09W09m09n09o0:E0:F0:G0:H0:I0:J0:[0:l0:m0:n0;<0;F0;M0;N0;b0<30<D0<E0<F0<P0<Z0<d0<n0<o0=00=:0=D0=N0=_0=l0>90>@0>J0>T0>^0>_0>i0>j0>k0>l0>m0?70?A0?K0?L0?M0?W0?a0?b0?l0@60@@0@J0@K0@L0@M0@N0@O0@Y0@f0A30A40AM0Af0Ag0BV0Bl0C60Ce0DT0EC0ED0EE0EF0EJ0EK0EU0E_0Ei0Ej0Ek0F50FF0FG0FQ0F[0Fe0Ff0Fg0G:0GM0G`0H30H40H50H60H70H80H90HD0HO0HP0HQ0HR0HS0HT0HU0HV0HW0HX0HY0HZ0H[0H\0H]0H^0H_0H`0Ha0Hb0Hc0Hd0He0Hf0Hg0Hh0Hi0Hj0Hk0Hl0Hm0Hn0Ho0I00I10I20I30I40I50I60I70I80I90I:0I;0I<0I=0I>0I?0I@0IA0IB0IC0Ij0Jc0KA0K_0L00LA0Lh0Ma0NJ0O30Og0Pm0Pn0Po0Qc0Ri0SG0Se0T60TG0U00UY0Uj0V;0Vb0W[0XD0Xm0YT0ZM0[60[_0\00\A0\h0]a0^J0_30_\0`E0`l0ae0b>0bW0bh0c90cJ0c[0dB0e;0eL0e]0fF0fo0gV0hO0h`0i10iN0ik0j<0jM0k40km0lY0lZ0lk0m<0mc0n\0oC10<10M10^11G12012M12j13113>13K13X13e14214314@14M14Z15=15N15_16016?16^17O17`18118B18O18\18i19619C19P19Q19b1:31:D1:Q1:\1:m1;>1;O1;P1;Z1;d1<51<F1<W1<h1=91=J1=W1=d1>11>@1>M1>Z1>g1?41?A1?N1?O1?f1@=1@>1@K1@X1@e1@l1A<1AK1AX1Ae1B21BK1Bd1CM1DH1DI1DZ1Dk1E<1EK1En1F`1G11GB1GSFFFFFFS3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP43AP22sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP43AP22sp2lo3LO03SPL5DISJDFFS3DST3SRC1n2ds2ss2B0S2sp2ds2ssS2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss2B0S2sp2ds2ssFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss2B0S3DST3SRC1n2ds2ss2B0S2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2ds2ssFS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSFFFFS2sp3DST3SRC1n2lo2ds2ss4LEND3ARD3ARS3AP13AP23AP33AP43AP53LO03SPLS2sp2ds2ssS2sp2ds2ssS3DST3SRC1n2ds2ss1N2B0S3DST3SRC1n2ds2ss1N2B0FFS3DST3SRC1n2ds2ss1N2B0FFFFFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLFFS1n2ds2ss4LENDS2sp2ds2ssS2sp2loFS3DST3SRC1n2ds2ss2B0S2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLFFS2lo2ds2ssS2lo2ds2ssS2sp2ds2ssS2sp2ds2ssFFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2loS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssFS2sp2ds2ssSFFFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssFFS2sp2ds2ssS2sp2ds2ssFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssFFFFFS2sp2ds2ssS3DST1n2ds2ssS3DST1n2ds2ssFS2sp2lo2ds2ss3LO03SPL3SPRS2sp2lo2ds2ss3LO03SPL3SPRFS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss1N2B0S2sp2ds2ssS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSS3DST3SRC1n2ds2ss4LEND2B02sp2lo3SPL5DISJD5DISJSFFFS2spFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssFFS2sp2ds2ssS2sp2lo2ds2ss3SPLFS2sp2ds2ssS2sp2ds2ssS2sp2ds2ssFFS2sp2lo2ds2ss3x171CS2sp2lo2ds2ss3x351CS2sp2lo2ds2ss3x171CS2sp2lo2ds2ss3x351CFFFFFFS2sp2lo3SPLS2sp2lo3SPLFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp3SRC1n2lo2ds2ss4LENS5DISJSS2sp3SRC1n2lo2ds2ss4LENS5DISJSS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2ra2sp3DST1n2lo2ds2ss4LEND3SPL5DISJD2HB5Ha_st5Hl_stS2sp2s03DST1n2lo2ds2ss4LEND3SPL5DISJD2HB5Ha_st5Hl_st2s12s22s32s42s52s6FFS2ra2sp3SRC1n2lo2ds2ss4LENS3SPL5DISJS2HB5Ha_st5Hl_stS2sp2s03SRC1n2lo2ds2ss4LENS3SPL5DISJS2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp3DST1n2lo2ds2ss4LEND5DISJDS2sp3DST1n2lo2ds2ss4LEND5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP52sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp3DST1n2lo2ds2ss5DISJDS2sp3DST1n2lo2ds2ss5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP32sp2lo3LO03SPL5DISJDS2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2sp3DST1n2lo2ds2ss3SPL5DISJDS2sp3DST1n2lo2ds2ss3SPL5DISJDS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp3DST3SRC1n2lo2ds2ss3SPL5DISJD5DISJS4LENSFS2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2ra2sp2lo2ds2ss3LO03SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3LO03SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp2lo2ds2ss3LO0S2sp2lo2ds2ss3LO0S3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS3DST3SRC1n2ds2ss3AP12sp2lo3LO03SPL5DISJDS2sp3DST1n2lo2ds2ss3SPL5DISJDS2sp3DST1n2lo2ds2ss3SPL5DISJDS2ds2ssS2sp2ds2ss2HBS2sp2ds2ss2HBS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2s62lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2AL2ds2ss4IMG'S2ra2sp2lo2ds2ss2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss2HB5Ha_st5Hl_st2s12s22s32s42s52s6S2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS3DST1n2ds2ssS3DST2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLFS2lo2ds2ssS2lo2ds2ssS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2AL2ds2ss4IMG'S2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2ds2ss2HBS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssFS2sp2ds2ss3SPR2HB5Ha_stS2sp2ds2ss3SPR2HB5Ha_stFS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2ds2ssS2AL2ds2ss5ALWF'S2AL2ds2ss4IMG'S2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ssS2sp2lo2ds2ss3LO03SPL3SPRS2sp2lo2ds2ss3LO03SPL3SPRS2ra2sp3DST1n2lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2s03DST1n2lo2ds2ss3SPL2HB5Ha_st5Hl_st2s12s22s32s42s52s6FS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2AL2ds2ss4IMG'S2ra2sp2lo2ds2ss3SPL2HB5Ha_st5Hl_stS2sp2s02lo2ds2ss3SPL2HB5Ha_st5Hl_st2s12s22s32s42s5S2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPLS2sp2lo2ds2ss3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Theorem amemmove_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (DST SRC n lo : Z) (ds ss : list byte),
    u8arr asegs m DST ds -> bytes_at asegs m SRC ss -> Z.of_nat (length ds) = n -> Z.of_nat (length ss) = n ->
    aobj asegs AL CS m DST n -> aobj asegs AL CS m SRC n ->
    n < 2^40 -> app_range DST (DST + n + 7) -> app_range SRC (SRC + n + 7) ->
    (1 <= n -> crange CS (DST - DST mod 64) 64 /\ crange CS (DST + n - 1 - (DST + n - 1) mod 64) 64) ->
    (1 <= n -> crange CS (SRC - SRC mod 64) 64 /\ crange CS (SRC + n - 1 - (SRC + n - 1) mod 64) 64) ->
    (forall c, CS c -> exists b, bytes_at asegs m (shadow_of AL c) [b]) ->
    amem_consts m -> amem_apart DST n ->
    stk asegs m lo (bv_unsigned sp) -> HSE < lo -> lo <= bv_unsigned sp - 2224 ->
    crange CS lo (bv_unsigned sp - lo) ->
    (DST + n <= lo \/ bv_unsigned sp <= DST) -> (SRC + n <= lo \/ bv_unsigned sp <= SRC) -> mem_inv asegs m ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 SRC -> a2 = Z_to_bv 64 n ->
    evtA asegs AL CS (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n lo ss m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x68498) fc None m (seg_rom asegs)).
  Proof.
    intros until ss. (intros ARR SRCB LEND LENS OBJD OBJS N ARD ARS HULLD HULLS SHRD AC dd_H; ddestruct dd_H as (AP1 & AP2 & AP3 & AP4 & AP5); intros ST LO0 SPL SCS DISJD DISJS MI -> -> ->). al_facts. unfold app_range in ARD, ARS.
    assert (B0 : 0 < DST /\ 0 <= n /\ DST + n + 7 <= HME /\ 0 < SRC /\ SRC + n + 7 <= HME) by lia.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(DST, DST + n); (lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof AC as AC'. destruct AC as [AC1 AC2 AC3 AC4 RC]. pose proof RC as RC'. destruct RC as [RC1 RC2 RC3 RC4 RC5 RC6 RC7 RC8].
    pose proof (rw_cells_of_u8arr asegs m DST ds ARR) as DSTC. clear ARR.
    destruct DISJD as [DISJD|DISJD]; destruct DISJS as [DISJS|DISJS].
    all: carve_frame 64%nat ST; rename FR into FRS; carve_frame 2080%nat ST.
    all: do 15 zstep.
    all: shrd_now SHRD MU SCS OBJD SHRD0.
    all: zstep; zstep; zstep; zstep.
    all: rewrite zb_lxor_ones by lia; if_falseU.
    {
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkS with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLS | exact SHRD0 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      clear SHRD0; shrd_now SHRD MU SCS OBJD SHRD1.
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkD with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLD | exact SHRD1 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      zstep.
      lazymatch goal with Hd : rw_cells _ ?mx DST [CB ?kk ?bs], Hs : bytes_at _ ?mx SRC ss |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply (imemmove_spec AL IMG ALWF CS CSOK n DST SRC ss);
                [ lia | exact LENS | exact Hs | (pose proof (proj2 Hd) as HW; cbn [cells_size csize] in HW; rewrite Nat.add_0_r in HW; replace (Z.of_nat kk) with n in HW by lia; exact HW) | exact (aobj_crange _ _ _ _ _ _ OBJD) | exact (aobj_crange _ _ _ _ _ _ OBJS)
                | lia | lia | lia | lia | assumption | reflexivity | reflexivity | reflexivity ])
      end.
      do 11 zstep.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -64)%Z end.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FRS H (bv_unsigned sp) end.
      unfold amemmove_post; finish.
      lazymatch goal with HB : bytes_at _ ?mx DST ss, HW : wr_at _ ?mx DST n |- u8arr _ ?mx DST ss => split; [exact HB| rewrite LENS; exact HW] end. }
    {
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkS with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLS | exact SHRD0 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      clear SHRD0; shrd_now SHRD MU SCS OBJD SHRD1.
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkD with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLD | exact SHRD1 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      zstep.
      lazymatch goal with Hd : rw_cells _ ?mx DST [CB ?kk ?bs], Hs : bytes_at _ ?mx SRC ss |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply (imemmove_spec AL IMG ALWF CS CSOK n DST SRC ss);
                [ lia | exact LENS | exact Hs | (pose proof (proj2 Hd) as HW; cbn [cells_size csize] in HW; rewrite Nat.add_0_r in HW; replace (Z.of_nat kk) with n in HW by lia; exact HW) | exact (aobj_crange _ _ _ _ _ _ OBJD) | exact (aobj_crange _ _ _ _ _ _ OBJS)
                | lia | lia | lia | lia | assumption | reflexivity | reflexivity | reflexivity ])
      end.
      do 11 zstep.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -64)%Z end.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FRS H (bv_unsigned sp) end.
      unfold amemmove_post; finish.
      lazymatch goal with HB : bytes_at _ ?mx DST ss, HW : wr_at _ ?mx DST n |- u8arr _ ?mx DST ss => split; [exact HB| rewrite LENS; exact HW] end. }
    {
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkS with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLS | exact SHRD0 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      clear SHRD0; shrd_now SHRD MU SCS OBJD SHRD1.
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkD with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLD | exact SHRD1 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      zstep.
      lazymatch goal with Hd : rw_cells _ ?mx DST [CB ?kk ?bs], Hs : bytes_at _ ?mx SRC ss |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply (imemmove_spec AL IMG ALWF CS CSOK n DST SRC ss);
                [ lia | exact LENS | exact Hs | (pose proof (proj2 Hd) as HW; cbn [cells_size csize] in HW; rewrite Nat.add_0_r in HW; replace (Z.of_nat kk) with n in HW by lia; exact HW) | exact (aobj_crange _ _ _ _ _ _ OBJD) | exact (aobj_crange _ _ _ _ _ _ OBJS)
                | lia | lia | lia | lia | assumption | reflexivity | reflexivity | reflexivity ])
      end.
      do 11 zstep.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -64)%Z end.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FRS H (bv_unsigned sp) end.
      unfold amemmove_post; finish.
      lazymatch goal with HB : bytes_at _ ?mx DST ss, HW : wr_at _ ?mx DST n |- u8arr _ ?mx DST ss => split; [exact HB| rewrite LENS; exact HW] end. }
    {
      lazymatch goal with OBJx : aobj _ _ _ ?mx SRC n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkS with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLS | exact SHRD0 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      clear SHRD0; shrd_now SHRD MU SCS OBJD SHRD1.
      lazymatch goal with OBJx : aobj _ _ _ ?mx DST n |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA_sp (bv_unsigned sp + -2144)
          (eapply amemmove_chkD with (DST := DST) (SRC := SRC) (n := n) (lo := lo);
           rewrite ?(unsigned_lit (bv_unsigned sp + -2144)) by lia;
           first [ exact OBJx | exact HULLD | exact SHRD1 | split; assumption | eassumption
                 | reflexivity | f_equal; lia | unfold app_range; lia | lia | eapply crange_sub; [exact SCS | lia | lia] ])
      end.
      zstep.
      lazymatch goal with Hd : rw_cells _ ?mx DST [CB ?kk ?bs], Hs : bytes_at _ ?mx SRC ss |- _ (MS _ _ _ _ _ ?mx _) =>
        callxA (eapply (imemmove_spec AL IMG ALWF CS CSOK n DST SRC ss);
                [ lia | exact LENS | exact Hs | (pose proof (proj2 Hd) as HW; cbn [cells_size csize] in HW; rewrite Nat.add_0_r in HW; replace (Z.of_nat kk) with n in HW by lia; exact HW) | exact (aobj_crange _ _ _ _ _ _ OBJD) | exact (aobj_crange _ _ _ _ _ _ OBJS)
                | lia | lia | lia | lia | assumption | reflexivity | reflexivity | reflexivity ])
      end.
      do 11 zstep.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp + -64)%Z end.
      lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FRS H (bv_unsigned sp) end.
      unfold amemmove_post; finish.
      lazymatch goal with HB : bytes_at _ ?mx DST ss, HW : wr_at _ ?mx DST n |- u8arr _ ?mx DST ss => split; [exact HB| rewrite LENS; exact HW] end. }
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
