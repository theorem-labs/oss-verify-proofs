(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface
AFake5_iface AH_fse_kit AF_fse_iface AF_fse_rd_iface AH_fse_B2 AH_fse_Bglue AH_fse_Hiface AH_fse_Biface AF_fse_rd_asm.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Import ITree.Exc.
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
Open Scope mspec_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac cl := repeat match goal with H : _ |- _ => clear H end.
Section CANSEC1. Context {rc : runConstT}.
Section Wrap.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Hypothesis U32R : prod_u32r_stmtA.
Hypothesis I32R : prod_i32r_stmtA.
Hypothesis WBOUND : fse_wbound_stmtA.
Hypothesis WRITE : fse_write_stmtA.
Hypothesis ISERR : fse_iserror_stmtA.
Variables (L : alayout) (RNG0 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(FR : bvmap 5 word) (fc : bv 32) (s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem).
Notation SP := (bv_unsigned sp).
Hypothesis HLB : forall b, In b LB -> exists p A n, b = HB p A n.
Hypothesis PAY : AHarness_iface.payload_atA LB D pl.
Hypothesis PAYB : bytes_at bsegs m0 D (map (Z_to_bv 8) pl).
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis D16 : D mod 16 = 0.
Hypothesis SZ : zlength pl < 2^26.
Hypothesis BOT : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis SPG : SP + ATRUN_DEPTH = al_sp0 L.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis TP : tp = Z_to_bv 64 ATP.
Hypothesis RSTK0 : rng RNG0 lo (al_top L - lo).
Hypothesis RI0 : rng_aimg RNG0.
Hypothesis RISH0 : rng_aimg_sh RNG0.
#[using="D HLB BOT LOS SPG"] Lemma pag_outsideBB : forall RNGx st mx pP P F a,
AHEAP AI L RNGx st (HB pP P PRODUCER_SIZE :: FB5 F :: LB) mx -> ablk F (F + 2048) ->
aclient_addr CI LB SP a ->
(a < lo \/ SP <= a) /\ ~ (F <= a < F + 2048) /\ ~ (SHF F <= a < SHF F + 256) /\ ~ (P <= a < P + PRODUCER_SIZE).
Proof.
intros RNGx st mx pP P F a AHx FH Ha. pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof atop_range as ATR. unfold AHARNESS_STACK in LOS.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
Local Ltac2 Set LiaHints.tbl := fun () => "00;0>20598018897.1529786595198.8334301889471.2236663620671.2136663620798.2636663620798.2943731946175.1445808702507.1553410728957.84696035827.64  9298445489.88 00000@00E00]01901U02?02Q02a03803=03bS2FB3A471H2H02H4S3PL2S3FH13FH33A471H2H02H42H5S3BOT2Hr3FH13ATR3PL11H2H02H1S3BOT3LOS1X3FH33ATR3PL31H2H0S3BOT2Hr3FH23FH33ATR2FB2DJ3DJP3R1c2RB1H2H0S3BOT3ATR3A471H2H0S2PB3A471H2H02H4S1X3FH23ATR3RSP3PR23PL2S3RSPS2Hr3FH23ATR3RSP3LY13LY43PR23PL21H2H0".
pose proof (harness_topF L SP SPG ltac:(lia)) as [T1 T2].
pose proof (AI_layout AI _ _ _ _ _ AHx) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof (ablk_disj_band _ _ FH) as FB. unfold KLS in FB.
assert (INP : In (HB pP P PRODUCER_SIZE) (HB pP P PRODUCER_SIZE :: FB5 F :: LB)) by (left; reflexivity).
assert (INF : In (FB5 F) (HB pP P PRODUCER_SIZE :: FB5 F :: LB)) by (right; left; reflexivity).
destruct (AI_block AI _ _ _ _ _ _ _ _ AHx INP) as (_ & (PR1 & PR2 & PR3 & PR4) & _).
pose proof (ablk_lin _ _ PR1) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
pose proof (ablk_disj_band _ _ PR1) as PB. unfold KLS in PB.
pose proof (AI_blocks_nodup AI _ _ _ _ _ AHx) as ND. apply NoDup_cons_iff in ND as [NIP _].
assert (SB : SHF F = F / 8 + ASHOFF) by (unfold SHF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
rewrite SB. unfold ASHOFF, PRODUCER_SIZE in *.
destruct Ha as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- clear - X FH2 FH3 FH4 FB ATR BOT LOS PL3 PB T1 LY3. Z.div_mod_to_equations. lia.
- pose proof (AI_aci_img AI iv Hiv). unfold AIMG_HI in *. cbn in Hr. clear - H Hr FH1 FB ATR BOT PL1. Z.div_mod_to_equations. lia.
- destruct (HLB _ Hb) as (p & A & N & ->). cbn in Hr.
assert (INB : In (HB p A N) (HB pP P 16 :: FB5 F :: LB)) by (right; right; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx INB INF ltac:(discriminate)) as DJ. cbn [ab_addr ab_size] in DJ.
assert (NE : HB p A N <> HB pP P 16) by (intros E; apply NIP; right; rewrite <- E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AHx INB INP NE) as DJP. cbn [ab_addr ab_size] in DJP.
destruct (AI_block AI _ _ _ _ _ _ _ _ AHx INB) as (_ & (R1 & R2 & R3 & R4) & _).
pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d). unfold AIMG_HI in R1a.
pose proof (ablk_disj_band _ _ R1) as RB. unfold KLS in RB.
clear - Hr DJ DJP R1a R1b R1c R2 R3 RB FB FH2 FH3 ATR BOT. Z.div_mod_to_equations. lia.
- assert (A47 : 0 <= a' < 2^47 /\ (ATOP <= a' \/ a' < AIMG_HI)).
{ destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; cbn in Hr; lia|].
destruct (HLB _ Hb') as (p & A & N & E'). discriminate. }
rewrite shad_div. unfold ASHOFF. unfold AIMG_HI in A47.
split; [| split; [| split]].
+ clear - A47 ATR BOT. Z.div_mod_to_equations. lia.
+ clear - A47 FB FH2 FH3. Z.div_mod_to_equations. lia.
+ clear - A47 FH1 FH2 FH3 ATR. Z.div_mod_to_equations. lia.
+ clear - A47 PB PL2 PL3. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="U32R I32R WBOUND WRITE ISERR HLB PAY PAYB PLB D16 SZ BOT LOS SPG SP16 RSTK0 RI0 RISH0"] Theorem fz_BB_main : forall pP s1' RNG1 ms,
fzC_state AI fflag L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms ->
evtF bsegs RNG1 (fzB_state AI fflag L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1) ms.
Proof.
intros pP s1' RNG1 ms FZC.
destruct FZC as (P & F & SPA & m & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & jb & jc & jd & junk
& ESPA & -> & AH & REST & FLE & AG & BR & RP & RPS & PCELL & F2048 & FH & FC & RF & RSF & FFC & SH & ST & FRA & STG & FRB & MI).
unfold zlength in *.
pose proof atop_range as ATR. pose proof LOS as LOS'. unfold AHARNESS_STACK in LOS'.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
Local Ltac2 Set LiaHints.tbl := fun () => "00X0?1054690857.12  14999122649.0  1760544892.192 18228993317.19219191014643.1921952185540.2   22766053480.13423490941431.1  24194177746.0  27241613824.2  27732208553.15 29757353573.0  29786644167.18730652496693.19233980288969.4  37775326631.14 38123278910.3  38948636245.0  40006224113.19240380733653.4  41980222686.12 42953480556.2  4567411936.192 46341829197.19252101720239.3  52101721001.3  52107990421.11 52564820711.15 52565051749.14 52565051749.16 53244475689.13955074838520.2  56043687309.10 56174447011.8  58148693845.0  59117673074.19265685863065.4  66151427842.16 696035827.2    8383862316.2   00000?00@00M00Z00g00l01801901:01?01e01f02302@02H02W02\02]02n03303B03G03T03a03e03i04>04d05C05b05n06306A06E06F06S06X07307807=S2T13LY36SPA120SS3FH23PL23LB'S3FH23PL23LB'S3FH23PL23LB'S3PL2S3FH23PL22HiSSS3DL2S3BOT3ATR4LOS'4SPAB3FH32PF3BSF3FBD3PBDSS3FH23PL23LB'S3FH23PL23LB'S2T13LY3S1H2H02H42H52H8S3DL4SS3FH13FH23PL23LB'S3D3jS3BOT4LOS'4SPABS3PL4S3FH23PL23LB'S3FH23PL23LB'S2O2S2O4S4LOS'4SPAB6SPA1202O1S3BOT3ATR4LOS'4SPAB3FH32PF3BSF3FBD3PBDS3BOT3ATR4LOS'4SPAB3FH33PL33BSFS3BOT3ATR4LOS'4SPAB3FH33PL33BSFS3FH23PL22HaS3PL1S3FH13FH41H2H0S2T1SS3FH23PL23LB'S3D2jS3D161H2H02H43P163DR45F2048S3RSPS3FH1".
pose proof (harness_topF L SP SPG ltac:(clear - RSP; lia)) as [T1 T2].
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA120).
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof BR as (BLKP & PB1 & PB2 & P16). unfold PRODUCER_SIZE in BLKP, PB2, RP, RPS.
pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
assert (SPT : SP + 16 <= 2^47) by (clear - T1 LY3; lia).
assert (RSTK1 : rng RNG1 lo (SP - lo)) by (eapply rng_sub'; [exact (rng_fp_le _ _ _ _ FLE RSTK0)| clear - T1 LOS' BOT; lia]).
pose proof (rng_fp_le _ _ _ _ FLE RI0) as RI1. pose proof (rng_fp_le _ _ _ _ FLE RISH0) as RISH1.
set (LB1 := HB pP P PRODUCER_SIZE :: FB5 F :: LB) in *.
assert (INP : In (HB pP P PRODUCER_SIZE) LB1) by (left; reflexivity).
assert (INF : In (FB5 F) LB1) by (right; left; reflexivity).
pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND.
assert (NIP : ~ In (HB pP P PRODUCER_SIZE) LB).
{ intros Hb. inversion ND as [|x l NI _]. apply NI. right. exact Hb. }
assert (PF : P + 16 <= F \/ F + 2048 <= P).
{ pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH INP INF ltac:(discriminate)) as DJ. cbn in DJ. unfold PRODUCER_SIZE in DJ. exact DJ. }
assert (DFACTS : ((pl = [] /\ D = AEMPTY) \/ ablk D (D + zlen pl)) /\ rng RNG1 D (zlen pl) /\ rng RNG1 (shad D) (nshad (zlen pl))
/\ (D + zlen pl <= P \/ P + 16 <= D) /\ (D + zlen pl <= F \/ F + 2048 <= D)).
{ destruct PAY as [(pD & HinD & NZ)|(-> & ->)].
- unfold zlength in HinD, NZ.
assert (IN1 : In (HB pD D (zlen pl)) LB1) by (right; right; exact HinD).
destruct (AI_block AI _ _ _ _ _ _ _ _ AH IN1) as (_ & (DR1 & DR2 & DR3 & DR4) & RDx & RDSx & _).
assert (NE2 : HB pP P PRODUCER_SIZE <> HB pD D (zlen pl)) by (intros E; apply NIP; rewrite E; exact HinD).
assert (NE3 : FB5 F <> HB pD D (zlen pl)) by discriminate.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH INP IN1 NE2) as D2j.
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH INF IN1 NE3) as D3j.
cbn [ab_addr ab_size] in D2j, D3j. unfold PRODUCER_SIZE in D2j.
split; [right; exact DR1|]. split; [exact RDx|]. split; [rewrite <- shlen_nshad; exact RDSx|].
split; [clear - D2j; lia| clear - D3j; lia].
- cbn [length Z.of_nat]. unfold AEMPTY.
split; [left; split; reflexivity|].
split; [eapply rng_sub'; [exact RI1| cl; lia]|].
split; [eapply rng_sub'; [exact RISH1| rewrite shad_div, nshad_div; unfold ASHOFF; cbn [Z.of_nat]; cl; Z.div_mod_to_equations; lia]|].
split; [clear - PL1; lia| clear - FH1; lia]. }
destruct DFACTS as (DLOC & RD & RDS & DP & DF).
assert (D8 : D mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
assert (PAYm : bytes_at bsegs m D (map (Z_to_bv 8) pl)).
{ destruct PAY as [(pD & HinD & NZ)|(-> & ->)].
- eapply bytes_at_magree; [exact AG| exact PAYB|]. rewrite length_map. intros a Ha.
eapply cl_block; [exact HinD| cbn; unfold zlength in Ha |- *; lia].
- unfold bytes_at. cbn [map length Z.of_nat]. split; [unfold AEMPTY; cl; lia|]. split; [unfold AEMPTY; cl; lia|]. intros i Hi. lia. }
assert (UNPX : forall R q mx, AHEAP AI L R q LB1 mx -> unpoisoned mx P (P + 16)).
{ intros R q mx AHx. destruct (AI_block AI _ _ _ _ _ _ _ _ AHx INP) as (_ & _ & _ & _ & SHP & _).
replace (P + 16) with (P + PRODUCER_SIZE) by reflexivity.
apply ablock_unpoisonedR; [exact SHP| clear - P16; Z.div_mod_to_equations; lia| clear - PL2; lia| unfold PRODUCER_SIZE; cl; lia| unfold PRODUCER_SIZE; clear - PL4; lia]. }
assert (UNDX : forall R q mx, AHEAP AI L R q LB1 mx -> unpoisoned mx D (D + zlen pl)).
{ intros R q mx AHx. destruct PAY as [(pD & HinD & NZ)|(-> & ->)].
- unfold zlength in HinD, NZ.
destruct (AI_block AI _ _ _ _ _ _ _ _ AHx (or_intror (or_intror HinD))) as (_ & (DR1 & DR2 & DR3 & DR4) & _ & _ & SHD & _).
pose proof (ablk_lin _ _ DR1) as (DL1 & DL2 & DL3 & DL4).
apply ablock_unpoisonedR; [exact SHD| clear - DR4; Z.div_mod_to_equations; lia| clear - DL2; lia| cl; lia| clear - DL4; lia].
- cbn [length Z.of_nat]. apply unpoisoned_nil. unfold AEMPTY; cl; lia. }
pose proof (proj2 FFC) as WRF. change (Z.of_nat (cells_size _)) with 2048 in WRF.
apply (rw_cells_split_CB _ _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x15f28); C8 (Z_to_bv 64 0x80d20)] _ _
[C8 (Z_to_bv 64 (fflag L 5 F))] [8%nat; 512%nat; 64%nat; 512%nat; 640%nat; 4%nat; 276%nat]) in FFC; [| reflexivity].
cbn [mk_CB_cells app] in FFC.
pose proof (rw_cells_nth _ _ _ 4 _ FFC eq_refl) as DATAC. cbn [firstn cells_size csize Nat.add] in DATAC. change (Z.of_nat 32) with 32 in DATAC.
pose proof (rw_cells_nth _ _ _ 6 _ FFC eq_refl) as NCJ. cbn [firstn cells_size csize Nat.add] in NCJ. change (Z.of_nat 608) with 608 in NCJ.
pose proof (rw_cells_nth _ _ _ 8 _ FFC eq_refl) as MSVC. cbn [firstn cells_size csize Nat.add] in MSVC. change (Z.of_nat 1760) with 1760 in MSVC.
pose proof (rw_cells_nth _ _ _ 10 _ FFC eq_refl) as FLP. cbn [firstn cells_size csize Nat.add] in FLP. change (Z.of_nat 2040) with 2040 in FLP.
apply (proj1 (rw_cells_app _ _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x15f28); C8 (Z_to_bv 64 0x80d20)] _)) in FFC.
destruct FFC as [HDR _].
pose proof (fse_rtall_of_aheap AI _ _ _ _ _ AH) as RT.
pose proof (UNPX _ _ _ AH) as UNP. pose proof (UNDX _ _ _ AH) as UND.
eapply evtF_mono.
{ exact (pB_all U32R I32R WBOUND WRITE ISERR gp tp sp FR fc SPA lo F P D pl RNG1 LOS BOT SPT SP16 ESPA RSTK1 RI1 FH FC F2048 RF RSF
BLKP P16 RP RPS PF DLOC D8 RD RDS DP DF PLB SZ
y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 18446744073709551602) s4 s5 (Z_to_bv 64 (zlen pl)) (Z_to_bv 64 D) y28 y29 y30 y31 m
jb jc jd _ _ _ MI ST PCELL PAYm RT UNP UND FRA DATAC NCJ MSVC SH). }
cbv beta. intros ms' PO.
destruct PO as (tl & msv & nc & data & dsz & bsz & rem & buf' & jb' & jc' & jd' & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7
& x25 & x27 & t3 & t4 & t5 & t6 & m' & EA & -> & MU & WM & MI' & ST' & PR' & PAY' & FRA' & NCA & DATAA & LB' & FB'
& MSVC' & SH').
unfold W_B in MU.
assert (SBF : SHF F = F / 8 + ASHOFF) by (unfold SHF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (BSF : 2147450880 <= SHF F /\ SHF F + 256 <= 17594333495296) by (rewrite SBF; unfold ASHOFF; clear - FH1 FH4; Z.div_mod_to_equations; lia).
pose proof (ablk_disj_band _ _ FH) as FBD. unfold KLS in FBD.
pose proof (ablk_disj_band _ _ BLKP) as PBD. unfold KLS in PBD.
Local Ltac xwb := cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ FZRB13].
apply (rw_cells_transport bsegs [(P + 8, P + 16); (SPA - 2224, SPA + 120); (F + 32, F + 1780); (SHF F, SHF F + 256)] m m' F _) in HDR;
[| exact MU| exact WM| xwb; clear - PF FH3 BSF FBD PBD SPAB LOS' BOT ATR; lia].
apply (rw_cells_transport bsegs [(P + 8, P + 16); (SPA - 2224, SPA + 120); (F + 32, F + 1780); (SHF F, SHF F + 256)] m m' (F + 2040) _) in FLP;
[| exact MU| exact WM| xwb; clear - PF FH3 BSF FBD PBD SPAB LOS' BOT ATR; lia].
apply (stk_transport_disjoint bsegs [(P + 8, P + 16); (SPA - 2224, SPA + 120); (F + 32, F + 1780); (SHF F, SHF F + 256)] m m' (SPA + 120) (SP + -104)) in STG;
[| exact MU| exact WM| xwb; clear - PL3 FH3 BSF SPA120 SPAB LOS' BOT ATR; lia].
apply (rw_cells_transport bsegs [(P + 8, P + 16); (SPA - 2224, SPA + 120); (F + 32, F + 1780); (SHF F, SHF F + 256)] m m' (SP + -104) _) in FRB;
[| exact MU| exact WM| xwb; clear - PL3 FH3 BSF SPA120 SPAB T1 LOS' BOT ATR; lia].
pose proof (wr_at_transport bsegs m m' F 2048 WRF WM) as WRF'.
assert (AH' : AHEAP AI L RNG1 (aps_m s1') LB1 m').
{ eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]; cbn [fst snd].
- eapply cr_block; [exact INP| cbn; lia| cbn; unfold PRODUCER_SIZE; lia].
- apply cr_stack; clear - SPAB SPA120 T1 LY3 BOT LOS'; lia.
- eapply cr_block; [exact INF| cbn; lia| cbn; lia].
- eapply cr_fshadow; [exact INF| clear - F2048; Z.div_mod_to_equations; lia| lia| lia| lia| lia]. }
assert (AG' : magree bsegs (aclient_addr CI LB SP) m0 m').
{ eapply magree_trans; [exact AG|]. eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|]. intros a Ha. cbn [outside].
destruct (pag_outsideBB _ _ _ pP P F a AH FH Ha) as (O1 & O2 & O3 & O4). unfold PRODUCER_SIZE in O4.
split; [clear - O4; lia|]. split; [clear - O1 SPAB SPA120 BOT LOS'; lia|].
split; [clear - O2; lia|]. split; [exact O3| exact I]. }
exists P, F, SPA, tl, msv, nc, data, dsz, bsz, rem, buf', jb', jc', jd',
(Z_to_bv 64 0x41b58ab3), (Z_to_bv 64 0x15f28), (Z_to_bv 64 0x80d20),
t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, x25, x27, t3, t4, t5, t6, m'.
split; [exact ESPA|]. split; [exact EA|]. split; [reflexivity|].
split; [exact AH'|]. split; [exact REST|]. split; [exact FLE|]. split; [exact AG'|].
split; [exact P16|]. split; [exact BLKP|]. split; [exact RP|]. split; [exact RPS|].
split; [exact PR'|]. split; [exact (UNPX _ _ _ AH')|].
split; [exact F2048|]. split; [exact FH|]. split; [exact FC|]. split; [exact RF|]. split; [exact RSF|].
split; [exact WRF'|]. split; [exact HDR|]. split; [exact FLP|].
split; [exact DATAA|]. split; [exact LB'|]. split; [exact FB'|]. split; [exact NCA|]. split; [exact MSVC'|]. split; [exact SH'|].
split; [exact ST'|]. split; [exact FRA'|]. split; [exact STG|]. split; [exact FRB|]. split; [exact MI'|].
split; [exact PAY'| exact (UNDX _ _ _ AH')].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Wrap.
#[using="Type"] Theorem fz_BB_proof : forall (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z), fzBB_stmt AI fflag.
Proof.
intros AI fflag. unfold fzBB_stmt.
intros U32R I32R WBOUND WRITE ISERR L RNG0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB D pl lo m0 pP s1' RNG1 ms
HLB PAY PAYB PLB D16 SZ BOT LOS SPG SP16 TP RSTK0 RI0 RISH0 FZC.
eapply fz_BB_main; eassumption.
Qed.
End CANSEC1.
