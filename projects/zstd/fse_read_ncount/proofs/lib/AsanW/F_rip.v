(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells F_m2s F_mem_is_zero.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
End CANSEC1.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Section CANSEC2. Context {rc : runConstT}.
Definition rip_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).
Section Proofs.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Notation B := (bv_unsigned a0).
Notation n := (bv_unsigned a1).
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 80)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis LAY : rt_layout m.
Hypothesis APP : app_blk B (B + n).
Hypothesis UNP : unpoisoned m B (B + n).
Hypothesis NSZ : (n <= 2^40)%Z.
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RSH : rng RNG (shad B) (shad (B + n - 1) + 1 - shad B).
Notation POST := (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
#[using="LO RSTK"] Lemma L5 : forall (m2 : word -> option byte) junk8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x8 x9 x18 x19 x20 x21 x28 x29 x30 x31,
rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs m2 lo (bv_unsigned sp + -64) ->
munch [(bv_unsigned sp + -80, bv_unsigned sp)]%Z m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
(0 <= lo)%Z ->
evtF asegs RNG POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9
x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x54c74) fc None m2 (seg_rom asegs)).
Proof.
intros until x31. intros FR ST2 MU2 WM2 MI2 LO0.
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>12367362435.8717776320431.8721918414723.8825878270255.8736115622447.8736423622048.8036993589379.883945979267.88 41809558659.8743060403331.8943987951406.8849343544638.7951481786499.8853767577775.8761917199020.8663235321900.8600000100500600:00>00B00C00D00E00F00J00K00L00P00T00XSS2LOSS2LOS2LOS2LOSSSSS2LOSSS2LOS2LOS2LO".
do 11 zstep. release_frame FR ST2 (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section AfterFrame.
Variables (m1 : word -> option byte) (junk8 : list byte).
Hypothesis FR : rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -64).
Hypothesis MU1 : munch [(bv_unsigned sp + -80, bv_unsigned sp)]%Z m m1.
Hypothesis WM1 : wmono asegs m m1.
Hypothesis MI1 : mem_inv asegs m1.
Hypothesis GOT1 : rt_got m1.
Hypothesis SHB1 : rt_shbase m1.
Hypothesis LAY1 : rt_layout m1.
Hypothesis UNP1 : unpoisoned m1 B (B + n).
Hypothesis NZ : (n <> 0)%Z.
Hypothesis LO0 : (0 <= lo)%Z.
Section Core.
Variables (AB AE : Z).
Hypothesis RAB : (B <= AB <= B + 7 /\ AB mod 8 = 0)%Z.
Hypothesis RAE : (B + n - 7 <= AE <= B + n /\ AE mod 8 = 0)%Z.
#[using="LO KLO APP NSZ RSTK RSH junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LAY1 UNP1 NZ LO0 RAB RAE"] Lemma L4 : forall x5 x11 x12 x13 x14 x15 x16 x17 x18,
evtF asegs RNG POST
(MS (mkR (Z_to_bv 64 347120) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
(Z_to_bv 64 (shad AE)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (shad AB)) (Z_to_bv 64 AE) (Z_to_bv 64 0xa2478) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54c60) fc None m1 (seg_rom asegs)).
Proof.
intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
Local Ltac2 Set LiaHints.tbl := fun () => "00R0?11801586693.10621552338115.95 22284289799.10622360111546.10722700267513.10724205896189.10626077190214.82 28381717185.97 29892437774.84 30985182006.88 33711491812.82 33878917058.84 35895327997.10636054547711.82 39845525545.84 44484923210.10647945733308.82 48436945605.87 53441407004.84 53441591016.87 53443629088.81 53451617827.95 54125010508.84 56170432943.84 59016535196.84 59308629336.1  66240313209.87 67485444837.95 67494333670.81 6978249238.102 7381600893.106 7777034463.84  8927112930.87  8927457302.84  00000;00R00S01:01S01e01j02B02M02`02k03=03O03Z03^03_03d03e04304A04L04Z04e04f05105505@05K05V05W05i05j06806FS2NZ2Rn3HspS2NZ3RAB3RAE2Rn2K81H2H4FS2NZ3RAB3RAE2Rn4APP'1H2H02H42H93H103H14S2NZ3RAB3RAE2Rn3ABE3Hsp1HS2LO3KLO2NZ2Rn3HspS3RAES3NSZ2NZ3RAB3RAE2Rn1H2H4S2NZ2Rn3SHDS2LO3KLO2NZ2Rn2LE1HS2NZ3RAB2RnS2LO3KLO2NZ2Rn3SHRS2LO3KLO2NZ2Rn3HspS2NZ3RAE2RnS2LOFS3RABFS2NZ2Rn3SHR2K8S2NZ2Rn3SHR2K8S2NZ2Rn3SHRS2NZ2Rn3SHR2K8S2NZ2Rn3SHRSS2NZ2Rn3SHRS2K9S2NZ2Rn3SHRS2NZ2Rn3SHRS2NZ2Rn3SHRSS2LO3KLO2NZ2Rn3HspSS2NZ2Rn2K83SHDS2NZ2Rn2K83SHD".
assert (SHR : (2147450880 <= shad B /\ shad B <= shad AB /\ shad AB <= shad (B + n - 1) + 1 /\ 2147450880 <= shad AE /\
shad AE <= shad (B + n - 1) + 1 /\ shad (B + n - 1) + 1 <= 17594333495296)%Z)
by (rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
zstep. if_cases K8; zify_cond K8.
{ eapply L5; eassumption. }
assert (ABE : (AB <= AE)%Z) by (rewrite !shad_div in K8; unfold ASHOFF in K8; Z.div_mod_to_equations; lia).
pose proof (unpoisoned_core_zero m1 B (B + n) AB AE UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ABE) as SB0.
assert (SHD : (shad AE - shad AB <= 2^40)%Z) by (rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
zstep. zstep. zstep.
call_sp mem_is_zero_spec;
[ exact MI1 | exact ST1 | lia
| zsimp; replace (shad AB + (shad AE - shad AB))%Z with (shad AE) by lia; exact SB0
| zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
fold_lits. zstep. if_cases K9; zify_cond K9. { exfalso. clear - K9. cbv in K9. lia. }
eapply L5; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="LO KLO APP NSZ RSTK RSH junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LAY1 UNP1 NZ LO0 RAB RAE"] Lemma L3 : forall x5 x12 x13 x14 x15 x16 x17,
evtF asegs RNG POST
(MS (mkR (Z_to_bv 64 347120) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
(Z_to_bv 64 (shad AE)) (Z_to_bv 64 2147450880) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (n + B)) (Z_to_bv 64 (shad AB)) (Z_to_bv 64 AE) (Z_to_bv 64 0xa2478) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54c0c) fc None m1 (seg_rom asegs)).
Proof.
intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
Local Ltac2 Set LiaHints.tbl := fun () => "00=0?13690503126.89 14362627026.11115389206808.98 19490030894.82 29792256216.89 33356455822.77 36975484175.77 37103537343.89 43612412595.77 52074235541.90 52076332702.92 59310676315.1119448783276.111 00000100<00F00^00_00f00g01601701K01f02B02SFS2NZ2Rn3SR2S2NZ2Rn2H0S2NZ3RAB3RAE2Rn4APP'3CK2SS2NZ2RnSS2NZ3RAB3RAE2RnSS2NZ3RAB3RAE2Rn4APP'S2NZ3RAB3RAE2Rn4APP'3CK22K6S2NZ2Rn3CK22K62K71H2H02H42H5S2NZ2Rn3CK22K62H0".
do 3 zstep.
destruct (unpoisoned_check_rd asegs m1 B (B + n) (n + B - 1) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
zstep. rewrite sxb_sval. zstep. if_cases K6; zify_cond K6.
{ apply L4. }
zstep. zstep. if_cases K7; zify_lts K7. 2:{ exfalso. Z.div_mod_to_equations. lia. }
apply L4.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Core.
#[using="LO KLO APP NSZ RI RSTK RSH junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LAY1 UNP1 NZ LO0"] Lemma L2 : forall x5 x12 x13 x14 x15 x16 x17,
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
(Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (n + B)) s3 s4 (Z_to_bv 64 0xa2478) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54bd0) fc None m1 (seg_rom asegs)).
Proof.
intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00K0?13690503126.10615389206808.11528903417478.78 29792256216.10630010276844.74 30506417931.86 30508859957.78 32749706759.97 32749706762.10537103537343.10639572309845.12140284579771.86 40389304636.86 43565598146.94 43611253673.94 46703120817.94 47144164815.94 51458250788.82 51467090341.74 59308628820.74 59310676310.1216023207647.86  6025305941.94  64800200592.99 8929152933.74  8937270827.83  9448783265.121 00000100;00R00S00T00k01B01T01f02802C02D02_02f02g02h02i03803G03Q03b04904P04k05:05I05ZFS2NZ2Rn2H0S2NZ2Rn4APP'2K53RAB3RAESSS2NZ2Rn4APP'2K53RAB3RAES2NZ2Rn4APP'2K53RAB3RAES2NZ2Rn1H2H02H42H5S2NZ2Rn1H2H02H42H5S2NZ2Rn2K53RAB3RAES2NZ2Rn3SR1SS3NSZ2NZ2Rn4APP'2K53RAB3RAES2NZ2RnSSSS2NZ2Rn4APP'2K5S2NZ2Rn4APP'2K5S2NZ2Rn2K5S2NZ2Rn3CK12K62K7S2NZ2Rn4APP'2K53RAB3RAES2NZ2Rn4APP'2K53RAB3RAES2NZ2Rn4APP'2K53RAB3RAE3CK1S2NZ2Rn4APP'2K5S2NZ2Rn4APP'2K5S2NZ2Rn3CK12K62H0".
if_cases K5; zify_cond K5. { exfalso; lia. }
do 3 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia.
remember (B + 7 - (B + 7) mod 2 ^ 3)%Z as AB eqn:HAB.
remember (n + B - (n + B) mod 2 ^ 3)%Z as AE eqn:HAE.
assert (RAB : (B <= AB <= B + 7 /\ AB mod 8 = 0)%Z) by (subst AB; Z.div_mod_to_equations; lia).
assert (RAE : (B + n - 7 <= AE <= B + n /\ AE mod 8 = 0)%Z) by (subst AE; Z.div_mod_to_equations; lia).
clear HAB HAE.
zstep. call m2s_spec; [assumption|assumption|assumption|assumption| zsimp; unfold KLOW, KHIGH, KEND; lia |]. zsimp.
do 3 zstep. call m2s_spec; [assumption|assumption|assumption|assumption| zsimp; unfold KLOW, KHIGH, KEND; lia |]. zsimp.
do 3 zstep.
destruct (unpoisoned_check_rd asegs m1 B (B + n) B 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b1 & RD1 & CK1).
unfold shad, ASHOFF in RD1.
pose proof (sval_range b1) as SR1.
zstep. rewrite sxb_sval. zstep. if_cases K6; zify_cond K6.
{ eapply L3; eassumption. }
zstep. zstep. if_cases K7; zify_lts K7. { exfalso. Z.div_mod_to_equations. lia. }
eapply L3; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="LO KLO APP NSZ RI RSTK RSH junk8 FR ST1 MU1 WM1 MI1 GOT1 SHB1 LAY1 UNP1 NZ LO0"] Lemma L1 : forall x5 x13 x14 x15 x16 x17,
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 t1 t2 a0 a1
(Z_to_bv 64 2147450879) (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879) x13 x14 x15 x16 x17
s2 s3 s4 (Z_to_bv 64 0xa2478) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54b88) fc None m1 (seg_rom asegs)).
Proof.
intros. pose proof (bv_unsigned_in_range 64 a1) as Rn. pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>59308628433.7459308628566.7559308628695.768929152288.74 8929152417.73 8929152550.76 8929152679.75 00000B00T00f01501A01N01[S2NZ2Rn4APP'2K12K2S2NZ2Rn4APP'2K12K3S2NZ2Rn4APP'2K12K4S2NZ2Rn4APP'2K1S2NZ2Rn4APP'S2NZ2Rn2K12K2S2NZ2Rn2K12K2".
if_cases K1; zify_cond K1.
- apply L2.
- do 7 zstep. fold_lits. zsimp. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
do 6 zstep. if_cases K3; zify_cond K3. { exfalso; lia. }
zstep. if_cases K4; zify_cond K4. { exfalso; lia. }
apply L2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End AfterFrame.
#[using="MI ST LO KLO GOT SHB LAY APP UNP NSZ RI RSTK RSH"] Lemma rip_body :
evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54afc) fc None m (seg_rom asegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
pose proof (bv_unsigned_in_range 64 a1) as Rn.
pose proof APP as [LE APP']. unfold KLOW, KHIGH, KEND in APP', KLO.
Local Ltac2 Set LiaHints.tbl := fun () => "01E0>11805467289.6611805467289.6711805467289.6811805467289.6911805645481.7411903774446.6811912744615.6712367362435.6712367362435.6913021749692.681340665966.68 1527479463.66 17646078182.5917776320428.6617776320431.6918848698606.6619049469500.6819199919342.662003044974.68 21918414723.6721918414723.7024630998586.6625240764910.6925314760359.6825878270255.6725878270255.6928913119921.7529514832494.6730180773870.6931081687356.6832377744366.6832651489978.6833039531175.6833680001082.6836115622447.6736115622447.6936425805088.6236993589379.6836993589379.7037107179452.6738040803179.5639219183342.663945979267.68 3945979267.70 40069102958.6741161757422.6841809558659.6641809558659.6942744733806.6743060403331.6943060403331.7143061775760.5743987951406.6843987951406.7045042151022.6845221239098.6846356275438.6849345641752.6149978085870.6851481786499.6851481786499.7052136437230.6853767577775.6753767577775.6956023003502.6756064834414.6756228262055.67563227834.67  56912526318.6957745675194.6759308628433.6459308628566.6559308628695.6659588178609.7560025031335.6961917199020.6661917199020.6863235321900.6563235321900.6863694018620.6967003974766.6767800801447.687010956092.66 8583720762.69 985337532.67  00000100200300400G00O00P00Q00R00V00^00_00`00d00h01001401<01D01E01F01J01R01S01W01[01\01d01l02002802<02=02A02E02I02M02N02O02S02W02_02`02a02i03103203303;03<03=03A03E03I03Q03U03]03^03f03g03h04004404804@04H04I04M04U04Y04h05705I05J05K05O05S05W05[05_05g05h05l060064SSSSS2LO3KLO4APP'2H42H5S2LO3KLOSSSS2HBS2LO3KLOSSS2LOS2LOS2LO3KLOS2HBS2LO3KLOS2LO3KLOSSS2HBS2LO3KLOSS2LOS2LOSS2LO3KLOS2LO3KLOS2HBS2LO3KLOS2HBSS2HBS2LOS2LOS2LOSSS2HBS2LOS2LO3KLOSSS2LO3KLOS2LO3KLOSSS2LO3KLOSSS2LOS2LOS2LOS2LO3KLOS2HBS2LO3KLOSS2LO3KLOSSS2LO3KLOS2LOS2LOS2LO3KLOS2LO3KLOSS2HBS2LO3KLOS2HBS2Rn4APP'2K02K2S2Rn4APP'2K02K3S2Rn4APP'2K02K12K4SSS2LOS2LOS2LOS2LOS2HBS2LO3KLOSS2HBS2HBS2HB".
assert (LO' : (lo <= bv_unsigned sp - 64)%Z) by lia.
carve_frame 64%nat ST.
do 8 zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
lazymatch goal with MU1 : munch _ m m1 |- _ =>
pose proof (unpoisoned_munch _ m m1 B (B + n) UNP MU1
ltac:(rewrite !shad_div; unfold ASHOFF; cbn; Z.div_mod_to_equations; lia)) as UNP1 end end.
zstep. if_cases K0; zify_cond K0.
{ do 11 zstep. release_frame FR ST (bv_unsigned sp). finish. }
do 7 zstep. fold_lits. zsimp. do 2 zstep.
zstep. if_cases K1; zify_cond K1.
- eapply L1; eassumption.
- do 7 zstep. fold_lits. zsimp. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
do 6 zstep. if_cases K3; zify_cond K3. { exfalso; lia. }
zstep. if_cases K4; zify_cond K4. { exfalso; lia. }
eapply L1; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.
#[using="Type"] Lemma rip_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_shbase m -> rt_layout m ->
app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a1) ->
unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a1) ->
(bv_unsigned a1 <= 2^40)%Z ->
rng_aimg RNG ->
rng RNG lo (bv_unsigned sp - lo) ->
rng RNG (shad (bv_unsigned a0)) (shad (bv_unsigned a0 + bv_unsigned a1 - 1) + 1 - shad (bv_unsigned a0)) ->
evtF asegs RNG (rip_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54afc) fc None m (seg_rom asegs)).
Proof. intros until lo. intros MI ST LO KLO GOT SHB LAY APP UNP NSZ RI RSTK RSH. eapply rip_body; eassumption. Qed.
End CANSEC2.
