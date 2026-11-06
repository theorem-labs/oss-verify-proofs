(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells ABytes AF_fse_iface AHarness_iface AKit FsKit AH_fse_kit AH_fse_pure AH_fse_calls AH_fse_fill AH_fse_B2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
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

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Section CANSEC1. Context {rc : runConstT}.
Section B2a.
Hypothesis U32R : prod_u32r_stmtA.
Hypothesis WBOUND : fse_wbound_stmtA.
Hypothesis WRITE : fse_write_stmtA.
Hypothesis ISERR : fse_iserror_stmtA.
Variables (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (SPA lo F P D : Z) (pl : list Z) (RNG : footprint).
Notation SP := (bv_unsigned sp).
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis SPT : SP + 16 <= 2^47.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis ESPA : SPA = (SP - 192) - (SP - 192) mod 32.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RI : rng_aimg RNG.
Hypothesis FH : ablk F (F + 2048).
Hypothesis FC : F + 2048 <= ATOP.
Hypothesis F2048 : F mod 2048 = 0.
Hypothesis RF : rng RNG F 2048.
Hypothesis RSF : rng RNG (shad F) 256.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis P16 : P mod 16 = 0.
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis PF : P + 16 <= F \/ F + 2048 <= P.
Hypothesis DLOC : (pl = [] /\ D = AEMPTY) \/ ablk D (D + zlen pl).
Hypothesis D8 : D mod 8 = 0.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis DF : D + zlen pl <= F \/ F + 2048 <= D.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis SZ26 : zlen pl < 2^26.
Ltac pB3_now := eapply (pB3 U32R WBOUND WRITE ISERR gp tp sp FR fc SPA lo F P D pl RNG); try eassumption.
Ltac rt_now2 := match goal with
| RT : fse_rt ?mr, MU : munch _ ?mr ?mc, WM : wmono _ ?mr ?mc |- _ =>
let H := fresh "RTN" in assert (H : fse_rt mc) by (eapply rt_WB; eassumption);
unfold fse_rt in H; destruct H as (? & ? & ? & ? & ? & ? & ?); assumption
end.
#[using="rc U32R WBOUND WRITE ISERR LOS LOC SPT SP16 ESPA RSTK RI FH F2048 RF RSF BLKP P16 RP RPS PF DLOC D8 RD RDS DP DF PLB SZ26"] Lemma pB2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x26 x28 x29 x30 x31 : word) (mr m : amem)
(tl msv rw r3 v' r4 bsz r5 : Z) (pre : list Z) (j8 j24 jdata jmsv : list byte),
let nc := Zupd msv v' (pre ++ repeat 0 (256 - length pre)) in
(rw = 0 -> exists c, uint32Range pl r3 0 1 = (c, r4) /\ v' = (if c =? 1 then -1 else rw + 1)) ->
(rw <> 0 -> v' = rw + 1 /\ r4 = r3) ->
uint32Range pl r4 (hdrSize nc msv tl) 512 = (bsz, r5) ->
fseA pl (zlen pl) = (tl, msv, nc, fse_data nc msv tl, hdrSize nc msv tl, bsz, r5) ->
0 <= rw <= 4095 -> 0 <= r3 <= zlen pl ->
u8arr asegs m (F + 608) (nc_arrA pre) ->
rw_cells asegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 r3)] ->
rw_cells asegs m SPA [C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148));
CB 8 j8; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); CB 24 j24; C8 (Z_to_bv 64 F)] ->
rw_cells asegs m (F + 32) [CB 512 jdata] ->
rw_cells asegs m (F + 1760) [CB 4 jmsv] ->
rw_cells asegs m (SHF F) (FSH Z64 Z64 F8S BF8 BF8) ->
stk asegs m lo SPA -> mem_inv asegs m ->
fse_rt mr -> bytes_at asegs mr D (map (Z_to_bv 8) pl) -> unpoisoned mr P (P + 16) -> unpoisoned mr D (D + zlen pl) ->
munch (W_B SPA F P) mr m -> wmono asegs mr m ->
evtF asegs RNG (phaseB_postA gp tp sp FR fc SPA lo F P D pl mr)
(MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rw) (Z_to_bv 64 2147450880) x20 (Z_to_bv 64 (F + 608)) (Z_to_bv 64 msv) x23 (Z_to_bv 64 P) (Z_to_bv 64 msv)
x26 (Z_to_bv 64 (SHF F)) x28 x29 x30 x31)
FR (Z_to_bv 64 0x810c8) fc None m (seg_rom asegs)).
Proof.
intros until jmsv. intros nc EC0 EC1 EB EA RW R3 NCA PR FRA DATAC MSVC SH ST MI RT PAY0 UNP0 UND0 MU WM.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
Local Ltac2 Set LiaHints.tbl := fun () => "0170?10091660788.10 10097965897.14411453387599.14111752483811.14111752483811.1441633378355.145 1633378355.169 19339842692.14419341945401.12 1948122878.144 22627202452.10 22629288745.14423298330693.11523492641683.12024445917831.13625349552462.11326261676839.14426276410089.26 28381206279.16329782367974.11329782367974.11429782367974.13329782367974.13429782367974.15830674972759.10731653792144.10731712045164.13631712045164.13731712045164.16031712045164.16133719989128.10233719989128.15835968369417.14437177686796.15939999590352.10239999590352.10739999590352.15841725161394.13841725161394.15942146777215.14443527720977.10744193279363.10 44199564094.14450692615968.11551357505765.14452544056194.1445377903808.144 54451418594.14155345847492.15855579877093.15956041590156.16256184999720.14356458644975.13758601187105.13759228179203.18 59360481565.14360592901373.14460912249238.10761035741573.12262697932550.14465887184146.14365887184146.14465889278895.12 67294985855.1166758013062.135 68032931094.1577054066514.135 7612119643.143 8575941471.137 8937270826.144 9181029202.25  00000100200J00_01901n02m02n02o03M03N03O03Z03c03d03m04E04]05005905B05W05l06K06Z06c07;07S08508W08`09C0:K0:L0:U0:b0;E0;F0;G0<70<T0<U0<V0=H0=I0>A0??0?T0@20A70Ad0BC0Bd0Cn0D@0DU0EE0EN0E`0F_0G90G:0G;0G_0H40HN0Hc0I;0IS0JK0JcFFS2R33FH23PL22F44LNC03LWSS3FH23PL22F44LNC03LWSS3FH23PL22F44LNC03LWS4LNCAS3LOS3LOC2PF2DP2DF3FH23PL23RSP4SPAB2D02F22F44LNC03LWSS3LOS3LOC2PF2DP2DF3FH23PL23RSP4SPAB2D02F22F44LNC03LWS4LNCA4LWS2FFS3FH23PL13PL22F44LNC03LWS4LNCAFFS3FH23PL21HS3FH23PL2FS3FH23PL2S2RW3FH23PL22F44LNC03LWSS5F20482F21H2H02H42H52H9S2FH5F20481H2H03H19S3FH23PL2S3FH23PL2S3FH23PL22F44LNC03LWSS3FH23PL22F44LNC03LWSS3FH23PL22F44LNC03LWS4LNCA4LWS2S5F20483FH23PL2S3FH23PL2S3FH23PL22F22F44LNC03LWSS3FH23PL22F22F44LNC03LWSS3FH23PL22F22F44LNC03LWS4LNCA4LWS2S3FH23PL22F22F44LNC03LWS4LNCA4LWS2S3FH23FH4S3FH23FH43PL22F44LNC03LWS4LNCA4LWS2S3LOS3LOC4SP163P162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D02F44LNC03LWS4LNCA1HFS3FH13FH2S3FH13FH23PL2S3FH13FH23PL22F44LNC03LWS4LNCA4LWS2FFS3LOS3LOC3FH23PL23RSP4SPAB2D02F44LNC03LWS4LNCA1HS2PF2D82DP2DF3FH13FH23PL13PL2FFS3LOS3LOC4BLKP2PF2DP2DF3FH13FH23PL23RSP4SPAB3BSF1HFS3LOS3LOC3FH23FH33PL23PL33RSP4SPAB2D02F44LNC03LWS4LNCA1HS3LOS3LOC2PF3FH23FH33PL23PL33RSP4SPAB2D02DT2F44LNC03LWS4LNCA1HS3FH23PL22F44LNC03LWSS3FH23PL22F44LNC03LWS3S3a4LNCAS3LOS3LOC2PF2DP2DF2R33FH23PL23RSP4SPAB2D02F44LNC03LWS3S3b4LNCA1H4LWS2S5F20482PF2DP2DF3FH13FH33PL13PL31H2H03H193H34S3FH23PL24SPAB2F44LNC03LWS4LNCAS2RW3FH23PL23RSP2D02F44LNC03LWS1KS3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA324SHDJ3PSH2D02F44LNC03LWS1K1HS5F20482F21H2H02H4S3FH23PL22F44LNC03LWSS3LOS3LOC3FH23PL23RSP4SPAB2D02F44LNC03LWS4LNCA1HS3FH23PL2S3FH23PL22B12B22B3S3LOS3LOC3SPT4ESPA3FH23PL23RSP4SPAB5SPA882D02F44LNC03LWS4LNCA1HS3FH23PL22F44LNC03LWS4LNCAFFS3LOS3LOC3FH13FH23PL13PL23RSP4SPAB1HS3FH23PL22F44LNC03LWSS3FH23PL22F44LNC03LWS4LNCAS3FH23PL22F44LNC03LWSS3FH23PL22F22F44LNC03LWSS2RW3FH23PL22F44LNC03LWSS3LOS3LOC3FH13FH23FH33PL13PL23RSP4SPAB2D02F22F44LNC03LWSS5F20482F21H2H02H42H52H9".
pose proof (fsh_unp_nc m F F2048 ltac:(lia) ltac:(unfold KEND; lia) _ _ _ _ SH) as UNA.
pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
assert (RNCS : rng RNG (shad (F + 608)) 64).
{ rewrite shad_frame_off by (first [lia | unfold KEND; lia | Z.div_mod_to_equations; lia]).
rewrite <- SHF_shad in RSF. change (608 / 8) with 76. eapply rng_sub'; [exact RSF| lia]. }
unfold W_B in *. unfold SHF, FSH, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND, KHIGH in *.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
pose proof RSF as RSF0. replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
assert (SHDJ : F + 2048 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= F).
{ rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. unfold ablk, AIMG_HI, KLS in FH. Z.div_mod_to_equations. lia. }
assert (PSH : P + 16 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= P).
{ unfold ablk, AIMG_HI, KLS in BLKP. lia. }
assert (RFRA : rng RNG SPA 88) by (eapply rng_sub'; [exact RSTK| lia]).
assert (D0 : 0 < D /\ D + zlen pl <= ATOP).
{ destruct DLOC as [[-> ->]|B]; [unfold AEMPTY; cbn; lia| pose proof (ablk_lin _ _ B) as (B1 & B2 & B3 & B4); unfold AIMG_HI in B1; lia]. }
destruct D0 as [D0 DT].
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & _ & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
unfold nc_arrA in NCA.
set (nc0 := pre ++ repeat 0 (256 - length pre)) in *.
assert (LNC0 : length nc0 = 256%nat).
{ assert (length nc = 256%nat) by exact F4. subst nc. unfold Zupd in H. rewrite upd_nat_length in H. exact H. }
assert (LWS : length (map (Z_to_bv 64) nc0) = 256%nat) by (rewrite length_map; exact LNC0).
assert (ACC0 : acc_in RNG (Z_to_bv 64 (Z.shiftr (F + 608 + 2 * msv) 3 + 2147450880), 1%nat)).
{ apply (rng_acc_litZ' RNG _ _ _ 1 1 RNCS eq_refl eq_refl). rewrite shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2^3) with 8.
clear - F2048 F2 FH2. Z.div_mod_to_equations. lia. }
assert (RD0 : ov_read_bytes asegs m (wa (Z.shiftr (F + 608 + 2 * msv) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0]).
{ apply (unpoisoned_full_rd asegs m (F + 608) (F + 1120)); [exact UNA| |];
rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; change (2^3) with 8; clear - F2048 F2; Z.div_mod_to_equations; lia. }
zstep. zstep.
rewrite (Z.shiftl_mul_pow2 msv 1) by lia. change (2^1) with 2. replace (msv * 2) with (2 * msv) by lia.
zstep. zstep.
zstep.
zstep. if_cases B0; zify_cond B0; [exfalso; apply B0; reflexivity|].
zstep. zstep.
pose proof (u16arr_store_ok asegs _ (F + 608) _ msv (wa (F + 608 + 2 * msv)) NCA ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write asegs _ (F + 608) _ msv (Z_to_bv 64 (rw + 1)) NCA ltac:(rewrite LWS; lia)) as NCA2.
clear NCA. store_done.
rewrite upd_map_upd_nat in NCA2. fold (Zupd msv (rw + 1) nc0) in NCA2.
zstep.
rename NCA2 into NCA.
zstep. if_cases K; zify_cond K.
-
rewrite shl48_landA in K by lia. assert (RWN : rw <> 0) by lia.
destruct (EC1 RWN) as [EV ER4]. subst r4.
pB3_now; try lia; try exact RSF0. subst nc. rewrite EV. exact NCA.
- rewrite shl48_landA in K by lia. assert (RWZ : rw = 0) by lia.
destruct (EC0 RWZ) as (c & ECc & EV).
pose proof (uint32Range_spec pl r3 0 1 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S3.
rewrite ECc in S3. destruct S3 as (S3a & S3b & _).
zstep. zstep. zstep. zstep. zstep.
assert (LNCA : length (u16s (map (Z_to_bv 64) (Zupd msv (rw + 1) nc0))) = 512%nat)
by (rewrite u16s_length, length_map; unfold Zupd; rewrite upd_nat_length, LNC0; reflexivity).
unfold prod_u32r_stmtA, APROD_U32R in U32R.
callt ltac:(eapply U32R with (SPV := SPA) (P := P) (D := D) (pl := pl) (size := r3) (mn := 0) (mx := 1) (lo := lo));
[ first [ reflexivity | assumption | (split; [eapply pay_WB; eassumption| exact PLB]) | lia | (unfold KHIGH; lia) | (clear - P16; Z.div_mod_to_equations; lia)
| (eapply unp_P_WB; eassumption) | (eapply unp_D_WB; eassumption) | rt_now2 | (destruct DLOC as [[-> _]|B]; [cbn; lia| intros; exact B]) ] .. | ].
rewrite ECc in *. cbn [fst snd] in *.
try clear PR. rename POST into PR. rename PC into ST. unfold prod_atA in PR.
zstep. if_cases K2; zify_cond K2.
+
pB3_now; try lia; try exact RSF0. subst nc. rewrite EV. replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; exact K2). exact NCA.
+
subst c.
assert (LWS2 : length (map (Z_to_bv 64) (Zupd msv (rw + 1) nc0)) = 256%nat)
by (rewrite length_map; unfold Zupd; rewrite upd_nat_length; exact LNC0).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (RD1 : ov_read_bytes asegs mx (wa (Z.shiftr (F + 608 + 2 * msv) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0])
by (apply (unpoisoned_full_rd asegs mx (F + 608) (F + 1120));
[ eapply (fsh_unp_nc mx F F2048 ltac:(lia) ltac:(unfold KEND; lia)); exact SH | |];
rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; change (2^3) with 8; clear - F2048 F2; Z.div_mod_to_equations; lia)
end.
zstep.
zstep. if_cases B1; zify_cond B1; [exfalso; apply B1; reflexivity|].
zstep.
pose proof (u16arr_store_ok asegs _ (F + 608) _ msv (wa (F + 608 + 2 * msv)) NCA ltac:(rewrite LWS2; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write asegs _ (F + 608) _ msv (Z_to_bv 64 (-1)) NCA ltac:(rewrite LWS2; lia)) as NCA2.
clear NCA. store_done.
rewrite upd_map_upd_nat in NCA2. unfold Zupd in NCA2. rewrite upd_nat_idem in NCA2. fold (Zupd msv (-1) nc0) in NCA2.
pB3_now; try lia; try exact RSF0. subst nc. rewrite EV. cbn [Z.eqb Pos.eqb]. exact NCA2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End B2a.
End CANSEC1.
