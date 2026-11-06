(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
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
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Section CANSEC1. Context {rc : runConstT}.
Section U32R.
Variables (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
Hypothesis PR : prod_atA m P D size.
Hypothesis PL : payload_atA m D pl.
Hypothesis SZ : 0 <= size <= zlen pl.
Hypothesis P0 : 0 < P.
Hypothesis P8 : P mod 8 = 0.
Hypothesis D0 : 0 < D.
Hypothesis ST : stk bsegs m lo SP.
Hypothesis LO : lo <= SP - 16.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis MI : mem_inv bsegs m.
Hypothesis MM : 0 <= mn <= mx.
Hypothesis RG : mx - mn < 2^24.
Hypothesis MX : mx < 2^31.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis BLKD : 0 < zlen pl -> ablk D (D + zlen pl).
Hypothesis D8 : D mod 8 = 0.
Hypothesis KLO : KHIGH <= lo.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis UNP : unpoisoned m P (P + 16).
Hypothesis UND : unpoisoned m D (D + zlen pl).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Notation POST := (prod_u32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m).
Notation W := [(P + 8, P + 16); (SP - 16, SP)].
Notation range := (mx - mn).
Definition ASHB : Z := 0x7fff8000.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
#[using="rc lo P0 P8 D0 LO RSP PLO DLO DP BLKP BLKD D8 KLO UNP UND"] Lemma inv_shadow : forall m1, munch W m m1 -> unpoisoned m1 P (P + 16) /\ unpoisoned m1 D (D + zlen pl).
Proof.
intros m1 MU. pose proof (ablk_lin _ _ BLKP) as LP.
pose proof (ablk_disj_band _ _ BLKP) as DBP. unfold KHIGH, KLS, AIMG_HI in *.
split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0070>13449311261.7623492641683.7632813024914.9632813024914.9838879299635.7643169481829.9643169481829.9800000400800H00e01?01Z01oS2E0S2N0S2P83DBP1H2H42H5S2DP2D83DBP2N02LD1H2H42H53H14S2P02D02LO3RSP3DLO2LP2E01HS2P82LO3PLO3KLO3DBP1H2H42H5S2LO3DLO3KLO2N02H42H5".
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- destruct (Z.eq_dec (zlen pl) 0) as [E0|N0].
+ replace (D + zlen pl) with D by lia. apply unpoisoned_nil. change (2^64) with 18446744073709551616 in *. lia.
+ pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. unfold AIMG_HI in LD.
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition INV (m1 : amem) (sz : Z) : Prop :=
rw_cells bsegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 sz)]
/\ bytes_at bsegs m1 D (map (Z_to_bv 8) pl)
/\ (exists junk8, rw_cells bsegs m1 (SP + -16) [CB 8 junk8; C8 ra])
/\ stk bsegs m1 lo (SP + -16)
/\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.
Ltac inv_close PRx PLx FRx STx MUx WMx MIx :=
split; [exact PRx|]; split; [exact PLx|]; split; [eexists; exact FRx|]; split; [exact STx|]; split; [exact MUx|]; split; [exact WMx| exact MIx].
Notation STpc pc mm x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 :=
(MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
#[using="Type"] Lemma draw_loop_0 : forall f sz result, draw_loop f pl sz 0 result = (result, sz).
Proof. intros [|f] sz result; reflexivity. Qed.
#[using="m P D PL P0 D0"] Lemma pl_nth : forall i, 0 <= i < zlen pl ->
nth_error (map (Z_to_bv 8) pl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i pl)) /\ 0 <= Znth i pl < 256.
Proof.
intros i Hi. destruct PL as [_ PLR]. unfold Znth.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>15302255622.7300000:S2P02D02Hi".
assert (L : (Z.to_nat i < length pl)%nat) by lia.
split.
- rewrite nth_error_map. rewrite (nth_error_nth' pl 0 L). reflexivity.
- apply (proj1 (Forall_forall _ _) PLR). apply nth_In. exact L.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="P0 D0 LO MM RG MX RSTK"] Lemma u32r_tailA : forall m1 result sz (x5 x6 x7 x10 x13 x14 x16 x17 x28 x29 x30 : word),
0 <= result < 2^24 -> INV m1 sz ->
(result, sz) = draw_loop 4 pl size range 0 ->
evtF bsegs RNG POST
(MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 x6 x7 s0 s1 x10 (Z_to_bv 64 mn) (Z_to_bv 64 result) x13 x14 (Z_to_bv 64 range) x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
F (Z_to_bv 64 0x82808) fc None m1 (seg_rom bsegs)).
Proof.
intros m1 result sz x5 x6 x7 x10 x13 x14 x16 x17 x28 x29 x30 RR (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) DL.
zstep. zstep. unfold v_remuw. Local Ltac2 Set LiaHints.tbl := fun () => "00B0?12641419845.94 17846519188.94 19620497065.10619628366494.94 21993699182.94 29140532593.10231947791659.95 33267308098.95 37133642481.94 41617845831.94 4641771484.101 47166584393.94 55873950010.95 57529845269.94 58695750297.10661785177838.94 61855716727.94 7464779885.94  00000400800?00F00G00H00L00_00o01601:01;01N01U01e01i01m02@S2MMS2MMS2MM2RGS2MM2RGSSS2LOS2P02D02MM2MX2RR2RMS2P02D02MM2RG2RRS2MM2RGS2LOSS2P02D02MM2RG2RR2RMS2MM2RGS2P02D02MM2MX2RRS2RRS2RRS2P02D02MM2MX2RR2RM".
zsimp.
rewrite (wrap32_small (range + 1)) by lia. rewrite (wrap32_small result) by lia.
replace (range + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
assert (RM : 0 <= result mod (range + 1) < range + 1) by (apply Z.mod_pos_bound; lia).
rewrite FseWalkKit.swrap32_small by lia.
zstep. rewrite FseWalkKit.swrap32_small by lia.
zstep. zstep. zstep.
release_frame FR1 ST1 SP.
zstep.
apply evtF_done. unfold prod_u32r_postA, uint32Range.
rewrite (u32_id range) by lia. rewrite <- DL.
replace (range =? 2^32 - 1) with false by (symmetry; apply Z.eqb_neq; lia).
cbn [fst snd]. rewrite (u32_id (mn + result mod (range + 1))) by lia.
replace (result mod (range + 1) + mn) with (mn + result mod (range + 1)) by lia.
do 14 eexists. exists m1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact PR1].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc PL P0 P8 D0 LO RSP PLO DLO DP BLKP BLKD D8 KLO UNP UND RP RPS RD RDS"] Lemma u32r_loopA : forall f sz rolling result m1 (x6 x14 x29 x30 : word),
0 < rolling < 2^(8 * (Z.of_nat f - 1)) -> 0 <= result < 2^(32 - 8 * Z.of_nat f) -> (f <= 4)%nat ->
0 <= sz <= zlen pl -> x6 = Z_to_bv 64 (sz + -1) -> INV m1 sz ->
(forall m2 (y6 y14 y28 y29 y30 : word), INV m2 (snd (draw_loop f pl sz rolling result)) ->
0 <= fst (draw_loop f pl sz rolling result) < 2^24 ->
evtF bsegs RNG POST (STpc 0x827f8 m2 (Z_to_bv 64 (-1)) y6 (Z_to_bv 64 (Z.shiftr P 3 + ASHB))
(Z_to_bv 64 (fst (draw_loop f pl sz rolling result))) (Z_to_bv 64 (P + 8)) y14 (Z_to_bv 64 range)
(Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (P + 8) 3 + ASHB)) y28 y29 y30)) ->
evtF bsegs RNG POST (STpc 0x82788 m1 (Z_to_bv 64 (-1)) x6 (Z_to_bv 64 (Z.shiftr P 3 + ASHB))
(Z_to_bv 64 result) (Z_to_bv 64 (P + 8)) x14 (Z_to_bv 64 range)
(Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr (P + 8) 3 + ASHB)) (Z_to_bv 64 rolling) x29 x30).
Proof.
induction f as [|f IH]; intros sz rolling result m1 x6 x14 x29 x30 RO RE F4 SZ1 -> (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) K.
{ exfalso. cbn in RO. Local Ltac2 Set LiaHints.tbl := fun () => "01\0?10837440789.12512524492090.10114155401004.13414512625100.99 14518897996.10514518897996.10715149611745.12615662338048.10215978017638.12716193676380.10916887847394.12818433127084.12718435116950.12518580387820.1041904045632.123 19617313304.12819628416273.11121823950629.13422958630842.10023492641683.10625071629079.13426636836818.11526902738586.12928978841823.12529782367974.10929782367974.12129782367974.12329782367974.12629782367974.13429782367974.13530515920440.1153098784273.115 31745718305.1283272954545.134 32810810841.10932810810841.12134212322600.12834212322600.12935649611869.12235649611870.13335847753748.12136974651228.10038392207929.13338392207930.12239166270122.1204052707526.128 40553477673.13440668734194.12840829096510.15740928202509.12540930299657.12240930299658.13341270674269.13841422282358.10141422282358.10241422282358.10341730628386.11843260008360.13343523888347.12343606267538.11544427921411.12847401336583.11347401336710.11447410194362.13047412291505.13148270654602.12648322944426.12849792122345.12252069406707.12652138671532.13454063599532.12754072487077.13554454175741.12254454175742.13354485145450.10454600075686.13456958518598.10356958518598.99 59310676439.15759314873579.11159314873579.11259314873579.11359314873579.11459314873579.11559314873579.12359314873579.97 59314923118.90 59382398767.12361776257753.13562035635803.12863277753146.10563374621462.10063374621462.12563374621462.99 64405586220.12564407683368.12264407683371.13365349223833.13466326736025.98 6696322385.138 68086849865.1258383620057.107 8383620057.128 8549002273.111 8549002400.112 8595070091.104 8595070091.125 9448783136.157 00000R00l00m01:01b02B02h03F03h04D04g05C05_05`06<06=06j06k07<07f08B08b09G09i0:E0:a0;=0;Y0<50<Q0=30=S0=o0>S0?80?]0@90@U0@V0@W0A<0AS0BB0Bg0Ce0DA0D`0EE0Ed0Ee0Ef0Eg0FI0F]0G50GQ0Gm0HI0He0IA0IB0J20J_0KL0L90LU0MD0M`0N?0N^0O@0Ob0Oc0Od0PF0Pe0QG0QZ0Rd0SC0Sf0TH0U60Ue0VD0VN0VX0W80WZ0W[0XY0Xj0YF0YS0ZC0ZD0ZE0Zn0[80[W0\90\]0]A0^60^c0_?0_[0`LS2P02D02RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F42F13P8'2Q8FS2RO2RE2F42F1S2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P241BS2RO2RE2F42F13P8'2Q83Q243P243SZPS2P02D02RO2RE2F42F13P8'2Q83Q243P243RD8S2P02D02RO2RE2F42F13P8'2Q83Q24S2P02D02RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P243RD82B2S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24FS2RO2RE2F42F13P8'2Q83Q243P24FS2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P243SZP2LDFS2RO2RE2F42F13P8'S2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P243SZPS2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P243SZPS2P02D02RO2RE2F42F13P8'2Q83Q243P242NRS2P02D02RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F43SZ12F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F43SZ12F13P8'2Q83Q243P243SZPS2P02P82D02RO2RE2F42F13P8'2Q83Q243P24S2P02P82D02RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24FFS2P02P82D02RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F42F13P8'S2P02P82D02RO2RE2F42LP2F13P8'2Q83Q243P243SZP2LDS2P02P82D02RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F43SZ12LP2F13P8'2Q83Q243P241B3SZP2LD2GB2GC2GD2CKS2RO2RE2F42F13P8'2Q83Q243P24S2P02RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F42F13P8'2Q83Q243P242NRS2RO2RE2F42F13P8'2Q83Q243P242SRFFFS2P02D02RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q8S2RO2RE2F42F13P8'2Q83Q24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24FS2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P243SZP2LD2LPS2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P243SZP2LDS2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P243SZP2LDS2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P243SZP2LDS2RO2RE2F42F13P8'2Q83Q243P24S2D02RO2RE2F42F13P8'2Q83Q243P242GB2GC2GD3RD82B2S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P242NRS2RO2RE2F42LP2F13P8'2Q83Q243P24S2P02D02RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F42F13P8'2Q83Q243P24FFS2P02D02RO2RE2F42F13P8'2Q83Q243P24S2DP2RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F42F13P8'2Q83Q243P24S2P02D02RO2RE2F42F1S2D02RO2RE2F43SZ12LP2F13P8'2Q83Q243P241B3SZP2LD2GB2GC2GD2CK2G23G2'3H103H24S2RO2RE2F42F13P8'2Q83Q243P242G1S2RO2RE2F43SZ12F13P8'2Q83Q243P242GAS2D02RO2RE2F42F13P8'2Q83Q243P242GBS2P02D02RO2RE2F43SZ12F13P8'2Q83Q243P242LD2GC1HS2P02D02RO2RE2F42LP2F13P8'2Q83Q243P243SZP2LD2GDS2RO2RE2F42F13P8'2Q83Q243P242G3S2RO2RE2F4S2RO2RE2F4S2RO2RE2F42F13P8'2Q83Q243P243SZPS2P02D02RO2RE2F42F13P8'2Q83Q243P24FS2P02D02LO3RSP3DLO2DP2D82RO2RE2F43SZ12LP2F13P8'2Q83Q243P241B1HS2RO2RE2F42F13P8'S2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F1S2P02D02D82RO2RE2F43SZ12F13P8'2Q83Q243P243SZP2LDFFS2P02D02LO3PLO2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F4S2RO2RE2F42F13P8'2Q83Q243P242NRS2P02D02RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F43SZ12F13P8'2Q83Q243P243SZPS2RO2RE2F43SZ12F13P8'2Q83Q243P243SZPS2P02D02RO2RE2F43SZ12LP2F13P8'2Q83Q243P243SZP2LD4LENPS2P02D02RO2RE2F44LENP2LP2F13P8'2Q83Q243P242LDS2RO2RE2F42F13P8'2Q83Q243P24S2RO2RE2F42F13P8'2Q83Q243P24S2D02RO2RE2F42F13P8'2Q83Q243P242GB2GC2GD2CK2G22H0".
lia. }
pose proof (bytes_at_bound _ _ _ _ PL1) as DB. rewrite length_map in DB.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
pose proof (ablk_lin _ _ BLKP) as LP. unfold KHIGH, AIMG_HI, ASHB in *.
destruct (inv_shadow m1 MU1) as [UNP1 UND1].
assert (F1 : (1 <= f)%nat). { destruct f; [exfalso; cbn in RO; lia| lia]. }
assert (P8' : 2^(8 * (Z.of_nat (S f) - 1)) = 256 * 2^(8 * (Z.of_nat f - 1))).
{ replace (8 * (Z.of_nat (S f) - 1)) with (8 + 8 * (Z.of_nat f - 1)) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
assert (Q8 : 2^(32 - 8 * Z.of_nat f) = 256 * 2^(32 - 8 * Z.of_nat (S f))).
{ replace (32 - 8 * Z.of_nat f) with (8 + (32 - 8 * Z.of_nat (S f))) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
assert (Q24 : 2^(32 - 8 * Z.of_nat (S f)) <= 2^16) by (apply Z.pow_le_mono_r; lia).
assert (P24 : 2^(8 * (Z.of_nat (S f) - 1)) <= 2^24) by (apply Z.pow_le_mono_r; lia).
assert (PP0 : 0 < 2^(8 * (Z.of_nat f - 1))) by (apply Z.pow_pos_nonneg; lia).
cbn [draw_loop] in K. change (2^8) with 256 in K.
replace (0 <? rolling) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in K.
change (2^16) with 65536 in Q24. change (2^24) with 16777216 in P24.
zstep. if_cases B; zify_cond B.
-
assert (sz = 0) by lia. subst sz.
replace (0 <? 0) with false in K by reflexivity.
apply K; [| cbn [fst]; lia].
cbn [snd]. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
- assert (SZP : 0 < sz) by lia.
pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. unfold AIMG_HI in LD.
replace (0 <? sz) with true in K by (symmetry; apply Z.ltb_lt; lia).
destruct (pl_nth (sz - 1) ltac:(lia)) as [NTH NR].
pose proof (unpoisoned_full_rd bsegs m1 P (P + 16) (Z.shiftr P 3 + 2147450880) UNP1
ltac:(rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
ltac:(unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)) as RDP.
zstep. zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep. zstep.
zstep. if_cases GA; zify_cond GA; [exfalso; lia|].
zstep. if_cases GB; zify_cond GB; [exfalso; lia|].
zstep. if_cases GC; zify_cond GC; [exfalso; lia|].
zstep. if_cases GD; zify_cond GD; [exfalso; lia|].
destruct (unpoisoned_check_rd bsegs m1 D (D + zlen pl) (sz + -1 + D) 1 UND1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (b & RDB & CK).
unfold shad, ASHOFF in RDB. replace (2147450880 + Z.shiftr (sz + -1 + D) 3) with (Z.shiftr (sz + -1 + D) 3 + 2147450880) in RDB by lia.
pose proof (sval_range b) as SR.
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN : forall (y29 y30 : word), evtF bsegs RNG POST
(STpc 0x827c0 m1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (sz + -1)) (Z_to_bv 64 (Z.shiftr P 3 + 2147450880))
(Z_to_bv 64 result) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 (sz + -1 + D)) (Z_to_bv 64 range)
(Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr (P + 8) 3 + 2147450880)) (Z_to_bv 64 rolling) y29 y30)).
{ intros y29 y30.
pose proof (unpoisoned_full_rd bsegs m1 P (P + 16) (Z.shiftr (P + 8) 3 + 2147450880) UNP1
ltac:(rewrite shad_div; unfold ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
ltac:(unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)) as RDS8.
zstep. zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
assert (RDV : ov_read_bytes bsegs m1 (Z_to_bv 64 (sz + -1 + D)) 1 = Some [Z_to_bv 8 (Znth (sz - 1) pl)]).
{ eapply (u8ro_read bsegs m1 D _ (sz - 1)); [exact PL1| exact NTH| lia| unfold wa; f_equal; lia]. }
zstep. cbv beta. rewrite byte_lit by exact NR.
zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. rewrite FseWalkKit.swrap32_small by lia.
zstep. rewrite wrap32_small by lia. rewrite (Z.shiftr_div_pow2 rolling 8) by lia. change (2^8) with 256.
assert (RD8 : 0 <= rolling / 256 < 2^(8 * (Z.of_nat f - 1))).
{ split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
rewrite (FseWalkKit.swrap32_small (rolling / 256)) by lia.
zstep.
assert (LOR : Z.lor (result * 256) (Znth (sz - 1) pl) = result * 256 + Znth (sz - 1) pl) by (apply (lor_byte result); lia).
rewrite LOR. rewrite (u32_id (result * 256)) in K by lia. rewrite LOR in K.
zstep. zstep.
if_cases B2; zify_cond B2.
+
eapply (IH (sz - 1) (rolling / 256) (result * 256 + Znth (sz - 1) pl)); try lia.
* f_equal. lia.
* replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
* exact K.
+
assert (R0 : rolling / 256 = 0) by lia. rewrite R0 in K. rewrite draw_loop_0 in K.
zstep.
apply K; [| cbn [fst]; lia].
cbn [snd]. replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1. }
zstep. if_cases G2; zify_cond G2.
+
zstep. zstep. if_cases G2'; zify_lts G2'; [| exfalso; Z.div_mod_to_equations; lia].
apply JOIN.
+ apply JOIN.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM RG MX BLKP BLKD D8 KLO GOT SHB UNP UND RI RSTK RP RPS RD RDS"] Lemma u32r_bodyA : evtF bsegs RNG POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APROD_U32R) fc None m (seg_rom bsegs)).
Proof.
unfold APROD_U32R. pose proof PR as PR0. unfold prod_atA in PR0. destruct PL as [PLB PLR].
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
pose proof (ablk_lin _ _ BLKP) as LP. unfold KHIGH, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00\0?11661072890.97 11663170033.10211668882636.87 20218831278.86 21220757229.82 22661531106.90 25071629079.86 25269714927.90 2764820010.83  27669770584.96 29140532593.86 29782367974.86 29782367974.99 3237827502.90  32716547054.86 32810810841.86 35647514710.98 35847753748.86 38394305073.98 39302646093.77 40928202498.98 41964136719.81 41968874930.93 42129232087.86 43260008360.99 45221239098.86 4641771484.85  53945583241.90 54452078582.98 55262987142.79 56007886318.86 58693111343.81 58697847442.93 59314873579.82 59314873579.88 59314873579.89 59314873579.90 59314873579.99 64405586211.98 64452585470.86 64644827283.98 64644827924.82 65933918483.83 65938089388.86 00000700>00E00W00^00_00`00a00b00i00j00k00l01401B01L01M01W01a01e01f02302B02C02D02I02M02Q02R02S02a02n03=03C03J03O03S03`03a03o04604=04D04HS2P02LPS2P02LPS2P02LPS2P02D02LO3PLO3DLOS2MM2RGSSSSS2P02LPSSSS2RG3K2'S2P02D02LO3KLOS2P02P82D0FS2P02P82D0S2P02P82D0S2LOFS2P02D02MM2MXS2P02D02MM2MX1KSSS3RSPS2LOS2SZFSS2P02D02LO3KLOS2P02D02MM2MXS2P02D02MM2MX1KS2MM1KS2P02GNS3GALS2G0S2P02D02RG2K3FS2P02D02LO3PLOS2MM2RGS2MM2RGS2MM2K2S2HB".
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep. zstep.
zstep. if_cases K; zify_cond K. { exfalso. lia. }
zstep. rewrite FseWalkKit.swrap32_small by lia. zstep.
if_cases K2; zify_cond K2.
-
zstep.
eapply (u32r_tailA _ 0 size); [lia| | ].
+ inv_close PR0 PLB FR ST MU WM MI.
+ rewrite K2. reflexivity.
- assert (K2' : 0 < range) by lia.
destruct (inv_shadow _ MU) as [UNP1 UND1].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
pose proof (unpoisoned_full_rd bsegs m1 P (P + 16) (Z.shiftr (P + 8) 3 + 2147450880) UNP1
ltac:(rewrite shad_div; unfold ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
ltac:(unfold ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)) as RDS8 end.
zstep. if_cases GN; zify_cond GN; [exfalso; lia|].
zstep. rewrite land7_mod. rewrite P8.
zstep. if_cases GAL; zify_cond GAL; [exfalso; lia|].
zstep. zstep. zstep. zstep. zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
do 6 zstep.
eapply (u32r_loopA 4 size range 0);
[ change (2^(8 * (Z.of_nat 4 - 1))) with (2^24); lia | cbn; lia | lia | lia | reflexivity | | ].
+ inv_close PR0 PLB FR ST MU WM MI.
+ intros m2 y6 y14 y28 y29 y30 I2 R2.
zstep. zstep. if_cases K3; zify_cond K3.
* eapply u32r_tailA; [exact R2| exact I2| ]. destruct (draw_loop 4 pl size range 0); reflexivity.
* exfalso. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End U32R.
#[using="Type"] Lemma prod_u32r_proofA : prod_u32r_stmtA.
Proof.
intros until lo. intros PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM RG MX BLKP BLKD D8 KLO GOT SHB UNP UND RI RSTK RP RPS RD RDS -> -> ->.
eapply u32r_bodyA; eassumption.
Qed.
Section I32R.
Hypothesis U32R : prod_u32r_stmtA.
Variables (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
Hypothesis PR : prod_atA m P D size.
Hypothesis PL : payload_atA m D pl.
Hypothesis SZ : 0 <= size <= zlen pl.
Hypothesis P0 : 0 < P.
Hypothesis P8 : P mod 8 = 0.
Hypothesis D0 : 0 < D.
Hypothesis ST : stk bsegs m lo SP.
Hypothesis LO : lo <= SP - 32.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis MI : mem_inv bsegs m.
Hypothesis MM : - 2^31 <= mn <= mx.
Hypothesis RG : mx - mn < 2^24.
Hypothesis MX : mx < 2^31.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis BLKD : 0 < zlen pl -> ablk D (D + zlen pl).
Hypothesis D8 : D mod 8 = 0.
Hypothesis KLO : KHIGH <= lo.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis UNP : unpoisoned m P (P + 16).
Hypothesis UND : unpoisoned m D (D + zlen pl).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Notation W := [(P + 8, P + 16); (SP - 32, SP)].
#[using="rc lo P0 P8 D0 LO RSP PLO DLO DP BLKP BLKD D8 KLO UNP UND"] Lemma inv_shadow_i : forall m1, munch W m m1 -> unpoisoned m1 P (P + 16) /\ unpoisoned m1 D (D + zlen pl).
Proof.
intros m1 MU. pose proof (ablk_lin _ _ BLKP) as LP.
pose proof (ablk_disj_band _ _ BLKP) as DBP. unfold KHIGH, KLS, AIMG_HI in *.
split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0070>13449311261.7723492641683.7732813024914.9732813024914.9938879299635.7757297616229.9757297616229.9900000400800H00e01?01Z01oS2E0S2N0S2P83DBP1H2H42H5S2DP2D83DBP2N02LD1H2H42H53H14S2P02D02LO3RSP3DLO2LP2E01HS2P82LO3PLO3KLO3DBP1H2H42H5S2LO3DLO3KLO2N02H42H5".
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- destruct (Z.eq_dec (zlen pl) 0) as [E0|N0].
+ replace (D + zlen pl) with D by lia. apply unpoisoned_nil. change (2^64) with 18446744073709551616 in *. lia.
+ pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. unfold AIMG_HI in LD.
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc U32R PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM RG MX BLKP BLKD D8 KLO GOT SHB UNP UND RI RSTK RP RPS RD RDS"] Lemma i32r_bodyA : evtF bsegs RNG (prod_i32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m)
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APROD_I32R) fc None m (seg_rom bsegs)).
Proof.
unfold APROD_I32R. pose proof PR as PR0. unfold prod_atA in PR0. destruct PL as [PLB PLR].
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
change (2^31) with 2147483648 in *. change (2^24) with 16777216 in *.
pose proof ST as (LO0 & _ & _).
pose proof (ablk_lin _ _ BLKP) as LP. unfold KHIGH, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "01D0?1205431166.117 12428150072.10312538619124.10612974476237.11312974476237.90 12974476237.93 15278287301.87 16747972023.10417982984349.1011946522126.103 20218831278.88 21218610667.85 21361659714.90 21599037272.10521991601993.84 21991653336.1042342125151.112 2342125151.89  2342125151.92  24016102874.86 25071629079.88 25071629079.90 25076071819.10425177572496.10429018421290.11529140532593.11229140532593.88 29140532593.92 30031366090.85 30228104044.86 31521058898.90 31945547798.10531947709866.85 31992077787.10432207983043.10132716547054.88 37332287007.10538538497302.85 39302646093.79 39420794044.84 39666761885.10141650369866.85 41968874930.97 41970972091.94 42129232087.88 42132737128.85 42134909396.10542146777215.85 42146777215.86 42379585229.85 42831019478.90 43449262167.86 45221239098.88 45243883939.1034641771484.111 4641771484.87  4641771484.91  5014952752.101 5014952752.86  50861135698.90 53325701526.10054882308316.84 55262987142.81 55480730258.90 56007886318.88 56172432037.85 56563527971.10357622410744.10457628690880.10858693061802.87 58695750298.11558695750299.94 58697847442.97 59213585203.86 59314873579.84 59314873579.87 64452585470.88 64653764637.96 65938089388.88 66765322899.90 67166151880.10268380093550.86 7449406787.85  7592627616.90  00000100200B00C00D00E00K00e00i00n01@01G01Y01]01^01_01c01g01k01o02002102?02@02M02N02O02P02U02_02m03103503603:03H03[03_03c04004404804904:04;04B04R04W04\04`04e04i04n05?05C05G05K05O05S05a05b05o06006>06L06M06^06a06d07307407507607:07@07O07]07d07h07i07m08?08F08JFFS2P02D02MM2MN2URSSSS2MM1LS2P02D02LO3PLO3DLO2DP4LENPS2SZS3PLOS2P02D02LO3PLO3DLOS2MM2RGS2P02D02LO3PLO3DLOS2MNSSS2LOS2LOS2LOS2RGSSS2P02D02LO3PLOFS2P02D02RG2URSSSS3RSPS2P02D02MMS2P02D02LO3KLOS2LOS2LOFS2RGS2P02D02LO3KLOS2P02D02MM2RG2MN2URS2LOS2LOS2P02D02MM2MXS2RGS2RGFFSS2P02D0S2P02D02MN2RG2URS3KLOS3KLOS2MXS3RSPS2LOS3RSPS2P02D02LO3KLO2LPS2LOS2LOS2LOS2MMS2MMS2P02D02LO3KLOSS2P02D02MM2MXSS2P02D02LO3PLOS2P02D02LO3KLOSS2P02D02LO3KLO2LPS1HS1HS2P02D02MM2MX1GFFFS2RGS2MM1KS2P02D02MM2MX1KS2P02D02LO3PLOS2MM2RGS2HBSS2MNS2P02D02LO3RSP3KLOS2MM2MNS2HB".
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep.
if_cases K. { exfalso. unfold bv_lts in K. rewrite !signed_lit in K by lia. apply Z.ltb_lt in K. lia. }
clear K.
destruct (inv_shadow_i _ MU) as [UNP1 UND1].
zstep. zstep.
if_cases K; rewrite bv_lts_zero_r in K.
-
assert (MN : mn < 0).
{ destruct (Z.lt_ge_cases mn 0) as [L|G]; [exact L| exfalso]. rewrite unsigned_lit in K by lia. apply Z.leb_le in K. lia. }
clear K.
zstep. zstep. sw32 (mx - mn).
zstep.
replace (Z_to_bv 64 (mx mod 18446744073709551616 - mn mod 18446744073709551616)) with (Z_to_bv 64 (mx - mn))
by (apply Z_to_bv_eqm; change (2^64) with 18446744073709551616; lia).
unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
zstep. sw32 (mx - mn). zstep. zstep.
unfold APROD_U32R in U32R.
call (U32R RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -16) P D pl size 0 (mx - mn) lo);
[ exact PR0 | split; [exact PLB| exact PLR] | exact SZ | exact P0 | exact P8 | exact D0 | exact ST
| lia | lia | exact PLO | exact DLO | exact DP | exact MI | lia | lia | lia
| exact BLKP | exact BLKD | exact D8 | unfold KHIGH; lia | exact GOT | exact SHB | exact UNP1 | exact UND1
| reflexivity | reflexivity | reflexivity | ].
pose proof (uint32Range_range pl size 0 (mx - mn) ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)
ltac:(change (2^32) with 4294967296; lia)) as UR.
assert (I32 : int32Range pl size mn mx = ((uint32Range pl size 0 (mx - mn)).1 + mn, (uint32Range pl size 0 (mx - mn)).2)).
{ unfold int32Range. replace (mn <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (uint32Range pl size 0 (mx - mn)); reflexivity. }
destruct (uint32Range pl size 0 (mx - mn)) as [r size'] eqn:EU. cbn [fst snd] in *.
zstep. zstep. sw32 (r + mn).
zstep.
replace (Z_to_bv 64 (r + mn mod 18446744073709551616)) with (Z_to_bv 64 (r + mn))
by (apply Z_to_bv_eqm; change (2^64) with 18446744073709551616; lia).
unfold bv_eqb. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
zstep. sw32 (r + mn).
zstep. zstep. zstep.
release_frame FR PC SP.
zstep.
apply evtF_done. unfold prod_i32r_postA. rewrite I32. cbn [fst snd].
do 14 eexists. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC| exact POST].
-
assert (MN : 0 <= mn).
{ destruct (Z.lt_ge_cases mn 0) as [L|G]; [exfalso| exact G]. rewrite (unsigned_neg mn) in K by lia. apply Z.leb_gt in K. lia. }
clear K.
zstep. zstep. zstep. zstep.
release_frame FR ST SP.
zstep.
unfold APROD_U32R in U32R.
eapply evtF_mono.
{ eapply (U32R RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl size mn mx lo);
[ exact PR0 | split; [exact PLB| exact PLR] | exact SZ | exact P0 | exact P8 | exact D0 | exact ST
| lia | lia | exact PLO | exact DLO | exact DP | exact MI | lia | lia | lia
| exact BLKP | exact BLKD | exact D8 | unfold KHIGH; lia | exact GOT | exact SHB | exact UNP1 | exact UND1
| exact RI | exact RSTK | exact RP | exact RPS | exact RD | exact RDS
| reflexivity | reflexivity | reflexivity ]. }
cbv beta. intros ms' PO. unfold prod_u32r_postA in PO. unfold prod_i32r_postA.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & ST' & PR').
assert (I32 : int32Range pl size mn mx = uint32Range pl size mn mx).
{ unfold int32Range. replace (mn <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite I32.
do 14 eexists. exists m'. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros; lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'| exact PR'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End I32R.
#[using="Type"] Lemma prod_i32r_proofA : prod_u32r_stmtA -> prod_i32r_stmtA.
Proof.
intros U32R. intros until lo. intros PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM RG MX BLKP BLKD D8 KLO GOT SHB UNP UND RI RSTK RP RPS RD RDS -> -> ->.
eapply i32r_bodyA; eassumption.
Qed.
End CANSEC1.
