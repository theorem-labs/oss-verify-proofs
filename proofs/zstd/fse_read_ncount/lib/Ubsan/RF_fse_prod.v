(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Section U32R.
Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
Hypothesis PR : prod_at m P D size.
Hypothesis PL : payload_at m D pl.
Hypothesis SZ : 0 <= size <= zlen pl.
Hypothesis PNZ : 0 < P.
Hypothesis PAL : P mod 8 = 0.
Hypothesis DNZ : 0 < D.
Hypothesis ST : stk usegs m lo SP.
Hypothesis LO : lo <= SP - 16.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis MI : mem_inv usegs m.
Hypothesis MM : 0 <= mn <= mx.
Hypothesis RG : mx - mn < 2^24.
Hypothesis MX : mx < 2^31.
Notation W := [(P + 8, P + 16); (SP - 16, SP)].
Notation POST := (prod_u32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m).
Notation range := (mx - mn).
Definition INV (m1 : fmem) (sz : Z) : Prop :=
rw_cells usegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 sz)]
/\ bytes_at usegs m1 D (map (Z_to_bv 8) pl)
/\ (exists junk8, rw_cells usegs m1 (SP + -16) [CB 8 junk8; C8 ra])
/\ stk usegs m1 lo (SP + -16)
/\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.
Notation STpc pc mm x5 x10 x12 x13 x14 x15 x16 x17 :=
(MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp x5 t1 t2 s0 s1 x10 (Z_to_bv 64 mn) x12 x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Ltac inv_close PRx PLx FRx STx MUx WMx MIx :=
split; [exact PRx|]; split; [exact PLx|]; split; [eexists; exact FRx|]; split; [exact STx|]; split; [exact MUx|]; split; [exact WMx| exact MIx].
#[using="SP pl RSP"] Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>48041415315.53000004S2Hc".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma draw_loop_0 : forall f sz result, draw_loop f pl sz 0 result = (result, sz).
Proof. intros [|f] sz result; reflexivity. Qed.
#[using="LO RSP MM RG MX"] Lemma u32r_tail : forall m1 result sz (x5 x13 x14 x15 x16 x17 : word),
0 <= result < 2^24 -> INV m1 sz ->
(result, sz) = draw_loop 4 pl size range 0 ->
evt usegs POST (STpc 0x145f8 m1 x5 (Z_to_bv 64 result) (Z_to_bv 64 range) x13 x14 x15 x16 x17).
Proof.
intros m1 result sz x5 x13 x14 x15 x16 x17 RR (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) DL.
zstep. zstep. unfold v_remuw. Local Ltac2 Set LiaHints.tbl := fun () => "00A0>12641419845.6917846519188.6919620497065.8119628366494.6921993699182.6929140532593.7731947791659.7033267308098.7037133642481.6941617845831.6947166584393.6955873950010.7057529845269.6958695750297.8161785177838.6961855716727.697464779885.69 00000400800?00F00G00H00L00V00Z00a00b00i01001701;01?01IS2MMS2MMS2MM2RGS2MM2RGSSS2LOS2MM2MX2RMS2RGS2MM2RGSS2RG2RMS2MM2RGS2MM2MXS2RRS2RRS2MM2MX2RM".
zsimp.
rewrite (wrap32_small (range + 1)) by lia. rewrite (wrap32_small result) by lia.
replace (range + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
assert (RM : 0 <= result mod (range + 1) < range + 1) by (apply Z.mod_pos_bound; lia).
rewrite swrap32_small by lia.
zstep. rewrite swrap32_small by lia.
zstep. zstep. zstep.
release_frame FR1 ST1 SP.
apply evt_done. unfold prod_u32r_post, uint32Range.
rewrite (u32_id range) by lia. rewrite <- DL.
replace (range =? 2^32 - 1) with false by (symmetry; apply Z.eqb_neq; lia).
cbn [fst snd]. rewrite (u32_id (mn + result mod (range + 1))) by lia.
replace (result mod (range + 1) + mn) with (mn + result mod (range + 1)) by lia.
do 14 eexists. exists m1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact PR1].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="m SP D PL RSP"] Lemma pl_nth : forall i, 0 <= i < zlen pl ->
nth_error (map (Z_to_bv 8) pl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i pl)) /\ 0 <= Znth i pl < 256.
Proof.
intros i Hi. destruct PL as [_ PLR]. unfold Znth.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>15302255622.54000004S2Hi".
assert (L : (Z.to_nat i < length pl)%nat) by lia.
split.
- rewrite nth_error_map. rewrite (nth_error_nth' pl 0 L). reflexivity.
- apply (proj1 (Forall_forall _ _) PLR). apply nth_In. exact L.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="PL PNZ DNZ LO RSP PLO DLO DP"] Lemma u32r_loop : forall f sz rolling result m1 (x5 x14 x17 : word),
0 < rolling < 2^(8 * (Z.of_nat f - 1)) -> 0 <= result < 2^(32 - 8 * Z.of_nat f) -> (f <= 4)%nat ->
0 <= sz <= zlen pl -> x14 = Z_to_bv 64 sz -> INV m1 sz ->
(forall m2 (y5 y14 y16 y17 : word), INV m2 (snd (draw_loop f pl sz rolling result)) ->
0 <= fst (draw_loop f pl sz rolling result) < 2^24 ->
evt usegs POST (STpc 0x145e8 m2 y5 (Z_to_bv 64 (fst (draw_loop f pl sz rolling result))) (Z_to_bv 64 range) (Z_to_bv 64 P) y14 (Z_to_bv 64 1) y16 y17)) ->
evt usegs POST (STpc 0x145b0 m1 x5 (Z_to_bv 64 result) (Z_to_bv 64 range) (Z_to_bv 64 P) x14 (Z_to_bv 64 1) (Z_to_bv 64 rolling) x17).
Proof.
induction f as [|f IH]; intros sz rolling result m1 x5 x14 x17 RO RE F4 SZ1 -> (PR1 & PL1 & [junk8 FR1] & ST1 & MU1 & WM1 & MI1) K.
{ exfalso. cbn in RO. Local Ltac2 Set LiaHints.tbl := fun () => "00i0>10830790425.8412530674954.7614514521172.8114514712820.9514519019639.7415145254097.8515666392380.7715973761020.8716894305496.8818433127084.8818433378714.8418580387820.8019615371042.8822952730506.7525071629079.9926908658338.8928976385747.8431747966235.8834213994768.8934214256658.8836972420972.7540553477673.994058895868.88 40674861000.8841270674270.9841415845446.7641417941834.7741417958218.7843523888347.9344434388281.8848274452913.8648320946320.8852073470664.8652138671532.9954063599532.8854072487078.9454485308000.7954600075686.9956952207613.7456953944186.7859314923118.6959321100275.7259376071221.8361774160593.9762042018657.8863281946242.9563368087213.7463368428826.8463368446758.7565349223833.9966332962689.736696322386.98 68084852549.848385552099.88 8387898049.81 8592580787.79 8592611975.84 00000K00^00c01J01W02602M02h03J03e03f03g03h04804904W05205M05h06C06S06W07207P07k08>08U09009109209M09o0:M0:Q0:l0;G0;b0;f0<30<N0<\0<j0<o0=J0=K0>A0>N0>O0>_0>g0?10?O0?j0@M0@V0A10ALS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q8S3SZPS2RO2RE2F43SZ12F12P82Q83Q243P241B2H42H5S2RO2RE2F42F1S2RO2RE2F42F12P82Q83Q243P243RD8S2RO2RE2F42F12P82Q83Q24S2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P243RD82B2S2RO2RE2F42F12P82Q83Q243P24SFFS2RO2RE2F42F12P8SS2RO2RE2F42F12P82Q83Q243P242NRS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P8S2HBS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P242NRS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q8S2RO2RE2F42F12P82Q83Q24S2RO2RE2F42F12P82Q83Q243P24SFS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P243RD82B2S2RO2RE2F42F12P82Q83Q243P242NRS2HBS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P24S2DPS2RO2RE2F42F1S2RO2RE2F42F12P82Q83Q243P24S3RSP2RO2RE2F4S3RSP2RO2RE2F4S3SZPS2RO2RE2F42F12P82Q83Q243P24FS2LO3PLO3DLO2RO2RE2F43SZ12DB2F12P82Q83Q243P241B2H43H10S2RO2RE2F42F1SS2RO2RE2F42F12P8S2LO3PLOS2RO2RE2F4S2RO2RE2F42F12P82Q83Q243P242NRS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F43SZ12F12P82Q83Q243P243SZPS3SZ13SZPS2RO2RE2F42F12P82Q83Q243P24S2RO2RE2F42F12P82Q83Q243P24".
lia. }
pose proof (bytes_at_bound _ _ _ _ PL1) as DB. rewrite length_map in DB.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (F1 : (1 <= f)%nat). { destruct f; [exfalso; cbn in RO; lia| lia]. }
assert (P8 : 2^(8 * (Z.of_nat (S f) - 1)) = 256 * 2^(8 * (Z.of_nat f - 1))).
{ replace (8 * (Z.of_nat (S f) - 1)) with (8 + 8 * (Z.of_nat f - 1)) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
assert (Q8 : 2^(32 - 8 * Z.of_nat f) = 256 * 2^(32 - 8 * Z.of_nat (S f))).
{ replace (32 - 8 * Z.of_nat f) with (8 + (32 - 8 * Z.of_nat (S f))) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
assert (Q24 : 2^(32 - 8 * Z.of_nat (S f)) <= 2^16) by (apply Z.pow_le_mono_r; lia).
assert (P24 : 2^(8 * (Z.of_nat (S f) - 1)) <= 2^24) by (apply Z.pow_le_mono_r; lia).
assert (P0 : 0 < 2^(8 * (Z.of_nat f - 1))) by (apply Z.pow_pos_nonneg; lia).
cbn [draw_loop] in K. change (2^8) with 256 in K.
replace (0 <? rolling) with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in K.
change (2^16) with 65536 in Q24. change (2^24) with 16777216 in P24.
zstep. if_cases B; zify_cond B.
-
assert (sz = 0) by (Z.div_mod_to_equations; lia). subst sz.
replace (0 <? 0) with false in K by reflexivity.
apply K; [| cbn [fst]; lia].
cbn [snd]. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
- assert (SZP : 0 < sz) by (Z.div_mod_to_equations; lia).
replace (0 <? sz) with true in K by (symmetry; apply Z.ltb_lt; lia).
destruct (pl_nth (sz - 1) ltac:(lia)) as [NTH NR].
zstep. zstep.
zstep. if_cases CK1; zify_cond CK1; [exfalso; lia|].
zstep. if_cases CK2; zify_cond CK2; [exfalso; lia|].
zstep. if_cases CK3; zify_cond CK3; [exfalso; lia|].
zstep. if_cases CK4; zify_cond CK4; [exfalso; lia|].
assert (RD : ov_read_bytes usegs m1 (Z_to_bv 64 (sz + D + -1)) 1 = Some [Z_to_bv 8 (Znth (sz - 1) pl)]).
{ eapply (u8ro_read usegs m1 D _ (sz - 1)); [exact PL1| exact NTH| lia| unfold wa; f_equal; lia]. }
zstep. cbv beta. rewrite byte_lit by exact NR.
zstep. zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. rewrite swrap32_small by lia.
zstep. rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
assert (RD8 : 0 <= rolling / 256 < 2^(8 * (Z.of_nat f - 1))).
{ split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
rewrite swrap32_small by lia.
zstep.
assert (LOR : Z.lor (result * 256) (Znth (sz - 1) pl) = result * 256 + Znth (sz - 1) pl) by (apply (lor_byte result); lia).
rewrite LOR. rewrite (u32_id (result * 256)) in K by lia. rewrite LOR in K.
zstep.
if_cases B2; zify_cond B2.
+
eapply (IH (sz - 1) (rolling / 256) (result * 256 + Znth (sz - 1) pl)); try lia.
* reflexivity.
* replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
* exact K.
+
assert (R0 : rolling / 256 = 0) by lia. rewrite R0 in K. rewrite draw_loop_0 in K.
apply K; [| cbn [fst]; lia].
cbn [snd]. replace (sz - 1) with (sz + -1) by lia. inv_close PR1 PL1 FR1 ST1 MU1 WM1 MI1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="PR PL SZ PNZ PAL DNZ ST LO RSP PLO DLO DP MI MM RG MX"] Lemma u32r_body : evt usegs POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PPROD_U32R) fc None m (seg_rom usegs)).
Proof.
unfold PPROD_U32R. pose proof PR as PR0. unfold prod_at in PR0. destruct PL as [PLB PLR].
pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
Local Ltac2 Set LiaHints.tbl := fun () => "00H0>20218831278.6621220805736.6122665722051.6325071629079.6625273942734.632762683152.62 29140532593.663233656463.63 39298451021.5741964136719.6141970972089.7242129232087.6645221239098.6653941418920.6355262987142.5958693111343.6158695750297.7259308579027.7159314923118.6164452585470.6664644827283.7064644827924.6265927642411.6365938089388.6600000800?00@00A00B00C00D00L00P00W00`00a00f00j00k01201;01B01H01P01W01^01e01iS2LO3DLOS2MM2RGSSSSSS2RG3K2'S2LOS2MM2MXS2MM2MX1KSS3RSPS2SZSS2MM2MXS2MM2MX1KS2RG2K3S2MM1KS2LO3PLOS2MM2RGS2MM2RGS2MM2K2S2HB".
carve_frame 16%nat ST.
zstep. zstep. zstep.
if_cases K; zify_cond K. { exfalso. lia. }
zstep. rewrite swrap32_small by lia. zstep.
if_cases K2; zify_cond K2.
-
zstep.
eapply (u32r_tail _ 0 size); [lia| | ].
+ inv_close PR0 PLB FR ST MU WM MI.
+ rewrite K2. reflexivity.
- assert (K2' : 0 < range) by (Z.div_mod_to_equations; lia).
zstep. zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
zstep. assert (A7 : Z.land P 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact PAL).
rewrite A7. zstep. if_false.
zstep. zstep. zstep.
eapply (u32r_loop 4 size range 0);
[ change (2^(8 * (Z.of_nat 4 - 1))) with (2^24); lia | cbn; lia | lia | lia | reflexivity | | ].
+ inv_close PR0 PLB FR ST MU WM MI.
+ intros m2 y5 y14 y16 y17 I2 R2.
zstep. zstep. if_cases K3; zify_cond K3.
* eapply u32r_tail; [exact R2| exact I2| ]. destruct (draw_loop 4 pl size range 0); reflexivity.
* exfalso. Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End U32R.
Lemma prod_u32r_proof : prod_u32r_stmt.
Proof.
intros until lo. intros PR PL SZ PNZ PAL DNZ ST LO RSP PLO DLO DP MI MM RG MX -> -> ->.
eapply u32r_body; eassumption.
Qed.
Section I32R.
Hypothesis U32R : prod_u32r_stmt.
Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (size mn mx lo : Z).
Hypothesis PR : prod_at m P D size.
Hypothesis PL : payload_at m D pl.
Hypothesis SZ : 0 <= size <= zlen pl.
Hypothesis P0 : 0 < P.
Hypothesis P8 : P mod 8 = 0.
Hypothesis D0 : 0 < D.
Hypothesis ST : stk usegs m lo SP.
Hypothesis LO : lo <= SP - 32.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis MI : mem_inv usegs m.
Hypothesis MM : - 2^31 <= mn <= mx.
Hypothesis RG : mx - mn < 2^24.
Hypothesis MX : mx < 2^31.
#[using="U32R PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM RG MX"] Lemma i32r_body : evt usegs (prod_i32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP P D pl size mn mx lo m)
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 mn) (Z_to_bv 64 mx) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PPROD_I32R) fc None m (seg_rom usegs)).
Proof.
unfold PPROD_I32R. pose proof PR as PR0. unfold prod_at in PR0. destruct PL as [PLB PLR].
pose proof (munch_refl [(P + 8, P + 16); (SP - 32, SP)] m) as MU. pose proof (wmono_refl usegs m) as WM.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
change (2^31) with 2147483648 in *. change (2^24) with 16777216 in *.
pose proof ST as (LO0 & _ & _).
Local Ltac2 Set LiaHints.tbl := fun () => "0130>12428150072.8412974476237.7312974476237.7412974476237.9314833884483.8515278353345.6717976303105.801946522126.84 20218831278.7121218610667.6621361659714.7321594450553.8521991601993.6521991653336.8424009893596.6625071629079.7125071629079.7325177572496.8529018421281.8829140532593.7129140532593.7329140532593.9230037805526.6531945547798.8531947709866.6631992077787.8532197107551.8037332287007.8538544868106.6539304743405.6239420778041.6639677382145.804061767392.85 41107862462.8441656318806.6541970972091.7542129232087.7142132737128.6642134909396.8542385795281.6542831019478.7343447116625.6645221239098.715004596652.80 5008742454.66 54882292313.6655262987142.6455480730258.7355810242966.8057622410744.8858693176363.6758695750289.8858695750299.7559207243829.6659314808559.6759314923118.6659314988138.6762900777713.8564186955846.8564452585470.7165938089388.7166765322899.7367160074706.8167789111905.8568377915240.667455515487.65 7592627616.73 00000100200300400<00B00F00K00S00Z00b00f00g00h00l00m00n00o01601701801901>01B01F01G01K01X01\01`01g01k02;02<02@02A02B02F02Q02U02Z02^02c02g02k03203303;03<03?03H03I03J03N03T03Z03c03f04304;04?04@04D04E04T04[04_FSSSS2LO3PLOS2MM1LS2SZS3PLOS2LO3DLOS2MM2RGS2LO3DLOS2MNSSS2RGSSFS2RG2URSSSS3RSPS2LOS2LOFS2RGS2MM2RG2MN2URS2LOS2LOS2MM2MXS2RGS2P03RSP2DP4LENPFS2RGFSS2MMS2P03RSP2MNS2MXS3RSPS2LOS3RSPS2MMS2MMS2MM2MXSS2LO3PLOSS1HS2MM2MX1GFFS2RGS2MM1KS2MM1KS2MM2MX1KS1HS2LO3DLO4LENPS2LO3PLOS2HBSS2MNSS2P02LO3RSP3PLOS2MM2MNS2HB".
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep.
if_cases K. { exfalso. unfold bv_lts in K. rewrite !signed_lit in K by lia. apply Z.ltb_lt in K. lia. }
clear K.
zstep. zstep.
if_cases K; rewrite bv_lts_zero_r in K.
-
assert (MN : mn < 0).
{ destruct (Z.lt_ge_cases mn 0) as [L|G]; [exact L| exfalso]. rewrite unsigned_lit in K by lia. apply Z.leb_le in K. lia. }
clear K.
zstep. match goal with |- context [Z_to_bv 64 (mx mod ?M - mn mod ?M)] => rewrite (Z_to_bv_eqm (mx mod M - mn mod M) (mx - mn)) by (rewrite (Zminus_mod mx mn); reflexivity) end.
zstep. sw32 (mx - mn).
zstep. if_false.
zstep. sw32 (mx - mn).
zstep. zstep.
unfold PPROD_U32R in U32R.
call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -16) P D pl size 0 (mx - mn) lo);
[ exact PR0 | split; [exact PLB| exact PLR] | exact SZ | exact P0 | exact P8 | exact D0 | exact ST
| lia | lia | exact PLO | exact DLO | exact DP | exact MI | lia | lia | lia
| reflexivity | reflexivity | reflexivity | ].
pose proof (uint32Range_range pl size 0 (mx - mn) ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)
ltac:(change (2^32) with 4294967296; lia)) as UR.
assert (I32 : int32Range pl size mn mx = ((uint32Range pl size 0 (mx - mn)).1 + mn, (uint32Range pl size 0 (mx - mn)).2)).
{ unfold int32Range. replace (mn <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (uint32Range pl size 0 (mx - mn)); reflexivity. }
destruct (uint32Range pl size 0 (mx - mn)) as [r size'] eqn:EU. cbn [fst snd] in *.
zstep. zstep. sw32 (r + mn).
zstep. if_false.
zstep. sw32 (r + mn).
zstep. zstep. zstep.
release_frame FR PC SP.
zstep.
apply evt_done. unfold prod_i32r_post. rewrite I32. cbn [fst snd].
do 14 eexists. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC| exact POST].
-
assert (MN : 0 <= mn).
{ destruct (Z.lt_ge_cases mn 0) as [L|G]; [exfalso| exact G]. rewrite (unsigned_neg mn) in K by lia. apply Z.leb_gt in K. lia. }
clear K.
zstep. zstep. zstep. zstep.
release_frame FR ST SP.
zstep.
unfold PPROD_U32R in U32R.
eapply evt_mono.
{ eapply (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl size mn mx lo);
[ exact PR0 | split; [exact PLB| exact PLR] | exact SZ | exact P0 | exact P8 | exact D0 | exact ST
| lia | lia | exact PLO | exact DLO | exact DP | exact MI | lia | lia | lia
| reflexivity | reflexivity | reflexivity ]. }
cbv beta. intros ms' PO. unfold prod_u32r_post in PO. unfold prod_i32r_post.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & ST' & PR').
assert (I32 : int32Range pl size mn mx = uint32Range pl size mn mx).
{ unfold int32Range. replace (mn <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite I32.
do 14 eexists. exists m'. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp. cbn [outside]. intros; lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'| exact PR'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End I32R.
Lemma prod_i32r_proof : prod_u32r_stmt -> prod_i32r_stmt.
Proof.
intros U32R. intros until lo. intros PR PL SZ P0 P8 D0 ST LO RSP PLO DLO DP MI MM RG MX -> -> ->.
eapply i32r_body; eassumption.
Qed.
