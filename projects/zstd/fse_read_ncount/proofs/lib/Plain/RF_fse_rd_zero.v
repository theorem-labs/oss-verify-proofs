(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_rd_base.
Import ListNotations.
Open Scope Z_scope.
Section Zero.
Variable C : rdctx.
Hypothesis OK : rd_ok C.
Variable POST : machine_state -> Prop.
Notation buf := (c_buf C).
Notation msv1 := (c_msv0 C + 1).
Notation BUF := (c_BUF C).
Notation NC := (c_NC C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
#[using="Type"] Lemma tab_rd : forall m1 i, mem_inv psegs m1 -> 0 <= i < 32 ->
ov_read_bytes psegs m1 (Z_to_bv 64 (68660 + i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) DB_TABLE 0)].
Proof.
intros m1 i MI Hi.
assert (RO : ro_cells psegs m1 68660 [CB 32 (map (Z_to_bv 8) DB_TABLE)]).
{ Local Ltac2 Set LiaHints.tbl := fun () => "0040=10351690818.817099647406.72130477481.8 60839208629.700000400500900:S2HiSS2HiS".
apply (ro_cells_image psegs m1 68660 (map (Z_to_bv 8) DB_TABLE) MI); [vm_compute; reflexivity| lia| cbn; lia]. }
destruct RO as [_ BA]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
eapply (u8ro_read psegs m1 68660 _ i); [exact BA| | lia| unfold wa; f_equal; lia].
rewrite nth_error_map. rewrite (nth_error_nth' DB_TABLE 0) by (cbn; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma zero_ctz1 : forall bs m1 (x1 x12 x14 x20 x22 x23 x25 x26 x27 x30 : word),
0 <= bs < 2^32 -> mem_inv psegs m1 ->
(forall y27, evt psegs POST (rd_lst C 0x13fb0 m1 x1 x12 x14 x20 x22 x23 (Z_to_bv 64 (bv_swrap 32 bs)) (Z_to_bv 64 68660) (Z_to_bv 64 (ctzv bs)) y27 x30)) ->
evt psegs POST (rd_lst C 0x13f88 m1 x1 x12 x14 x20 x22 x23 (Z_to_bv 64 (bv_swrap 32 bs)) x25 x26 x27 x30).
Proof.
intros bs m1 x1 x12 x14 x20 x22 x23 x25 x26 x27 x30 Hbs MI K.
pose proof (ctzv_range bs Hbs) as Rk. Local Ltac2 Set LiaHints.tbl := fun () => "0090>14937404944.3624578435691.222523523745.35 27521348600.4028913119920.3628913119921.3559588178608.3659588178609.3562186928258.1900000100500600700800900:00;00?FS2RkFFSSSSS2Rk".
destruct (db_table_ok (ctzv bs) ltac:(lia)) as [Ri Et].
pose proof (tab_rd m1 (db_idx (ctzv bs)) MI Ri) as RD. rewrite Et in RD.
unfold rd_lst in *.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite (ctz_index_form bs Hbs).
zstep. cbv beta. rewrite byte_lit by lia.
apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma zero_load1 : forall m1 msvw tlw nc ip' bc' cn (x1 x12 x14 x20 x22 x24 x26 x27 x30 : word),
rd_inv C m1 nc msvw tlw -> 0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= bc' < 32 -> 0 <= cn < 2^31 ->
x14 = Z_to_bv 64 (BUF + ip') -> x22 = Z_to_bv 64 bc' ->
(forall y1 y27, evt psegs POST (rd_lst C 0x1400c m1 y1 x12 x14 x20 x22 (Z_to_bv 64 (cn + 36))
(Z_to_bv 64 (bv_swrap 32 (le32 buf ip' / 2 ^ bc'))) (Z_to_bv 64 68660)
(Z_to_bv 64 (ctzv (le32 buf ip' / 2 ^ bc'))) y27 x30)) ->
evt psegs POST (rd_lst C 0x13fbc m1 x1 x12 x14 x20 x22 (Z_to_bv 64 cn) x24 (Z_to_bv 64 68660) x26 x27 x30).
Proof.
intros m1 msvw tlw nc ip' bc' cn x1 x12 x14 x20 x22 x24 x26 x27 x30 INV Hip0 Hip4 Hbc Hcn -> -> K.
destruct INV as (_ & _ & HBUF & _ & _ & _ & _ & _ & _ & MI).
Local Ltac2 Set LiaHints.tbl := fun () => "00N0>11449825958.6411449825958.6711449825958.7414533046805.2614937404944.5215534906497.512523523744.52 25708257752.5328913119920.5228913119921.5128913119926.543132576385.51 34624433032.6035120240342.2835616724156.5239733894568.5340686558679.3840688657782.3243929283712.5254738759716.2456641621271.3057076067641.5057637079050.3559588178608.5259588178609.5159588178614.5459588178615.536455047083.53 68173727475.388923287491.38 00000100200300>00?00@00A00B00C00D00E00F00G00R00S00T00Y00^00_00j01501601:01;01<01=01>01C01G01LFFFS4Hip04Hip4FFFFSSSFFS4Hip04Hip4FFS3HbcS3HbcFS4Hip04Hip4S4Hip04Hip4FS2RkSSSSS3HbcS2RkS3Hbc".
destruct (buf_rd C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rd C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rd C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rd C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
set (bs' := le32 buf ip' / 2 ^ bc') in *.
assert (Rbs : 0 <= bs' < 2^32) by (subst bs'; apply shr_range; [apply le32_range; apply (buf_all_bytes C OK)| lia]).
pose proof (ctzv_range bs' Rbs) as Rk. destruct (db_table_ok (ctzv bs') ltac:(lia)) as [Ri Et].
pose proof (tab_rd m1 (db_idx (ctzv bs')) MI Ri) as RDT. rewrite Et in RDT.
unfold rd_lst in *.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc' 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
fold (le32 buf ip'). fold bs'.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite (ctz_index_form bs' Rbs).
zstep. cbv beta. rewrite byte_lit by lia.
zstep.
apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma zero_rep : forall f s rep s1 rep1 m1 msvw tlw pc (x1 x12 x20 x27 x30 : word),
rep_loop buf f s rep = Ok (s1, rep1) ->
rd_inv C m1 (r_nc s) msvw tlw ->
0 <= r_bitStream s < 2^32 -> 0 <= r_ip s -> r_ip s + 4 <= zlen buf -> 0 <= r_bitCount s < 32 ->
0 <= r_charnum s -> r_charnum s + 36 * Z.of_nat f <= 2^30 ->
rep = ctzv (r_bitStream s) / 2 ->
(pc = 0x13fb0 \/ pc = 0x1400c) ->
(forall y1 y27,
0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
0 <= r_charnum s1 <= 2^30 -> rep1 = ctzv (r_bitStream s1) / 2 -> rep1 < 12 ->
r_nc s1 = r_nc s /\ r_remaining s1 = r_remaining s /\ r_threshold s1 = r_threshold s /\ r_nbBits s1 = r_nbBits s /\ r_previous0 s1 = r_previous0 s ->
evt psegs POST (rd_lst C 0x1402c m1 y1 x12 (Z_to_bv 64 (BUF + r_ip s1)) x20 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1))
(Z_to_bv 64 (bv_swrap 32 (r_bitStream s1))) (Z_to_bv 64 68660) (Z_to_bv 64 (ctzv (r_bitStream s1))) y27 x30)) ->
evt psegs POST (rd_lst C pc m1 x1 x12 (Z_to_bv 64 (BUF + r_ip s)) x20 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_charnum s))
(Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) (Z_to_bv 64 68660) (Z_to_bv 64 (ctzv (r_bitStream s))) x27 x30).
Proof.
induction f as [|f IH]; intros s rep s1 rep1 m1 msvw tlw pc x1 x12 x20 x27 x30 RL INV Hbs Hip0 Hip4 Hbc Hcn0 Hcn Erep Hpc K.
{ cbn in RL. discriminate RL. }
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & (HB0 & HB1) & _).
pose proof (ctzv_range _ Hbs) as Rk.
cbn [rep_loop] in RL.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
change (2^30) with 1073741824 in *. rewrite Nat2Z.inj_succ in Hcn.
destruct (Z.leb_spec 12 rep) as [GE|LT].
-
Local Ltac2 Set LiaHints.tbl := fun () => "00K0>1667314836.39 1667314836.42 18348088741.4320444856350.5829782203372.4331171024386.4232150612422.4332460736809.4332671791780.4332676405654.5535506171687.4340688772470.5741207267526.584304519849.52 47364278768.4347377289922.5548792160851.5850003811752.4451189755707.5651456153634.5554410652210.56557369777.54  58030444185.4359315036641.3959315036641.4261756416939.4363511350903.4300000400800900:00;00E00F00G00S00_00b00f00k00l01?01R01X01a01k02302402=02@02G02N02V02WS2RkS2RkSSSS4Hcn03HcnSSS2HH3HB03HB1S2HH3HB03HB1S1BS2I3S3HcnFS4Hip04Hip43HB03HB1S4Hip42HH3HB03HB11BS4Hcn0S2LT1H2H0S4Hcn03HcnS4Hip41BFS2GE1H2H0S1BS3K241BS3K241BS4Hip41BS".
assert (K24 : 24 <= ctzv bs) by (subst rep; Z.div_mod_to_equations; lia).
unfold FseNCount.Zlength in RL.
assert (LOAD : forall ip' bc' (y1 y14 y22 y24 y26 y27 : word),
(let! w := readLE32 buf ip' in let! bs0 := shr32 w bc' in let! repeats' := repeats_of bs0 in
rep_loop buf f (FseNCount.mkR nc ip' bs0 bc' (cn + 3 * 12) rem thr nb p0) repeats') = Ok (s1, rep1) ->
y14 = Z_to_bv 64 (BUF + ip') -> y22 = Z_to_bv 64 bc' ->
evt psegs POST (rd_lst C 0x13fbc m1 y1 x12 y14 x20 y22 (Z_to_bv 64 cn) y24 (Z_to_bv 64 68660) y26 y27 x30)).
{ intros ip' bc' y1 y14 y22 y24 y26 y27 RL' -> ->.
destruct (readLE32 buf ip') as [w| | |] eqn:ER; cbn [bind] in RL'; try discriminate RL'.
destruct (shr32 w bc') as [bs'| | |] eqn:ES; cbn [bind] in RL'; try discriminate RL'.
destruct (repeats_of bs') as [rep'| | |] eqn:EP; cbn [bind] in RL'; try discriminate RL'.
destruct (readLE32_inv _ _ _ ER) as (I1 & I2 & ->). destruct (shr32_inv _ _ _ ES) as (I3 & ->).
assert (Rbs' : 0 <= le32 buf ip' / 2 ^ bc' < 2^32) by (apply shr_range; [apply le32_range; apply (buf_all_bytes C OK)| lia]).
rewrite (repeats_of_ctzv _ Rbs') in EP. injection EP as <-.
eapply (zero_load1 m1 msvw tlw nc ip' bc' cn); try eassumption; try reflexivity; try lia.
intros z1 z27.
eapply (IH (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' (cn + 3 * 12) rem thr nb p0) _ s1 rep1 m1 msvw tlw 0x1400c);
cbnR; try eassumption; try reflexivity; try lia. }
clear IH K. unfold rd_lst in LOAD |- *.
assert (T0 : evt psegs POST
(MS (mkR x1 (Z_to_bv 64 (c_SP C + -112)) (c_gp C) (c_tp C)
(Z_to_bv 64 (BUF + zlen buf + -7)) (Z_to_bv 64 (BUF + zlen buf + -4)) (Z_to_bv 64 1431655765)
(Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 BUF) (Z_to_bv 64 32) (Z_to_bv 64 1) x12 (Z_to_bv 64 2) (Z_to_bv 64 (BUF + ip))
(Z_to_bv 64 18446744071562067968) (Z_to_bv 64 24) (Z_to_bv 64 23)
(Z_to_bv 64 NC) (Z_to_bv 64 125613361) x20 (Z_to_bv 64 msv1) (Z_to_bv 64 bc) (Z_to_bv 64 cn)
(Z_to_bv 64 (bv_swrap 32 bs)) (Z_to_bv 64 68660) (Z_to_bv 64 (ctzv bs)) x27
(Z_to_bv 64 858993459) (Z_to_bv 64 252645135) x30 (Z_to_bv 64 16843009))
(c_F C) (Z_to_bv 64 0x13fb4) (c_fc C) None m1 (seg_rom psegs))).
{ zstep.
if_cases B; zify_cond B.
-
replace (ip <=? zlen buf - 7) with false in RL by (symmetry; apply Z.leb_gt; lia).
zstep. replace (BUF + ip - (BUF + zlen buf + -7)) with (ip - zlen buf + 7) by lia.
rewrite (swrap32_small (ip - zlen buf + 7)) by lia.
zstep. zstep. zstep. zstep. zstep.
eapply (LOAD _ _ _ _ _ _ _ _ RL); [f_equal; lia|]. f_equal.
rewrite !land_31. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
change 18446744073709551616 with (2^64). rewrite (Z.mod_mod_divide _ (2^64) 32) by (exists (2^59); reflexivity).
f_equal. lia.
- replace (ip <=? zlen buf - 7) with true in RL by (symmetry; apply Z.leb_le; lia).
zstep. eapply (LOAD _ _ _ _ _ _ _ _ RL); [f_equal; lia| reflexivity]. }
destruct Hpc as [-> | ->].
+ zstep. if_cases B; zify_cond B; [exfalso; lia|]. exact T0.
+ zstep. if_cases B; zify_cond B; [| exfalso; lia]. exact T0.
-
injection RL as <- <-. cbnR.
assert (K24 : ctzv bs < 24) by (subst rep; Z.div_mod_to_equations; lia).
specialize (fun y1 y27 => K y1 y27 Hbs Hip0 Hip4 Hbc ltac:(lia) Erep LT ltac:(repeat split; reflexivity)).
unfold rd_lst in K |- *.
destruct Hpc as [-> | ->].
+ zstep. if_cases B; zify_cond B; [| exfalso; lia]. apply K.
+ zstep. if_cases B; zify_cond B; [exfalso; lia|]. zstep. apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma zero_load2 : forall s3 m1 msvw tlw ip' (x1 x14 x22 x23 x24 x26 x27 : word),
rd_inv C m1 (r_nc s3) msvw tlw ->
0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s3 < 32 ->
r_ip s3 = ip' -> r_bitStream s3 = le32 buf ip' / 2 ^ r_bitCount s3 ->
x14 = Z_to_bv 64 (BUF + ip') -> x22 = Z_to_bv 64 (r_bitCount s3) ->
(forall y1 y23 y26 y27, evt psegs POST (rd_cnt C s3 m1 y1 y23 y26 y27)) ->
evt psegs POST (rd_lst C 0x14068 m1 x1 (Z_to_bv 64 (r_remaining s3)) x14 (Z_to_bv 64 (r_threshold s3)) x22
x23 x24 (Z_to_bv 64 (r_charnum s3)) x26 x27 (Z_to_bv 64 (r_nbBits s3))).
Proof.
intros s3 m1 msvw tlw ip' x1 x14 x22 x23 x24 x26 x27 INV Hip0 Hip4 Hbc Eip Ebs -> -> K.
destruct INV as (_ & _ & HBUF & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>14533046805.2215534906496.4921481239870.3525995870148.493132576384.49 35120240342.2440138410406.3543929283713.4854738759716.2056641621271.2659588178608.4959588178609.4800000;00<00A00F00G00R00W00X00c00n00o010S4Hip04Hip4FS3HbcS3HbcFS4Hip04Hip4S3HbcFS4Hip04Hip4S4Hip04Hip4SS".
destruct (buf_rd C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rd C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rd C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rd C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
pose proof K as K'. unfold rd_cnt, rd_lst in K'.
destruct s3 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip.
unfold rd_lst.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
fold (le32 buf ip'). rewrite <- Ebs.
apply K'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma zero_reload : forall s2 s3 m1 msvw tlw (x1 x23 x24 x26 x27 : word),
rd_inv C m1 (r_nc s2) msvw tlw -> reload buf s2 = Ok s3 ->
0 <= r_ip s2 -> r_ip s2 + 4 <= zlen buf -> 0 <= r_bitCount s2 < 64 ->
(forall y1 y23 y26 y27, evt psegs POST (rd_cnt C s3 m1 y1 y23 y26 y27)) ->
evt psegs POST (rd_lst C 0x14058 m1 x1 (Z_to_bv 64 (r_remaining s2)) (Z_to_bv 64 (BUF + r_ip s2)) (Z_to_bv 64 (r_threshold s2))
(Z_to_bv 64 (r_bitCount s2)) x23 x24 (Z_to_bv 64 (r_charnum s2)) x26 x27 (Z_to_bv 64 (r_nbBits s2))).
Proof.
intros s2 s3 m1 msvw tlw x1 x23 x24 x26 x27 INV RL Hip0 Hip4 Hbc K.
pose proof (reload_inv buf s2 s3 (buf_all_bytes C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (I1 & I2 & I3 & ->).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & (HB0 & HB1) & _).
destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold reload_pos in *. unfold FseNCount.Zlength in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00N0>10029754702.3510992306353.4211001195444.3511706759828.3513703880721.3221479112868.3225993772992.4225993772992.4325995870149.5626766602107.3526766602234.3429786561501.3229788724074.3330195467701.3530614832779.3332458649881.3532665485845.343497148261.33 35504068375.3535916362634.4542815240411.354304519847.42 47366385985.3447375192773.4255726401616.3558024162856.3459078035918.3563370427949.3267439684295.358929299744.35 00000400@00L00Q00V00[00`00e00j00k00l00m00n00o01401501A01D01H01I01R01S01f02:02B02F02J02K02T02jS2B2S2HH3HB03HB1S2HH3HB03HB1S3HbcS3HbcS3HbcS3HbcS3HbcS3HbcSSSSSS3HbcSS2HH3HB03HB1S1QS2B1FS4Hip42B1FS4Hip04Hip43HB03HB1S4Hip42HH3HB03HB12B1S3Hbc2B2S2B1S2B2SS4Hip42B1S4Hip42HH3HB03HB11Q2B1".
rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (LOAD : forall ip' bc' (y1 y14 y22 y23 y24 y26 y27 : word),
fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
y14 = Z_to_bv 64 (BUF + ip') -> y22 = Z_to_bv 64 bc' ->
evt psegs POST (rd_lst C 0x14068 m1 y1 (Z_to_bv 64 rem) y14 (Z_to_bv 64 thr) y22 y23 y24 (Z_to_bv 64 cn) y26 y27 (Z_to_bv 64 nb))).
{ intros ip' bc' y1 y14 y22 y23 y24 y26 y27 E1 E2 -> ->. rewrite E1, E2 in *.
eapply (zero_load2 (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb p0) m1 msvw tlw ip'); try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
clear K. unfold rd_lst in LOAD |- *.
zstep. rewrite (wrap32_small bc) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite (swrap32_small (bc / 8)) by lia.
zstep.
if_cases B1; zify_cond B1.
- zstep. zstep.
if_cases B2; zify_cond B2.
+ replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD
by (symmetry; apply orb_true_iff; right; apply Z.leb_le; lia).
zstep. zstep. rewrite land_7.
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia].
+ replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with false in LOAD
by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
zstep. replace (BUF + ip - (BUF + zlen buf + -4)) with (ip - zlen buf + 4) by lia.
rewrite (swrap32_small (ip - zlen buf + 4)) by lia.
zstep. zstep. zstep.
rewrite (Z.add_comm _ bc). rewrite (clamp_bc bc (ip - zlen buf + 4)) by lia.
zstep. zstep.
eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); first [reflexivity | f_equal; lia | f_equal; f_equal; lia].
- replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD
by (symmetry; apply orb_true_iff; left; apply Z.leb_le; lia).
zstep. zstep. rewrite land_7.
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma zero_tail : forall s1 m1 msvw tlw fl (x1 x27 : word),
rd_inv C m1 (r_nc s1) msvw tlw ->
0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
0 <= r_charnum s1 <= 2^30 -> ctzv (r_bitStream s1) / 2 < 12 -> 0 <= r_remaining s1 < 2^31 ->
(let rep1 := ctzv (r_bitStream s1) / 2 in
let! bs := shr32 (r_bitStream s1) (2 * rep1) in
let s2 := FseNCount.mkR (r_nc s1) (r_ip s1) bs (r_bitCount s1 + 2 * rep1 + 2) (r_charnum s1 + 3 * rep1 + Z.land bs 3)
(r_remaining s1) (r_threshold s1) (r_nbBits s1) (r_previous0 s1) in
if msv1 <=? r_charnum s1 + 3 * rep1 + Z.land bs 3 then Ok (Brk s2) else let! s3 := reload buf s2 in Ok (Cont s3)) = Ok fl ->
(forall s' y1 y20 y23 y24 y26 y27 y30, fl = Brk s' -> r_nc s' = r_nc s1 -> rd_brk_ok C s' ->
evt psegs POST (rd_exit C s' m1 y1 y20 y23 y24 y26 y27 y30)) ->
(forall s' y1 y23 y26 y27, fl = Cont s' -> r_nc s' = r_nc s1 -> evt psegs POST (rd_cnt C s' m1 y1 y23 y26 y27)) ->
evt psegs POST (rd_lst C 0x1402c m1 x1 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (BUF + r_ip s1)) (Z_to_bv 64 (r_threshold s1))
(Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s1)))
(Z_to_bv 64 68660) (Z_to_bv 64 (ctzv (r_bitStream s1))) x27 (Z_to_bv 64 (r_nbBits s1))).
Proof.
intros s1 m1 msvw tlw fl x1 x27 INV Hbs Hip0 Hip4 Hbc Hcn Hrep Hrem RR KB KC.
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
pose proof (ctzv_range _ Hbs) as Rk.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. cbv zeta in RR.
set (k := ctzv bs) in *. set (rep := k / 2) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00S0>101305884.41  10434093890.4112619097965.5416911362127.4817709097046.5118459507902.5118461605044.6518461605045.5419615514370.4319622043024.4223746375204.4125041511207.412505950386.41 2509909495.35 27396979568.4827519251446.5129890292957.4829890420804.4330439707575.4133257856505.4335589194279.3836400373101.4140829896556.3746950398903.4247130424411.4847130556610.4355705194801.5455903789380.4155916873729.3556428502566.4959060989939.4259251310730.388337467334.35 8931407120.42 9120371982.40 00000=00f01601701@01D01H01L01M01R01b01h01n02402A02B02H02N02O02\02_02`02a02d02j03003103703=03M03P03T03Y03i047S3Hbc2Rk4RrepS4Hip04Hip43Hbc3Hcn4Hrem3HM02Rk4Rrep2L31BS3Hcn2Rk4Rrep2M1FS2Rk4RrepS2RkS2RkS2RkFS3HM0S3Hcn2Rk4Rrep2L3S4Rbs2S4RrepS4RrepS3Hbc2Rk4RrepFS4Hip0S4Hip0SS3Hbc2Rk4RrepS1HSSS1BS4Hip4S4Hip4SS4RrepS4RrepS3Hbc2Rk4Rrep2M1S1BS2RkS3HbsS3Hcn2Rk4Rrep2L3S4Hrep2Rk1H2H0".
assert (Rrep : 0 <= rep <= 11 /\ 2 * rep <= k <= 2 * rep + 1) by (subst rep; Z.div_mod_to_equations; lia).
rewrite shr32_ok in RR by lia. cbn [bind] in RR.
set (bs2 := bs / 2 ^ (2 * rep)) in *.
assert (Rbs2 : 0 <= bs2 < 2^32) by (subst bs2; apply shr_range; lia).
assert (L3 : 0 <= Z.land bs2 3 <= 3) by (rewrite land_3; pose proof (Z.mod_pos_bound bs2 4 ltac:(lia)); lia).
change (2^30) with 1073741824 in *. change (2^31) with 2147483648 in *.
unfold rd_lst.
destruct (ctz_masks k ltac:(lia)) as (M1 & M2 & M3). fold rep in M1, M2, M3.
zstep. rewrite M1. zstep. rewrite M2. zstep. rewrite M3. zstep.
zstep. rewrite (wrap32_swrap32_u32 bs Hbs). rewrite (Z.mod_small (2 * rep) 32) by lia.
rewrite Z.shiftr_div_pow2 by lia. fold bs2.
zstep. zstep. rewrite (land_swrap32 bs2 3) by lia.
zstep. rewrite (swrap32_small (2 * rep + rep + cn + Z.land bs2 3)) by lia.
replace (2 * rep + rep + cn + Z.land bs2 3) with (cn + 3 * rep + Z.land bs2 3) by lia.
zstep. zstep. rewrite (swrap32_small (bc + 2 * rep + 2)) by lia.
zstep.
if_cases B; zify_cond B.
-
replace (msv1 <=? cn + 3 * rep + Z.land bs2 3) with true in RR by (symmetry; apply Z.leb_le; lia).
injection RR as <-.
pose proof (KB (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)) as KB'.
unfold rd_exit, rd_lst in KB'. cbnR.
eapply KB'; [reflexivity| reflexivity|]. unfold rd_brk_ok. cbnR. change (2^31) with 2147483648. lia.
- replace (msv1 <=? cn + 3 * rep + Z.land bs2 3) with false in RR by (symmetry; apply Z.leb_gt; lia).
destruct (reload buf (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)) as [s3| | |] eqn:RL;
cbn [bind] in RR; try discriminate RR. injection RR as <-.
pose proof (fun y1 y23 y24 y26 y27 => zero_reload (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)
s3 m1 msvw tlw y1 y23 y24 y26 y27 INV RL) as ZR. cbnR. unfold rd_lst in ZR.
eapply ZR; try lia.
intros y1 y23 y26 y27. apply KC; [reflexivity|].
pose proof (reload_inv buf _ s3 (buf_all_bytes C OK) RL) as RI. cbnR. cbv zeta in RI.
destruct (RI ltac:(lia) ltac:(unfold FseNCount.Zlength; lia) ltac:(lia)) as (_ & _ & _ & ->). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma zero_run : forall tl s m1 msvw tlw fl (x1 x25 x26 x27 : word),
5 <= tl <= 15 ->
rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
rzero_block buf msv1 s = Ok fl ->
(forall s' y1 y20 y23 y24 y26 y27 y30, fl = Brk s' -> r_nc s' = r_nc s -> rd_brk_ok C s' ->
evt psegs POST (rd_exit C s' m1 y1 y20 y23 y24 y26 y27 y30)) ->
(forall s' y1 y23 y26 y27, fl = Cont s' -> r_nc s' = r_nc s -> evt psegs POST (rd_cnt C s' m1 y1 y23 y26 y27)) ->
evt psegs POST (rd_lst C 0x13f88 m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_threshold s))
(Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s)))
x25 x26 x27 (Z_to_bv 64 (r_nbBits s))).
Proof.
intros tl s m1 msvw tlw fl x1 x25 x26 x27 Htl INV HC HP HB32 RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
unfold rzero_block in RR. rewrite (repeats_of_ctzv _ Rbs) in RR. cbn [bind] in RR.
destruct (rep_loop buf (S (Z.to_nat (FseNCount.Zlength buf))) s (ctzv (r_bitStream s) / 2)) as [[s1 rep1]| | |] eqn:RLP;
cbn [bind] in RR; try discriminate RR.
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))))) as MI.
eapply zero_ctz1; [exact Rbs| exact MI|]. intros y27.
Local Ltac2 Set LiaHints.tbl := fun () => "00?0>15346620246.3919612831529.3919615387047.5324439825071.3924818253387.3934108802820.393469311006.53 3738606783.39 38994879804.3942546463553.5351208876684.3956355263262.3962943365376.3965711610522.537406823177.53 00000>00?00@00I00J00W00X00]00m01E01O01T01\01m01nS4HB323Lnc3RbcFFS3Lnc3RbsFS3Lnc3Rip3RcnFS3LncS3Rcn3Lnc2HH3HM0S4Rthr4Rrem5Rrem23Lnc2E2S3Lnc4Rip4S3LncS3Lnc2HHS3Lnc5Erep15Hrep1F".
eapply (zero_rep _ s _ s1 rep1 m1 msvw tlw 0x13fb0); try exact RLP; try exact INV; try lia; try reflexivity.
{ unfold FseNCount.Zlength. change (2^30) with 1073741824. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
intros z1 z27 Hbs1 Hip0 Hip4 Hbc1 Hcn1 Erep1 Hrep1 (E1 & E2 & E3 & E4 & E5).
rewrite <- E2, <- E3, <- E4.
eapply (zero_tail s1 m1 msvw tlw fl); try eassumption; try lia.
- rewrite E1. exact INV.
- cbv zeta. rewrite <- Erep1. exact RR.
- intros s' y1 y20 y23 y24 y26 y27' y30 EF EN BK. apply KB; [exact EF| rewrite EN; exact E1| exact BK].
- intros s' y1 y23 y26 y27' EF EN. apply KC; [exact EF| rewrite EN; exact E1].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Zero.
