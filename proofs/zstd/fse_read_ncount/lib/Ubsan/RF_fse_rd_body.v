(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RF_fse_rd_mem RF_fse_rd_loop RF_fse_rd_hdr.
Import ListNotations.
Open Scope Z_scope.
Section Body.
Variable C : rdctx.
Hypothesis OK : rd_ok C.
Notation buf := (c_buf C).
Notation msv1 := (c_msv0 C + 1).
Notation BUF := (c_BUF C).
Notation NC := (c_NC C).
#[using="OK"] Theorem rd_body8 : forall rt msv tlr n (tl0 : word) (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
u8arr usegs (c_m C) NC (u16s (map (Z_to_bv 64) (c_rt0 C))) ->
rw_cells usegs (c_m C) (c_MSVP C) [C4 (Z_to_bv 64 (c_msv0 C))] ->
rw_cells usegs (c_m C) (c_TLP C) [C4 tl0] ->
bytes_at usegs (c_m C) BUF (map (Z_to_bv 8) buf) ->
stk usegs (c_m C) (c_lo C) (c_SP C) -> mem_inv usegs (c_m C) ->
read_ncount_body8 buf msv1 (c_rt0 C) = Ok (rt, msv, tlr, n) ->
evt usegs (rd_body_post C rt msv tlr n)
(MS (mkR (c_ra C) (Z_to_bv 64 (c_SP C)) (c_gp C) (c_tp C) t0 t1 t2 (c_s0 C) (c_s1 C)
(Z_to_bv 64 NC) (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 BUF) (Z_to_bv 64 (zlen buf)) a5 a6 a7
(c_s2 C) (c_s3 C) (c_s4 C) (c_s5 C) (c_s6 C) (c_s7 C) (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
(c_F C) (Z_to_bv 64 0x13f40) (c_fc C) None (c_m C) (seg_rom usegs)).
Proof.
intros rt msv tlr n tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI RB.
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & (HNP & HNA) & (HVP & HVA) & (HTP & HTA) & HBP).
unfold RD_STACK in *.
destruct (read_body8_inv buf msv1 (c_rt0 C) rt msv tlr n (proj1 HH) RB) as (_ & HX & -> & sF & RL & F1 & F2 & F3 & -> & -> & ->).
Local Ltac2 Set LiaHints.tbl := fun () => "01O0>1010228364.72 11670174649.7111801586693.8712589306748.6814013085244.7214198392384.7114487398976.691490495417.72 15299202042.6215523843769.7216077671799.6416125039003.8716637712524.7217286780044.7217471526139.8617471526139.871802836281.71 18499706688.7119107270796.7119618399906.761974571836.69 20038558908.7120309704588.7120924707980.7221155567546.7122163107130.7224630998586.7224858468259.6025703506617.7226049497404.7228140551564.7028373541751.8329803348876.7130138556224.7130196181434.7130572420492.7131721149295.8632070795196.7132651489978.7132914133132.6933376210745.7033680001082.7135091177529.7135210019136.7135214167690.7435418171532.7135814319382.8237211491939.7637281413696.7238098496572.7239281079872.7240030907712.7040285629760.7144109304508.7145221239098.7246232973498.7146698159680.7247101426873.7147171185465.7147668679400.6848206670400.7148392300352.7148768966412.5148820458937.7250134779708.7150553141825.7150877661611.6452567164907.6952567164907.7052567164907.7152567164907.7254261855034.695494439228.72 55585846116.6456145720764.70563227834.71  56484770361.7157020425481.6857745675194.705815946124.71 59314923118.6461944904708.8462175402556.7162900777713.8863331384996.6765805175866.7265835966665.8366500674351.6466664437305.7166772733324.7167273256512.7268186327228.717929436345.69 8002142652.71 8583720762.71 00000500M00N00Z00b00g00l01D01I01a01i02502:02?02[03303K03P03U03^03f03n04304804A04J04S04[05305;05@05P05U05Z05c05h06?06G06P06U06m07607N07S07T07Y07a07f07k08308808=08B08J08S08\08a09909Q09e09j09o0:80:P0:X0:a0:j0:o0;40;90;>0;G0;O0;X0;`0;i0<A0<I0<R0<W0<a0<i0=10=C0=S0=\0=h0>10>I0>N0>S0>[0?30?;0?DS3LWSS2LO3SBS3LWS3STS3SMS3SNSFS3HM03LWS2LAS3LWS2HBS3LWSS3LWSS2LO3SBS3LWS3STS3SMS3SNSS3LWSS2LO3SBS3LWS3STS3SMS3SNSS2HH3LWSS3HM03LWS2LAS3LWSS3LWSS3HM03HM13SNT3LWS2LA3SNM3SNSS3HM03HM13SNB3LWS3LBS2LAS2LO3SBS3LWS3STS3SMS3SNSS3LWSS3LWSS3HM03LWSS3LWS2HBS3LWS2HBS3LWSS3LWSS3RSP3LWSS3RSP3LWSS3RSP3LWSS2LO3LWSS2LO3SBS3LWS3STS3SMS3SNSS3LWS2HBS3LWSS3HM03HM13LWS2LAS3LWSS3LWSS3RSP3LWSS3LWSS3HM03HM12LO3SNS3LWS2LAS3LWS2HBS3RSP3LWSS3LWSS2LO3SBS3LWS3STS3SMS3SNSS3RSP3LWSS2LO3SBS3LWS3STS3SMS3SNSS3LWSFS3LWSS3LWS2LAS3LWSS3LWSS3LWS2HBS3LWSS3LWSS3LWSS3LWS2HBS3RSP3LWSS3RSP3LWSS3LWSS2LO3SBS3LWS3STS3SMS3SNSS2LO3SBS3LWS3STS3SMS3SNSS3HM03HM13HN13LWS2LAS3LWSS3LWSS3HM03HM1S2LO3SBS3LWS3STS3SMS3SNSS3LWS2HBS3HM03LWSS3HM03LWSS3LWSS3LWSS3LWSS3LWSS3RSP3LWSS3LWS2HBS3HM03LWSS3LWS2HBS3RSP3LWSS2LO3SBS3LWS3STS3SMS3SNSS3LWS2LAS3RSP3LWSS3LWSS2HH3LWS1KS3LWS2LAS3LWS2HBS3HM03HM13LWS2LA1HS3HM03HM13LWS2LAS3RSP3LWSS3HM03LWS2LAS3HM03LWSS2LO3SBS3LWS3STS3SMS3SNSS3LWSS3LWSS3LWS2HBS2LO3SBS3LWS3STS3SMS3SNSS3LWS2HBS3RSP3LWS".
destruct (rd_s0_inv buf msv1 (c_rt0 C) (buf_all_bytes C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
pose proof (munch_refl (rd_W C) (c_m C)) as MU. pose proof (wmono_refl usegs (c_m C)) as WM. unfold rd_W, RD_STACK in MU.
assert (LWS : length (map (Z_to_bv 64) (c_rt0 C)) = length (c_rt0 C)) by apply length_map.
assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
remember (c_m C) as m eqn:Em.
carve_frame 128%nat ST.
do 14 zstep.
zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
do 6 zstep.
zstep. if_cases K1; zify_cond K1;
[exfalso; rewrite (proj2 (Z.ltb_lt 0 BUF) ltac:(lia)), (proj2 (Z.ltb_ge (BUF + zlen buf) 1) ltac:(lia)) in K1; vm_compute in K1; discriminate K1|].
zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
assert (LV3 : Z.land (c_MSVP C) 3 = c_MSVP C mod 4) by (change 3 with (Z.ones 2); apply Z.land_ones; lia).
zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
do 3 zstep.
if_cases K; zify_cond K; [| exfalso; lia].
zstep. rewrite (sx32_small (c_msv0 C)) by lia.
zstep. rewrite (swrap32_small msv1) by lia.
zstep. zstep. rewrite (shl32_shr31 msv1) by lia.
zstep. zstep. zstep.
set (bsA := u16s (map (Z_to_bv 64) (c_rt0 C))) in *.
assert (LA : length bsA = (2 * length (c_rt0 C))%nat) by (subst bsA; rewrite u16s_length, LWS; reflexivity).
set (n1 := Z.to_nat (2 * msv1)).
pose proof (rw_cells_of_u8arr _ _ _ _ ARR) as RA. clear ARR.
pose proof (rw_cells_split_CB usegs _ NC [] _ bsA [] [n1; (length bsA - n1)%nat] RA ltac:(cbn [sum_nat]; lia)) as RS.
cbn [app mk_CB_cells] in RS. clear RA.
change [CB n1 (firstn n1 bsA); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]
with ([CB n1 (firstn n1 bsA)] ++ [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) in RS.
apply rd_rw_cells_app in RS. destruct RS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
call (rd_memset_specZ NC (2 * msv1) 0); [exact R1 | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
assert (ARR : u8arr usegs x13 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (c_rt0 C))))).
{ pose proof (proj2 (rd_rw_cells_app usegs x13 NC [CB n1 (repeat (Z_to_bv 8 0) n1)]
[CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) (conj POST R2)) as RJ.
pose proof (rw_cells_merge usegs x13 NC [] [CB n1 (repeat (Z_to_bv 8 0) n1); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))] [] RJ) as RM. cbn [app] in RM.
apply u8arr_of_rw_cells in RM. cbn [cells_bytes cbytes app] in RM. rewrite app_nil_r in RM.
rewrite firstn_all2 in RM by (rewrite length_skipn; lia).
replace n1 with (2 * Z.to_nat msv1)%nat in RM by (subst n1; lia).
subst bsA. rewrite u16s_zero_prefix in RM by lia. exact RM. }
clear POST R2.
zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
subst m.
eapply (rd_header C OK x13 tl0 sF); try eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Body.
