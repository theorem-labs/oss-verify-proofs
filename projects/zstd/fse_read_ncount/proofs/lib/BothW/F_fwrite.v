(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen Stdio_iface StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import MonadF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
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
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma bv_eqb_refl' : forall (x : word), bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
End CANSEC1.
Ltac if_lit :=
lazymatch goal with
| |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
Section CANSEC2. Context {rc : runConstT}.
Section WithTowrite.
Hypothesis TW : towrite_stmt.
#[using="TW"] Lemma fwx_nofit0 : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wpos wbase wfn bufp fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
rw_cells bsegs m Fp (file_cells flags 0 wpos wbase wfn bufp 0 fd mode lbf tail) ->
Z.land (bv_unsigned flags) 8 = 0 ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < bufp < 2^63) -> (0 < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv bsegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 ->
evtF bsegs RNG (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' (Z_to_bv 64 wfn) t2' s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 wfn) fc None m' (seg_rom bsegs)
/\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' Fp (file_cells flags bufp bufp bufp wfn bufp 0 fd mode' lbf tail))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8f0c0) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros FC FL8 -> -> -> BUFP L SR WFN WFE ST LO LO0 MI Fp0 SEPF RSTK RFP.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size file_cells csize Nat.add length] in BF.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "01E0?11912744615.76 12367362435.76 12367362435.97 12479474034.89 13021749692.76 15045097248.69 1527479463.74  16631425162.89 17646078182.68 17776320428.75 17776320430.97 18519693520.89 19049469500.76 19882575240.98 20401687768.74 20401687768.76 20401687768.77 21729101182.76 21918414723.76 21918414723.98 22700267513.90 23429214083.10224630998586.74 25314760359.76 25878270252.75 25878270255.96 26938711784.89 27025699012.3  27027730801.89 31081687356.77 31926340733.88 32651489978.76 33039531175.77 33680001082.77 36115622446.97 36115622447.76 36166524798.76 36425780322.89 36993589379.77 36993589379.98 37107179452.76 37151080034.89 39400444670.74 3945979267.76  3945979267.97  39496117886.69 3971437694.76  41809558659.74 41809558659.96 43059578431.66 43060403331.77 43060403331.98 43987951406.97 43987951407.76 44149825348.69 45221239098.76 45659830526.77 46602213840.89 49345641752.88 51147908213.89 51481786499.76 51481786499.97 53085287934.76 53767577772.75 53767577775.96 55509061630.77 56228262055.76 563227834.76   57745675194.76 58817367048.79 58819464192.10059308587409.4  60025031335.77 61917199020.75 61917199023.96 63235321900.95 63235321901.73 63694018620.77 67128048304.89 67800801447.76 7010956092.74  8356584753.89  8583720762.77  8929209696.89  985337532.76   00000400800<00L00S00W00[00c00g00n01501;01B01F01M01T01[01k01o02302902=02E02I02P02W02X02`02h02o03803@03D03L03S03Z03j04104504904@04A04Q04U04Y04b05205605:05A05E05I05P05W05`05h06806@06D06P06T06X06h06o07607F07J07R07Z07^07b07h07l08308:08A08H08O08X08\08c08g08o09309:S2BFS2BFS2BFS3WFN2LO4SEPF2BFS2BF2HBS2BFS2BFS3WFN2BFS2BFS2LO2BFS2LO2BFS1L2BFS2BF2HBS2BFS2LO2BFS2LO2BFS2LO2BFS3WFN2LO4SEPF2BFS2BFS2BFS2BF1HS2BFS3RSP2BFS2BFS2LO2BFS2LO2BFFS3Fp02BFS3Fp02BFS2BF2HBS4SEPF2BFS3RSP2BFS2BFS3RSP2BFS2LO2BFS2LO2BFS3WFN2LO4SEPF2BFS2LO2BFS2BFS2BFS2BF2HBFS3WFN2LO4SEPF2BFS2BFS2BFS4BUFP2BFS3WFN2LO4SEPF2BFS2BFS2BFS2LO2BFS2BFS2BFS2LO2BFS2LO2BFS4BUFP2BFS3RSP2BFS3WFN2LO4SEPF2BFS3WFN2BFS2BFS3WFN3WFE2BFS2BFS2BFS3WFN2LO4SEPF2BFS2LO2BFS2LO2BFS3WFN2LO4SEPF2BFS2BFS3RSP2BFS3RSP2BFS2BFS2BFS1L2HrS2BFS2LO2BFS2LO2BFS2LO2BFS2LO2BFS2BF2HBS4BUFP2BFS2BFS2BF2HBS2BFS3RSP2BFS2BFS2BF2HB".
carve_frame 64%nat ST.
do 13 step.
if_lit.
step. step.
eapply evtF_cut.
{ eapply (TW RNG _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (buf := bufp) (bufsize := 0);
[ rewrite unsigned_lit by (clear - BF Fp0; lia); exact FC | exact FL8 | lia | lia | lia | exact MI | rewrite unsigned_lit by (clear - BF Fp0; lia); exact RFP ]. }
cbv beta. intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode' & m1 & -> & MU1 & WM1 & MI1 & FC1).
rewrite unsigned_lit in MU1, FC1 by lia.
change (ret_pc (Z_to_bv 64 0x8f17c)) with (ret_pc (Z_to_bv 64 0x8f17c)).
rewrite (ret_pc_even 0x8f17c) by (cbn; lia).
transport_after_call bsegs m0 m1 MU1 WM1.
unfold file_cells in FC1.
step. if_lit.
do 5 step.
if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?land_W64, ?Z.mod_small in Hr by lia. clear - Hr L. lia. }
do 13 step.
rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
release_frame FR ST (bv_unsigned sp).
apply evtF_done. do 12 eexists. exists m1.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
unfold file_cells. rewrite ?Z.add_0_r in FC1. exact FC1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithTowrite.
#[using="Type"] Lemma zb_length' : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
#[using="Type"] Lemma land8_of_land40 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof.
intros f H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 3) as [->|NE].
- pose proof (f_equal (fun z => Z.testbit z 3) H) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
change (Z.testbit 8 3) with true. change (Z.testbit 40 3) with true in T. exact T.
- change 8 with (2^3). Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784496489.665600237222.7000001007SS2NE1e".
rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 3 i); [lia|]. apply Bool.andb_false_r.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Theorem fwrite_diag_proof {St : Type} : @fwrite_diag_stmt St.
Proof.
unfold fwrite_diag_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SEPS1 SEPS2 SSP MI RSTK RIMG RSRC SP47 S47.
destruct W0 as (flags & mode & e & wend & tail & FC & FL40 & WEND & HE).
pose proof (land8_of_land40 _ FL40) as FL8.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length' in BS.
assert (LSB : length (zb s) = length s) by apply zb_length'.
set (S := bv_unsigned a0) in *.
assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
unfold FWRITE_DEPTH, GLOBALS_TOP in *. unfold zlength in *.
change bsegs with bsegs in *.
destruct SSP as [GOT GUARD]. change bsegs with bsegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
unfold stderr_fwrite. unfold zlength.
Local Ltac2 Set LiaHints.tbl := fun () => "02O0?1020717701.15  10964462801.15 11041912942.83 11903774446.84 11912744615.83 12049713765.12 12049713765.13 12367362435.12512367362435.83 12537225902.15 12539062667.12 13021749692.83 15047393154.15 15241746926.84 1527479463.81  16075456879.2  16075686255.12 17461567149.9  17646078182.74 17776320428.12217776320431.82 18612176510.84 18848698606.81 19049469500.84 2003044974.83  20401687768.81 20401687768.83 20401687768.84 20493199470.83 21234881815.11 21234881815.12 2143598318.81  21918414723.12321918414723.83 22700267513.91 23758422989.16 24630998586.81 24925249977.4  25069813135.5  25314760359.84 25878270241.12525878270254.83 26389836210.15 29287675159.11 29430403662.11 29430403662.12 30987184534.5  31081687356.84 32651489978.83 32780499404.16 33039531175.84 33580864366.83 33680001082.84 33866269080.16 33868106429.12 33868106429.13 33919554158.83 34466804606.84 35007132596.15 36115622433.12536115622446.83 3640025710.83  36423785506.11636784519921.0  36993589379.12636993589379.84 37086311785.15 37107179452.83 3945979267.126 3945979267.83  40069102958.83 40408656490.15 40821660493.15 41072247790.84 41269076427.11641538052883.95 41809558659.12541809558659.81 42312801371.2  42744733806.83 42799229438.83 43059266230.72 43060403331.12743060403331.84 43344500412.3  43509785545.95 43511861488.73 43511861488.74 43987951392.12643987951406.83 44507898553.4  45221239098.84 45455091219.95 45461361962.73 45461361962.74 46982844833.0  47785557246.83 48450343931.11 48450343931.12 48490912238.84 48557425064.15 49343544638.11549978085870.84 51050267440.11651481786499.12651481786499.84 52539131753.15 53415683838.83 53516912528.11553731901390.11 53767577761.12553767577775.82 55067441390.84 56170202939.73 56170202939.74 56184910850.95 56228262055.83 563227834.83   56334502338.70 56453571879.12 56912526318.84 5723247861.12  5723247861.13  57607666860.11 57607666860.12 57622410744.7  57745675194.83 58807254914.5  60025031335.84 60385159294.84 60425195980.16 60427033321.12 60427033321.13 61396519294.81 61917199022.12461917199023.82 62473508590.81 63235321900.80 63235321902.12463248046318.84 63694018620.84 64303045347.11 64303045347.12 64305402310.15 65782973294.83 67564779019.4  67625520844.16 67800801447.83 67843257763.95 68278643190.11 7010956092.81  7237633976.11  7237633976.12  7618315246.84  7783944110.15  7837651876.15  8583720762.84  985337532.83   9895807037.15  00000500B00J00R00W00X00Y00^00c00d00e00i00j01201701;01?01L01Q01Y01a02302;02?02G02K02O02S02[02\02]02e02j02o03603703=03B03J03O03W03_03d03e03j03o04;04?04E04F04K04S04Y04Z04[04\04d05605705?05G05O05W05X05]05b05c05g05l06106906?06D06L06Q06V06[06`06d06l07>07F07K07P07T07Y07Z07[07c07k08008608;08<08=08>08P08U08Z08b08c08h09009509:09?09@09R09W09X09`09h0:00:10:20:70:<0:B0:J0:K0:S0:T0:U0:V0:W0:a0:g0:o0;40;F0;G0;H0;I0;[0;c0;k0<30<;0<C0<K0<O0<V0<]0<e0<m0=20=30=80==0=A0=E0=I0=M0=U0=V0=W0=]0=a0=fS3GLOS5SEPS15SEPS2S2LO3GLOS2LO3GLOS3LSBFFS3LSBS3LSBSSS2HBSS2LO3GLOS3LSBS2LSS2LSS5SEPS15SEPS2S3LSBS2LO3LSBS2LO3LSBS2LO3GLO5SEPS13LSBS2LO3GLOS2HBS2LO3GLOS2LOS2LOS2LOS2LO3GLOSSS2LO3GLOS3LSBS3LSBS3LSB1HFS4SP47S3GLOS2LO3GLOS3LSBS2LO3LSBS2LO3LSBS3GLOSS3GLOS3GLOS2LO3GLO3RSPS2HBS4SP47FS3LSBS2LO3GLOS4SP47FFFS2LO3GLOS2LO3GLO5SEPS13LSBSS2LO3LSBS2LO3LSBS2LO3GLOS2LO3LSBSS3LSBS3LSBSS2HBS3LSBS3LSBS2LO3GLOS4SP47S3S47S2LO3GLOS3LSBS3LSBS3LSBS3LSBS2LSS2LO3GLOS2LO3GLO5SEPS13LSBS2LO3LSBS3LSBS3LSBS2LOS3LSBSSS2LO3LSBS2LO3LSBS3GLOS4SP47S3LSBSSSS2LO3GLO5SEPS13LSBS3GLOS3GLOS2LO3GLOSS3LSBS2LO3GLOS3LSBS3LSBS3LSBSS2LO3GLO5SEPS13LSBS3LSBSS2LO3LSBS2LO3LSBS2LO3GLOSSS3LSBS3LSBS4SP47S2LS3LSBSS2LO3GLOFFSSS1H2LO3GLOS4SP47S2LO3GLOS3LSBS2LO3GLO5SEPS13LSBFFFS2LO3GLO5SEPS13LSBS2LO3LSBS2LO3LSBS2LO3GLOS2LO3LSBS2LO3LSBS2LO3GLOS2HBS2LS2BSS2LS2BSS2BS3RA0S2LO3GLOS3GLOFS3LSBS3LSBS2LSS2HBS2LOS2LOS2LO3GLOSSS4SP47S2HBS3S47".
replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
unfold file_cells in FC.
rewrite EA0.
eapply implAM_evt. 2:{ intros ms' H; exact H. } cbv beta.
carve_frame 64%nat ST.
do 8 step. do 3 step. step. step. step. if_lit.
step. step. step.
rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite Z.mul_1_l.
assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
eapply (evtF_cut bsegs RNG (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 0x8f280) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
(Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length s)))
(Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
(Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom bsegs)
/\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1
/\ stk bsegs m1 lo (bv_unsigned sp + -64)
/\ rw_cells bsegs m1 RSTDERR (file_cells flags 0x5f5bd8 0x5f5bd8 0x5f5bd8 F_STDIO_WRITE 0x5f5bd8 0 2 mode1 0xffffffff tail))).
{ destruct WEND as [-> | [-> ->]].
- eapply evtF_mono.
{ eapply (fwx_nofit0 TW RNG) with (lo := lo); [exact FC | exact FL8 | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
first [rewrite ESP; exact ST | exact MI | rewrite ESP; solve_rng | eapply rng_sub; [exact RIMG| cbn; lia| cbn; lia] ]. }
cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
rewrite ESP in MU1, ST1.
do 12 eexists. exists m1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact FC1.
- eapply evtF_mono.
{ eapply (fwx_nofit RNG) with (lo := lo); [exact FC | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
first [rewrite ESP; exact ST | exact MI | rewrite ESP; solve_rng | eapply rng_sub; [exact RIMG| cbn; lia| cbn; lia] ]. }
cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
rewrite ESP in MU1, ST1.
do 11 eexists. exists mode, m1. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
eapply (rw_cells_transport bsegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
assert (SRC1 : bytes_at bsegs m1 S (to_bytes s)).
{ eapply (bytes_at_transport bsegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
assert (GOT1 : rw_cells bsegs m1 632224 [C8 (Z_to_bv 64 6247696)]).
{ eapply (rw_cells_transport bsegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
assert (GUARD1 : rw_cells bsegs m1 6247696 [C8 canary]).
{ eapply (rw_cells_transport bsegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
assert (FC1' : rw_cells bsegs m1 RSTDERR (file_cells flags 0x5f5bd8 (0x5f5bd8 + zlength (@nil Z)) 0x5f5bd8 F_STDIO_WRITE 0x5f5bd8 0 2 mode1 0xffffffff tail)).
{ unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC1. }
clear FC1 GOT GUARD SRC.
apply evtF_done.
eapply implAM_post_evt''.
{ eapply (stdio_write_spec (St:=St) RNG) with (lo := lo) (S := S) (canary := canary) (buf := []) (fd := 2);
[ exact FC1'
| apply bytes_at_nil; clear; lia
| exact SRC1
| reflexivity | reflexivity | reflexivity
| right; reflexivity
| rewrite ESP; exact ST1 | rewrite ESP; unfold STDIO_WRITE_DEPTH; clear - LO; lia | exact GLO
| split; [exact GOT1 | exact GUARD1] | exact MI1
| try (rewrite ?ESP; unfold got_ssp, ssp_guard, zlength; cbn [length Z.of_nat]; clear - LO GLO RA0 BS LS SEPS1 SEPS2 SP47 S47 RSP; lia) .. ];
first [ rewrite ESP; solve_rng | exact RIMG | unfold zlength; exact RSRC
| eapply rng_sub; [exact RIMG| cbn; lia| unfold zlength; cbn; lia] ]. }
cbv beta. intros [] st2 ms2 PO2.
destruct PO2 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
rewrite ESP in MU2, ST2. unfold STDIO_WRITE_DEPTH in MU2.
rewrite (ret_pc_even 0x8f280) by (cbn; lia).
assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (rw_cells_transport bsegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
eapply (rw_cells_transport bsegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
clear FR. unfold file_cells in FC2.
step. step. unfold zlength. rewrite (bv_eqb_refl' (Z_to_bv 64 (Z.of_nat (length s)))). cbv iota.
do 4 step.
do 9 step.
release_frame FR2 ST2 (bv_unsigned sp).
apply evtF_done. unfold fwrite_diag_post.
rewrite v_sltiu_b2z. replace (bv_unsigned (Z_to_bv 64 (Z.of_nat (length s))) <? bv_wrap 64 1) with false
by (symmetry; apply Z.ltb_ge; rewrite unsigned_lit by (clear -LS; lia); change (bv_wrap 64 1) with 1; clear -LS; lia).
cbn [Z.b2z]. rewrite (unsigned_lit 0) by lia.
replace (Z.land (bv_unsigned (Z_to_bv 64 (0 + -1))) 1) with 1 by (vm_compute; reflexivity).
do 14 eexists. exists m2.
split; [reflexivity|].
split. { apply (munch_trans _ m m0 m2); [| apply (munch_trans _ m0 m1 m2)].
- eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia. }
split. { eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]. }
split; [exact MI2|]. split; [exact ST2|].
split.
{ exists flags, mode1, 0x5f5bd8, 0x5f5bd8, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
split; [exact SSP2 | reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
