(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen Stdio_iface StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import MonadF.
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
rw_cells asegs m Fp (file_cells flags 0 wpos wbase wfn bufp 0 fd mode lbf tail) ->
Z.land (bv_unsigned flags) 8 = 0 ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < bufp < 2^63) -> (0 < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 ->
evtF asegs RNG (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' (Z_to_bv 64 wfn) t2' s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 wfn) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' Fp (file_cells flags bufp bufp bufp wfn bufp 0 fd mode' lbf tail))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8ef30) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FC FL8 -> -> -> BUFP L SR WFN WFE ST LO LO0 MI Fp0 SEPF RSTK RFP.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size file_cells csize Nat.add length] in BF.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "01E0?11912744615.76 12367362435.76 12367362435.97 12479474034.89 13021749692.76 15045097248.69 1527479463.74  17646078182.68 17776320428.75 17776320430.97 18519693520.89 19049469500.76 19882575240.98 20401687768.74 20401687768.76 20401687768.77 21729101182.76 21918414723.76 21918414723.98 22700267513.90 23429214083.10224630998586.74 25314760359.76 25878270252.75 25878270255.96 26938711784.89 27025699012.3  27027730801.89 31081687356.77 31926340733.88 32651489978.76 33039531175.77 33680001082.77 36115622446.97 36115622447.76 36166524798.76 36425780322.89 36993589379.77 36993589379.98 37107179452.76 37151080034.89 39400444670.74 3945979267.76  3945979267.97  39496117886.69 3971437694.76  41809558659.74 41809558659.96 43059578431.66 43060403331.77 43060403331.98 43987951406.97 43987951407.76 44149825348.69 45221239098.76 45659830526.77 46602213840.89 49345641752.88 51147908213.89 51481786499.76 51481786499.97 51640933681.89 53085287934.76 53767577772.75 53767577775.96 55509061630.77 5567388554.89  56228262055.76 563227834.76   57745675194.76 58817367048.79 58819464192.10059308587409.4  60025031335.77 61917199020.75 61917199023.96 63235321900.95 63235321901.73 63694018620.77 67128048304.89 67800801447.76 7010956092.74  8583720762.77  8929209696.89  985337532.76   00000400800<00L00S00W00[00_00f00m01301:01>01E01L01S01c01g01k02102502=02A02H02O02P02X02`02g03003803<03D03K03R03b03i03m04104804904I04M04Q04Z04j04n05205905=05A05H05O05X05`06006806<06H06L06P06T06d06k07207B07J07N07V07^07b07f07l08008708>08E08L08S08\08`08g08o09309:S2BFS2BFS2BFS3WFN2LO4SEPF2BFS2BF2HBS2BFS2BFS2BFS2LO2BFS2LO2BFS1L2BFS2BF2HBS2BFS2LO2BFS2LO2BFS2LO2BFS3WFN2LO4SEPF2BFS2BFS2BFS2BF1HS2BFS3RSP2BFS2BFS2LO2BFS2LO2BFFS3Fp02BFS3Fp02BFS2BF2HBS4SEPF2BFS3RSP2BFS2BFS3RSP2BFS2LO2BFS2LO2BFS3WFN2LO4SEPF2BFS2LO2BFS2BFS2BFS2BF2HBFS3WFN2LO4SEPF2BFS2BFS2BFS4BUFP2BFS3WFN2LO4SEPF2BFS2BFS2BFS2LO2BFS2BFS2BFS2LO2BFS2LO2BFS4BUFP2BFS3RSP2BFS3WFN2LO4SEPF2BFS3WFN2BFS2BFS3WFN3WFE2BFS2BFS2BFS2BFS3WFN2LO4SEPF2BFS2LO2BFS2LO2BFS3WFN2LO4SEPF2BFS3WFN2BFS2BFS3RSP2BFS3RSP2BFS2BFS2BFS1L2HrS2BFS2LO2BFS2LO2BFS2LO2BFS2LO2BFS2BF2HBS4BUFP2BFS2BFS2BF2HBS3RSP2BFS2BFS2BF2HB".
carve_frame 64%nat ST.
do 13 step.
if_lit.
step. step.
eapply evtF_cut.
{ eapply (TW RNG _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (buf := bufp) (bufsize := 0);
[ rewrite unsigned_lit by (clear - BF Fp0; lia); exact FC | exact FL8 | lia | lia | lia | exact MI | rewrite unsigned_lit by (clear - BF Fp0; lia); exact RFP ]. }
cbv beta. intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode' & m1 & -> & MU1 & WM1 & MI1 & FC1).
rewrite unsigned_lit in MU1, FC1 by lia.
change (ret_pc (Z_to_bv 64 0x8efec)) with (ret_pc (Z_to_bv 64 0x8efec)).
rewrite (ret_pc_even 0x8efec) by (cbn; lia).
transport_after_call asegs m0 m1 MU1 WM1.
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
change asegs with asegs in *.
destruct SSP as [GOT GUARD]. change asegs with asegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
unfold stderr_fwrite. unfold zlength.
Local Ltac2 Set LiaHints.tbl := fun () => "02O0?100583406.84   1020717701.15  10964462801.15 11912744615.83 12049713765.12 12049713765.13 12367362435.12512367362435.83 13021749692.83 15047393154.15 1527479463.81  15617080686.83 15788351726.81 16075456879.2  16075686255.12 17461567149.9  17646078182.74 17776320428.12217776320431.82 18263559150.84 18612176510.84 18909637614.84 19049469500.84 20313996398.83 20401687768.81 20401687768.83 20401687768.84 20595493486.83 21585288942.84 21918414723.12321918414723.83 22364848944.11622700267513.91 23758422989.16 24630998586.81 25069813135.5  25314760359.84 25842017996.16 25878270241.12525878270254.83 25886974446.84 27453056622.83 27518329099.4  29278640489.15 29430403662.11 29430403662.12 29541009769.15 30186197195.11630772921545.95 30783404016.73 30783404016.74 30987184534.5  31081687356.84 32651489978.83 32780499404.16 33039531175.84 33680001082.84 33866269080.16 33868106429.12 33868106429.13 34466804606.84 35022110958.81 35831884529.0  36115622433.12536115622446.83 36423785506.11636993589379.12636993589379.84 37107179452.83 37320641714.15 3734855790.83  3855268788.15  3945979267.126 3945979267.83  40408656490.15 40821660493.15 41025917715.95 41032163370.73 41032163370.74 41365689036.16 41367525865.12 41367525865.13 41809558659.12541809558659.81 41991077614.84 42312801371.2  42553980846.15 42799229438.83 43059266230.72 43060403331.12743060403331.84 43344500412.3  43893807606.11 43987951392.12643987951406.83 45099762158.84 45221239098.84 45404150692.15 46030209441.0  46270630510.83 46543646636.11 46543646636.12 46785618030.83 47785557246.83 48557425064.15 49154229527.11 49343544638.1155067561657.4   50693720814.84 50981925049.4  51481786499.12651481786499.84 53415683838.83 53516912528.11553767577761.12553767577775.82 56170202939.73 56170202939.74 56184910850.95 56228262055.83 563227834.83   56334502338.70 5723247861.12  5723247861.13  57622410744.7  57745675194.83 57839090926.81 58549673379.95 58669809006.83 58807254914.5  598607867.11   598607867.12   60025031335.84 60385159294.84 61396519294.81 61674577390.84 61917199022.12461917199023.82 62844815310.11 63235321900.80 63235321902.12463694018620.84 64303045347.11 64303045347.12 64305402310.15 64519296279.11 64519296279.12 6746606355.95  67800801447.83 7010956092.81  7237633976.11  7237633976.12  7590245671.12  8277095563.12  8279457710.15  8583720762.84  9333008750.83  985337532.83   9895807037.15  00000800=00J00O00P00Q00V00[00_00`00e00m01501901=01J01O01W01_01g02902A02E02M02Q02U02Y02a02i02n03303803?03@03F03N03S03T03\03d03l04404904:04?04D04E04J04O04P04Q04]04a04g04h04m05305405505605H05P05Q05Y05a05i05n06306706<06D06E06J06O06U06Z06_06`06a06b06c06d06i06n07607:07;07M07U07Z07_07c07g07o08708?08E08F08G08O08P08Q08Y08k08l08m09209709?09D09I09N09`09e09m0:50:60:70:<0:A0:G0:O0:P0:Q0:[0:a0:i0:n0;60;>0;C0;H0;M0;_0<10<90<A0<I0<J0<R0<Z0<^0<e0<l0=40=50=60=;0=@0=D0=H0=L0=M0=N0=O0=U0=]0=a0=fS2LO3GLOS3GLOS5SEPS15SEPS2S3LSBFFS3LSBS3LSBS2HBSS3LSBS2LO3GLOS2LO3GLOS2LSS2LSS5SEPS15SEPS2S3LSBS2LO3LSBS2LO3LSBS2LO3GLOS2LO3GLO5SEPS13LSBS2LO3GLOS2HBS2LO3GLOS2LOS2LOS2LOS2LO3GLOS2LO3GLOS3LSBS3LSBS3LSBS3LSB1HFS4SP47S2LO3GLOS3LSBFS2LO3LSBS2LO3LSBS2LO3GLOS2LO3GLOS3GLOSS3GLOS3GLOSS3LSBS3LSBSSS2LO3GLO3RSPS2HBS4SP47FS3LSBS4SP47FFFS2LO3GLO5SEPS13LSBS2LO3GLOSS2LO3LSBS2LO3LSBS2LO3LSBS3LSBS3LSBS2HBS3GLOS2LO3GLOSS3LSBS3LSBS4SP47S3S47S3LSBSSFFFS3LSBS3LSBS2LO3GLOS2LSSS2LO3GLO5SEPS13LSBS2LO3LSBS3LSBS3LSBS2LOS2LSS2LO3LSBS2LO3LSBS2LO3GLOS4SP47SSS2LO3GLOSSS2LO3GLOS2LO3GLO5SEPS13LSBSSS3LSBS3GLOS2LO3GLOS3GLOS3LSBS3LSBS2LO3GLO5SEPS13LSBS3LSBS2LO3LSBS2LO3LSBSSS3LSBS3LSBS4SP47S2LS3LSBFFS1H2LO3GLOS4SP47S2LO3GLOS3LSBS2LO3GLOS2LO3GLOS3GLOS3GLOS3LSBS2LO3GLO5SEPS13LSBS2LO3GLO5SEPS13LSBS2LO3GLOS2LO3LSBS2LO3LSBSS2LO3LSBS2LO3LSBS2HBS2LS2BSS2LS2BSS2BS3RA0SSS3LSBS3LSBS2HBS2LOS2LOSSSS4SP47S2LO3GLOS2HBS3S47".
replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
rewrite EA0.
eapply implAM_evt. 2:{ intros ms' H; exact H. } cbv beta.
carve_frame 64%nat ST.
do 8 step. do 3 step. step. step. step. if_lit.
step. step. step.
rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite Z.mul_1_l.
assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
eapply (evtF_cut asegs RNG (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 0x8f0f0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
(Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length s)))
(Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
(Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono asegs m0 m1 /\ mem_inv asegs m1
/\ stk asegs m1 lo (bv_unsigned sp + -64)
/\ rw_cells asegs m1 RSTDERR (file_cells flags 0x5f5b18 0x5f5b18 0x5f5b18 F_STDIO_WRITE 0x5f5b18 0 2 mode1 0xffffffff tail))).
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
eapply (rw_cells_transport asegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
assert (SRC1 : bytes_at asegs m1 S (to_bytes s)).
{ eapply (bytes_at_transport asegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
assert (GOT1 : rw_cells asegs m1 631824 [C8 (Z_to_bv 64 6247504)]).
{ eapply (rw_cells_transport asegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
assert (GUARD1 : rw_cells asegs m1 6247504 [C8 canary]).
{ eapply (rw_cells_transport asegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
assert (FC1' : rw_cells asegs m1 RSTDERR (file_cells flags 0x5f5b18 (0x5f5b18 + zlength (@nil Z)) 0x5f5b18 F_STDIO_WRITE 0x5f5b18 0 2 mode1 0xffffffff tail)).
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
rewrite (ret_pc_even 0x8f0f0) by (cbn; lia).
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (rw_cells_transport asegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
eapply (rw_cells_transport asegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
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
{ exists flags, mode1, 0x5f5b18, 0x5f5b18, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
split; [exact SSP2 | reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
