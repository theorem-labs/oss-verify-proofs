(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen Stdio_iface StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma bv_eqb_refl' : forall (x : word), bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
Lemma impl_post_evt'' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
impl usegs (at_node usegs) t Q ms -> (forall r ms', Q r ms' -> evt usegs (Q' r) ms') ->
impl usegs (at_node usegs) t Q' ms.
Proof.
induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma implM_post_evt'' : forall {St A} (c : M St A) s Q Q' ms,
implM usegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt usegs (Q' a s') ms') ->
implM usegs c s Q' ms.
Proof.
intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt''; [exact H|].
intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.
Section WithTowrite.
Hypothesis TW : towrite_stmt.
#[using="TW"] Lemma fwx_nofit0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wpos wbase wfn bufp fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
rw_cells usegs m Fp (file_cells flags 0 wpos wbase wfn bufp 0 fd mode lbf tail) ->
Z.land (bv_unsigned flags) 8 = 0 ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < bufp < 2^63) -> (0 < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv usegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
evt usegs (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' (Z_to_bv 64 wfn) t2' s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 wfn) fc None m' (seg_rom usegs)
/\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' Fp (file_cells flags bufp bufp bufp wfn bufp 0 fd mode' lbf tail))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x170e4) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros FC FL8 -> -> -> BUFP L SR WFN WFE ST LO LO0 MI Fp0 SEPF.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size file_cells csize Nat.add length] in BF.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "0130>11912744615.7212367362435.7212367362435.9312377119857.8513021749692.7215045097248.651527479463.70 17646078182.6418519693520.8519049469500.7220401687768.7020401687768.7220401687768.7321729101182.7221918414723.7221918414723.9424630998586.7025314760359.7226304383434.8526938711784.8527025699012.3 27027730801.8531081687356.7331760275889.8532651489978.7233039531175.7333680001082.7336166524798.7236425780322.8536993589379.7336993589379.9437107179452.7237151080034.8539400444670.703945979267.72 3945979267.93 39496117886.653971437694.72 41809558659.7041809558659.9243059578431.6243060403331.7343060403331.9444149825348.6545221239098.7245659830526.7346602213840.8549345641752.8451147908213.8551481786499.7251481786499.9353085287934.7255509061630.7355512385361.8656228262055.72563227834.72  57745675194.7259308587409.4 60025031335.7363694018620.7367128048304.8567800801447.727010956092.70 8583720762.73 8929209696.85 981331806.84  985337532.72  00000400800900E00I00M00Q00U00X00\00c00j01101=01A01B01G01K01O01P01X01`01d01h01m02102602B02F02J02K02O02P02\02`02a02j03603:03;03B03F03G03P03U03a03f03g03l04004104=04I04O04S04X04]04c04g04k05105505905>05?05H05LS2BFS2BFSS2LO4SEPF2BFS2HBS2BFS2BFS2BFS1LS2HBS2LO2BFS2LO2BFS2LO2BFS2LO4SEPF2BFS2BFSS3RSPS2BFS2BFFS3Fp02BFS3Fp02BFS2HBS2BFS3RSPS2BFS3RSPS2LO4SEPF2BFS2LOS2BFSS2HBFS2LO4SEPF2BFS2BFSS4BUFP2BFS2LO4SEPF2BFS2BFSS2LO2BFS2BFSS4BUFP2BFS3RSPS2LO4SEPF2BFS3WFNSS3WFES2BFSS2LO4SEPF2BFS2LO4SEPF2BFS2BF1HS2BFS3RSPS3RSPS1L2HrS2BFS2HBS4BUFPS2BFS2HBS3RSPSS4SEPF2BFS2HB".
carve_frame 64%nat ST.
do 13 step.
if_lit.
step. step.
eapply evt_cut.
{ eapply (TW _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (buf := bufp) (bufsize := 0);
[ rewrite unsigned_lit by (clear - BF Fp0; lia); exact FC | exact FL8 | lia | lia | lia | exact MI ]. }
cbv beta. intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode' & m1 & -> & MU1 & WM1 & MI1 & FC1).
rewrite unsigned_lit in MU1, FC1 by lia.
change (ret_pc (Z_to_bv 64 0x171a0)) with (ret_pc (Z_to_bv 64 0x171a0)).
rewrite (ret_pc_even 0x171a0) by (cbn; lia).
transport_after_call usegs m0 m1 MU1 WM1.
unfold file_cells in FC1.
step. if_lit.
do 5 step.
if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?land_W64, ?Z.mod_small in Hr by lia. clear - Hr L. lia. }
do 13 step.
rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 12 eexists. exists m1.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST|].
unfold file_cells. rewrite ?Z.add_0_r in FC1. exact FC1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithTowrite.
Lemma zb_length' : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma land8_of_land40 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof.
intros f H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i 3) as [->|NE].
- pose proof (f_equal (fun z => Z.testbit z 3) H) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
change (Z.testbit 8 3) with true. change (Z.testbit 40 3) with true in T. exact T.
- change 8 with (2^3). Local Ltac2 Set LiaHints.tbl := fun () => "0020=29784496489.565600237222.6000001007SS2NE1e".
rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 3 i); [lia|]. apply Bool.andb_false_r.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Theorem fwrite_diag_proof {St : Type} : @fwrite_diag_stmt St.
Proof.
unfold fwrite_diag_stmt. intros until s. intros TW W0 SRC BYT LS -> -> -> ST LO GLO SP47 S47 SEPS1 SEPS2 SSP MI.
destruct W0 as (flags & mode & e & wend & tail & FC & FL40 & WEND & HE).
pose proof (land8_of_land40 _ FL40) as FL8.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length' in BS.
assert (LSB : length (zb s) = length s) by apply zb_length'.
set (S := bv_unsigned a0) in *.
assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
unfold FWRITE_DEPTH, GLOBALS_TOP in *. unfold zlength in *.
change usegs with usegs in *.
destruct SSP as [GOT GUARD]. change usegs with usegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
unfold stderr_fwrite. unfold zlength.
Local Ltac2 Set LiaHints.tbl := fun () => "01k0?1020717701.15  10964462801.15 11041912942.78 11912744615.78 12049713765.12 12049713765.13 12367362435.12012367362435.78 13021749692.78 13180766859.4  13270953206.11 15047393154.15 1527479463.76  15776184302.79 16075456879.2  16075686255.12 16354687726.79 17040090734.78 17461567149.9  17646078182.69 18612176510.79 19049469500.79 19666039969.0  20401687768.76 20401687768.78 20401687768.79 21656386382.11 21918414723.11821918414723.78 22700267513.86 23483264238.76 24630998586.76 24925249977.4  24997280151.11 24997280151.12 25069813135.5  25314760359.79 26757167854.79 26773522284.11 26773522284.12 27335527918.79 27839504919.11 27872294706.15 29430403662.11 29430403662.12 29717511207.12 30987184534.5  31081687356.79 32651489978.78 32800704432.11133039531175.79 33680001082.79 33885744366.76 34466804606.79 36204177774.78 3640025710.78  36423785506.11136993589379.12136993589379.79 3705199371.111 37107179452.78 37738008046.79 3945979267.121 3945979267.78  40408656490.15 40821660493.15 41072247790.79 41809558659.12041809558659.76 42799229438.78 43059266230.67 43060403331.12243060403331.79 43344500412.3  45221239098.79 46600235374.78 47178742894.78 47785557246.78 48490912238.79 48557425064.15 49343544638.11051481786499.12151481786499.79 51595499316.15 53047206446.15 53415683838.78 5363218414.79  54110201841.0  54324225646.78 55067441390.79 56228262055.78 563227834.78   56334502338.65 5723247861.12  5723247861.13  57581223022.78 57622410744.7  57745675194.78 58410567675.11 58410567675.12 58807254914.5  5977814539.12  5979651374.15  60025031335.79 60385159294.79 61118828649.15 61396519294.76 62473508590.76 63694018620.79 64055126052.15 64303045347.11 64303045347.12 64305402310.15 65782973294.78 67313011897.4  67800801447.78 7010956092.76  7237633976.11  7237633976.12  7484401769.15  8583720762.79  985337532.78   9895807037.15  00000500B00J00O00P00Q00V00[00_00d00h00i00n01601:01>01F01N01[01`01n02202302702;02?02@02E02J02M02U02[02`02a02b02j02o03703803903A03B03G03L03Q03R03^03b03h03m04204804@04N04V04^04f04k05005505905A05F05K05Q05V05^05c05h06606>06C06H06L06R06Z06b07007807907>07C07H07I07J07X07`07a07i08108608<08D08E08F08N08X08^08c08h09009109209709E09F09T09\09`09a09h09o0:70:?0:D0:I0:M0:Q0:U0:V0:\0:`0:eS3GLOS5SEPS15SEPS2S2LO3GLOS3LSBFFS3LSBS3LSBS2HBS3GLOS2LSSS3LSBS2LO3GLOS2LSS2LSS2LO3GLOS2LO3GLOS5SEPS15SEPS2S3LSBS2LO5SEPS13LSBS2HBSS2LOS2LOS2LOSS3LSBS3LSBS1HS2LO3GLOS4SP47S3GLOSSS2LO3GLOS3LSBS2LO3GLOSSS2LO3GLOSS3GLOS3GLOS3GLOSS2LO3GLO3RSPS2HBS4SP47S3LSBS3LSBS4SP47S2LO3GLOS2LO5SEPS13LSBS2LO3GLOS2LO3GLOS2LO3LSBS3LSBS3LSBS3LSBS2HBS2LO3GLOS3LSBS3LSBS4SP47S3S47S2LO3GLOS3LSBS3LSBS2LO5SEPS13LSBS2LO3LSBS3LSBS3LSBS2LOS4SP47S2LO3GLOS2LO3GLOS2LO5SEPS13LSBS2LO3GLOSS3LSBS3LSBS3LSBSSS2LO5SEPS13LSBS2LO3GLOSS2LO3GLOS2LO3GLOS3LSBS4SP47S2LS3LSBFFS2LO3GLOS1H2LO3GLOS4SP47S3GLOS3GLOS2LO3GLOSSS3LSBS2LO5SEPS13LSBSS2LO5SEPS13LSBS2LO3GLOS2HBSS2LS2BSS2LS2BSS2BS3RA0S2LO3GLOS3GLOS3LSBS2HBS2LOS2LOSS4SP47S2HBS3S47".
replace (0 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold file_cells in FC.
rewrite EA0.
eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
carve_frame 64%nat ST.
do 8 step. do 3 step. step. step. step. if_lit.
step. step. step.
rewrite (unsigned_lit (Z.of_nat (length s))) by (clear - LS; lia). rewrite Z.mul_1_l.
assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO; lia).
eapply (evt_cut usegs (fun ms' => exists (t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode1 : word) (m1 : mem),
ms' = MS (mkR (Z_to_bv 64 0x172a4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' (Z_to_bv 64 F_STDIO_WRITE) t2'
(Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length s)))
(Z_to_bv 64 RSTDERR) (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length s))) a3' a4' a5' a6' a7'
(Z_to_bv 64 (Z.of_nat (length s))) (Z_to_bv 64 RSTDERR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 F_STDIO_WRITE) fc None m1 (seg_rom usegs)
/\ munch [(lo, bv_unsigned sp + -64); (RSTDERR, RSTDERR + 232)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1
/\ stk usegs m1 lo (bv_unsigned sp + -64)
/\ rw_cells usegs m1 RSTDERR (file_cells flags 0x4f600 0x4f600 0x4f600 F_STDIO_WRITE 0x4f600 0 2 mode1 0xffffffff tail))).
{ destruct WEND as [-> | [-> ->]].
- eapply evt_mono.
{ eapply (fwx_nofit0 TW) with (lo := lo); [exact FC | exact FL8 | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
[rewrite ESP; exact ST | exact MI]. }
cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
rewrite ESP in MU1, ST1.
do 12 eexists. exists m1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. exact FC1.
- eapply evt_mono.
{ eapply fwx_nofit with (lo := lo); [exact FC | reflexivity | reflexivity | reflexivity | try (rewrite ?ESP; clear - HE LS RSP LO GLO BS; cbn; lia) .. ];
[rewrite ESP; exact ST | exact MI]. }
cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
rewrite ESP in MU1, ST1.
do 11 eexists. exists mode, m1. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
eapply (rw_cells_transport usegs _ m0 m1); [exact FC | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
cbv beta. intros ms1 (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode1 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FC1).
pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0. fold S in RA0.
assert (SRC1 : bytes_at usegs m1 S (to_bytes s)).
{ eapply (bytes_at_transport usegs _ m0 m1); [exact SRC | exact MU1 | cbn; rewrite ?LSB; unfold to_bytes; rewrite ?length_map; clear - SEPS1 SEPS2 LO GLO; lia]. }
assert (GOT1 : rw_cells usegs m1 121776 [C8 (Z_to_bv 64 324000)]).
{ eapply (rw_cells_transport usegs _ m0 m1); [exact GOT | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
assert (GUARD1 : rw_cells usegs m1 324000 [C8 canary]).
{ eapply (rw_cells_transport usegs _ m0 m1); [exact GUARD | exact MU1 | exact WM1 | cbn; clear - LO GLO; lia]. }
assert (FC1' : rw_cells usegs m1 RSTDERR (file_cells flags 0x4f600 (0x4f600 + zlength (@nil Z)) 0x4f600 F_STDIO_WRITE 0x4f600 0 2 mode1 0xffffffff tail)).
{ unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r. exact FC1. }
clear FC1 GOT GUARD SRC.
apply evt_done.
eapply implM_post_evt''.
{ eapply (stdio_write_spec (St:=St)) with (lo := lo) (S := S) (canary := canary) (buf := []) (fd := 2);
[ exact FC1'
| apply bytes_at_nil; clear; lia
| exact SRC1
| reflexivity | reflexivity | reflexivity
| right; reflexivity
| rewrite ESP; exact ST1 | rewrite ESP; unfold STDIO_WRITE_DEPTH; clear - LO; lia | exact GLO
| split; [exact GOT1 | exact GUARD1] | exact MI1
| try (rewrite ?ESP; unfold got_ssp, ssp_guard, zlength; cbn [length Z.of_nat]; clear - LO GLO RA0 BS LS SEPS1 SEPS2 SP47 S47 RSP; lia) .. ]. }
cbv beta. intros [] st2 ms2 PO2.
destruct PO2 as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
rewrite ESP in MU2, ST2. unfold STDIO_WRITE_DEPTH in MU2.
rewrite (ret_pc_even 0x172a4) by (cbn; lia).
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply (rw_cells_transport usegs _ m1 m2); [| exact MU2 | exact WM2 | cbn; clear - LO GLO RSP; lia].
eapply (rw_cells_transport usegs _ m0 m1); [exact FR | exact MU1 | exact WM1 | cbn; clear - LO GLO RSP; lia]. }
clear FR. unfold file_cells in FC2.
step. step. unfold zlength. rewrite (bv_eqb_refl' (Z_to_bv 64 (Z.of_nat (length s)))). cbv iota.
do 4 step.
do 9 step.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold fwrite_diag_post.
do 15 eexists. exists m2.
split; [reflexivity|].
split. { apply (munch_trans _ m m0 m2); [| apply (munch_trans _ m0 m1 m2)].
- eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear - LO GLO RSP; intros; lia. }
split. { eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]. }
split; [exact MI2|]. split; [exact ST2|].
split.
{ exists flags, mode1, 0x4f600, 0x4f600, tail. split; [| split; [exact FL40 | split; [right; split; reflexivity | clear; lia]]].
unfold file_cells. rewrite ?Z.add_0_r in FC2. exact FC2. }
split; [exact SSP2 | reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
