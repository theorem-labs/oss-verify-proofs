(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_syscalls F_memcpy StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Lemma memcpy_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv usegs m ->
evt usegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c130) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros BA LEN DC SEP HN HS HD MI.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>29765905911.4631113014002.4558047180137.4400000800<00@S3LEN2HNS2HSS2HD".
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply Ubsan.F_memcpy.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
intros ms' P. unfold Ubsan.F_memcpy.memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 wfn) fc None m' (seg_rom usegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp).
Lemma fwx_nofit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
rw_cells usegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv usegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
evt usegs (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x170e4) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "00k0>11912744615.7112367362435.7112367362435.7313021749692.711527479463.69 17646078182.6218519693520.6519049469500.7121729101182.7121918414723.7121918414723.7424630998586.6925314760359.7131081687356.7232477129627.6432477130256.6532651489978.7133039531175.7233680001082.7236166524798.7136425780322.6536993589379.7236993589379.7437107179452.7139400444670.693945979267.71 3945979267.73 3971437694.71 41809558659.6941809558659.7243059266230.6043060403331.7243060403331.7445221239098.7145659830526.7246602213840.6549345641752.6451147908213.6551481786499.7151481786499.7353085287934.7155509061630.7256228262055.71563227834.71  57745675194.7159308587409.6559308588058.6459728269064.6560025031335.7263694018620.7267541566890.6967541566890.7167541566890.7267800801447.717010956092.69 8583720762.72 8929209696.65 951455556.65  985337532.71  00000100200300700800900A00E00N00O00P00T00U00Y00_00e00i00j00n01701;01<01=01A01J01K01L01U01V01W01[01\01]01a01j01o02002502602702@02I02J02N02R02X02a02i02j02n03203603:03;03?03C03D03O03SSSSS2HBSSS4WPOS1LS2HBS2LO4SEPFSSS2HBSS2HBS4WENDS4WENDS2HBSS2HBS2LO4SEPFS2LOSSS2HBS2LO4SEPFSSS2LO4SEPFSSS2LOSSS2HBS2LO4SEPFS3WFNSS3WFESSS2LO4SEPFS2LO4SEPFSS2HBS2HBS1L2HrS4WEND2HwS4WPOS1LSS2HBS2LOS2LOS2LOSS2HBS2HBFS4WEND4WPOSS2HB".
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
do 13 step.
rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
release_frame FR ST (bv_unsigned sp).
unfold fwx_nofit_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
/\ rw_cells usegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
/\ bytes_at usegs m' S src.
Lemma fwx_tail : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
(F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l i lo : Z),
rw_cells usegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells usegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells usegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
bytes_at usegs m S src -> Z.of_nat (length src) = l ->
stk usegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
(wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
(0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
evt usegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
(Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x171dc) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (rw_cells_bound _ _ _ _ FC) as BF.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "00P0?12367362435.10915334555922.10516085926792.87 17176034095.10617178147273.87 21492138011.10521918414723.11023110294546.85 26279284492.11326956891786.10129504480019.10631422378390.10231546306377.1133208951753.113 34529339780.11335462865823.10536182916719.10636425881493.10236993589379.11038480577237.1133945979267.110 41809558659.10943060403331.11145498937913.10649345641752.10151481786499.11052903095684.11354669263073.86 62288641514.10764292837380.87 65799097344.113944823876.87   00000800J00\00n01@01N01V01^01i02102902A02M02^02l03:03;03G03O03W03_03g03o04004804@04R04d05205A05O05^S3CAP2LJS3CAP3LO05SEPW12LJS3CAP3LEN2I02IL2LJS3CAP3LEN5SEPS12LJS3CAP3LEN5SEPS12LJS3CAP5SEPW22LJS3CAP2LJS3CAP2LJS3CAP2LJ2HBS3CAP2LJS3CAP2LJS3CAP2LJS3CAP3Fp02LJS3CAP3LO04SEPF2LJS3CAP5SEPW22LJS3CAP5SEPW12LJFS3CAP3LO02LJS3CAP2LJS3CAP2LJS3CAP2LJS3CAP2LJS3CAP2LJFS3CAP2LJS3CAP2LJS3CAP3LEN5SEPS32LJS3CAP3LO05SEPW12LJS3CAP3LEN2LJ1HS3CAP3SHI2LJ2BSS3CAP5SEPW22LJS3CAP2W03WHI2LJ".
apply (rw_cells_split_CB usegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app usegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
step. step. step.
replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
call memcpy_callw.
1:{ exact SRC. }
1:{ rewrite Nat2Z.id. reflexivity. }
1:{ rewrite Nat2Z.id. exact DSTa. }
1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
rewrite !Nat2Z.id in *.
change usegs with usegs in *.
do 4 step.
do 9 step.
release_frame FR ST (bv_unsigned sp).
rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (DST' : rw_cells usegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
by (apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
end.
cbn [app] in DST'. rewrite !LEN in *.
unfold fwx_ret_post, file_cells. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma fwx_fit_plain : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l lo : Z),
rw_cells usegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells usegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
bytes_at usegs m S src -> Z.of_nat (length src) = l ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
(2^31 <= lbf < 2^32) ->
stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) -> (bv_unsigned sp < 2^63) ->
mem_inv usegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
evt usegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x170e4) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "01A0>11912744615.8512367362435.8513021749692.8514596272711.8115045126238.811527479463.83 17282469374.8517283573989.8117646078182.7618519693520.7918612176510.8619049469500.8521729101182.8521918414723.8524630998586.8325314760359.8526338883506.8031081687356.8632477129627.7832477130256.7932651489978.8533039531175.8633680001082.8634215875436.8134466804606.8636166524798.8536993589379.8637107179452.8538480577237.8338480577237.8538480577237.8638575169662.8639266251006.8539400444670.833945979267.85 3971437694.85 41809558659.8342799229438.8543059266230.7443060403331.8645221239098.8545630148274.8145659830526.8645987129429.8147727736507.8147785557246.8550141583378.8151481786499.855204216388.81 53085287934.8553415683838.8555509061630.8655659921210.8156182120749.8056228262055.85563227834.85  57406176638.8657745675194.8558806679105.8159308586639.8159308587409.7959308588058.7859728269064.7959873971070.8560025031335.8660153793118.8160385159294.8560565052414.8561098694187.8061396519294.8362071687806.836214192043.81 63694018620.8667379821965.8167800801447.857010956092.83 7352836843.81 8583720762.86 8929209696.79 951455556.79  985337532.85  00000100200600=00>00?00N00T00U00f01401801A01B01H01I01N01R01X01^01d01e01k02302A02J02K02O02S02W02[02j03903B03C03L03M03[03_03`03f03l04504C04N04\04c04d05n06706E06N06S06X06Y06_06n07407@07H07P07Y07j08908:08?08M08\08a08o09>09J09N09Y09Z09^09b09h09i0:70:;SSS2HBS5SEPS2SSS4CAPE2LO5SEPW1S4SEPFSS3LEN4WEND2W03FITS3LEN2LO5SEPS2S2HBS2LO4SEPFSS4SPHISS3LBFS2HBS4WENDS4WENDS4SPHISS4SPHIS2LO3LO0S3LEN2LO5SEPS2S2LO4SEPFSS2HBS2LOS2LOS2LOS4CAPE2LO5SEPW1S4CAPE2LO5SEPW1S2LO4SEPFSS2LO4SEPFSS3LEN2LO5SEPS2S2LOSS4SPHIS4SPHIS2LO4SEPFS4CAPE3LEN3FITS4CAPE4WENDS3LEN2LO5SEPS2S5SEPS3SS3LEN4WEND2W03FIT2LO3LO04SPHI3Fp04SEPF5SEPW15SEPW25SEPS15SEPS25SEPS32BS2HwS2LO4SEPFS3LEN2LO5SEPS2S2LO4SEPFS3Fp0S3LBFSS4SPHIS4CAPE2LO5SEPW1S4SPHIS4CAPE5SEPW2S3NEG2HlS3FIT2HrS4WEND2HwS3LEN4WEND2W03FITS4CAPE2LO5SEPW1SS3SHIS3LEN2LO5SEPS2S4CAPE2LO5SEPW1S3LBFS3LEN2LO5SEPS2S4CAPE2LO5SEPW1S4CAPE5SEPW1S2HBS3FIT5SEPS1SS2HBS2W0S4SPHIFS4CAPE4WEND2W0S2HB".
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
do 3 step.
pose proof (sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
specialize (NEG ltac:(lia)).
if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | lia | lia | exact MU | exact WM | exact MI | lia ..].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
