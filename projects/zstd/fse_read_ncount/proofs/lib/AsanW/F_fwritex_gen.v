(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit Stdio_kitI.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
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

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.
Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 wfn) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).
#[using="Type"] Lemma fwx_nofit : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
mem_inv asegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 ->
evtF asegs RNG (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8ef30) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF RSTK RFP.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "01<0>11912744615.7512367362435.7512367362435.7713021749692.751527479463.73 17646078182.6617776320430.7717776320431.7418519693520.6919049469500.7519882575240.7821729101182.7521918414723.7521918414723.7823429214080.8124630998586.7325314760359.7525878270255.7425878270255.7631081687356.7632477129627.6832477130256.6932651489978.7533039531175.7633680001082.7636115622446.7536115622446.7736166524798.7536425780322.6936993589379.7636993589379.7837107179452.7539400444670.733945979267.75 3945979267.77 3971437694.75 41809558659.7341809558659.7643059266230.6443060403331.7643060403331.7843987951406.7543987951406.7745221239098.7545659830526.7646602213840.6949345641752.6851147908213.6951481786499.7551481786499.7753085287934.7553767577775.7453767577775.7655509061630.7656228262055.75563227834.75  57745675194.7558817367051.7859308587409.6959308588058.6859728269064.6960025031335.7661917199023.7461917199023.7663235321900.7263235321900.7563694018620.7667541566890.7367541566890.7567541566890.7667800801447.757010956092.73 8583720762.76 8929209696.69 951455556.69  985337532.75  00000100200300700800900=00A00I00M00N00[00\00]00^00b00c00g00k00o01501;01?01@01D01H01L01Y01]01^01_01c02002102202?02@02A02E02F02G02K02O02S02`02e02f02k02l02m03:03>03B03O03P03T03X03Y03_03h04004104504904=04A04E04I04M04Q04R04V04Z04[04f04jSSSS2HBSSS2LOS2LOS4WPOS1LS2HBSS3WFN2LO4SEPFSSSS2HBSS2LOS2LOS2HBS4WENDS4WENDS2HBSS2HBS2LOS2LOS3WFN2LO4SEPFS2LOSSS2HBS3WFN2LO4SEPFSSS3WFN2LO4SEPFSSS2LOSSS2LOS2LOS2HBS3WFN2LO4SEPFS3WFNSS3WFESSS3WFN2LO4SEPFS2LOS2LOS3WFN2LO4SEPFSS2HBS2HBSS1L2HrS4WEND2HwS4WPOS1LSS2LOS2LOS2LOS2LOS2HBS2LOS2LOS2LOSS2HBS2HBFS4WEND4WPOSS2HB".
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
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
/\ rw_cells asegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
/\ bytes_at asegs m' S src.
#[using="Type"] Lemma fwx_tail : forall RNG (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
(F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l i lo : Z) (SLO1 SHI1 RLO1 RHI1 SLO2 SHI2 RLO2 RHI2 : Z),
rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells asegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
bytes_at asegs m S src -> Z.of_nat (length src) = l ->
stk asegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
(wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
(0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
(KHIGH <= lo) -> (lo <= bv_unsigned sp - 64 - 2240) -> (l <= 2^40) ->
ashenv m0 -> ashsafe [(Fp + 40, Fp + 48); (wpos, wpos + l)] -> appW [(Fp + 40, Fp + 48); (wpos, wpos + l)] ->
shclean m0 SLO1 SHI1 RLO1 RHI1 -> (SLO1 <= S) -> (S + l <= SHI1) -> (SLO1 < SHI1) ->
shclean m0 SLO2 SHI2 RLO2 RHI2 -> (SLO2 <= wpos) -> (wpos + l <= SHI2) -> (SLO2 < SHI2) ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG Fp 232 -> rng RNG S l -> rng RNG wpos (Z.of_nat cap) ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF asegs RNG (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
(Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8f028) fc None m (seg_rom asegs)).
Proof.
intros until RHI2. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI
KH LOI L40 ENV SAFE APW SH1 S11 S12 S13 SH2 S21 S22 S23 RSTK RIMG RFP RS RW RSH1 RSH2.
Local Ltac2 Set LiaHints.tbl := fun () => "00h0?10527006084.14212367362435.14612428150072.14116085926792.12317178147273.12317776320431.14619882575236.14519882575240.14920270305492.12321918414723.14722128007262.11323110294546.1212388488507.141 25076071819.14125076071819.14225878270255.14626279284492.15026958989051.13828040491972.14230974585716.12331546306377.1503208951753.150 33808416095.12334529339780.15036115622447.14636425881493.13936847183684.14136993589379.14737527262967.12338480577237.1503945979267.147 41809558659.14642875227558.12343060403331.14843987951406.14745397843364.14245490414147.12349343544681.13851363698911.11251481786499.14752903095684.15053618304519.12353767577775.14654669263073.12255732601977.12356183014873.12357622410744.14258092753942.13959518437986.12361917199020.14563235321900.14564292837380.12364546719448.12365799097344.1508760885306.123 944823876.123  00000c00k00l01<02502A02I02Q02]02e02m03503n04<04o05;05F05N06G06\06h07C07O08H08T08`08a08i09909A09I09Q0:D0:L0:X0:Y0:e0:m0;50;=0<60<B0<N0=A0=I0=Q0>L0>T0?M0?Y0?e0@40@D0A=0AM0A\S3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJS3CAP2LJFS3CAP3LEN3L402LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfrS3CAP3LO02LJS3CAP2LJS3CAP2LJS3CAP3S112LJS3CAP2LJS3CAP2KHS3CAP2LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfrS3CAP2LJ5SEPfrS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJS3CAP3LO02LJS3CAP2LJ2HBS3CAP2LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfrS3CAP3LO04SPHI3LOI2LJS3CAP3Fp02LJS3CAP3LEN4SEPF5SEPS13LOI2LJS3CAP3LOI2LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfrS3CAP3LO02LJS3CAP3LO02LJFS3CAP2LJS3CAP3LEN3S122LJS3CAP2LJS3CAP2LJS3CAP2LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJS3CAP2LJS3CAP3LO02LJFS3CAP3S212LJS3CAP2LJS3CAP2KHS3CAP2LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfrS3CAP3LEN2LJS3CAP3LO02LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJS3CAP2LJS3CAP2LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfr1HS3CAP2LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfrS3CAP3LO02LJS3CAP3LO02LJS3CAP3SHI2LJ2BSS3CAP3LEN3L402LJS3CAP3LEN4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2LJ5SEPfrS3CAP3LEN3S222LJS3CAP2W03WHI2LJ".
assert (APW' : appW [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)]) by (apply appW_cons; [right; cbn; lia| exact APW]).
assert (SAFE' : ashsafe [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)]) by (apply ashsafe_cons_high; [unfold KHIGH in KH; lia| exact SAFE]).
pose proof (ashenv_transport _ _ _ ENV MU WM SAFE') as ENV'.
pose proof (shclean_transport_app _ _ _ _ _ _ _ SH1 MU WM APW' S13) as SH1'.
pose proof (shclean_transport_app _ _ _ _ _ _ _ SH2 MU WM APW' S23) as SH2'.
pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
pose proof (rw_cells_bound _ _ _ _ FC) as BF.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
unfold file_cells in FC.
apply (rw_cells_split_CB asegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
cbn [mk_CB_cells app] in DST.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
step. step. step.
replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
call (memcpy_callw RNG SLO1 SHI1 RLO1 RHI1 SLO2 SHI2 RLO2 RHI2).
1:{ exact SRC. }
1:{ rewrite Nat2Z.id. reflexivity. }
1:{ rewrite Nat2Z.id. exact DSTa. }
1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ exact KH. } 1:{ exact ENV'. }
1:{ exact SH1'. } 1:{ lia. } 1:{ lia. } 1:{ exact SH2'. } 1:{ lia. } 1:{ lia. }
1:{ lia. } 1:{ lia. } 1:{ lia. }
1:{ solve_rng. }
rewrite !Nat2Z.id in *.
match goal with H : stk _ _ lo _ |- _ => rename H into STc end.
match goal with H : rw_cells _ _ wpos [CB (length src) src] |- _ => rename H into DSTc end.
do 4 step.
do 9 step.
release_frame FR STc (bv_unsigned sp).
rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (DST' : rw_cells asegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
by (apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact DSTc|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
end.
cbn [app] in DST'. rewrite !LEN in *.
unfold fwx_ret_post, file_cells. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fwx_fit_plain : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(cap : nat) (junk src : list byte) (S l lo : Z) (SLO1 SHI1 RLO1 RHI1 SLO2 SHI2 RLO2 RHI2 : Z),
rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
rw_cells asegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
bytes_at asegs m S src -> Z.of_nat (length src) = l ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
(0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
(2^31 <= lbf < 2^32) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) -> (bv_unsigned sp < 2^63) ->
mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
(wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
(S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
(KHIGH <= lo) -> (lo <= bv_unsigned sp - 64 - 2240) -> (l <= 2^40) ->
ashenv m -> ashsafe [(Fp + 40, Fp + 48); (wpos, wpos + l)] -> appW [(Fp + 40, Fp + 48); (wpos, wpos + l)] ->
shclean m SLO1 SHI1 RLO1 RHI1 -> (SLO1 <= S) -> (S + l <= SHI1) -> (SLO1 < SHI1) ->
shclean m SLO2 SHI2 RLO2 RHI2 -> (SLO2 <= wpos) -> (wpos + l <= SHI2) -> (SLO2 < SHI2) ->
rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng RNG Fp 232 -> rng RNG S l -> rng RNG wpos (Z.of_nat cap) ->
rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
evtF asegs RNG (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8ef30) fc None m (seg_rom asegs)).
Proof.
intros until RHI2. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3
KH LOI L40 ENV SAFE APW SH1 S11 S12 S13 SH2 S21 S22 S23 RSTK RIMG RFP RS RW RSH1 RSH2.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "01R0?11912744615.11612065430310.11212367362435.11613021749692.11614596272711.11215045126238.1121527479463.114 15778993099.12117282469374.11617283573989.11217646078182.10717776320431.11518519693520.11018612176510.11719049469500.11619726487638.11219882575240.11920280676042.11221729101182.11621918414723.11624630998586.11425314760359.11625878270255.11526338883506.11131081687356.11732477129627.10932477130256.11032651489978.11633039531175.11733680001082.11734215875436.11234466804606.11736115622446.11636166524798.11636993589379.11737107179452.11638480577237.11438480577237.11638480577237.11738575169662.11739266251006.11639400444670.1143945979267.116 3971437694.116 41809558659.11442799229438.11643059266230.10543060403331.11743987951406.11644140409580.11245221239098.11645492894813.11245630148274.11245659830526.11745987129429.11247727736507.11247785557246.11650141583378.11250742586459.11251481786499.1165204216388.112 53085287934.11653415683838.11653767577775.11555509061630.11755659921210.11256182120749.11156228262055.116563227834.116  56756499907.11257406176638.11757745675194.11658806679105.11258817367051.11959308586639.11259308587409.11059308588058.10959728269064.11059873971070.11660025031335.11760153793118.11260385159294.11660565052414.11661098694187.11161396519294.11461917199023.11562071687806.1146214192043.112 63235321900.11363694018620.11767379821965.11267800801447.1167010956092.114 7352836843.112 8583720762.117 8929209696.110 951455556.110  985337532.116  00000100600700;00B00C00D00E01401:01;01?01H02302702<02=02B03103203803903=03B03F03L03R03X03Y03_03g04R04V05E05F05J05N05R05V06E07407c07d08S08T09?09C09D09H09M09S09X09^0:M0:[0:f0;Q0;X0;]0;^0;c0<R0==0=A0>00>50>:0>;0>A0>F0?50?;0@80@90@A0@I0@R0@`0AO0AP0AU0B@0Bo0C40C_0Cc0DR0EO0ES0EW0FP0FQ0FU0FY0F_0F`0Fn0G2SS3S22SS2HBS5SEPS2SSSS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS4SEPFSS2LOS3LEN3L40S4CAPE3LEN4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS2HBS3S23SS3S11S4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS15SEPS23LOISS4SPHISS2LOS3LBFS2HBS4WENDS4WENDS4SPHISS4SPHIS2LO3LO0S4CAPE3LEN4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS2LOS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS15SEPS23LOISS2HBS2LOS2LOS2LOS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS15SEPS23LOISS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS15SEPS23LOISS4CAPE3LEN4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS2LOSS2LOS3S13S4SPHIS3S21S4SPHIS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS15SEPS23LOIS4CAPE3LEN3FITS4CAPE4WENDS4CAPE3LEN4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS5SEPS3S3LOISS3L40S4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS15SEPS23LOIS4CAPE3LEN4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS2LOS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS15SEPS23LOIS3Fp0S3LBFSS4SPHIS3S12S4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS4SPHIS4CAPE3LEN4WEND3FIT4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2HwSS3NEG2HlS3FIT2HrS4WEND2HwS4CAPE4WEND2W0S4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS25SEPS33LOISS3SHIS4CAPE3LEN4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS3LBFS4CAPE3LEN4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS2LOS4CAPE3LEN3FIT4SEPF5SEPW15SEPW25SEPS25SEPS33LOIS4CAPE3LEN4WEND3FIT4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2HwS2LOS2HBS4CAPE4WEND3FIT4SEPF5SEPW15SEPW25SEPS15SEPS25SEPS33LOI2HwSS2HBS2W0S4SPHIFS4CAPE4WEND2W0S2HB".
carve_frame 64%nat ST.
do 13 step.
if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
do 3 step.
if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
do 3 step.
pose proof (sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
specialize (NEG ltac:(lia)).
if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
eapply (fwx_tail RNG) with (SLO1 := SLO1) (SHI1 := SHI1) (RLO1 := RLO1) (RHI1 := RHI1) (SLO2 := SLO2) (SHI2 := SHI2) (RLO2 := RLO2) (RHI2 := RHI2);
first [ exact FR | exact FC | exact DST | exact SRC | exact LEN | exact ST | exact MU | exact WM | exact MI
| exact KH | exact L40 | exact ENV | exact SAFE | exact APW | exact SH1 | exact SH2 | exact RSTK | exact RIMG | exact RFP | exact RS | exact RW | exact RSH1 | exact RSH2 | lia ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
