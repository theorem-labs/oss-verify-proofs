(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells ShadowTac F_irt F_rip F_tryinit I_printf_lib I_printf_common I_printf_formats.
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

Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Notation rt_ckpf m := (rw_cells asegs m 0x133ff8 [C8 (Z_to_bv 64 4294967296)]).
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma vfprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (j16 : list byte) (rav s0v s1v s2v : word),
mem_inv asegs m ->
rw_cells asegs m (bv_unsigned sp) [CB 16 j16; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
rng RNG (bv_unsigned sp) 48 ->
evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom asegs))
(MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x45d74) fc None m (seg_rom asegs)).
Proof.
intros until s2v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
do 6 zstep. apply evtF_done. reflexivity.
Qed.
#[using="Type"] Lemma vprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (rav s0v s1v : word),
mem_inv asegs m ->
rw_cells asegs m (bv_unsigned sp) [CB 24 j24; C8 s1v; C8 s0v; C8 rav] ->
rng RNG (bv_unsigned sp) 48 ->
evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom asegs))
(MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x45204) fc None m (seg_rom asegs)).
Proof.
intros until s1v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
do 5 zstep. apply evtF_done. reflexivity.
Qed.
#[using="Type"] Lemma fprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (j32 : list byte) (va : list cell) (rav s0v s1v s2v : word),
mem_inv asegs m ->
rw_cells asegs m (bv_unsigned sp) ([CB 32 j32; C8 s2v; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 48%nat ->
rng RNG (bv_unsigned sp) 112 ->
evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom asegs))
(MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x46190) fc None m (seg_rom asegs)).
Proof.
intros until s2v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
rewrite cells_size_app, SZ in B. cbn in B.
apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
do 6 zstep. apply evtF_done. reflexivity.
Qed.
End CANSEC1.
Ltac iprem :=
lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- mem_inv _ _ => first [assumption | eassumption]
| |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
| |- stk _ _ _ _ => first [assumption | eassumption]
| |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
| |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
| |- bytes_at _ _ _ _ => first [assumption | eassumption]
| |- unpoisoned _ _ _ => first [assumption | eassumption]
| |- wr_at _ _ _ _ => first [assumption | eassumption]
| |- app_blk _ _ => first [assumption | eassumption]
| |- Forall _ _ => first [assumption | eassumption]
| |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
| |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end]
| |- ?g => unfold KHIGH, sf_hide in *; first [assumption | lia]
end.
Section CANSEC2. Context {rc : runConstT}.
Definition fprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j32,
ms' = MS (mkR (Z_to_bv 64 0x46190) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2
a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp - 48)) x13 x14 x15 x16 x17
(Z_to_bv 64 (bv_unsigned sp - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8f2f0) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2432, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp - 112)
/\ rw_cells asegs m' (bv_unsigned sp - 112)
[CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
/\ rt_inited m'.
Section FPRINTF.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 2432)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis INI : rt_inited m.
Hypothesis CKP : rt_ckpf m.
Hypothesis RPF : rt_real_printf m.
Hypothesis A1 : a1 = Z_to_bv 64 A.
Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).
Notation MID := (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
#[using="MI ST LO KLO GOT SHB INI CKP RPF RI RSTK"] Lemma fprintf_i_A : forall Q,
(forall m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
munch [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -112) ->
rw_cells asegs m1 (bv_unsigned sp + -112)
[CB 8 j8; C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
rt_got m1 -> rt_shbase m1 -> rt_inited m1 -> rt_real_printf m1 ->
evtF asegs RNG Q (MS (mkR (Z_to_bv 64 0x46150) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 a1 a0
(Z_to_bv 64 0x1eac3) a1 (Z_to_bv 64 (bv_unsigned sp + -48)) x13 x14 x15 x16 x17
(Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x4523c) fc None m1 (seg_rom asegs))) ->
evtF asegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x460d0) fc None m (seg_rom asegs)).
Proof.
intros Q K.
pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "0120?11513985511.77 13114317212.10813114317212.11013270676710.76 14289303062.89 14773250736.76 15032830052.78 15632881006.10817522630622.10818887455772.79 20824881200.78 2115072284.76  21518274460.78 21600875239.77 23400781414.75 25122868580.78 26817889712.79 27373230610.71 27373230610.86 2770259888.79  29852097692.77 3020683420.77  32869782320.78 35633624860.79 37321754422.75 37321754422.90 38264599196.78 38889038000.79 43055122012.68 44873666096.77 45685315612.78 45685315612.93 46999964426.60 47287692011.10147382493616.78 48325856741.10948325856743.10749632921830.76 50125791591.77 50125791591.92 50925296560.78 51384633319.77 51843947621.10951843947623.92 52371274268.78 53150882660.78 53400667952.11054002075495.77 54096612892.79 55002379676.78 56172315833.71 56172315833.86 57052305983.71 57052305983.86 59308628304.1  59308628433.1  59308628566.1  59452298416.93 60330452198.70 62431484700.11062431484700.93 65436951088.77 6898299397.71  6898299397.86  8395658290.104 8788598064.78  00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00V00d00e00f00j00k00l00m01101201301401501601701801901:01;01<01=01>01?01@01A01B01C01D01H01L01P01T01X01Y01Z01[01\01]01^01_01`01aSSSSSSSSSSSSSSSSSFFSSSSSS2LO3KLO3SPR1HS2LO3KLO3SPR1HSSS2LOSSSS2LOSSSSSSSSSSSSSSSSSSSS2LOS2LOS2K1S2K2S2K3SSSSSFFSS".
assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
pose proof CKP as CKPc. pose proof RPF as RPFc.
change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
change (?P) with (sf_hide P) in RPF.
recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
carve_frame 112%nat ST0.
do 15 zstep. zstep.
call_sp tryinit_spec. all: match goal with |- ?g => idtac "=="; idtac g end. all: iprem.
zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
zstep. zstep. zstep.
call_sp tryinit_spec. all: iprem.
zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
do 4 zstep. zstep.
eapply K; try assumption; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Hypothesis PCI : printf_common_int_stmt A n.
#[using="A n MI ST LO KLO GOT SHB INI CKP RPF A1 NA FZ RI RSTK RSHF PCI"] Lemma fprintf_i_pre_int :
evtF asegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x460d0) fc None m (seg_rom asegs)).
Proof.
apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "00?0?11805645481.95 17222273888.98 18442817054.82 27375328819.82 31382798176.98 35208144345.11037321754422.86 46999964426.80 50356509686.10651843947620.10552106616342.10156170217624.82 60318033760.98 62431484700.1066896203300.82  00000A00B00F00G00H00I00W00[00\00]00^00_00`00a00bS2LO3KLO2NA2H42H5SS2LOFSSS2LO3KLO3SPR1HS2LOSSSSSSF".
assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
{ eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations; lia. }
change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ.
call_sp PCI. all: iprem.
do 4 zstep. do 3 zstep. zstep.
apply evtF_done. unfold fprintf_i_mid.
replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
lazymatch goal with FR : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Variables (sstr : list byte) (RLO RHI : Z).
Notation Sa := (bv_unsigned a2).
Notation NS := (Z.of_nat (length sstr) + 1)%Z.
Hypothesis LAY : rt_layout m.
Hypothesis SSTR : bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]).
Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= Sa)%Z.
Hypothesis APPS : app_blk Sa (Sa + NS).
Hypothesis SPOS : (0 < Sa)%Z.
Hypothesis USTR : unpoisoned m Sa (Sa + NS).
Hypothesis NSZ : (NS <= 2^40)%Z.
Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
Hypothesis RS : rng RNG Sa NS.
Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
Hypothesis PCS : printf_common_s_stmt A n.
#[using="A n MI ST LO KLO GOT SHB INI CKP RPF A1 NA FZ RI RSTK RSHF sstr RLO RHI LAY SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RS RSH1 PCS"] Lemma fprintf_i_pre_s :
evtF asegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x460d0) fc None m (seg_rom asegs)).
Proof.
apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "00N0?11801389858.10111803549481.12711803549481.13014788810421.10614790997494.10917219881159.12018448874142.10621594911267.10927369286323.10627923144266.10631380405447.12035208144345.13235892935514.10037321754422.11038270114779.10538285077374.12146999964426.96 50356509686.12851843947620.12752106616342.12556185189400.10659503987035.10659504015996.12260328355015.12060866711165.10662431484700.1286515440607.106 6611983004.109 68185727392.1066911148708.106 00000600P00g01601E01F01J01K01L01M01N01O01Z01k01l01m02102202302402502602702802>02?02@02A02F02GS4SEPSS2LO3KLO2NA4SEPS3AS'2H42H5S2LO3KLO4SEPS3AS'2H42H5S2LO3KLO2R13SPRS2LO3KLO2R13SPRSS2LOSFFSSS2LO3KLO2R1S2LO3KLO2R13SPR1HSSS2LOSSSSSSSS4SEPSSFFS3SPRF".
assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof APPS as APPS'. destruct APPS' as [LES AS']. unfold KLOW, KHIGH, KEND in AS'.
assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
{ eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations; lia. }
assert (LAY1 : rt_layout m1).
{ eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
assert (SSTR1 : bytes_at asegs m1 Sa (sstr ++ [Z_to_bv 8 0])).
{ eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
assert (USTR1 : unpoisoned m1 Sa (Sa + NS)).
{ eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations; lia. }
assert (WR11 : wr_at asegs m1 (shad RLO) (shad RHI - shad RLO)) by (eapply wr_at_transport; eassumption).
change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ; change (?P) with (sf_hide P) in LAY;
change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in USTR; change (?P) with (sf_hide P) in WR1.
chunk_split FR1 8%nat FRV. chunk_split FRV 1%nat FRW.
call_sp PCS. all: iprem.
chunk_join FRV FRW. chunk_join FR1 FRV.
do 4 zstep. do 3 zstep. zstep.
apply evtF_done. unfold fprintf_i_mid.
replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
lazymatch goal with FR : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FPRINTF.
Definition vprintf_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24 j16,
ms' = MS (mkR (Z_to_bv 64 0x45d74) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
a0 (Z_to_bv 64 0x9de28) (Z_to_bv 64 0x9de28) a0 a1 x13 x14 x15 x16 x17
a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8f2f0) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 2416, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp - 96)
/\ rw_cells asegs m' (bv_unsigned sp - 48) [CB 24 j24; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m' (bv_unsigned sp - 96) [CB 16 j16; C8 s2; C8 a1; C8 a0; C8 (Z_to_bv 64 0x45204)]
/\ rt_inited m'.
Section VPRINTF.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 2416)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis INI : rt_inited m.
Hypothesis CKP : rt_ckpf m.
Hypothesis RPF : rt_real_printf m.
Hypothesis A0 : a0 = Z_to_bv 64 A.
Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).
Hypothesis PCI : printf_common_int_stmt A n.
#[using="A n MI ST LO KLO GOT SHB INI CKP RPF A0 NA FZ RI RSTK RSHF PCI"] Lemma vprintf_i_pre :
evtF asegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x451a0) fc None m (seg_rom asegs)).
Proof.
pose proof (munch_refl [(bv_unsigned sp + -2416, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "01M0?11093997488.11011723034140.76 11805645481.13211805645481.99 12037418212.77 13284814180.92 13284814186.94 14793086774.74 14793086774.90 15632881007.12615632881007.93 16475027684.11017522630623.12617522630623.93 19340579248.95 19664730524.11119954217393.12120616350130.13823139947184.11325393266480.79 25613863711.11925779550180.11026939498908.11126939498908.79 26939498908.95 29158023216.11129323744831.70 29738897271.12629738897271.12831377886384.79 31378308326.69 31384895300.13431704748700.11135142651312.11135208144345.14636178739012.13437438167600.78 37821204774.1013946739303.109 40705516082.10541194412848.11141873551410.11941873551411.86 41873552432.10341875649554.70 42250564406.10742250564406.12343055122012.67 43422820272.76 43678327964.78 46998232647.10347287692008.11847289789135.85 47561401098.59 47804764645.78 47804764650.11047804764650.94 48010218486.11150148821093.78 50356509686.14250644243556.11050644243556.14150644243562.12752277671964.11152277671964.12852277671964.14253710135069.10355952418663.75 56003195754.11256170217624.86 56170217625.11956170218651.10356172315833.70 57405284894.86 59308628304.1  59308628433.1  59308628566.1  59308628695.1  59510497308.93 59510497308.95 60286080022.88 60681498140.11062065839047.12864043097572.12564043097578.12764284135708.11366937699537.1116896202279.103 6896203300.86  6896203301.119 6898299397.70  7495246620.79  7589930820.134 00000100200C00T00U00V00W00e01301401501601701801901:01;01<01=01>01B01C01D01E01F01G01K01L01M01N01O01P01Q01R01S01T01U01Y01Z01[01\01]01^01_01`01n02<02@02A02B02C02D02E02I02J02K02L02M02N02O02P02Q02R02S02T02U02Y02Z02[02\02]02^02_02c02g02k02o03303403503603703803903:03;03<03=03>03?03@03A03BSSS2LO3KLO2NA2H42H5S2LO3KLO2NA2H42H5SSSS2LO3KLO3SPR1HS2LO3KLO3SPR1HSSSSSSSSSSSS2LOSSSSSS2LOSSSSSSSSSSS2LOSSSFFFFS2LO3KLO3SPR1HS2LO3KLO3SPR1HS2LOSSSSSS2LOSSSSSSSSSSSSS2LOSSSSSSS2LOS2K1S2K2S2K3S2K4SSSSSSSSSFFFFSS".
assert (RSTK' : rng RNG (bv_unsigned sp + -2416) 2416) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
pose proof CKP as CKPc. pose proof RPF as RPFc.
change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
change (?P) with (sf_hide P) in RPF.
recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
carve_frame 48%nat ST0.
do 7 zstep. zstep.
call_sp tryinit_spec. all: iprem.
zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
do 4 zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
by (eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia)
end end.
change (?P) with (sf_hide P) in FZ.
call_sp PCI. all: iprem.
clear FZ1.
do 4 zstep. zstep.
do 7 zstep. zstep.
match goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => carve_frame 48%nat H end.
do 9 zstep. zstep.
call_sp tryinit_spec. all: iprem.
zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. cbv in K4. lia. } clear K4.
do 4 zstep. zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
assert (FZ2 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
by (unfold sf_hide in FZ; eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia)
end end.
call_sp PCI. all: iprem.
clear FZ2.
do 5 zstep. zstep.
apply evtF_done. unfold vprintf_i_mid.
replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
replace (bv_unsigned sp - 2416)%Z with (bv_unsigned sp + -2416)%Z by lia.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3] rest FRa) as FRm1; cbn [app cells_size csize Nat.add] in FRm1 end;
lazymatch goal with FRb : rw_cells asegs mf (bv_unsigned sp + -96) (?c1 :: ?c2 :: ?rest) |- _ =>
pose proof (rw_cells_merge asegs mf _ [] [c1; c2] rest FRb) as FRm2; cbn [app cells_size csize Nat.add] in FRm2 end end.
do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm1. exact FRm2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End VPRINTF.
#[using="Type"] Corollary vprintf_i_pre_d : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2416)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
a0 = Z_to_bv 64 FMT_D ->
shadow_bytes m (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0%Z) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64)) ->
evtF asegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x451a0) fc None m (seg_rom asegs)).
Proof. intros. eapply vprintf_i_pre; try eassumption. { unfold FMT_D. Local Ltac2 Set LiaHints.tbl := fun () => "0010=2309797376.51000001S".
lia. } exact printf_common_d_stmt. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Corollary fprintf_i_pre_toobig : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
a1 = Z_to_bv 64 FMT_TOOBIG ->
shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0%Z) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64)) ->
evtF asegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x460d0) fc None m (seg_rom asegs)).
Proof. intros. eapply fprintf_i_pre_int; try eassumption. { unfold FMT_TOOBIG. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68284883888.51000001S".
lia. } exact printf_common_toobig_stmt. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition fprintf_i_pre_s_stmt (A n : Z) : Prop :=
forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sstr : list byte) (RLO RHI : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m -> rt_layout m ->
a1 = Z_to_bv 64 A ->
shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
bytes_at asegs m (bv_unsigned a2) (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr ->
(bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
app_blk (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (0 < bv_unsigned a2)%Z ->
unpoisoned m (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (Z.of_nat (length sstr) + 1 <= 2^40)%Z ->
(RLO <= bv_unsigned a2 /\ bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
rng RNG (bv_unsigned a2) (Z.of_nat (length sstr) + 1) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
evtF asegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x460d0) fc None m (seg_rom asegs)).
End CANSEC2.
Ltac fis PC A := unfold fprintf_i_pre_s_stmt; intros; eapply fprintf_i_pre_s; try eassumption; [unfold A; lia | exact PC].
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Corollary fprintf_i_pre_usage : fprintf_i_pre_s_stmt FMT_USAGE 16. Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32002469942.66000001S".
fis printf_common_usage_spec FMT_USAGE. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Corollary fprintf_i_pre_cantopen : fprintf_i_pre_s_stmt FMT_CANTOPEN 20. Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45811522422.66000001S".
fis printf_common_cantopen_spec FMT_CANTOPEN. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Corollary fprintf_i_pre_readerr : fprintf_i_pre_s_stmt FMT_READERR 22. Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010>66268284310.66000001S".
fis printf_common_readerr_spec FMT_READERR. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC3.
