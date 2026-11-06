(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase AKit AKit2 RT_stubs F_ammap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
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
Definition mmapz_entry := 0x662c4.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).
Section CANSEC2. Context {rc : runConstT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
fp_le RNG RNG' /\ fp_bw RNG'
/\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
/\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono bsegs m m'
/\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
/\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
/\ rmap_cells m'.
#[using="Type"] Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
(FRESH : Z -> bool)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (size lo : Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
mem_inv bsegs m ->
a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
rmap_cells m ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
(forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
(forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
implS bsegs RNG' (K a) (epostF Q) ms') ->
(forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
implS bsegs RNG' (K a) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
implS bsegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RSTK FROK UNR KONT.
pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM). word_range a1 A1R.
unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
eapply (implF_ebind _ _ _ _ _ _ _
(fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
\/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
mmapz_post RNG sp a size lo m RNG' m' /\
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs))).
2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
eapply KONT; [exact FR | exact PO]. }
iprefix.
Local Ltac2 Set LiaHints.tbl := fun () => "03@0?10667180602.78 11613226300.77 1162083360.80  1162083374.77  11805467289.72 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 12119712956.76 14866570234.74 16540621984.79 16540621996.73 16930578542.1021717300718.75  17776320428.73 17778417576.10117976286208.2  1800609155.102 1800609155.74  18689773242.75 19010102024.89 19147070446.78 19596407918.74 19622476014.75 21459134830.74 21632953838.78 21811810457.78 2190890265.76  21916162286.75 22007898888.89 22219720579.76 22219720579.79 22389541692.72 2268497582.74  22885694752.70 2350913305.76  23667722478.78 24468186791.76 24487705898.71 24559885228.75 24559885230.78 24638473347.10225071629079.10225792608750.72 2582348142.74  25878270253.74 25878270255.77 26015742015.89 26771530286.74 27066288442.75 27198656366.76 27408782881.79 27408782895.76 27907155234.89 28344324846.75 28417259964.74 28905040648.89 29212037676.18 29448452775.76 2952178542.75  29531591534.74 29870281326.74 30231011258.76 31086372590.77 31378308326.66 31929422314.77 31940628442.68 32300784295.78 32440122478.74 32501562499.78 32501562499.81 32716547054.10233680001082.75 33729650550.10133890036512.80 33890036526.77 33962954137.75 34122977177.78 3438046198.102 34430152252.75 34648577006.78 34673642734.77 35012330478.10235082589626.76 35100153219.75 35100153219.76 35938186734.75 36107562391.92 36508527854.77 37496806766.76 3750459246.76  37827660420.67 38138004598.79 38162635894.10238534813827.75 38534813827.78 39058966403.76 39058966403.79 39208223342.74 39363066990.75 40042239854.76 40091925677.74 40091925677.75 40333419028.88 40457739452.74 42092305134.78 4231308936.89  42426800622.72 42589343470.76 4262544750.76  4288869222.89  43059266230.64 43648940078.74 43985854248.10143987951407.74 43988483203.10143988483203.72 44223460412.78 44464229507.78 44464229507.81 44834901102.75 45221239098.10245848756903.72 46185173998.75 46382356647.75 46468661564.10246690469870.75 4721565934.74  47402774638.75 4751458172.69  48870803502.74 49649769127.75 49725372071.75 49802719470.78 50244754108.76 5087518190.102 51495512430.78 51509148455.74 51678667180.75 51678667182.78 51711223320.88 52105090727.74 52457006958.76 53767577772.73 53769674920.10154139164014.76 54243526019.10254243526019.74 54627154184.89 55182052846.78 56241442027.10156255680316.78 563227834.74   56759370246.7  56763417884.86 56765693756.89 56765693885.88 56771238972.10256771238972.10357204723438.77 57745675194.74 58776000537.75 58899613550.77 58995781614.72 59308628179.4  59314873579.7  59714667374.74 59972613898.87 60537240323.74 60537240323.80 60669017326.76 60858483367.1026094239292.75  6165337146.77  61988516505.77 62007472750.75 62283267516.75 62826138350.75 63235321891.10063235321901.71 6325400110.74  63305555623.74 63341493050.78 63473042798.76 64930771950.75 64997134979.10264997134979.75 65104334021.87 65106320572.3  65474045550.78 65704139943.77 66021542019.77 66021542019.80 66400913390.72 66410366446.10266864513518.74 67134106962.10267643606599.69 68141967982.75 7735119015.78  8405736896.102 8405736896.103 8539011822.78  8583720762.72  9107720828.74  9528707694.72  00000500900=00A00B00C00D00E00F00G00K00P00T00X00a00j00n01201801901:01?01D01M01V01_01h02102202302<02A02B02C02G02P02T02U02^02_02`02d02h02i02j03303<03@03D03Q03Z03_03h03l04004404=04A04F04S04T04]04f04o05405=05>05G05P05Q05Z05[05\05e05j05k05o06306406506606:06C06L06U06Z06[06\06e06l07507>07G07K07L07M07N07O07P07Q07Z07c07l08008408908=08F08K08T08]08f08g08k09409809<09=09>09B09C09D09M09R09S09\09]09a09j0:30:<0:=0:F0:G0:H0:Q0:U0:^0:g0:h0:l0;00;10;20;;0;?0;C0;L0;M0;N0;S0;\0;`0;d0;i0<90<G0<O0<]0<e0<m0=60=;0=<0=E0=N0=[0>00>90>:0>;0><0>E0>F0>J0>O0>P0>Y0>]0>f0>j0>n0?70?80?=0?F0?O0?P0?Q0?Z0?c0?l0?m0?n0?o0@80@A0@J0@\0@]0@f0@g0@h0@i0A20A70A;0ADS3SPRS2HBS2LOS2LOSSSSSSS2HBS3SPRS2LOS2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS4SPOSSSS3SPRS3AIMS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS3AIMSSS2HBS4CEIL2LOS2LOSS4CEIL2LOSSS2LOS2LOSSS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LO3AM3S4CEIL2LOS3SPRS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS2HBS3AIMS3SAL1H2H02H4SS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOSS4SPOS2SZS4SPOS2SZSS4CEIL2LOSSS4CEIL2LOS3SPRSS2LOS2LOSSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRSSS4CEIL2LOS3AIM1HS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOSSSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS3AM3S2HBS4CEIL2LOS3AIMS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2LOS4CEIL2LOS2LOS2LOSSS2HBSSS4CEIL2LOS3SPRSS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSS2LOS2LOSSS4CEIL2LOS2LOS2LOS4CEIL2LOSSS3AIMS4CEIL2LOS2LOS2HBS3SPRS4SPOS3AM23AM31HS4SPOS3AM23AM3S3AM22K1S4SPOS3AM23AM3S3AM22K1S3AM22K1S4CEIL2LOS3SPRSS4CEIL2LOS4CEIL2LOS4NAME3A1R2K0S4SPOS3AM32K11H2LT2K2S4CEIL2LOSSSS4CEIL2LOSS2HBS3SPRSS4CEIL2LOS2HBS4CEIL2LOS2LOS2LOS4CEIL2LOSS3SPRS4CEIL2LOS4CEIL2LOSSS4SPOS2SZS4SPOS2SZS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO4SPOS3AM3SS4CEIL2LOSFFS4CEIL2LOS3SPRS2HBS4CEIL2LO".
carve_frame 48%nat ST.
step. step. step. step. step.
step.
step. step. step.
step.
step. if_lit.
zstep. zstep. step. if_lit.
zstep. zstep. zstep. zstep.
setreg 9 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS SZ; Z.div_mod_to_equations; lia).
step. step. step. step. step.
step.
carve_frame 272%nat ST.
step. step. step. step. step. step. step. step.
step. step.
step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME A1R. lia. }
step. step. step. lstep.
zstep. step. if_lit.
zstep.
step. step. step. step. step. step. step. step. step.
release_frame FR0 ST (bv_unsigned sp + -48).
step. setreg 13 (Z_to_bv 64 34) ltac:(vm_compute; reflexivity).
step. step. step. step. step.
step.
icallk rt_mmap_stubP.
intros a RNG' ms' (rsp & HF & Hdec & ->).
destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
pose proof (fstepS_mmap_grant 0 size 34 _ RNG RNG' HF (eq_refl : Z.land 34 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS SZ; lia).
rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
pose proof HF as HF0. destruct HF0 as [[FPLE _] [_ BW]].
destruct (FRESH a) eqn:HFR.
2: { fstepS_transport HF. apply evtF_done. left. split; [reflexivity|]. split; [exact AM2|]. split; [exact AM1|]. split; [atop_facts; exact AM3| exact FPLE]. }
destruct (FROK a HFR AM2 AM3) as [AIM AFR].
fstepS_transport HF.
unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
replace (ret_pc (Z_to_bv 64 418636)) with (Z_to_bv 64 418636 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
apply (munch_weaken _ [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z) in MU.
2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
sys_mem_zeros.
step. step. step.
step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS. lia. }
zstep. step.
setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
step. step. step. step. step. step.
step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS. lia. }
zstep. step.
setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
step. if_lit.
step. step.
step. step. step. step. if_lit. step.
step. step. step. step. step. step. step.
lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
apply evtF_done. right. split; [reflexivity|].
do 15 eexists. split. 2: reflexivity.
unfold mmapz_post.
split; [exact FPLE|]. split; [exact BW|]. split; [exact AM1|]. split; [exact AM2|]. split; [exact AM3|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|].
unfold rmap_cells. repeat (split; [assumption|]). assumption.
Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rmapd_entry := 0x6ea94.
#[using="Type"] Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
mem_inv bsegs m ->
a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
rmap_cells m ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
(forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
(forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' ->
implS bsegs RNG' (K addr) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
implS bsegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
unfold rmapd_entry in *. word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
eapply (implF_ebind _ _ _ _ _ _ _
(fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' /\
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs))).
2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
eapply KONT. exact PO. }
iprefix.
step. step. step. step.
step. step. step.
Local Ltac2 Set LiaHints.tbl := fun () => "03Y0>10444057070.7210667180602.7511805467289.6911805467289.7111805467289.7211805467289.7311805467289.7512352412732.7212685940462.7213596006226.7115107956284.7515813913888.7615813913902.7416290529959.7216581074286.7217098239598.7117151130279.721717300718.72 17424134738.711772731779.73 1772731779.75 17776320428.7017778417576.9217976286208.2 17995455655.7118363204284.7118689773242.7318890355993.7318900419239.751892362350.71 19147070446.7519365467182.9319376804346.9319391258279.7319625521020.9319920749038.7219961167854.7219970277031.7120447870595.7520447870595.7720894983726.9320921468142.722124193155.71 2124193155.91 21632953838.7522102740889.7522117252524.8022163107130.7222242271214.7222652873582.7122749971310.7123667722478.7524179267756.7224179267758.7424390924092.6924409718067.7124451155438.7124578566572.8024630998586.7225025521262.7125071629079.9326115614154.9326227646574.7126436197998.7127066288442.7227198656366.7327408782893.7127408782895.7329212037676.2029322360558.7229409371564.8030023022247.7330196181434.7130231011258.7330403814844.713071671100.75 31086372590.7531521058898.71315996476.72  31929422315.7331940628442.6532127996803.7132127996803.9332651489978.7133227529838.7134417933740.7234417933741.7134648577006.7534673642734.7534924112160.6635082589626.7335111703823.7135111703823.7635938186734.7236107562391.8336113525291.9336115622447.7136180999398.6336508527854.7536590710439.7337496806766.733750459246.73 38442283758.7139363066990.7339530135918.7139571573379.7539571573379.7740042239854.7341099708142.6941317949302.9242085054489.7342092305134.7542236688921.7342501437472.9342501437472.9442503534630.7042505299482.6542509314849.7742511604512.8042511604641.7942589343470.734262544750.73 42775782659.9342817538363.8042831019478.7143059266230.614339538087.72 43413664432.7143985854248.9243987951407.714472014211.72 4472014211.73 44752146798.7144834901102.7345352467587.7545352467587.7746185173998.7246232973498.7146610241646.7146690469870.7346895624871.7547196384886.9347296502915.7247296502915.7447402774638.7247605026514.7149288693539.8049802719470.7550293387118.6950645511577.7551063395886.9351124399687.665114850435.72 5114850435.93 5120733337.72 51495512430.7552457006958.735289276057.75 53405636718.7153767577772.7053769674920.9254139164014.7355182052846.7555419944174.725575378976.76 5575378990.74 55770193284.6456050883492.1356759370246.7 56779838332.6557204723438.7558762852128.7658762852142.7458899613550.7559192637571.6959192637571.9259314873579.7 59314873579.8 59445865454.7159758911548.7560341225226.7860511482402.8060669017326.7361254491452.7261305990311.696165337146.75 61892124754.7161917199008.9061917199020.7061955427318.9362007472750.7362145070432.7562145070444.7062302209411.7162302209411.9362790826668.806299892651.92 63235321891.9163235321901.686326792124.71 63307181686.7563341493050.7563473042798.7363581907118.9364288695406.7264896830119.7564930771950.7265104334021.7865104452412.5 65474045550.7565769723580.7365805175866.6966330498732.7266330498734.7467284288444.7367471419575.7967642860590.9367777981223.9367800019075.7267800019075.9468141967982.736867211502.69 7130566823.71 7600465283.73 7600465283.75 778093996.80  8405736896.93 8405736896.94 8539011822.75 8939781870.69 9099241916.73 9144120558.69 945059608.79  00000900>00?00@00A00B00C00G00P00Y00]00a00e00f00o01801901B01K01L01M01Q01U01[01\01`01e01f01g02002902B02G02H02L02U02^02_02`02a02j03303403503>03?03C03H03Q03Z03c03l04004404804904B04F04K04T04U04g05005905>05G05K05O05\05e05i05j05o06406806<06E06N06R06_06l06m06n07307<07@07D07M07V07Z07_07`07a07j08008408808908B08C08L08U08^08g09009109209;09D09E09F09O09P09W09^09k0:80:E0:L0:Y0:b0:k0:l0:m0;20;60;70;;0;?0;C0;D0;E0;N0;W0;X0;Y0;b0;g0<00<90<:0<;0<<0<=0<F0<O0<\0<e0<n0<o0=80=90=:0=;0=<0=E0=N0=O0=X0=\0=`0=i0>20>;0>?0>C0>G0>L0>\0>]0>f0>j0>n0?70?80?90?H0?Z0?c0?g0?h0?l0@50@90@:0@?0@H0@L0@P0@Q0@Z0@^0@b0@c0@d0@h0@l0A00A40A80A90A>0AG0AP0AY0AZ0Ac0B00B=0BF0BJ0BO0BS0BW0B[0B`0Bi0Bj0Bk0Bl0C50C>0C?0C@0CA0CE0CF0CG0CP0CY0C]0Cf0CgS4CEIL2LOS3SPRSSSSSS2HBS4CEIL2LOS4CEIL2LOS2HBS2LOS2LOSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSS2LOS2LOS4SPOSSS2HBS3SPRSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRSS2HBS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOSS2A0S3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS2HBSS4CEIL2LOS2A0S3SPRS4CEIL2LOSS4CEIL2LO4SPOS3AM3S4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS2LOS2LOS3SAL1H2H02H4S4CEIL2LOS2A0SS3SPRS3SPRS2HBS2HBS4CEIL2LOS4CEIL2LOS2HBS4SPOS2A03ASZS4SPOS2A03ASZSSS3SPRS4CEIL2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS2LOS3SPRSSS4CEIL2LOS2A01HS2LOS2LOSS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOSS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S4SPOS2A03AM3S4CEIL2LOS4CEIL2LOSSS3SPRS2LOSS2HBS2LOS2LOSSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LO3AM3S4CEIL2LOS4CEIL2LOSS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS3AALS4SPOS3AM23AM31HSS4CEIL2LOS2LOS2LOS4CEIL2LOSSS4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S4CEIL2LOS2HBSS2LOS4CEIL2LOS2HBSS3SPRS4CEIL2LOS2LOS2LOSS4CEIL2LOS2LOS2LOSSS2A0S2LOS2LOS2LOS2HBSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4SPOS2A03AM3S4SPOS2A03ASZS4CEIL2LOS2HBS3SPRS2LOS2LOS2HBS3ASZS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOSSSS2A0FFS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS".
carve_frame 96%nat ST.
step. step. step. step. step. step. step.
step. step. step.
step. step. step.
step. step. if_lit.
zstep. zstep. step. if_lit.
zstep. zstep. zstep. zstep.
setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
step. if_lit.
zstep.
setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
step. step. step. step. step.
step.
carve_frame 272%nat ST.
step. step. step. step. step. step. step. step.
step. step.
step. if_lit.
zstep.
step. step. step. step. step. step. step. step. step.
release_frame FR0 ST (bv_unsigned sp + -96).
step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).
step. step. step. step. step.
step.
icallk rt_mmap_stubP.
intros a RNG' ms' (rsp & HF & Hdec & ->).
destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
pose proof (fstepS_mmap_grant addr size 50 _ RNG RNG' HF (eq_refl : Z.land 50 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS ASZ A0; lia).
rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
pose proof HF as HF0. fstepS_transport HF.
destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
replace (ret_pc (Z_to_bv 64 419772)) with (Z_to_bv 64 419772 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
apply (munch_weaken _ [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
sys_mem_zeros.
step. step. step.
step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }
zstep. step.
setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
step. step. step. step. step. step.
step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
zstep. step.
setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
step. if_lit.
step. step.
step. step. step. step. if_lit. step.
step. step. step. step. step. step. step. step. step.
lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
apply evtF_done. right. split; [reflexivity|].
do 15 eexists. split. 2: reflexivity.
unfold rmap_postD. destruct HF0 as [[FPLE _] [_ BW]].
split; [exact FPLE|]. split; [exact AM3|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
unfold rmap_cells. repeat (split; [assumption|]). assumption.
Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
