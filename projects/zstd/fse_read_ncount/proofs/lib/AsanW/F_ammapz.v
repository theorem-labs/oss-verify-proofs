(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase AKit AKit2 RT_stubs F_ammap.
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
Definition mmapz_entry := 0x663d8.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).
Section CANSEC2. Context {rc : runConstT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
fp_le RNG RNG' /\ fp_bw RNG'
/\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
/\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono asegs m m'
/\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
/\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
/\ rmap_cells m'.
#[using="Type"] Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
(FRESH : Z -> bool)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (size lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
mem_inv asegs m ->
a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
rmap_cells m ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
(forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
(forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
implS asegs RNG' (K a) (epostF Q) ms') ->
(forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
implS asegs RNG' (K a) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
implS asegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RSTK FROK UNR KONT.
pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM). word_range a1 A1R.
unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
eapply (implF_ebind _ _ _ _ _ _ _
(fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
\/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
mmapz_post RNG sp a size lo m RNG' m' /\
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))).
2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
eapply KONT; [exact FR | exact PO]. }
iprefix.
Local Ltac2 Set LiaHints.tbl := fun () => "03@0?10667180602.78 11490489838.75 11613226300.77 1162083360.80  1162083374.77  11805467289.72 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 11903774446.75 12119712956.76 12844062062.76 13219133678.75 14345671670.10214782759150.75 14866570234.74 14869079534.10216295403374.76 16473946862.78 16540621984.79 16540621996.73 16640242030.76 17657838574.78 17776320428.73 17778417576.10117976286208.2  1800609155.102 1800609155.74  18104477166.78 18105812974.75 18499304074.87 1863552366.76  18689773242.75 19506020846.75 19537406216.89 21411268654.74 21811810457.78 2190890265.76  22206135662.76 22219720579.76 22219720579.79 22389541692.72 22885694752.70 23505687086.74 2350913305.76  24468186791.76 24487705898.71 24559885228.75 24559885230.78 24638473347.10224689793902.74 2478755310.78  25071629079.10225878270253.74 25878270255.77 26015742015.89 27066288442.75 27408782881.79 27408782895.76 2772514414.78  27907155234.89 28417259964.74 28636712686.77 28859544046.74 29212037676.18 29448452775.76 29693776878.75 30231011258.76 31034701358.74 31378308326.66 31929422314.77 31940628442.68 31990679214.74 32099668718.78 32103103726.76 32300784295.78 32501562499.78 32501562499.81 33473183726.78 33680001082.75 33890036512.80 33890036526.77 33962954137.75 34122977177.78 34430152252.75 35082589626.76 35100153219.75 35100153219.76 35436073198.74 36107562391.92 36148814574.77 37729779438.76 37827660420.67 38162635894.10238534813827.75 38534813827.78 3888239342.75  39055981550.75 39058966403.76 39058966403.79 40069102958.74 40091925677.74 40091925677.75 40245254920.89 40333419028.88 40457739452.74 41535431150.72 42744733806.74 4288869222.89  43059266230.64 43679308552.89 43985854248.10143987951407.74 43988483203.10143988483203.72 44223460412.78 44464229507.78 44464229507.81 44647645960.89 45221239098.10245848756903.72 46382356647.75 46468661564.10246657085550.10247215438702.75 47291567726.75 4751458172.69  48945323886.76 49649769127.75 49725372071.75 49978085870.10250244754108.76 50346867566.76 50357606254.77 50569832494.74 51509148455.74 51678667180.75 51678667182.78 51711223320.88 52105090727.74 53767577772.73 53769674920.10153791967854.72 54243526019.10254243526019.74 54352578414.76 56241442027.10156255680316.78 563227834.74   56759370246.7  56763417884.86 56765693756.89 56765693885.88 56771238972.10256771238972.10356912526318.72 57496811886.78 57745675194.74 58512233326.74 58776000537.75 59308628179.4  59314873579.7  59608349294.75 59989976054.10160077573358.77 60537240323.74 60537240323.80 60858483367.1026094239292.75  61628829678.72 6165337146.77  61988516505.77 62283267516.75 62923854958.75 63235321891.10063235321901.71 63305555623.74 63341493050.78 64135124206.78 64997134979.10264997134979.75 65088762478.74 65104334021.87 65106320572.3  65217526774.79 65704139943.77 66021542019.77 66021542019.80 66423386478.74 6642473454.72  66656729710.74 6676984046.78  67134106962.10267643606599.69 67943285742.10268343577710.75 7735119015.78  802261998.102  8390799470.75  8405736896.102 8405736896.103 8583720762.72  8684881006.74  8874890888.89  9055284462.77  9107720828.74  00000500>00B00F00J00K00L00M00N00O00P00Y00]00f00o01001901>01G01P01Y01]01a01j02302702;02A02B02C02L02U02V02_02d02m03203;03<03=03F03G03H03L03P03Y03Z03[03\03`03d03e03n04704804<04@04M04R04V04Z04c04g04k05405=05J05K05T05Y05b05c05l06506>06G06P06Q06R06S06\06a06e06i06j06k06o07407507607?07F07O07X07\07]07^07_07h08108208308<08@08D08I08N08R08[08d08e08i08n09209609709809<09=09>09C09H09I09J09N09W09`09i09j0:30:40:50:>0:B0:K0:T0:]0:^0:b0:f0:g0:h0:l0;00;90;:0;;0;D0;H0;L0;Q0;a0;o0<70<E0<M0<U0<^0<g0<l0=50=60=C0=X0=a0=b0=k0=l0=m0=n0>20>;0>@0>A0>E0>N0>R0>V0>W0>\0>e0>f0>g0?00?90?B0?C0?D0?E0?F0?O0?X0?a0?j0@<0@=0@F0@O0@P0@Y0@b0@c0@d0@i0A20A70A@0ADS3SPRS4CEIL2LOS2HBS2LOS2LOSSSSSSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS4SPOSSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS3SPRS4CEIL2LOS3AIMS4CEIL2LOSSS4CEIL2LOSSS2HBS2LOS4CEIL2LOSSSS2LOS2LOSS4CEIL2LOS4CEIL2LOSS2LOS2LOS4CEIL2LO3AM3S3SPRS2LOS2LOS4CEIL2LOS2LOS2HBS4CEIL2LOS4CEIL2LOS3SAL1H2H02H4SS4CEIL2LOS3SPRS4CEIL2LOSS4SPOS2SZS4SPOS2SZS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS3SPRS2LOS2LOSSS2HBS3SPRSSS4CEIL2LOS3AIM1HS4CEIL2LOS4CEIL2LOS2LOSSSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS2LOS2LOS3AIMS3AM3S2HBS4CEIL2LOS4CEIL2LOSS2LOS3AIMS2LOS2LOSSS2HBSSS3AIMS3SPRSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2LOS2LOSSS2LOS2LOS4CEIL2LOSSS4CEIL2LOS2LOS2HBS3SPRS4SPOS3AM23AM31HS4SPOS3AM23AM3S3AM22K1S4SPOS3AM23AM3S3AM22K1S3AM22K1S4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOSS4NAME3A1R2K0S4SPOS3AM32K11H2LT2K2S4CEIL2LOSS4CEIL2LOSSSS2HBS4CEIL2LOS3SPRSS2HBS4CEIL2LOS2LOS2LOSS3SPRS4CEIL2LOSSS4CEIL2LOS4SPOS2SZS4SPOS2SZSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO4SPOS3AM3SS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOFFS3SPRS4CEIL2LOS3AIMS4CEIL2LOS2HB".
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
replace (ret_pc (Z_to_bv 64 418912)) with (Z_to_bv 64 418912 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
apply evtF_done. right. split; [reflexivity|].
do 15 eexists. split. 2: reflexivity.
unfold mmapz_post.
split; [exact FPLE|]. split; [exact BW|]. split; [exact AM1|]. split; [exact AM2|]. split; [exact AM3|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|].
unfold rmap_cells. repeat (split; [assumption|]). assumption.
Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rmapd_entry := 0x6eba8.
#[using="Type"] Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
mem_inv asegs m ->
a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
rmap_cells m ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
(forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
(forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' ->
implS asegs RNG' (K addr) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
unfold rmapd_entry in *. word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
eapply (implF_ebind _ _ _ _ _ _ _
(fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' /\
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))).
2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
eapply KONT. exact PO. }
iprefix.
step. step. step. step.
step. step. step.
Local Ltac2 Set LiaHints.tbl := fun () => "03Y0>10667180602.7511490489838.7211805467289.6911805467289.7111805467289.7211805467289.7311805467289.7512352412732.7212844062062.7315107956284.751543849006.93 15813913888.7615813913902.7416290529959.7216295403374.7316395817388.8016473946862.7516640242030.7316643491566.6917151130279.7217292611950.7117657838574.751772731779.73 1772731779.75 17776320428.7017778417576.9217976286208.2 17995455655.7118104477166.7518105812974.7318363204284.711863552366.73 18689773242.7318848698606.7218890355993.7318900419239.7519376804346.9319391258279.7319506020846.7219625521020.9319970277031.712003044974.71 20447870595.7520447870595.7720633589486.722099171026.71 2124193155.71 2124193155.91 21456922734.7122102740889.7522163107130.7222206135662.7322591915566.9324179267756.7224179267758.7424365389228.8024390924092.6924409718067.7124630998586.722478755310.75 25071629079.9325255714158.7226115614154.9326346213514.7826494020268.8027066288442.7227408782893.7127408782895.7327624344046.722772514414.75 27730847314.7127911502958.7128636712686.7528830049838.9329212037676.2029693776878.7230023022247.7330196181434.7130231011258.7330403814844.713071671100.75 30890730486.9331287922286.71315996476.72  31929422315.7331940628442.6532099668718.7532103103726.7332127996803.7132127996803.9332431485806.7132651489978.7133473183726.7534417933740.7234417933741.7134924112160.6635082589626.7335111703823.7135111703823.7635153358318.7236107562391.8336113525291.9336115622447.7136148814574.7536180999398.6336590710439.7337729779438.7337844949358.713787933806.71 38687199342.7139055981550.7239129884846.9339571573379.7539571573379.7742085054489.7342236688921.7342501437472.9342501437472.9442503534630.7042505299482.6542509314849.7742511604512.8042511604641.7942775782659.9342817538363.8042831019478.7143059266230.614339538087.72 43413664432.7143985854248.9243987951407.71446960878.69  4472014211.72 4472014211.73 45352467587.7545352467587.7746232973498.7146895624871.7547196384886.9347291567726.7347296502915.7247296502915.7448945323886.7349288693539.8050346867566.7350357606254.7550362574674.7150645511577.7550647975150.7251124399687.665114850435.72 5114850435.93 5120733337.72 51840259694.715289276057.75 53767577772.7053769674920.9254160885230.7154352578414.7354688491502.7255188037614.7255442533998.7155530626798.725575378976.76 5575378990.74 55770193284.6456050883492.1356702368758.7556759370246.7 56779838332.6557496811886.7558762852128.7658762852142.7459012487214.9359192637571.6959192637571.9259314873579.7 59314873579.8 59410257006.7259608349294.7359758911548.7559970707310.6960077573358.7560357415926.9260511482402.8061254491452.7261305990311.696165337146.75 61917199008.9061917199020.7062145070432.7562145070444.7062302209411.7162302209411.9362923854958.736299892651.92 63235321891.9163235321901.686326792124.71 63341493050.7564135124206.7564896830119.7565104334021.7865104452412.5 65769723580.7365805175866.6965806924526.6965977411438.7166330498732.7266330498734.7466680029612.8066747928658.716676984046.75 67284288444.7367471419575.7967777981223.9367800019075.7267800019075.9468156076782.7168309604434.7168343577710.7368685913326.696897720302.71 7130566823.71 7600465283.73 7600465283.75 8390799470.72 8405736896.93 8405736896.94 9055284462.75 9099241916.73 945059608.79  9492323756.80 00000500>00?00@00A00B00C00G00P00T00]00a00e00f00o01301<01E01N01O01X01a01b01c01g01k02102202;02D02H02Q02V02_02`02a02f02g03003403503>03?03@03I03R03S03T03]03^03c03l04504904=04A04E04F04K04T04U04^05005105505:05>05B05K05T05]05f05o06806E06N06O06T06Y06]06a06b06k06o07<07I07R07[07\07]07f07k08408808<08@08E08F08G08P08V08Z08^08g08h08i09209;09D09M09V09_09`09a09b09c09j0:10:>0:K0:X0:_0:l0:m0:n0;30;70;80;<0;@0;D0;M0;N0;O0;P0;Q0;V0;W0;X0;a0;b0;c0;l0<90<B0<K0<T0<U0<^0<_0<`0<a0<b0<k0<l0=00=40==0=F0=O0=X0=a0=j0=n0>20>60>;0><0>L0>M0>V0>Z0>^0>g0>h0>i0?80?J0?S0?\0?`0?i0@20@30@70@;0@<0@A0@E0@I0@M0@Q0@R0@S0@\0@`0@d0@h0@l0A10A:0A;0AH0AU0AY0A^0Ag0B00B40B80B<0BE0BN0BR0BW0BX0BY0BZ0Bc0Bl0C50C>0CG0CH0CI0CJ0CS0CT0CU0C^0Cb0Cc0CgS3SPRS4CEIL2LOSSSSSS2HBS4CEIL2LOS2HBS4CEIL2LOS2LOS2LOSS4CEIL2LOS2A0S4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSS2LOS2LOS4SPOSSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS3SPRS4CEIL2LOSSS3SPRSS4CEIL2LOS2HBSS4CEIL2LOSSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOSS3SPRS4CEIL2LOS4CEIL2LOS2LOS2LOS2A0S2HBSS3SPRS4CEIL2LOSS4CEIL2LOS4CEIL2LO4SPOS3AM3SS2A0S3SPRS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SAL1H2H02H4S4CEIL2LOSS3SPRS3SPRS2HBS2HBSS4CEIL2LOS2HBS4SPOS2A03ASZS4SPOS2A03ASZS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS3SPRS4CEIL2LOS2LOS2LOS2LOS3SPRSSS4CEIL2LOS2A01HS2LOS2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSSS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S4SPOS2A03AM3SSS3SPRS2LOSS2HBS2LOS2LOS4CEIL2LOSSSSS3SPRSSS4CEIL2LOSSS4CEIL2LOS4CEIL2LO3AM3S4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSSSS4CEIL2LOSS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS3AALSS4SPOS3AM23AM31HSS4CEIL2LOS2LOS2LOS4CEIL2LOSSS4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSS2LOS2HBSS3SPRS2LOS2LOS2LOS2LOSSS4CEIL2LOS2LOS2LOS2LOS2HBS3SPRS4CEIL2LOSS4SPOS2A03AM3S4SPOS2A03ASZS2HBS3SPRS4CEIL2LOS4CEIL2LOS2LOS2LOS2A0S4CEIL2LOS4CEIL2LOS2HBS3ASZSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOFFS4CEIL2LOS2HBSS2A0".
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
replace (ret_pc (Z_to_bv 64 420048)) with (Z_to_bv 64 420048 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
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
