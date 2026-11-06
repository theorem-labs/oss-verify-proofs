(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit.
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
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma asan_inited_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem),
rw_cells asegs m 0xa3158 [C1 (Z_to_bv 8 1)] ->
rng_aimg RNG ->
evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59080) fc None m (seg_rom asegs)).
Proof.
intros until m. intros INI RIMG.
do 6 step. apply evtF_done. reflexivity.
Qed.
#[using="Type"] Lemma get_current_thread_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (ctx t lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
rw_cells asegs m 0xa1ce0 [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m 0xa1ce4 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] ->
rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
0 < ctx -> ctx + 4096 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 ->
evtF asegs RNG (fun ms' => exists a1' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5c790) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> TI TK T88 TSD CT C0 C1 RIMG RSTK RCTX.
unfold ATP, ATP88, ATSD in *.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "00H0>10345787758.6211805467289.6214869079534.621670727951.58 20433961190.5623488737418.5831399144472.5732600174396.6237317216127.623828146333.58 43059266230.5444185318113.6645221239098.6245381151734.6246134254574.6254164510851.6254164510851.6459314873579.5960320050063.6561482382924.5861674577390.6263235321901.6163235321901.6367081926311.6200000900:00C00J00K00L00M00Q00]00a00e00f00j00k01401501601<01=01>01G01K01O01PS4CEIL2LOSS4CEIL2LOS2C02C1SSSS2HBS4CEIL2LO2C1S2LOS2LOSS2HBSS4CEIL2LOSSS2C01KSSS4CEIL2LOS2LOS2LOS".
carve_frame 16%nat ST.
do 3 step.
do 4 step. if_false.
lstep. step.
do 7 lstep.
step. if_cases K; zify_cond K; [exfalso; lia|]. step.
do 3 step.
release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stack_top_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (t top bot : Z),
mem_inv asegs m ->
a0 = Z_to_bv 64 t ->
rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> t + 4096 <= ATOP ->
rng RNG t 4096 ->
evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5c954) fc None m (seg_rom asegs)).
Proof.
intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>12881681230.4823050724945.5828633426269.5729930635003.5729945897162.4830593954605.5534781285532.4835665276497.4939224602138.4847414121168.5462378699483.5767680999039.5700000400500600@00J00K00L00M00N00O00Y00ZS2BTSSS2B02BT2TTS2B02BT2TTSSSSSS2B02BT2TTF".
lstep. step. step. if_lit.
do 2 step.
do 3 zstep.
rewrite (sel_mask_true (bot <? top) top) by (first [apply Z.ltb_lt; lia | lia]).
step. apply evtF_done. eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stack_bottom_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (t top bot : Z),
mem_inv asegs m ->
a0 = Z_to_bv 64 t ->
rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
0 <= bot -> bot < top -> top <= 2^47 -> 0 <= t -> t + 4096 <= ATOP ->
rng RNG t 4096 ->
evtF asegs RNG (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 bot) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5c9ac) fc None m (seg_rom asegs)).
Proof.
intros until bot. intros MI -> TB SW B0 BT TT T0 TC RT. atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>12881681230.4823050724945.5828633426269.5729930635003.5730593954605.5534781285532.4835665276497.4939224602138.4847414121168.5462378699483.5762392661226.4867680999039.5700000400500600@00A00B00C00D00E00O00Y00ZS2BTSSS2B02BT2TTSSSSSS2B02BT2TTS2B02BT2TTF".
lstep. step. step. if_lit.
do 2 step.
do 3 zstep.
rewrite (sel_mask_true (bot <? top) bot) by (first [apply Z.ltb_lt; lia | lia]).
step. apply evtF_done. eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma uchain_invalid_nil : forall m top pc p f k tr,
uchain m top pc p f k tr -> ~ (p < f /\ f < top - 16 /\ f mod 8 = 0 /\ (0 < k)%nat) -> tr = [].
Proof. intros m top pc p f k tr H Hn. destruct H; [reflexivity| exfalso; apply Hn; auto | exfalso; apply Hn; auto]. Qed.
Definition uwf_post (S pc top spf : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word)
(gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(size : nat) (tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists a2' a5' a6' a7' m' tb',
ms' = MS (mkR raf (Z_to_bv 64 (spf + 64)) gp tp t0 t1 t2 s0f s1f
(Z_to_bv 64 S) (Z_to_bv 64 pc) a2' (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) a5' a6' a7'
s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc raf) fc None m' (seg_rom asegs)
/\ munch [(S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size + Z.of_nat (length tr)))]
/\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
/\ (forall i, (i < size)%nat -> nth_error tb' i = nth_error tb i)
/\ map bv_unsigned (firstn (length tr) (skipn size tb')) = tr.
End CANSEC1.
Local Ltac uwf_epilogue := do 10 step.
Local Ltac uwf_tail IH HC size tb :=
let K3 := fresh "K3" in let K4 := fresh "K4" in let K5 := fresh "K5" in let Etr := fresh "Etr" in
let AL2 := fresh "AL2" in let NA2 := fresh "NA2" in
step; if_cases K3; zify_cond K3;
[ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
| step; if_cases K4; zify_cond K4;
[ pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue
| do 2 zstep; step; if_cases K5; zify_cond K5;
[
assert (AL2 : _ mod 8 = 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5)
| assert (NA2 : _ mod 8 <> 0) by (change 7 with (Z.ones 3) in K5; rewrite Z.land_ones in K5 by lia; exact K5);
pose proof (uchain_invalid_nil _ _ _ _ _ _ _ HC ltac:(lia)) as Etr; rewrite Etr in *; uwf_epilogue ] ] ].
Local Ltac all_exits_post MU WM SZC TB LTB :=
apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|];
split; [cbn [length app]; rewrite ?Z.add_0_r; exact SZC|]; split; [exact TB|]; split; [exact LTB|];
split; [intros; reflexivity| reflexivity].
Local Ltac push_exits_post MU WM SZC TB LTB size :=
apply evtF_done; unfold uwf_post; do 6 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [assumption|];
split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat 1) with (Z.of_nat (Datatypes.S size)) by lia; exact SZC |];
split; [exact TB|]; split; [rewrite upd_length; exact LTB|];
split; [let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply nth_error_upd_other; lia|];
cbn [length app]; rewrite skipn_upd_here by lia; cbn [firstn map]; rewrite unsigned_lit by lia; reflexivity.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma uwf_loop : forall m0 top pc prev frame k tr,
uchain m0 top pc prev frame k tr ->
forall RNG (gp tp t0 t1 t2 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : amem)
(S spf lo : Z) (raf s0f s1f s2f s3f s4f s5f s6f : word) (size : nat) (tb : list word),
(forall i, frame - 16 <= i < top -> m (wa i) = m0 (wa i)) ->
mem_inv asegs m ->
prev < frame -> frame < top - 16 -> frame mod 8 = 0 ->
Z.of_nat size + Z.of_nat k = 30 -> length tb = 255%nat ->
rw_cells asegs m (S + 8) [C4 (Z_to_bv 64 (Z.of_nat size))] ->
u64arr asegs m (S + 16) tb ->
rw_cells asegs m spf [C8 s6f; C8 s5f; C8 s4f; C8 s3f; C8 s2f; C8 s1f; C8 s0f; C8 raf] ->
ATOP <= lo -> lo <= spf -> spf + 64 <= S -> S + 2072 <= frame -> top <= 2^47 -> 0 <= pc < 2^64 ->
rng RNG lo (top - lo) ->
evtF asegs RNG (uwf_post S pc top spf raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc size tb tr m)
(MS (mkR raf (Z_to_bv 64 spf) gp tp t0 t1 t2 (Z_to_bv 64 30) (Z_to_bv 64 (top - 16))
(Z_to_bv 64 S) (Z_to_bv 64 pc) (Z_to_bv 64 frame) (Z_to_bv 64 4096) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (Z.of_nat size)) a6 a7
(Z_to_bv 64 APGSZ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x738a0) fc None m (seg_rom asegs)).
Proof.
intros m0 top pc prev frame k tr H.
induction H as [prev frame k Hn | prev frame k fp rav H1 H2 H3 H4 B1 B2 Hra
| prev frame k fp rav tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH];
intros until tb; intros AG MI PF FT AL SK LTB SZC TB FR CEIL LOS SPS SPV TOP PC RR; unfold APGSZ in *.
-
Local Ltac2 Set LiaHints.tbl := fun () => "02I0?1382808063.92  15663904246.10115663904246.85 15663904246.86 15663904246.88 16343469883.76 16343469883.80 16343469883.81 16343469883.86 16343469883.87 18583298732.63 19516957492.85 20653787124.92 21067153625.81 21905600206.92 24387043777.83 24387043777.84 24387043777.86 24982578229.82 24982578229.83 25069844013.82 25071629079.92 25741009379.99 26368353420.91 27483488978.84 28089145306.81 28089145306.82 28971349255.71 28971349255.81 28971349255.88 28971349255.89 28971349255.90 28971349255.91 28971349255.92 29782367974.82 29782367974.83 29782367974.84 31541494890.83 31541494890.84 31541494890.86 31541494890.99 31547849040.80 31547849169.74 31547849169.79 34847714694.72 34847714694.82 34847714694.89 34847714694.90 34847714694.91 34847714694.92 34847714694.93 35253806554.83 35253806554.84 35253806554.86 35253806554.99 35808729858.82 36195068176.81 36326404376.82 40491529500.92 41284834327.72 41284834327.82 41284834327.89 41284834327.90 41284834327.91 41284834327.92 41284834327.93 42665077102.79 42831019478.92 43910933382.72 43910933382.82 43910933382.89 43910933382.90 43910933382.91 43910933382.92 43910933382.93 44377876869.92 45085165190.72 45085165190.82 45085165190.89 45085165190.90 45085165190.91 45085165190.92 45085165190.93 49702710056.82 49953495276.82 51699189033.99 54013143093.10155741588583.89 55744329939.64 55744329939.73 55744329939.77 56132021948.82 56503047610.81 56503047610.82 56503047610.83 56503047610.84 56503047610.85 57622410744.86 57622410744.87 58405661021.85 59125726983.71 59125726983.81 59125726983.88 59125726983.89 59125726983.90 59125726983.91 59125726983.92 59219614523.81 59314873579.65 59314873579.74 59314873579.75 59314873579.78 59314873579.80 59704698465.82 59704698465.83 61454732420.70 61454732420.80 61454732420.87 61454732420.88 61454732420.89 61454732420.90 61454732420.91 61700344799.92 61816264330.81 62862332548.84 62862332548.85 63415094134.90 63415094134.91 644747271.71   644747271.81   644747271.88   644747271.89   644747271.90   644747271.91   644747271.92   66260016006.86 66260016006.87 66343263023.93 66898818500.82 67118017411.85 67463309166.74 67463309166.78 67660570899.80 67660570899.81 8140247284.71  8140247284.81  8140247284.88  8140247284.89  8140247284.90  8140247284.91  8140247284.92  9982036214.84  9982036217.88  00000100=00D00K00R00Y00`00g00n01501901@01E01f01k01o02302702802902@02A02J02Z02[03403M03`04004@04P04`05005@05A05B05C05H05M05R05W05\05a05f06906I06Y06i07907I07Y07d07o08:08J08R08V08g08l09009109209309409509609709;09N09^09n0:>0:N0:^0:n0:o0;B0;R0;b0<20<B0<R0<b0=40=?0=H0=T0=Z0=^0=e0=l0>00>70>A0>H0>X0>h0?30?>0??0?R0?b0@20@B0@R0@b0A20A60AS0B30BB0Bb0C10C<0CG0CZ0Cj0D:0DJ0DZ0Dj0E:0E>0EB0EJ0ER0Eb0F20FE0FU0Fe0G50GE0GU0Ge0HC0Ha0I70I;0I<0I=0I>0IW0J00JC0JS0Jc0K30KC0KS0Kc0L30LCSS2H44LTB'2HiS2H42HiS2H42HiS2H42HiS2FT2HiS2FT2HiS2FT2HiS2K32HiS2K32HiS2SKS2H42SKS3SPVS2H42AL3LTB4CEIL3LOS3SPS3SPV2K21HS3SPSS2H4S2H4S2H4SSS2H42SKSS2H44LTB'S2FT3LOS3SPS3SPVFS2FT4CEIL3LOS3SPS3SPV3TOPS2FT4CEIL3LOS3SPS3SPV3TOPS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVSSSS3HraS3HraS3HraS3HraS3HraS3HraS3HraS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2H42SK3LTBS2H42SK3LTBS2H42SK3LTBS2H42SK3LTB4LTB'S2H43SPSS2H4S2H44CEIL3LOS3SPSS3LTBS2SKSSSSSSSS2HBS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVSS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2H42FT2SK3SPV3TOPS2H42SK3SPVS2H44LTB'S2H44LTB'2HiS2H41KS2SKS2H42SKS2H42SKS2H4S2H42K3S2H42K42K3S2H42K4S2H43Hfp3LTB3NA2S2H43Hfp3LTB3NA2S3SPV2K32HiS3SPV2K32HiFS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2K2S2SK3LTB4CEIL3LOS3SPS3SPV1K1HS2H42SK3LTB4CEIL3LOS3SPS3SPV1K1HS2H43Hra3LTB2K1S2H42SK3LTB4CEIL3LOS3SPS3SPV1K1HS2H43Hra3LTB2K1S2H42SK3LTBS2H42SK3LTBS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2HBS2H4S3SPV2K3S3SPV2K3S2H23LOS3SPS3SPVS2H23LOS3SPS3SPVS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS4CEIL3LOS3SPS3SPV3TOP2K32Hi1HS4CEIL3LOS3SPS3SPV3TOP2K32Hi1HS2H42FT2SK3LOS3SPS3SPVS2H4FSSS2FT4CEIL3LOS3SPS3SPV3TOPS2FT4CEIL3LOS3SPS3SPV3TOPS2FT2SK3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2FT3LOS3SPS3SPVS2H23LOS3SPS3SPVS2H23LOS3SPS3SPV".
assert (K0 : k = 0%nat) by (destruct k; [reflexivity| exfalso; apply Hn; repeat split; auto; lia]). subst k.
pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. if_cases K; zify_cond K; [| exfalso; lia].
uwf_epilogue.
apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
split; [intros; reflexivity| reflexivity].
-
pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. if_cases K; zify_cond K; [exfalso; lia|].
assert (B2' : bytes_at asegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
{ eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
pose proof (bytes_at_read8 _ _ _ B2') as R2.
step. clear R2 B2'.
step. if_cases K1; zify_cond K1; [| exfalso; lia].
uwf_epilogue.
apply evtF_done. unfold uwf_post. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [cbn [length]; rewrite Z.add_0_r; exact SZC|]. split; [exact TB|]. split; [exact LTB|].
split; [intros; reflexivity| reflexivity].
-
pose proof (munch_refl [(S + 8, S + 12); (S + 16, S + 2056)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. if_cases K; zify_cond K; [exfalso; lia|].
assert (B2' : bytes_at asegs m (frame + -8) (le8 (Z_to_bv 64 rav))).
{ eapply bytes_at_agree; [replace (frame + -8) with (frame - 8) by lia; exact B2|].
intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
assert (B1' : bytes_at asegs m (frame + -16) (le8 (Z_to_bv 64 fp))).
{ eapply bytes_at_agree; [replace (frame + -16) with (frame - 16) by lia; exact B1|].
intros i Hi. rewrite length_le8 in Hi. apply AG. lia. }
pose proof (bytes_at_read8 _ _ _ B2') as R2.
step. clear R2 B2'.
step. if_cases K1; zify_cond K1; [exfalso; lia|].
step. if_cases K2; zify_cond K2.
+
replace (rav =? pc) with true in * by (symmetry; apply Z.eqb_eq; lia).
pose proof (bytes_at_read8 _ _ _ B1') as R1.
step. clear R1 B1'.
uwf_tail IH HC size tb.
*
all_exits_post MU WM SZC TB LTB.
* all_exits_post MU WM SZC TB LTB.
*
eapply evtF_mono.
{ lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
size tb) end.
all: try eassumption; try lia.
intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia]. }
intros ms' PO. cbn [app] in *. exact PO.
* all_exits_post MU WM SZC TB LTB.
+
replace (rav =? pc) with false in * by (symmetry; apply Z.eqb_neq; lia).
do 3 zstep.
step.
rewrite (Z.shiftl_mul_pow2 (Z.of_nat size) 3) by lia. change (2^3) with 8.
replace (S + 16 + Z.of_nat size * 8) with (S + 16 + 8 * Z.of_nat size) by lia.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (u64arr_store_ok asegs mm (S + 16) tb (Z.of_nat size) (wa (S + 16 + 8 * Z.of_nat size)) TB ltac:(lia) eq_refl) as SOK end.
step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
pose proof (u64arr_write asegs mm (S + 16) tb (Z.of_nat size) (Z_to_bv 64 rav) TB ltac:(lia)) as TB2 end.
clear TB. store_done. rename TB2 into TB.
pose proof (bytes_at_read8 _ _ _ B1') as R1.
step. clear R1 B1'.
replace (Z.of_nat size + 1) with (Z.of_nat (Datatypes.S size)) in * by lia.
replace (Z.to_nat (Z.of_nat size)) with size in TB by lia.
uwf_tail IH HC (Datatypes.S size) (upd tb size (Z_to_bv 64 rav)).
* push_exits_post MU WM SZC TB LTB size.
* push_exits_post MU WM SZC TB LTB size.
* eapply evtF_mono.
{ lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (IH RNG gp tp t0 t1 t2 _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm S spf lo raf s0f s1f s2f s3f s4f s5f s6f
(Datatypes.S size) (upd tb size (Z_to_bv 64 rav))) end.
all: try eassumption; try lia.
- intros i Hi. transitivity (m (wa i)); [apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia | apply AG; lia].
- rewrite upd_length. exact LTB. }
intros ms' PO. unfold uwf_post in PO |- *.
destruct PO as (a2' & a5' & a6' & a7' & m' & tb' & -> & MU' & WM' & MI' & SZ' & TB' & LTB' & OLD & NEW).
exists a2', a5', a6', a7', m', tb'. split; [reflexivity|].
split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
split; [cbn [length app]; replace (Z.of_nat size + Z.of_nat (Datatypes.S (length tr))) with (Z.of_nat (Datatypes.S size) + Z.of_nat (length tr)) by lia; exact SZ'|].
split; [exact TB'|]. split; [exact LTB'|]. split.
{ intros i Hi. rewrite (OLD i) by lia. apply nth_error_upd_other. lia. }
cbn [length app]. rewrite (skipn_S_nth tb' size (Z_to_bv 64 rav)).
2:{ rewrite (OLD size) by lia. apply nth_error_upd_here. lia. }
cbn [firstn map]. rewrite unsigned_lit by lia. f_equal. exact NEW.
* push_exits_post MU WM SZC TB LTB size.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition unwind_fast_post (S pc top : Z) (sp : word) (raf s0f s1f s2f s3f s4f s5f s6f : word)
(gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z)
(tb : list word) (tr : list Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists a2' a3' a4' a5' a6' a7' m' tb',
ms' = MS (mkR raf sp gp tp t0 t1 t2 s0f s1f
(Z_to_bv 64 S) (Z_to_bv 64 pc) a2' a3' a4' a5' a6' a7'
s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc raf) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
/\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
/\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr.
#[using="Type"] Lemma unwind_fast_spec : forall RNG (raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : amem) (S pc bp top bot lo : Z) (tb : list word) (tr : list Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= S ->
mem_inv asegs m ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 top -> a4 = Z_to_bv 64 bot -> a5 = Z_to_bv 64 30 ->
rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
(exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
uchain m top pc bot bp 29%nat tr ->
0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2072 <= bp -> 0 <= pc < 2^64 ->
rng_aimg RNG -> rng RNG lo (top - lo) ->
evtF asegs RNG (unwind_fast_post S pc top sp raf s0f s1f s2f s3f s4f s5f s6f gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo tb tr m)
(MS (mkR raf sp gp tp t0 t1 t2 s0f s1f a0 a1 a2 a3 a4 a5 a6 a7 s2f s3f s4f s5f s6f s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x737e0) fc None m (seg_rom asegs)).
Proof.
intros until tr. intros ST CEIL LO SPS MI -> -> -> -> -> -> GPG PG [szj SZC] TB LTB UC B0 BB BT BA TOP SB PC RIMG RR.
unfold GOT_PGSZ, APGSZ in *.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "0230>10495592464.7010640816421.6510640816421.6611912744615.7212367362435.7212421467044.8513021749692.72131523600.72  13219133678.731382808063.76 14782759150.731498874631.70 1527479463.70 17208403286.6617210513774.6517420090896.7217646078182.6317776320431.711873650771.68 19049469500.7320175078107.8420633589486.7021918414723.7222000155536.7322076304297.6523489831422.8424630998586.7024689793902.7224982578614.6925065190167.8425314760359.7325878270254.7226368353420.7526492401682.6526494647592.7026494647592.7226494647592.7326494647592.7627923971379.7228575982988.7229545175216.7229782367974.7029932732146.7629939653874.6529939654001.6631081687356.7331700093303.6831700093680.6731708080634.7832651489978.7232654119520.7032852234768.7333039531175.7333364883216.7333680001082.7336115622446.7236427878680.8636993589379.7337107179452.723758653584.73 3787933806.72 38687199342.723945979267.72 39896594704.7340491529500.7240491529500.7641136219232.6541182563063.7041535431150.7341809558659.7042785251600.7242831019478.7242831019478.7643059266230.6143060403331.734353604764.72 43987951406.7244377876869.7645221239098.7349347851012.8650290054027.7051425718543.7251481786499.7351678667183.7153767577775.7155530626798.7055584287907.6555688371807.8556228262055.72563227834.72  57745675194.7257990401424.7258370469874.6558512233326.7259308580184.8059314873579.6759314873579.6859314873579.6960000447288.8360000447288.8460025031335.7360223348125.7661700344799.7661917199023.7162386374993.6662386375120.6762739985321.6563235321900.6963694018620.7364074620521.6565088762478.726559606672.72 65946435216.7366036615624.7066260016006.726642473454.73 6647326864.72 66656729710.7266747928658.7266747928658.7666816134988.7666927558498.6567800801447.7267943285742.7368309604434.7268309604434.7668352504208.707010956092.70 802261998.73  8583720762.73 985337532.72  00000900>00C00D00E00J00N00S00\00]00f00g00h00i00j00o01001>01U01Y01Z01c01d01i02602?02C02L02M02R02S02a02o03003103203303403503@03D03E03\04304J04N04e05<05S05W05X05a05b05k05o06=06A06B06F06K06T06]06^06g07007507:07;07D07E07J07N07R07V07W07\07j07k07o08008508608708E08S08\08]08^08_08c08g09009=09F09h0:20:90:@0:J0:T0:U0:Z0:^0:l0;:0;H0;U0;c0;g0<20<;0<D0<I0<J0<c0<l0=50=>0=G0=T0=b0=c0=d0=m0>60>C0>H0>L0>U0>Y0>]S3SPS3LTBS3LTBS3LTBSSS3SPSS2HBS3SPSS4CEIL2LOSS4CEIL2LOSSSSS3SPSSS2LO3SPS2BT2SBS4CEIL2LO3SPS2BT3TOP2SBS2HBSS4CEIL2LOSS3SPSS4CEIL2LO3SPSS2PC4LTB'S2HBS4CEIL2LOSS3SPSSS2LO3SPS2BT2SBS2LO3SPS2BT2SBSSSSSSS3SPS2SB2HiS2HBSS4CEIL2LO3SPS2BT3TOP2SBS4CEIL2LO3SPS2BT3TOP2SBS4CEIL2LO3SPS2BT3TOP2SBS2HBS4CEIL2LO3SPS2BT3TOP2SBS4CEIL2LO3SPS2BT3TOP2SBS4CEIL2LO3SPS3TOP2SB2K3S2HBFS3SPS3LTBSS3SPS3LTBS2HBS2LO3SPS2BT2SBS2LOSS2HBS3SPSS4CEIL2LOS4CEIL2LOSS3SPS3LTBS3SPS3LTBS3LTBS3SPSFS4CEIL2LOSS3SPSS2HBS2HBS2LOSS3SPSS2LO3SPS2BT2SBSS2HBSS3SPSSSS2LO3SPS2BT2SBS2LO3SPS2BT2SBS4CEIL2LOSSSS2HBS2HBS3SPS3LTBS4CEIL2LO3SPSS4CEIL2LOS4CEIL2LO3SPS3LTB2BT2SB2K01H2H02H9S2BB2BT2K1S2BB2K2S2BT2K3S3LTB4LTB'S3LTB4LTB'SS3SPSS2HBS2LO3SPS2BT2SBS2B02BB2BT3TOPS2B02BB2BT3TOPS4CEIL2LO3SPSS2LO3SPS2BT2SBS2HBS2BT3TOP2SBS4CEIL2LOS3SPS3LTBS3SPSSS4CEIL2LO3SPS3TOP2SB2Hi1HS4CEIL2LOS3SPS3LTBS4CEIL2LOS4CEIL2LOS4CEIL2LO3SPSS2LO3SPS2BT2SBSSS4CEIL2LOS4CEIL2LOS4CEIL2LO3SPSS3SPSS2HBS4CEIL2LOS2HBS2HB".
carve_frame 64%nat ST.
do 9 step.
step. do 3 zstep.
step. if_lit.
do 3 step.
step. if_lit.
step. zstep.
step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (u64arr_store_ok asegs mm (S + 16) tb 0 (wa (S + 16)) TB ltac:(lia) ltac:(f_equal; lia)) as SOK end.
step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
pose proof (u64arr_write asegs mm (S + 16) tb 0 (Z_to_bv 64 pc) TB ltac:(lia)) as TB2;
rewrite Z.mul_0_r, Z.add_0_r in TB2 end.
clear TB. store_done. rename TB2 into TB. cbn [Z.to_nat upd] in TB.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite Z.shiftr_div_pow2 in K0 by lia. Z.div_mod_to_equations. lia. }
step. if_cases K1; zify_cond K1. { exfalso. lia. }
step. if_cases K2; zify_cond K2. { exfalso. lia. }
zstep. step. if_cases K3; zify_cond K3. { exfalso. lia. }
zstep. step. if_cases K4; zify_cond K4.
{ exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact BA. }
zstep. step.
replace (top + -16) with (top - 16) by lia.
change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)).
eapply evtF_mono.
{ lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (uwf_loop m top pc bot bp 29 tr UC RNG gp tp t0 t1 t2 _ _ _ _ _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm
S (bv_unsigned sp + -64) lo raf s0f s1f s2f s3f s4f s5f s6f 1%nat (upd tb 0 (Z_to_bv 64 pc))) end.
all: try eassumption; try lia.
- intros i Hi. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. lia.
- rewrite upd_length. exact LTB. }
intros ms' PO. unfold uwf_post in PO. unfold unwind_fast_post.
destruct PO as (a2' & a5' & a6' & a7' & m' & tb' & -> & MU' & WM' & MI' & SZ' & TB' & LTB' & OLD & NEW).
exists a2', (Z_to_bv 64 4096), (Z_to_bv 64 (S + 16)), a5', a6', a7', m', tb'.
split. { replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn in Hx |- *. tauto. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
split. {
match goal with FRH : rw_cells asegs ?mx (bv_unsigned sp + -64) ?cs, STH : stk asegs ?mx' lo _ |- _ =>
constr_eq mx mx';
pose proof (rw_cells_transport asegs _ _ _ _ cs FRH MU' WM' ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
pose proof (stk_transport_disjoint asegs _ _ _ _ _ STH MU' WM' ltac:(cbn [disjoint_from]; lia)) as ST'
end.
eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in FR' by lia. exact FR'. }
split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|].
destruct tb' as [|w tb'']; [cbn in LTB'; lia|].
specialize (OLD 0%nat ltac:(lia)). cbn [nth_error] in OLD.
destruct tb as [|w0 tb0]; [cbn in LTB; lia|]. cbn in OLD. injection OLD as ->.
cbn [firstn map skipn] in NEW |- *. rewrite unsigned_lit by lia. f_equal. exact NEW.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
Notation unwind_impl_W sp S t :=
([(bv_unsigned sp - 160, bv_unsigned sp); (S + 8, S + 12); (S + 16, S + 2056); (S + 2056, S + 2064); (t + 3168, t + 3169)]%Z) (only parsing).
Section CANSEC3. Context {rc : runConstT}.
Definition unwind_impl_post (S pc bp t : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (tr : list Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' tb',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (unwind_impl_W sp S t) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (S + 8) [C4 (Z_to_bv 64 (1 + Z.of_nat (length tr)))]
/\ u64arr asegs m' (S + 16) tb' /\ length tb' = 255%nat
/\ map bv_unsigned (firstn (Datatypes.S (length tr)) tb') = pc :: tr
/\ rw_cells asegs m' (S + 2056) [C8 (Z_to_bv 64 bp)]
/\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)].
#[using="Type"] Lemma unwind_impl_spec : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : amem) (S pc bp ctx t top bot lo : Z) (tb : list word) (tr : list Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp <= S ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 pc -> a2 = Z_to_bv 64 bp -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 30 ->
rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
rw_cells asegs m GOT_PGSZ [C8 (Z_to_bv 64 APGSZ)] -> rw_cells asegs m APGSZ [C8 (Z_to_bv 64 4096)] ->
rw_cells asegs m (t + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] ->
rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
(exists szj, rw_cells asegs m (S + 8) [C4 szj]) -> u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
(exists bpj, rw_cells asegs m (S + 2056) [C8 bpj]) ->
uchain m top pc bot bp 29%nat tr ->
AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
0 <= bot -> bot < bp -> bp < top - 16 -> bp mod 8 = 0 -> top <= 2^47 -> S + 2080 <= bp -> 0 <= pc < 2^64 ->
rng_aimg RNG -> rng RNG lo (top - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
evtF asegs RNG (unwind_impl_post S pc bp t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo tr m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5ad28) fc None m (seg_rom asegs)).
Proof.
intros until tr. intros ST CEIL LO SPS MI TP -> -> -> -> -> -> INI TI TK T88 TSD CT GPG PG TT SW UW [szj SZC] TB LTB [bpj BPJ] UC
C0 C1 T0 T1 CT2 B0 BB BT BA TOP SB PC RIMG RR RCTX RT. unfold sclr, iclr, KLS, AIMG_LO in *.
unfold AIMG_HI, AINITED, ATSDI, ATSDK, ATP88, ATSD, GOT_PGSZ, APGSZ in *.
pose proof (munch_refl (unwind_impl_W sp S t) m) as MU. pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "0900?100583406.101  100583406.94   10345787758.10110345787758.93 10495592464.94 10495592464.98 10651418877.94 10971937885.95 11012435216.91 11472836995.10811472836995.93 1162083375.107 1162083375.92  11801586693.94 11855220722.99 11855220723.98 1203502396.101 12156634575.10112881681230.88 12881681230.89 131523600.93   131523600.99   13205419683.10213205419683.11613205419683.92 13205419683.94 13205419683.97 13219133678.10113219133678.94 13222841501.10213222841501.11613222841501.94 13222841501.97 1382808063.94  14142343699.10114142343699.93 14304650515.94 14304650515.98 14782759150.10114782759150.94 14869079534.10114869079534.93 15441266042.10815441266042.93 15702970684.94 15813913889.10015886001168.93 15886001168.99 16078321778.93 16078321789.10916198329987.98 16347293843.93 16347293843.99 16583372664.97 16872280319.93 16872280319.99 17292611950.93 17420090896.93 17420090896.99 17433132810.89 17516299301.89 17776320430.10817776320431.92 18012046483.93 18012046483.99 18676448912.10118676448912.94 18748206397.94 19053851900.10519134181499.10719134181499.92 20052925308.10120052925309.10020099824796.11620099824796.92 20099824796.94 20099824796.97 20268128884.10120268128885.10020313996398.93 20313996398.99 20432822032.93 20633589486.94 20633589486.98 2130161072.92  21335892240.93 21335892240.99 21514303854.93 21681464571.98 21713897404.93 21786113610.11621786113610.97 22000155536.10122000155536.94 22152944003.99 22163107130.91 22226183811.10922226183811.94 22284289799.94 22472485749.10922472485754.93 22632813821.94 22700267513.95 23037462803.93 23037462803.99 23041094553.101231265399.101  23415352819.10723415352819.92 24336903790.10124336903790.94 24389875337.10024456154079.10224487705898.88 24559885231.98 24630998586.94 24630998586.98 24689793902.93 24689793902.99 24757080307.10724757080307.92 25067826030.93 25483987182.94 25483987182.98 25835920692.99 25878270254.10825878270254.93 25898482559.91 25941134723.99 26058469174.89 26058469174.95 26291562981.10426368353409.93 26507015092.10526507015092.10626790051320.10626790051320.91 27124605839.10227124605839.92 27124605839.94 27408782880.10127408782881.10027453056622.93 27453056622.99 27581510035.94 27581510035.98 27624344046.91 27723960707.10727723960707.93 27839378576.91 28064031399.98 28279352979.10128279352979.93 28575982988.10529193796462.93 29193796462.99 29410813971.10129410813971.94 2945393305.98  29527312409.99 29568420603.10729568420603.92 29596872563.10729596872563.92 2977330067.93  30103876263.99 30196181434.93 3051486595.109 3051486595.93  30785479993.93 3081889402.108 3081889402.93  30864596874.88 30864596874.89 30864596874.95 31298910190.91 31398019229.10231492042131.93 31492042131.99 31498876583.99 31599054030.95 31693862858.92 31705983472.1053180723727.102 3180723727.116 3180723727.92  3180723727.94  3180723727.97  32307613550.10132307613550.94 32431485806.93 32635795829.10032651489978.93 32651489978.99 32852234768.10132852234768.94 33364883216.10133364883216.94 33416350702.93 33680001082.10133680001082.94 33807428668.10133811408209.10033811408209.11633811408209.97 33890036524.97 34041507097.99 34064067704.10634064067704.90 34417933743.98 34592119827.93 34592119827.99 35101720189.94 35561507310.10135561507310.93 35909988007.93 36115622446.10836115622446.93 3662364220.94  36641385327.87 36692649235.10136692649235.94 37054621351.10137317216127.10137317216127.93 37429491794.10237429491794.11637429491794.92 37429491794.94 37429491794.97 3758653584.101 3758653584.93  37750569872.10137750569872.94 37844949358.93 3787933806.93  3787933806.99  38040769427.10138040769427.94 38687199342.93 38687199342.99 38802323967.10238859095568.93 38859095568.99 3888239342.101 3888239342.94  39156633850.10839156633851.92 39579879187.94 39579879187.98 39771606844.91 39835013820.99 39896594704.10139896594704.93 39909714457.99 40091925676.10640091925676.91 40374333670.84 40491529500.10240491529500.11640491529500.92 40491529500.94 40491529500.97 40655079551.94 40655079551.98 40799841351.91 41413083773.10041480320778.88 41480320778.89 41535431150.10141535431150.94 41622522515.93 41622522515.99 41788515822.91 41882312464.93 41894607218.10841894607218.93 42200251523.10942200251523.94 42785251600.93 42785251600.99 42805740039.10442831019478.10242831019478.11642831019478.92 42831019478.94 42831019478.97 43059266230.82 43186076965.86 43188973678.93 43188973678.99 43287406227.93 43287406227.99 4353604764.102 4353604764.116 4353604764.92  4353604764.97  43593987216.91 43767264935.10143956831987.98 4397356589.96  43987951393.10943987951406.93 4399453729.115 4399453732.99  44338125843.91 44377876869.94 44484923210.94 4464196338.108 4464196339.92  44959237658.91 44977136295.94 45182187139.10145221239098.10145221239098.93 45799194044.93 45843842876.10146134254574.10146134254574.93 46298727534.94 46298727534.98 46408864147.93 46481665774.94 46481665774.98 46595657582.93 46629035023.10246629035023.11646629035023.92 46629035023.94 46629035023.97 46887021955.10846887021955.93 46903013776.94 46903013776.98 47364406313.93 47663274663.93 48057003647.10148057003647.94 48307028028.94 48989959150.10148989959150.94 4911618544.106 4911618544.91  49425192486.86 49724318719.93 49724318719.99 49834049331.92 49870597903.10749870597903.92 50141517948.90 50317564526.93 50317564526.99 50362574674.10250362574674.11650362574674.92 50362574674.94 50362574674.97 50409066490.99 50409066491.98 50470234962.10250470234962.11650470234962.92 50470234962.94 50470234962.97 50487304575.10150487304575.94 50492992828.10550628941955.10850628941955.93 50637889923.10050637889923.99 50647975150.94 50647975150.98 50693720814.10150693720814.94 51028639888.10151028639888.93 51322024558.93 51322024558.99 51665594094.10151665594094.94 51678667183.10751678667183.92 52074235540.10552567164907.10152567164907.10252567164907.11652567164907.91 52567164907.92 52567164907.93 52567164907.94 52567164907.97 52567164907.98 52567164907.99 52899476003.1065300105810.102 5300105810.116 5300105810.92  5300105810.94  5300105810.97  53014488720.93 53767577775.10753767577775.92 54208467631.11654208467631.97 54317840060.93 54636957394.10254636957394.11654636957394.92 54636957394.94 54636957394.97 54688270867.10154688270867.94 54688491502.91 54722921710.93 54722921710.99 55188037614.91 55442533998.93 55442533998.99 55530626798.94 55530626798.98 55600578299.98 5575378976.101 5575378977.100 55958408871.94 56170430638.85 56185989799.94 563227834.93   563227834.99   56619611914.86 56759370246.93 56769499027.93 56769499027.99 57482523656.95 57574008851.10157574008851.93 57745675194.93 57745675194.99 57824410556.10557839090926.94 57839090926.98 57882368572.98 57990401424.93 57990401424.99 58170045820.10158170045821.10058433308988.10558512233326.93 58512233326.99 58822632304.10658822632304.90 5896867971.107 5896867971.91  59218010518.10459271104114.10859271104114.93 59314873579.88 59453936022.89 59506921496.99 59522377383.93 5953130734.101 5953130734.94  60221428356.95 60345424700.93 60857959228.10561282599065.1016129476974.93  6129476974.99  61335394435.10161335394435.10261628829678.10161628829678.94 61674577390.10161674577390.93 61700344799.94 61779350972.10561917199020.10661917199023.92 61980591891.10161980591891.94 61994440323.11061994440323.94 62359644839.1016257413363.98  62670790311.93 62704248302.93 62704248302.99 63045513727.93 63045513727.99 63101459338.90 63235321900.10663235321900.90 63478620285.94 6352112787.101 6352112787.94  63759975843.10563912036540.99 64119023379.93 65088762478.93 65088762478.99 65122667651.10165122667651.10265485175549.94 6559606672.93  6559606672.99  65626122629.1026566541509.88  6566541509.89  6566541509.95  65813570969.10165880641191.99 65946435216.10165946435216.94 66214737008.97 66330498734.99 66330498735.98 66348204563.93 66348204563.99 66423386478.93 66423386478.99 6642473454.101 6642473454.94  6647326864.93  6647326864.99  66656729710.93 66656729710.99 66747928658.10266747928658.11666747928658.92 66747928658.94 66747928658.97 67266277258.95 67655947248.10667655947251.92 67943285742.10167943285742.93 67965490855.91 68034022143.93 68096078318.10168096078318.94 68309604434.10268309604434.11668309604434.92 68309604434.94 68309604434.97 68352504208.94 68352504208.98 6951018343.101 7228974012.99  7779942894.91  7848643581.94  7963185902.93  7963185902.99  802261998.101  802261998.93   8465484435.91  8583720762.101 8583720762.94  8684881006.93  8684881006.99  8800126135.93  8805124206.93  8805124206.99  894743207.93   896106003.91   9074023790.91  9244339772.105 9275778164.101 9275778165.100 9333008750.93  9333008750.99  9570122235.107 9570122235.92  9675386044.93  9860811768.106 9860811771.92  00000900B00K00T00]00f01301701@01F01G01Z01h02C02D02E02I02W02^02e02j02o03?03M03Y03i04204;04D04I04U04Z04f04g05305?05K05W05`05i06206;06<06=06A06O06T06Y06Z06[06\06h07407507A07M07V07[07`07a07e08808F08R08^08c08h09509F09G09H09I09J09Z09_09`0:00:10:20:;0:D0:I0:R0:[0:_0:d0:i0;20;30;70;;0;?0;D0;I0;J0;N0;T0;U0;V0;W0;X0;e0<O0<[0<g0<h0<i0<j0<k0=40==0=F0=J0=K0=Y0=]0=a0=j0>30>40>50>>0>G0>P0>Q0>d0?20?>0??0?J0?U0?V0?d0@;0@O0@P0@Q0@a0@m0A=0AK0AY0Ab0Ak0B70BC0BL0BR0BS0BX0BY0Be0C10Ce0Cn0D70DC0DO0DP0DQ0DR0DS0DT0DU0Da0Db0Df0Dl0Dm0Dn0Do0E00E40E80E<0EE0EJ0EV0Eb0Ec0Eg0F@0FW0Fg0Fh0G40GD0GE0GN0GW0G`0Ga0Ge0Gi0H20H;0HD0HM0HV0HZ0H^0Hb0Hc0Hi0Hj0I80I90I:0I;0II0IU0Ia0In0J70J@0JA0JT0Jb0Jf0K10K=0KI0KJ0KV0Kb0Ko0L<0LE0LR0LZ0L_0Ld0Li0Ln0M70M@0MI0MU0Ma0Mj0N30N40N90N>0NG0NP0NQ0NR0N^0Nj0Nn0O20O;0OD0OE0OX0Of0Og0Ol0PA0PJ0PO0Pc0Po0Q;0Q<0Q=0QE0QM0QV0Q_0Qk0R70R@0RE0RF0RG0RM0RN0RS0RX0RY0R]0Ra0Re0Ri0Rm0S10S50S>0SG0SS0S_0S`0T00T50TE0TJ0TK0TL0TM0T`0Tn0U40U50UA0UB0UC0UD0UE0UI0UJ0UK0UO0US0UW0U[0Ud0Um0V60V?0VK0VT0V]0Vf0W60W70WC0WS0WT0WZ0W[0W`0We0Wf0Wg0X30X?0XC0XL0XU0XV0XW0X[0Xg0Y30Y40Y:0Y;0Y<0YE0YN0Y[0Yh0Z10Z>0ZF0ZG0ZH0ZU0Zb0Zk0[80[@0[L0[X0[i0[o0\00\10\20\;0\D0\M0\V0\[0\`0\i0]20];0]D0]W0]e0]f0]g0]h0]i0]j0]k0]l0]m0]n0]o0^00^90^F0^S0^\0^i0_10_:0_M0_[0_a0_b0_f0`30`@0`I0`V0`^0`j0a60a?0aH0aQ0aZ0ac0al0b50b>0b?0bM0b[0b\0bg0bh0bl0c00c10cJ0cV0cb0ck0d70dC0dG0dK0d\0de0dn0e20e;0eD0eE0eF0eW0e`0ei0ej0ek0f10f20f70f80f90fC0fD0fJ0fK0fT0f]0fa0fe0g60g70g@0gI0gJ0gK0gT0g]0gf0go0h30hD0hW0he0i10i=0iC0iD0iE0iF0iG0iP0iY0ie0j10j20jE0jS0j`0jl0k80kE0kI0kU0k^0kg0kh0ki0l60l?0lH0lI0lN0lS0lX0lY0lZ0l_0ld0le0m30mA0mM0mY0mb0mk0n40n=0nF0nO0nX0na0nn0o;0oD0oQ0oY0oa0ob0oc0ol10510610B10K10T10a10n11711D11L11Q11V11W11[11d12112:12C12L12U12a12e12i13213;13Q13Z13c13d14014914J14K14L14U14^14_14`14d14e14fS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPS3LTBS3SPS3LTBS4CEIL2LO3HspS2BTS3SPS3LTBS4LTB'SS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS3SPS3Hsp4CEIL2LO2T12C13LTBFFS2HBS2LO3SPS2BT2SBS2BB2BTS2BB2BTS3SPSS3SPSS4CEIL2LO3SPS2C1S3LTB3CT24LTB'S4CEIL2LO2C1S4CEIL2LO3SPS2C1S3LTB3CT2S4CEIL2LOS4CEIL2LOS3SPSS4CEIL2LO2T1S3SPSS4CEIL2LO2T1SS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOFFS2HBS2LO3SPS2BT2SBS3SPSS3SPSFFSS4CEIL2LO2T1S4CEIL2LO2T1FS4CEIL2LO2C1S4CEIL2LO2C1S4CEIL2LOS3SPSS3SPSSS2LOS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS4CEIL2LO2T1S4CEIL2LO2T1S3SPSS3SPSS4CEIL2LO3HspS4CEIL2LO3SPS3HspFFFFS4CEIL2LO3SPS2T1S3SPSSS4CEIL2LO3SPS2T1FFS4CEIL2LOS4CEIL2LOS3SPSS4CEIL2LOS4CEIL2LOS2HBS3SPSS3SPSS4CEIL2LOFS2HBS2HBS2HBS3SPSS3SPSSS2HBS4LTB'SFFFS4CEIL2LO3HspS4CEIL2LO3SPS3LTB2C02C12T13CT22BA2SB3Hsp1HS4CEIL2LO2T1S4CEIL2LO2T1SFFFS4CEIL2LOS4CEIL2LOS2LO4LTB'S2HBSS2LO3SPS2BT2SBS2HBS2HBS4CEIL2LOS4CEIL2LOFFS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS4CEIL2LO2C1SS4CEIL2LO1HS4CEIL2LO1HFS2LO3SPS2BT2SBS3SPS3Hsp4CEIL2LO2T12C1S3SPS3Hsp4CEIL2LO2T1FFS4CEIL2LO3SPS2T1S4CEIL2LO2T1S4CEIL2LO3SPS2T1S2LO3SPS2BT2SBS2LO3SPS2BT2SBS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4LTB'SS3SPSSS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO3SPS3LTB2C02C12T02T13CT22BA2SB1K3Hsp4POST1HS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1SSFFFFS4CEIL2LO2T1SS2HBS4LTB'SFFFS2B0S2B0S2B0S4CEIL2LOS3SPSS4CEIL2LO2T1S4CEIL2LO2T1SS2BBS4CEIL2LO3SPS2BT3TOP2SB1HS4CEIL2LO3SPS2BT3TOP2SBS4CEIL2LO3SPS2T1SS4CEIL2LO2T1S4CEIL2LO3SPS2T1SS4CEIL2LOS4CEIL2LOS4CEIL2LOFS2HBS2HBS3SPS3LTBS3SPS3LTBS3SPS3LTBS3SPS3LTBS4CEIL2LOS2HBS2HBS2HBSS4LTB'SS2LO3SPS2BT2SBSFFS2LO3SPS2BT2SBS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO3HspS4CEIL2LOS4CEIL2LOSS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS2HBS3LTB2T02T1S4CEIL2LO2T1S4CEIL2LO2T1SS4CEIL2LO2C1S4CEIL2LO2C1S4CEIL2LO3SPSS3LTB2T04LTB'S4CEIL2LOS4CEIL2LO3SPSS3LTB2T0S3SPSS3SPSS3SPSS3SPSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOSS3SPSS3SPSS4CEIL2LOS4CEIL2LOFFS4CEIL2LO2T1S4CEIL2LO2T1S2HBS2HBS3SPS3LTBS3SPS3LTBSS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBSS3LTBS4CEIL2LO3SPS2T14LTB'S3SPS3LTBS3LTBS4CEIL2LO3SPS3LTB2T1S4CEIL2LO2C1S4CEIL2LO2C1SFS3LTB2T0S3LTB2T0S4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS3SPSFFS4LTB'SS3SPSS3SPSFS2HBS2HBS2HBS2HBS2HBS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1SS4CEIL2LO3SPS2T1S3SPSS4CEIL2LO3SPS2T1S3SPSSFSS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS4LTB'SS4CEIL2LO2T1SFFFS2LOSSS2HBS2HBS2HBS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3SPS2T1SS4CEIL2LO2T1S4CEIL2LO3SPS2T1SS4LTB'SS3SPSS3SPSFSS4CEIL2LO2C1S4CEIL2LO2C1S2HBS4CEIL2LOS4CEIL2LOFFS2C0S4CEIL2LO2C1S4CEIL2LO2C1SS4LTB'SSS4CEIL2LOS4CEIL2LOS4CEIL2LO3SPSS3LTB2T04LTB'S4CEIL2LOS4CEIL2LO3SPSS3LTB2T0FFS4CEIL2LO3SPSS3LTB2T04LTB'S4CEIL2LOS4CEIL2LO3SPSS3LTB2T0S4CEIL2LO2C1S4CEIL2LO2C1S4CEIL2LO3SPS3HspS4LTB'SSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPSS3SPSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBFSSSSSSSSSSS3SPS3HspS4CEIL2LO3SPSS3LTB2T04LTB'S4CEIL2LOS4CEIL2LO3SPSS3LTB2T0S3SPS3LTBS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS4LTB'SS2HBS4CEIL2LO3SPSS3LTB2T04LTB'S4CEIL2LOS4CEIL2LO3SPSS3LTB2T0S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOFS2LO3SPS2BT2SBS2LO3SPS2BT2SBSS3SPS2BT2SBSS2HBS2HBSS4CEIL2LO3SPS3TOP2SB2Ha1HS4CEIL2LO2T1S4CEIL2LO2T1S3SPS3HspS4CEIL2LO2T1S4CEIL2LO2T1S2HBS2HBS4CEIL2LO3SPS3HspS4CEIL2LOS4CEIL2LOS2HBS3SPS3LTBS3SPS3LTBFFS4CEIL2LO3SPS3HspS4CEIL2LOS4CEIL2LOFFS4LTB'SS3PC3FFS3LTB2T01KSS4LTB'SS4CEIL2LOS4CEIL2LOS2SBS2HBS4CEIL2LO3SPS3HspSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO3SPS3HspS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS4CEIL2LO2T1S4CEIL2LO2T1S4LTB'SSFSS4CEIL2LOS4CEIL2LOS4CEIL2LO2C1S4CEIL2LO2C1SS2LO3SPS2BT2SB4LTB'S2LO3SPS2BT2SBS4CEIL2LO3HspS4CEIL2LO2T1S4CEIL2LO2T1S3SPS3LTB3HspS2HBS4CEIL2LO2T1S4CEIL2LOS4CEIL2LOSSS4CEIL2LO3HspS3SPS3LTBS3SPS3LTBSS3TOPS3TOPS3TOPSSS3SPSS3SPSFS2LO3SPS2BT2SBS2LO3SPS2BT2SBS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPS3LTBS3SPS3LTBS4CEIL2LOS4CEIL2LOS4CEIL2LO3SPSS3LTB2T04LTB'S4CEIL2LOS4CEIL2LO3SPSS3LTB2T0S2LO3HspFFS4CEIL2LOS4CEIL2LOSS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LO3SPSS3LTB2T04LTB'S4CEIL2LOS4CEIL2LO3SPSS3LTB2T0S3SPSS3SPSFS2HBS4CEIL2LOS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S2HBS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LO3SPS2T12SB2HaS4CEIL2LOS4CEIL2LOSS4CEIL2LO2T1S4CEIL2LOS4CEIL2LO3SPS3HspFFS4CEIL2LOS4CEIL2LOFFS2HBFF".
carve_frame 80%nat ST.
do 11 step.
do 6 step.
step.
step. callp asan_inited_spec; [exact INI|]. step. if_lit.
box RT.
step. call_sp get_current_thread_spec;
[exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
unbox RT. rename POST into ST. try rename MI0 into MI.
lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI end.
step. if_cases K; zify_cond K; [exfalso; lia|].
zstep. lstep. step. step.
step. if_lit.
step. step. callp stack_top_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
do 3 step. callp stack_bottom_spec; [exact MI | reflexivity | exact TT | exact SW | lia | lia | lia | lia | exact T1 |].
step. step. if_lit.
do 8 step.
step.
carve_frame 64%nat ST.
do 8 step.
do 6 zstep.
change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615.
rewrite (land_ones_l bp) by lia.
step.
step. if_lit. step. if_lit. step. if_lit.
do 5 step.
do 8 step.
release_frame FR0 ST (bv_unsigned sp + -80).
step.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (UC' : uchain mm top pc bot bp 29 tr)
by (eapply uchain_frame; [exact UC|]; intros a Ha; apply MU; unfold wa; rewrite unsigned_lit by lia; cbn; lia) end.
name_sp sp (-80). rewrite <- Hsp in ST.
eapply evtF_cut.
{ eapply unwind_fast_spec;
[ exact ST | exact CEIL | | | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact GPG | exact PG | eexists; exact SZC | exact TB | exact LTB | exact UC' | | | | exact BA | | | exact PC
| exact RIMG | exact RR ].
all: lia. }
cbv beta. unfold unwind_fast_post.
lazymatch goal with |- forall ms', _ -> evtF _ _ _ _ => idtac end.
lazymatch type of MU with munch _ _ ?mcur => post_call asegs mcur end.
unname_sp.
clear UC'. rename PC0 into ST. rename PC1 into SZ'. rename PC2 into TB'. rename PC3 into LTB'. rename POST into TR'.
lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI' end.
step.
do 12 step.
release_frame FR ST (bv_unsigned sp).
apply evtF_done. unfold unwind_impl_post. do 17 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact SZ'|]. split; [exact TB'|]. split; [exact LTB'|]. split; [exact TR'|].
split; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC3.
