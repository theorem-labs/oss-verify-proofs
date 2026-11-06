(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AModelFacts F_memsetZ F_aunwind F_aalloc_s.
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
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma thread_stats_spec : forall RNG (ctx t lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
rw_cells asegs m 0xa1ce0 [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m 0xa1ce4 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] ->
rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 ->
evtF asegs RNG (fun ms' => exists a1' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (t + 2800)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5b95c) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ST CEIL LO MI TP TI TK T88 TSD CT CX0 CX1 T0 T1 RIMG RSTK RCTX. band_lin.
unfold AIMG_HI, ATP88, ATSD in *.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
Local Ltac2 Set LiaHints.tbl := fun () => "00R0>10345787758.6711801586693.7111805467289.6714869079534.6715449178405.6317986879152.6318748206397.7120433961190.6122284289799.7122632813821.7122700267513.7226730776422.6331399144472.6332600174396.6735101720189.713525607222.66 36635088338.6437317216127.673830242848.64 43061431595.5944484923210.7145221239098.6746134254574.6749425192486.6354164510851.6754164510851.7056172315833.6259314873579.6561674577390.6763235321901.6663235321901.6967081926311.677249401110.66 7848643581.71 00000900J00K00T00X00^00k00l00m01:01A01F01G01K01X01g01n02;02?02C02D02I02R02W02X02Y02Z02a02j02n03203303403AS4CEIL2LOS3Hsp4CEIL2LO3CX1SS4CEIL2LOS2LOS4CEILS4CEIL2LO3HspSFS4CEIL2LO3HspS3Hsp1HS3CX1SS2HBS4CEIL2LO3HspS4CEIL2LO3SPR1HS2T02T1S4CEIL2LO3CX1S2LOS2LOFS3SPRS4CEIL2LOS3CX0SSSS2T02K0S4CEIL2LOS2LOS2LOSSS4CEIL2LO3Hsp".
carve_frame 16%nat ST.
do 2 step.
step. call_sp (get_current_thread_spec RNG).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ _ _ => assumption
end.
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- rng _ _ _ => solve_rng
| |- _ => atop_facts; lia
end.
rename POST into ST.
step. if_cases K0; zify_cond K0. { exfalso. lia. }
zstep. zstep.
do 3 step.
release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Section CANSEC2. Context {rc : runConstT}.
Definition allocD_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
(n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
F (ret_pc ra0) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
/\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
/\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
/\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
End CANSEC2.
