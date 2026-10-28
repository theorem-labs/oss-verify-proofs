(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Record sb_layout {RCEIL : RunCeiling} (S OUT A D DSZ STEREO G0 G1 EXC ESZ OQ IQ MSP PG ER lo usp : Z) (LBL : list block) : Prop := SBLAY {
lay_top_lo : alloc_ceiling <= lo;
lay_top_OUT : alloc_ceiling <= OUT;
lay_top_A : alloc_ceiling <= A;
lay_top_STEREO : alloc_ceiling <= STEREO;
lay_OUT_A : OUT + 8000 <= A \/ A + 48 <= OUT;
lay_OUT_STEREO : OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT;
lay_A_STEREO : A + 48 <= STEREO \/ STEREO + 24 <= A;
lay_OUT_stk : OUT + 8000 <= lo \/ lo + (usp - lo) <= OUT;
lay_A_stk : A + 48 <= lo \/ lo + (usp - lo) <= A;
lay_STEREO_stk : STEREO + 24 <= lo \/ lo + (usp - lo) <= STEREO;
lay_pos_S : 0 < S;
lay_ceil_S : S + 160 <= alloc_ceiling;
lay_img_S : S + 160 <= 65536 \/ 450560 <= S;
lay_pos_D : 0 < D;
lay_ceil_D : D + DSZ <= alloc_ceiling;
lay_img_D : D + DSZ <= 65536 \/ 450560 <= D;
lay_pos_G0 : 0 < G0;
lay_ceil_G0 : G0 + 256 <= alloc_ceiling;
lay_img_G0 : G0 + 256 <= 65536 \/ 450560 <= G0;
lay_pos_G1 : 0 < G1;
lay_ceil_G1 : G1 + 256 <= alloc_ceiling;
lay_img_G1 : G1 + 256 <= 65536 \/ 450560 <= G1;
lay_pos_EXC : 0 < EXC;
lay_ceil_EXC : EXC + ESZ <= alloc_ceiling;
lay_img_EXC : EXC + ESZ <= 65536 \/ 450560 <= EXC;
lay_pos_OQ : 0 < OQ;
lay_ceil_OQ : OQ + 32 <= alloc_ceiling;
lay_img_OQ : OQ + 32 <= 65536 \/ 450560 <= OQ;
lay_pos_IQ : 0 < IQ;
lay_ceil_IQ : IQ + 32 <= alloc_ceiling;
lay_img_IQ : IQ + 32 <= 65536 \/ 450560 <= IQ;
lay_pos_MSP : 0 < MSP;
lay_ceil_MSP : MSP + 64 <= alloc_ceiling;
lay_img_MSP : MSP + 64 <= 65536 \/ 450560 <= MSP;
lay_pos_PG : 0 < PG;
lay_ceil_PG : PG + 16 <= alloc_ceiling;
lay_img_PG : PG + 16 <= 65536 \/ 450560 <= PG;
lay_pos_ER : 0 < ER;
lay_ceil_ER : ER + 16 <= alloc_ceiling;
lay_img_ER : ER + 16 <= 65536 \/ 450560 <= ER;
lay_S_D : S + 160 <= D \/ D + DSZ <= S;
lay_S_G0 : S + 160 <= G0 \/ G0 + 256 <= S;
lay_S_G1 : S + 160 <= G1 \/ G1 + 256 <= S;
lay_S_EXC : S + 160 <= EXC \/ EXC + ESZ <= S;
lay_S_OQ : S + 160 <= OQ \/ OQ + 32 <= S;
lay_S_IQ : S + 160 <= IQ \/ IQ + 32 <= S;
lay_S_MSP : S + 160 <= MSP \/ MSP + 64 <= S;
lay_S_PG : S + 160 <= PG \/ PG + 16 <= S;
lay_S_ER : S + 160 <= ER \/ ER + 16 <= S;
lay_D_G0 : D + DSZ <= G0 \/ G0 + 256 <= D;
lay_D_G1 : D + DSZ <= G1 \/ G1 + 256 <= D;
lay_D_EXC : D + DSZ <= EXC \/ EXC + ESZ <= D;
lay_D_OQ : D + DSZ <= OQ \/ OQ + 32 <= D;
lay_D_IQ : D + DSZ <= IQ \/ IQ + 32 <= D;
lay_D_MSP : D + DSZ <= MSP \/ MSP + 64 <= D;
lay_D_PG : D + DSZ <= PG \/ PG + 16 <= D;
lay_D_ER : D + DSZ <= ER \/ ER + 16 <= D;
lay_G0_G1 : G0 + 256 <= G1 \/ G1 + 256 <= G0;
lay_G0_EXC : G0 + 256 <= EXC \/ EXC + ESZ <= G0;
lay_G0_OQ : G0 + 256 <= OQ \/ OQ + 32 <= G0;
lay_G0_IQ : G0 + 256 <= IQ \/ IQ + 32 <= G0;
lay_G0_MSP : G0 + 256 <= MSP \/ MSP + 64 <= G0;
lay_G0_PG : G0 + 256 <= PG \/ PG + 16 <= G0;
lay_G0_ER : G0 + 256 <= ER \/ ER + 16 <= G0;
lay_G1_EXC : G1 + 256 <= EXC \/ EXC + ESZ <= G1;
lay_G1_OQ : G1 + 256 <= OQ \/ OQ + 32 <= G1;
lay_G1_IQ : G1 + 256 <= IQ \/ IQ + 32 <= G1;
lay_G1_MSP : G1 + 256 <= MSP \/ MSP + 64 <= G1;
lay_G1_PG : G1 + 256 <= PG \/ PG + 16 <= G1;
lay_G1_ER : G1 + 256 <= ER \/ ER + 16 <= G1;
lay_EXC_OQ : EXC + ESZ <= OQ \/ OQ + 32 <= EXC;
lay_EXC_IQ : EXC + ESZ <= IQ \/ IQ + 32 <= EXC;
lay_EXC_MSP : EXC + ESZ <= MSP \/ MSP + 64 <= EXC;
lay_EXC_PG : EXC + ESZ <= PG \/ PG + 16 <= EXC;
lay_EXC_ER : EXC + ESZ <= ER \/ ER + 16 <= EXC;
lay_OQ_IQ : OQ + 32 <= IQ \/ IQ + 32 <= OQ;
lay_OQ_MSP : OQ + 32 <= MSP \/ MSP + 64 <= OQ;
lay_OQ_PG : OQ + 32 <= PG \/ PG + 16 <= OQ;
lay_OQ_ER : OQ + 32 <= ER \/ ER + 16 <= OQ;
lay_IQ_MSP : IQ + 32 <= MSP \/ MSP + 64 <= IQ;
lay_IQ_PG : IQ + 32 <= PG \/ PG + 16 <= IQ;
lay_IQ_ER : IQ + 32 <= ER \/ ER + 16 <= IQ;
lay_MSP_PG : MSP + 64 <= PG \/ PG + 16 <= MSP;
lay_MSP_ER : MSP + 64 <= ER \/ ER + 16 <= MSP;
lay_PG_ER : PG + 16 <= ER \/ ER + 16 <= PG;
lay_lbl_ceil : forall b, In b LBL -> 0 < blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling /\ (blk_addr b + blk_size b <= 65536 \/ 450560 <= blk_addr b);
lay_lbl_S : forall b, In b LBL -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S;
lay_lbl_D : forall b, In b LBL -> D + DSZ <= blk_addr b \/ blk_addr b + blk_size b <= D;
lay_lbl_G0 : forall b, In b LBL -> G0 + 256 <= blk_addr b \/ blk_addr b + blk_size b <= G0;
lay_lbl_G1 : forall b, In b LBL -> G1 + 256 <= blk_addr b \/ blk_addr b + blk_size b <= G1;
lay_lbl_EXC : forall b, In b LBL -> EXC + ESZ <= blk_addr b \/ blk_addr b + blk_size b <= EXC;
lay_lbl_OQ : forall b, In b LBL -> OQ + 32 <= blk_addr b \/ blk_addr b + blk_size b <= OQ;
lay_lbl_IQ : forall b, In b LBL -> IQ + 32 <= blk_addr b \/ blk_addr b + blk_size b <= IQ;
lay_lbl_MSP : forall b, In b LBL -> MSP + 64 <= blk_addr b \/ blk_addr b + blk_size b <= MSP;
lay_lbl_PG : forall b, In b LBL -> PG + 16 <= blk_addr b \/ blk_addr b + blk_size b <= PG;
lay_lbl_ER : forall b, In b LBL -> ER + 16 <= blk_addr b \/ blk_addr b + blk_size b <= ER }.

Ltac sb_class s out a d ster g0 g1 exc oq iq msp pg er b :=
match b with
| _ => let x := match goal with |- _ => constr_eq b s end in constr:(1%nat)
| _ => let x := match goal with |- _ => constr_eq b out end in constr:(2%nat)
| _ => let x := match goal with |- _ => constr_eq b a end in constr:(3%nat)
| _ => let x := match goal with |- _ => constr_eq b d end in constr:(4%nat)
| _ => let x := match goal with |- _ => constr_eq b ster end in constr:(5%nat)
| _ => let x := match goal with |- _ => constr_eq b g0 end in constr:(6%nat)
| _ => let x := match goal with |- _ => constr_eq b g1 end in constr:(7%nat)
| _ => let x := match goal with |- _ => constr_eq b exc end in constr:(8%nat)
| _ => let x := match goal with |- _ => constr_eq b oq end in constr:(9%nat)
| _ => let x := match goal with |- _ => constr_eq b iq end in constr:(10%nat)
| _ => let x := match goal with |- _ => constr_eq b msp end in constr:(11%nat)
| _ => let x := match goal with |- _ => constr_eq b pg end in constr:(12%nat)
| _ => let x := match goal with |- _ => constr_eq b er end in constr:(13%nat)
| _ => let e := match goal with E : b = ?e |- _ => e end in
let b' := nb_base e in sb_class s out a d ster g0 g1 exc oq iq msp pg er b'
| _ => constr:(0%nat)
end.
Ltac sb_pose_pair L c1 c2 :=
lazymatch c1 with
| 0%nat => lazymatch c2 with | 2%nat => pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 3%nat => pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 5%nat => pose proof (lay_STEREO_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 1%nat => lazymatch c2 with | 4%nat => pose proof (lay_S_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_S_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_S_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_S_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_S_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_S_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_S_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_S_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_S_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 2%nat => lazymatch c2 with | 0%nat => pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 3%nat => pose proof (lay_OUT_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 5%nat => pose proof (lay_OUT_STEREO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 3%nat => lazymatch c2 with | 0%nat => pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 2%nat => pose proof (lay_OUT_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 5%nat => pose proof (lay_A_STEREO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 4%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_D_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_D_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_D_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_D_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_D_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_D_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_D_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_D_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 5%nat => lazymatch c2 with | 0%nat => pose proof (lay_STEREO_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 2%nat => pose proof (lay_OUT_STEREO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 3%nat => pose proof (lay_A_STEREO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 6%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_G0_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_G0_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_G0_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_G0_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_G0_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_G0_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_G0_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 7%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_G0_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_G1_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_G1_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_G1_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_G1_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_G1_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_G1_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 8%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_G0_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_G1_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_EXC_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_EXC_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_EXC_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_EXC_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_EXC_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 9%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_G0_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_G1_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_EXC_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_OQ_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_OQ_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_OQ_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_OQ_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 10%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_G0_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_G1_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_EXC_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_OQ_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_IQ_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_IQ_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_IQ_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 11%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_G0_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_G1_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_EXC_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_OQ_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_IQ_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_MSP_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_MSP_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 12%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_G0_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_G1_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_EXC_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_OQ_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_IQ_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_MSP_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 13%nat => pose proof (lay_PG_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
| 13%nat => lazymatch c2 with | 1%nat => pose proof (lay_S_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_D_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_G0_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 7%nat => pose proof (lay_G1_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 8%nat => pose proof (lay_EXC_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 9%nat => pose proof (lay_OQ_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 10%nat => pose proof (lay_IQ_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 11%nat => pose proof (lay_MSP_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | 12%nat => pose proof (lay_PG_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L) | _ => idtac end
end.

Ltac sb_img_fact L c :=
lazymatch c with
| 1%nat => pose proof (lay_img_S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 4%nat => pose proof (lay_img_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 6%nat => pose proof (lay_img_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 7%nat => pose proof (lay_img_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 8%nat => pose proof (lay_img_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 9%nat => pose proof (lay_img_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 10%nat => pose proof (lay_img_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 11%nat => pose proof (lay_img_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 12%nat => pose proof (lay_img_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| 13%nat => pose proof (lay_img_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L)
| _ => idtac
end.
Ltac sb_apart :=
match goal with
| L : sb_layout ?s ?out ?a ?d ?dsz ?ster ?g0 ?g1 ?exc ?esz ?oq ?iq ?msp ?pg ?er ?lo ?usp ?lbl |- (?x <= ?y \/ _)%Z =>
let bx := nb_base x in let by_ := nb_base y in
let c1 := sb_class s out a d ster g0 g1 exc oq iq msp pg er bx in
let c2 := sb_class s out a d ster g0 g1 exc oq iq msp pg er by_ in
sb_pose_pair L c1 c2;
tryif is_Zlit_zb bx then sb_img_fact L c2 else idtac;
tryif is_Zlit_zb by_ then sb_img_fact L c1 else idtac
end.

Ltac sb_lbl_fact L s out a d ster g0 g1 exc oq iq msp pg er c b Hb :=
lazymatch c with
| 1%nat => pose proof (lay_lbl_S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 4%nat => pose proof (lay_lbl_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 6%nat => pose proof (lay_lbl_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 7%nat => pose proof (lay_lbl_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 8%nat => pose proof (lay_lbl_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 9%nat => pose proof (lay_lbl_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 10%nat => pose proof (lay_lbl_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 11%nat => pose proof (lay_lbl_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 12%nat => pose proof (lay_lbl_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| 13%nat => pose proof (lay_lbl_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
| _ => pose proof (lay_lbl_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L b Hb)
end.

Ltac sb_keeper_base T :=
match T with
| (_ <= bv_unsigned _)%Z => idtac
| (_ <= alloc_ceiling)%Z => idtac
| (alloc_ceiling <= _)%Z => idtac
| (alloc_ceiling = _)%Z => idtac
| context [sb_buf_size _] => idtac
| (_ + _ <= _ \/ _ + _ <= _)%Z => idtac
| (?v = _ \/ ?v = _) => is_var v
| (_ <= ?v < _)%Z => is_var v | (_ <= ?v <= _)%Z => is_var v | (_ < ?v <= _)%Z => is_var v | (_ < ?v < _)%Z => is_var v
| (?v < _)%Z => is_var v | (?v <= _)%Z => is_var v
| (_ <= ?v)%Z => is_var v | (_ < ?v)%Z => is_var v
| @eq Z ?v _ => is_var v | @eq Z _ ?v => is_var v
| (?v < _)%nat => is_var v | (?v <= _)%nat => is_var v | (_ <= ?v < _)%nat => is_var v
| @eq nat ?v _ => is_var v | @eq nat _ ?v => is_var v
end.
Ltac sb_box_junk :=
repeat match goal with H : ?T |- _ => nb_is_arith T; tryif sb_keeper_base T then fail else change T with (jboxed T) in H end.

Ltac sb_lia :=
nb_unbox_anchored;
first [ sb_apart; lia
| lia
| nb_unbox_junk; cbv delta [BITS_SIZEOF SBSTATE_SIZEOF HOUT_BYTES] in *; lia ].

Lemma disjoint_from_blocks_ivs : forall L e n,
(forall b, In b L -> e + n <= blk_addr b \/ blk_addr b + blk_size b <= e) -> disjoint_from (blocks_ivs L) e n.
Proof.
induction L as [|b L IH]; intros e n H; cbn; [exact I|].
split; [| apply IH; intros b' Hb'; apply H; right; exact Hb'].
specialize (H b ltac:(left; reflexivity)). lia.
Qed.
Lemma outside_blocks_of : forall L W,
(forall b, In b L -> forall iv, In iv W -> snd iv <= blk_addr b \/ blk_addr b + blk_size b <= fst iv) ->
forall b a, In b L -> blk_addr b <= a < blk_addr b + blk_size b -> outside W a.
Proof.
intros L W H b a Hb Ha. induction W as [|[u v] W IH]; cbn; [exact I|].
split.
- specialize (H b Hb (u, v) ltac:(left; reflexivity)). cbn in H. lia.
- apply IH. intros b' Hb' iv Hiv. apply H; [exact Hb'| right; exact Hiv].
Qed.

Ltac sb_lbl :=
lazymatch goal with
| |- disjoint_from (blocks_ivs _) ?e ?n =>
lazymatch goal with L : sb_layout ?s ?out ?a ?d ?dsz ?ster ?g0 ?g1 ?exc ?esz ?oq ?iq ?msp ?pg ?er ?lo ?usp ?lbl |- _ =>
apply disjoint_from_blocks_ivs; let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
let bx := nb_base e in
let c := sb_class s out a d ster g0 g1 exc oq iq msp pg er bx in
sb_lbl_fact L s out a d ster g0 g1 exc oq iq msp pg er c b Hb; nb_unbox_anchored; lia end
| |- forall b, In b _ -> _ =>
lazymatch goal with L : sb_layout ?s ?out ?a ?d ?dsz ?ster ?g0 ?g1 ?exc ?esz ?oq ?iq ?msp ?pg ?er ?lo ?usp ?lbl |- _ =>
let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
lazymatch goal with |- (?x <= _ \/ _)%Z =>
let bx := nb_base x in
let c := sb_class s out a d ster g0 g1 exc oq iq msp pg er bx in
sb_lbl_fact L s out a d ster g0 g1 exc oq iq msp pg er c b Hb; nb_unbox_anchored; lia end end
end.

Ltac sb_lia_cheap := nb_unbox_anchored; solve [ X1c4.clear_sec_props; X1bw.lean_keep; X1c4.lia_tuned ].
Ltac sb_inside_full :=
lazymatch goal with
| |- (_ <= _ /\ _ <= _) \/ _ => first [ left; split; sb_lia | right; sb_inside_full ]
| |- _ <= _ /\ _ <= _ => split; sb_lia
| |- _ => sb_lia
end.
Ltac sb_inside_pick :=
lazymatch goal with
| |- (_ <= _ /\ _ <= _) \/ _ => first [ left; assert_succeeds (split; sb_lia_cheap); split; sb_lia | right; sb_inside_pick ]
| |- _ <= _ /\ _ <= _ => split; sb_lia
end.
Ltac sb_inside := first [ sb_inside_pick | sb_inside_full ].
Ltac sb_conj :=
lazymatch goal with
| |- True => exact I
| |- (_ <= _ /\ _ <= _) \/ _ => sb_inside
| |- _ /\ _ => split; [ sb_conj | sb_conj ]
| |- disjoint_from (blocks_ivs _) _ _ => sb_lbl
| |- forall b, In b _ -> _ => sb_lbl
| |- outside (blocks_ivs ?L) ?x => assumption
| |- _ => sb_lia
end.
Ltac slia ::= cbv delta [BITS_SIZEOF SBSTATE_SIZEOF HOUT_BYTES]; sb_conj.

Lemma drep_write : forall OUT STEREO m SL d L a bs,
DREP OUT STEREO m SL d L -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall b, In b L -> a + Z.of_nat (length bs) <= blk_addr b \/ blk_addr b + blk_size b <= a) ->
DREP OUT STEREO (write_to_mem m (wa a) bs) SL d L.
Proof.
intros OUT STEREO m SL d L a bs R Ha Hl OUTS.
eapply decst_rep_munch; [exact R | apply munch_of_write; [exact Ha| exact Hl] | apply wmono_of_write |].
eapply outside_blocks_of. intros b Hb iv [<-|[]]. cbn. specialize (OUTS b Hb). lia.
Qed.
Lemma drep_munch : forall OUT STEREO m m' SL d L W,
DREP OUT STEREO m SL d L -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => forall b, In b L -> snd iv <= blk_addr b \/ blk_addr b + blk_size b <= fst iv) W ->
DREP OUT STEREO m' SL d L.
Proof.
intros OUT STEREO m m' SL d L W R MU WM FA.
eapply decst_rep_munch; [exact R | exact MU | exact WM |].
eapply outside_blocks_of. intros b Hb iv Hiv. exact (proj1 (Forall_forall _ _) FA iv Hiv b Hb).
Qed.

Lemma excready_write : forall OUT STEREO m SL d L a bs,
DREP OUT STEREO m SL d L -> EXCREADY m SL d -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall b, In b L -> a + Z.of_nat (length bs) <= blk_addr b \/ blk_addr b + blk_size b <= a) ->
EXCREADY (write_to_mem m (wa a) bs) SL d.
Proof.
intros OUT STEREO m SL d L a bs R EX Ha Hl OUTS.
eapply dec_exc_ready_munch; [exact R | exact EX | apply munch_of_write; [exact Ha| exact Hl] | apply wmono_of_write |].
eapply outside_blocks_of. intros b Hb iv [<-|[]]. cbn. specialize (OUTS b Hb). lia.
Qed.
Lemma excready_munch : forall OUT STEREO m m' SL d L W,
DREP OUT STEREO m SL d L -> EXCREADY m SL d -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => forall b, In b L -> snd iv <= blk_addr b \/ blk_addr b + blk_size b <= fst iv) W ->
EXCREADY m' SL d.
Proof.
intros OUT STEREO m m' SL d L W R EX MU WM FA.
eapply dec_exc_ready_munch; [exact R | exact EX | exact MU | exact WM |].
eapply outside_blocks_of. intros b Hb iv Hiv. exact (proj1 (Forall_forall _ _) FA iv Hiv b Hb).
Qed.

Lemma stderr_wfile_write : forall m a bs, stderr_wfile m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(a + Z.of_nat (length bs) <= RSTDERR \/ RSTDERR + 232 <= a) -> stderr_wfile (write_to_mem m (wa a) bs).
Proof.
intros m a bs sfH_; first [ sf_destruct 7%nat sfH_ as flags mode e wend tail FC FL | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & FC & FL) ]; intros Ha Hl DJ. first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [| exact FL].
eapply rw_cells_transport; [exact FC | apply munch_of_write; [exact Ha| exact Hl] | apply wmono_of_write |]. cbn -[Z.add Z.of_nat]. unfold X1fl.got_ssp, X1fl.ssp_guard in *. split; [lia| exact I].
Qed.
Lemma stderr_wfile_munch : forall m m' W, stderr_wfile m -> munch W m m' -> wmono rsegs m m' -> disjoint_from W RSTDERR 232 -> stderr_wfile m'.
Proof.
intros m m' W sfH_; first [ sf_destruct 7%nat sfH_ as flags mode e wend tail FC FL | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & FC & FL) ]; intros MU WM DJ. first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [| exact FL].
eapply rw_cells_transport; [exact FC | exact MU | exact WM | exact DJ].
Qed.
Lemma ssp_cells_write : forall m a bs c, ssp_cells m c -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(a + Z.of_nat (length bs) <= X1fl.got_ssp \/ X1fl.got_ssp + 8 <= a) -> (a + Z.of_nat (length bs) <= X1fl.ssp_guard \/ X1fl.ssp_guard + 8 <= a) ->
ssp_cells (write_to_mem m (wa a) bs) c.
Proof.
intros m a bs c [G1 G2] Ha Hl D1 D2. split.
- eapply rw_cells_transport; [exact G1 | apply munch_of_write; [exact Ha| exact Hl] | apply wmono_of_write |]. cbn -[Z.add Z.of_nat]. unfold X1fl.got_ssp, X1fl.ssp_guard in *. split; [lia| exact I].
- eapply rw_cells_transport; [exact G2 | apply munch_of_write; [exact Ha| exact Hl] | apply wmono_of_write |]. cbn -[Z.add Z.of_nat]. unfold X1fl.got_ssp, X1fl.ssp_guard in *. split; [lia| exact I].
Qed.
Lemma ssp_cells_munch : forall m m' W c, ssp_cells m c -> munch W m m' -> wmono rsegs m m' ->
disjoint_from W X1fl.got_ssp 8 -> disjoint_from W X1fl.ssp_guard 8 -> ssp_cells m' c.
Proof.
intros m m' W c [G1 G2] MU WM D1 D2. split.
- eapply rw_cells_transport; [exact G1 | exact MU | exact WM | exact D1].
- eapply rw_cells_transport; [exact G2 | exact MU | exact WM | exact D2].
Qed.

Definition iv_cover (W2 : list (Z * Z)) (iv : Z * Z) : Prop :=
fst iv >= snd iv \/ exists iv', In iv' W2 /\ fst iv' <= fst iv /\ snd iv <= snd iv'.
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[u v] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma outside_In : forall W iv x, outside W x -> In iv W -> ~ (fst iv <= x < snd iv).
Proof. induction W as [|[u v] W IH]; intros iv x Ho Hi; cbn in *; [tauto|]. destruct Hi as [<-|Hi]; [cbn; tauto| apply IH; tauto]. Qed.
Lemma sub_fp_cover : forall W1 W2 T1 T2,
Forall (iv_cover W2) W1 -> sub_fp T1 T2 -> sub_fp (W1 ++ T1) (W2 ++ T2).
Proof.
intros W1 W2 T1 T2 FA ST x Hx. apply outside_app in Hx. destruct Hx as [H2 HT]. apply outside_app. split; [| apply ST; exact HT].
clear ST HT. induction W1 as [|[u v] W1 IH]; cbn; [exact I|]. inversion FA; subst. split; [| apply IH; assumption].
destruct H1 as [E | (iv' & Hin & L1 & L2)]; cbn in *; [lia|]. pose proof (outside_In _ _ _ H2 Hin). lia.
Qed.
Lemma sub_fp_nil_l : forall T, sub_fp [] T. Proof. intros T x _. exact I. Qed.
Lemma sub_fp_refl : forall T, sub_fp T T. Proof. intros T x H. exact H. Qed.

Ltac fp_split W :=
lazymatch W with
| ?h :: ?t => let r := fp_split t in lazymatch r with (?p, ?tl) => constr:((h :: p, tl)) end
| _ => constr:((@nil (Z * Z), W))
end.

Ltac iv_cover_try_full W2full W2 :=
lazymatch W2 with
| ?iv' :: ?rest =>
first [ right; exists iv'; split; [ cbn [In]; tauto | cbn [fst snd]; nb_unbox_anchored; lia ]
| iv_cover_try_full W2full rest ]
| _ => left; cbn [fst snd]; nb_unbox_anchored; lia
end.

Ltac iv_cover_try_pick W2full W2 :=
lazymatch W2 with
| ?iv' :: ?rest =>
first [ right; exists iv'; split; [ idtac | cbn [fst snd]; assert_succeeds sb_lia_cheap; nb_unbox_anchored; lia ]; cbn [In]; tauto
| iv_cover_try_pick W2full rest ]
end.
Ltac iv_cover_try W2full W2 := first [ iv_cover_try_pick W2full W2 | iv_cover_try_full W2full W2 ].
Ltac sb_subfp :=
cbv delta [BITS_SIZEOF SBSTATE_SIZEOF HOUT_BYTES];
lazymatch goal with
| |- sub_fp ?Wc ?Wq =>
let rc := fp_split Wc in let rq := fp_split Wq in
lazymatch rc with (?pc, ?tc) => lazymatch rq with (?pq, ?tq) =>
change (sub_fp (pc ++ tc) (pq ++ tq)); apply sub_fp_cover;
[ repeat (apply Forall_cons; [ iv_cover_try pq pq |]); apply Forall_nil
| first [ apply sub_fp_refl | apply sub_fp_nil_l ] ]
end end
end.

Ltac transport_chunks segs m a bs ::=
let Ha := fresh "Ha_" in let Hl := fresh "Hl_" in
assert (Ha : (0 <= a)%Z) by lia;
assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; lia);
sb_box_junk;
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : bits_rep segs m ?A2 ?D2 ?b2 |- _ =>
first [ apply (bits_rep_frame segs m (write_to_mem m (wa a) bs) A2 D2 b2 [(a, a + Z.of_nat (length bs))%Z]) in H;
[ | solve [eauto] | apply munch_of_write; [exact Ha | exact Hl] | apply wmono_of_write
| cbn [disjoint_from]; simpl_sizes; slia | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : EXCREADY m ?sl ?d, R : DREP ?o ?st m ?sl ?d ?L |- _ =>
first [ apply (excready_write o st m sl d L a bs R) in H; [ | exact Ha | exact Hl | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : DREP ?o ?st m ?sl ?d ?L |- _ =>
first [ apply (drep_write o st m sl d L a bs) in H; [ | exact Ha | exact Hl | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : rtables_pristine m |- _ =>
first [ apply (rtables_pristine_write m a bs) in H; [ | exact Ha | simpl_sizes; unfold RTABLES_LO, RTABLES_HI; slia | exact Hl ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : stderr_wfile m |- _ =>
first [ apply (stderr_wfile_write m a bs) in H; [ | exact Ha | exact Hl | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ssp_cells m ?c |- _ =>
first [ apply (ssp_cells_write m a bs c) in H; [ | exact Ha | exact Hl | simpl_sizes; unfold X1fl.got_ssp; slia | simpl_sizes; unfold X1fl.ssp_guard; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end;
clear Ha Hl; nb_unbox_junk.

Lemma blocks_ivs_app : forall L1 L2, blocks_ivs (L1 ++ L2) = blocks_ivs L1 ++ blocks_ivs L2.
Proof. intros. unfold blocks_ivs. apply map_app. Qed.
Lemma blocks_ivs_sb9 : forall (s : sbd_state bptr) S a,
blocks_ivs (sb_blocks s S a) =
[(S, S + SBSTATE_SIZEOF); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256); (a_exc a, a_exc a + 4 * sbd_subframeSize s);
(a_oq a, a_oq a + 32); (a_iq a, a_iq a + 32); (a_pg a, a_pg a + 16); (a_er a, a_er a + 16); (a_msp a, a_msp a + 64)].
Proof. intros. reflexivity. Qed.

Ltac transport_after_call segs m m' MU WM ::=
sb_box_junk;
cbv beta iota delta [ctlW sbW] in MU; rewrite ?blocks_ivs_app, ?blocks_ivs_sb9 in MU;
cbv beta iota delta [creq_ivs creq_size app lsp_order] in MU;
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : bits_rep segs m ?A2 ?D2 ?b2 |- _ =>
first [ apply (bits_rep_frame segs m m' A2 D2 b2 W) in H;
[ | solve [eauto] | exact MU | exact WM | cbn [disjoint_from]; slia | cbn [disjoint_from]; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : EXCREADY m ?sl ?d, R : DREP ?o ?st m ?sl ?d ?L |- _ =>
first [ apply (excready_munch o st m m' sl d L W R) in H; [ | exact MU | exact WM | repeat (apply Forall_cons; [cbn [fst snd]; slia|]); first [apply Forall_nil | slia] ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : DREP ?o ?st m ?sl ?d ?L |- _ =>
first [ apply (drep_munch o st m m' sl d L W) in H; [ | exact MU | exact WM | repeat (apply Forall_cons; [cbn [fst snd]; slia|]); first [apply Forall_nil | slia] ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : rtables_pristine m |- _ =>
first [ apply (rtables_pristine_munch' W m m') in H; [ | exact MU | cbn [disjoint_from]; unfold RTABLES_LO, RTABLES_HI; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stderr_wfile m |- _ =>
first [ apply (stderr_wfile_munch m m' W) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ssp_cells m ?c |- _ =>
first [ apply (ssp_cells_munch m m' W c) in H; [ | exact MU | exact WM | cbn [disjoint_from]; unfold X1fl.got_ssp; slia | cbn [disjoint_from]; unfold X1fl.ssp_guard; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H;
[ | eapply (munch_weaken W Wq m m'); [ sb_subfp | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end;
nb_unbox_junk.

Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.

Lemma stk_store_ok : forall m lo hi a (j : nat),
stk rsegs m lo hi -> lo <= a -> a + Z.of_nat j <= hi -> store_ok rsegs m (wa a) j = true.
Proof.
intros m lo hi a j (H0 & H1 & H) Hlo Hhi.
replace a with (lo + (a - lo)) by lia. apply (wr_at_store_ok rsegs m lo (hi - lo)); [| lia | lia].
split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (H (lo + i) ltac:(lia))).
Qed.
Lemma lts_ge_false' : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma lts_true' : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> a < b ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_lt. lia. Qed.

Lemma vla16 : forall n, (n = 4 \/ n = 8 \/ n = 40 \/ n = 80) -> Z.land (4 * n + 15) (-16) = 4 * n.
Proof. intros n [-> |[-> |[-> | ->]]]; reflexivity. Qed.
Lemma vla16' : forall n, (n = 4 \/ n = 8 \/ n = 40 \/ n = 80) -> Z.land (n * 4 + 15) (-16) = 4 * n.
Proof. intros n H. rewrite (Z.mul_comm n 4). apply vla16. exact H. Qed.

