(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Arr Walk Image.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout R_cache_defs R_glue_defs R_quar_defs R_qrec_defs R_qput R_qdrain R_qmerge R_qrecycle R_qmerge3.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_R_qrecycle_C () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A23;R_glue_defs:qcache_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs3qwfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;R_quar_defs6qbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53A238R_qdrain6q_lockC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53A23;R_quar_defs3r24C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:R_qrecycle;qrec_A_specC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239R_qmerge3:merge_specC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma qrec_A_spec_closed : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (CACHE STACK : word) (MIN SB lo : Z) (gl : list batch),
  qcache_rep m QG gl -> qwf SB gl -> (qbytes gl < 2^56)%Z -> (0 <= MIN < 2^63)%Z -> (0 < SB)%Z -> q_lock m 0 1 ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96)%Z -> (r24 SB + 2^32 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (qrec_E_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 CACHE STACK F fc
               ([(q_lockw, q_lockw + 4); (QG, QG + 32); (bv_unsigned sp - 96, bv_unsigned sp)] ++ bivs gl)%Z
               (rec_x gl MIN) (rec_r gl MIN) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 QUAR) (Z_to_bv 64 MIN) CACHE STACK a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qrecycle_entry) fc None m (seg_rom asegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_R_qrecycle_C ()) [] "h05CACHEh11Fh23MINh32SBh45STACKh52a4h62a5h72a6h82a7h92fch:2glh;2gph<2loh=1mh>2rah?2s0h@2s1hA3s10hB3s11hC2s2hD2s3hE2s4hF2s5hG2s6hH2s7hI2s8hJ2s9hK2sphL2t0hM2t1hN2t2hO2t3hP2t4hQ2t5hR2t6hS2tpp;1p;2p;3p;4p;`g0000j11Tg000Uj15Tg0013j17Tg001Vj10Tg002;j2HTg002gj1DTg003Ij2;Tg003ij1:Tg004Ij13Tg004gj3>Tg005ij2=Tg006dj1<Tg007bj26Tg008?j29Tg008[j24Tg0097j2GTg009Rj3FTg00:Mj28Tg00;7j4CTg00;lj2BTg00<Ij1ATg00=Dj2@Tg00=aj2?Tg00>Xl`ETf0R0#1#1p=2g00?ZR1#1R2#2R3#2R4#1#5R5#7R6%02R7#5/H6%54#7%53#7#D\6g00@?R31;33#:,;3#:f6R8%11#2#0#1#0#0#1#0#1#2#2#0#1#0#2#2#3;>0f3R9f1R:'=f2R;#<%32R2%01R<#0R=#1#2#3'6'9g00@]R>/48%0=#0#0#3,62,98'G19>8f;R=%317F>g00A;R>f<R1f7R?fXR@,85CCf8RAfYRB,85%1<#2#2#3'B'4f:R<#A%34,62'@f9R4'4f[RC,85%07#0#0#3,62'4f@R2,?>f^f]f\PCfZPBP@fWfVfUfTfSfRfQfPfOfNfMfLfKfJfIfHfGfFfEfDfCfBfAP2f?f>f=P1P=g00B3P<P4PAP?P8f5f4P9P;P:P0M`EUUUUUUUUUUUW:X<3X33W2X46X06W=W9W1XR6XQ6XP6XO6XB6XA6XJ6XI6XH6XG6XF6XE6XD6XC6X86X76X66X56X@6X?6XN6XM6XL6XS6X;6XK6W>o"). Qed.
