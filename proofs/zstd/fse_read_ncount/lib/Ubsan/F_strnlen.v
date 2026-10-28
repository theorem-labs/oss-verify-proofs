(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memchr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Open Scope bv_scope.
Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
(Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ bytes_at usegs m' (bv_unsigned a0) buf.
Lemma strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
stk usegs m lo (bv_unsigned sp) ->
bytes_at usegs m (bv_unsigned a0) buf ->
memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
mem_inv usegs m ->
(lo <= bv_unsigned sp - 32)%Z ->
(bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(0 < bv_unsigned a0)%Z ->
evt usegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c62c) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros ST BUF OK MI LO SEP A0.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
Local Ltac2 Set LiaHints.tbl := fun () => "00U0>11805467289.5611805467289.5811805467289.5917221588796.5619006120615.5921446233972.5923230285244.5825566553219.5925566553219.7625566553219.7826216087156.5627294894486.6533680001082.5634290115814.4938806986883.5638806986883.7438806986883.7639945551616.6839945925021.6941564619544.6741564619544.6843061775753.4745221239098.5949961420788.585180980284.59 53506443062.6553519189168.5054618151079.5855104759171.5855104759171.7555104759171.77563227834.58  59314923118.696166287527.56 61943857494.698931259039.69 8935173664.83 00000100200300700800=00A00B00C00G00L00M00Q00R00S00T00X00\00c00d00h00l01001501901:01;01<01=01>01B01F01O01P01T01^01hSSSS2HBSS3SEPS2HBSSS2HlS3SEPSS2HBSSSS2HlS2LOS2LO2HlSS2HlS2LOS2HBS3SEPS2HBSSSSSS2HlS2HBS2A02Hl1KSS2HlS2A02AB2HlS2A02AB2Hl".
carve_frame 32%nat ST.
do 9 zstep.
call memchr_spec.
1:{ exact BUF. }
1:{ rewrite unsigned_lit by lia. exact OK. }
1:{ assumption. }
rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
unfold memchr_res.
destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
- pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
zstep. if_cases K; zify_cond K. { exfalso. lia. }
do 7 zstep.
replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
by (unfold strnlen_res; rewrite FB; lia).
release_frame FR ST (bv_unsigned sp). finish.
- zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
do 6 zstep.
lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
release_frame FR ST (bv_unsigned sp). finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
