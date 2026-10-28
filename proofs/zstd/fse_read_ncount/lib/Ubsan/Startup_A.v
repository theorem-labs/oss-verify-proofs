(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun STRW_tac Startup_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_memset F_memcpy.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation rsegs := UImg.usegs.
Notation RLIBC := 0x4f1c0%Z (only parsing).
Notation RTLL := 0x4ef38%Z (only parsing).
Notation RTD := 0x2ee68%Z (only parsing).
Notation RTP := 0x2ef30%Z (only parsing).
Notation RSYSINFO := 0x4f1a8%Z (only parsing).
Notation RDEFSTACK := 0x1edd0%Z (only parsing).
Notation RGOT_DYNAMIC := 0x1db38%Z (only parsing).
Definition rinit_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (sysinfo auxvp page_size : word) (m : word -> option byte) (t : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RTD, 0x2efb8); (0x4ef40, 0x4ef70); (RLIBC, 0x4f228)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
(Z_to_bv 64 0x2eee0) (Z_to_bv 64 0x4f1f8) (Z_to_bv 64 0x2ef40) z64)
/\ rw_cells rsegs m' RLIBC (libc_cells (Z_to_bv 8 1) auxvp (Z_to_bv 64 224) (Z_to_bv 64 8) page_size)
/\ rw_cells rsegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
/\ rw_cells rsegs m' RSYSINFO [C8 sysinfo]
/\ rw_cells rsegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
/\ rw_cells rsegs m' RGOT_DYNAMIC [C8 z64]
/\ (0 < t < 4194304)%Z.
Lemma rinit_tls_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sysinfo page_size auxvp : word),
stk rsegs m lo (bv_unsigned sp) ->
rw_cells rsegs m (bv_unsigned a0 + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 10)] ->
rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) auxvp z64 z64 page_size) ->
rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
rw_cells rsegs m RSYSINFO [C8 sysinfo] ->
rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
mem_inv rsegs m ->
(lo <= bv_unsigned sp - 64)%Z -> (0x50000 <= lo)%Z ->
(bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 48 <= 2^64)%Z ->
impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid)
(epost (rinit_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo sysinfo auxvp page_size m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x14a6c) fc None m (seg_rom rsegs)).
Proof.
intros until auxvp. intros ST AUX TDC LC MT SI DS GD MI LO LOLO A0LO A0HI.
unfold td_cells, libc_cells in *.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RTD, 0x2efb8); (0x4ef40, 0x4ef70); (RLIBC, 0x4f228)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
apply impl_enode.
Local Ltac2 Set LiaHints.tbl := fun () => "01A0>10146958134.5711912744615.6412367362435.6412367362435.6914688241258.6815047425079.571527479463.63 16755391217.7016783546602.7017646078182.5617829607510.5718614651754.7019455218034.5720477992146.5721659150374.5721918414723.6421918414723.6823840393334.57239629926.57  24201315450.5725314760359.6525480695794.5726689785713.7027001829489.7029337639238.5731902214762.7033039531175.6534793062946.5735348392294.5736169207658.7036423489301.6036935961841.7036993589379.6536993589379.6937179979249.7037247810541.5737694659606.5737783947379.693828603370.70 39226607666.573945979267.65 3945979267.69 41332440703.6941474177302.5941809558659.6341809558659.6741960863026.5743060403331.6643060403331.7043061415849.5444832123242.7046995586026.7047392732017.7048543174498.5749206852870.5749345641752.5951481786499.6551481786499.7051760532470.6353541764610.5754829261425.7055255588418.5756150179194.5956228262055.6456555195377.6857451325814.5757454708842.7057639039217.7058193956502.5759245058545.6759950529258.7060025031335.666120414314.67 61264284866.5765042022385.706576192881.70 67800801447.6567948467434.70706553106.57  7327131507.66 984575878.57  00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00L00M00N00R00S00T00U00V00W00X00Y00Z00[00\00]00^00b00c00d00e00f00g00k00l00m00n00o01001101201301401501601701;01<01=01>01?01@01A01B01C01D01E01F01G01H01I01J01K01L01MFSSSSFSSSSFSFFFSSFFFSFSSFSSFFSS2LOSSSSFFSSFSSSS2HtSSFSSS2LOSSSFFSSSSFSFS2HtSSFSSFSSSSFSSSSFSF".
carve_frame 64%nat ST.
steps_to 0x14b44%Z.
steps_to 0x14cc8%Z.
step_ecall.
split. { at_node_solve. }
intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [ci [-> Ht]].
sys_nret.
steps_to 0x14d18%Z.
release_frame FR ST (bv_unsigned sp). astep.
unfold rinit_tls_post, td_cells, libc_cells. cbv delta [Fork.PID_MAX_ENVELOPE] in Ht. sys_finish; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
