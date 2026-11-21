(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.I7S Require SBase S_U2C SMemsetOk. (* 1.4: S_ZAw Requires SMemsetOk (inflateInit_'s memset) *)

Module S_U2A.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.I7S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition L_ZA : Z := 86380.              (* 0x150f0: inflateInit_ after jalr zalloc *)
Definition L_CALL2 : Z := 85652.           (* 0x14e30: uncompress2_z, mv a0,sp before the first jal inflate *)
Definition RA_II : Z := 85540.             (* 0x14dc0: uncompress2_z after jal inflateInit_ *)

End FXG.
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma mem_u32_relit : forall M a e e', mem_u32 R_segs M a e -> e mod 4294967296 = e' mod 4294967296 -> mem_u32 R_segs M a e'.
Proof.
  intros M a e e' H E. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

(* 1.4: a u32 / u64 zero inside a memset region *)
Lemma mz_u32 : forall M a len off, mem_zero R_segs M a len -> 0 <= off -> off + 4 <= len -> 0 <= a + off ->
  a + off + 4 <= two64 -> mem_u32 R_segs M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u32, mem_is. change (length (Z_to_le_bytes 4 0)) with 4%nat.
  rewrite (mem_zero_sub R_segs M a len off 4 Hz) by lia. reflexivity.
Qed.
Lemma mz_u64 : forall M a len off, mem_zero R_segs M a len -> 0 <= off -> off + 8 <= len -> 0 <= a + off ->
  a + off + 8 <= two64 -> mem_u64 R_segs M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u64, mem_is. change (length (Z_to_le_bytes 8 0)) with 8%nat.
  rewrite (mem_zero_sub R_segs M a len off 8 Hz) by lia. reflexivity.
Qed.

(* 1.4: split the u64 fact at a (on the current memory) into its two u32 halves *)
End FXG.
Ltac split64 a ahi nlo nhi :=
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    match goal with H : mem_u64 R_segs Mx a _ |- _ =>
      pose proof (mem_u64_lo32 _ _ _ _ H) as nlo; pose proof (mem_u64_hi32 _ _ _ _ H) as nhi; cbn in nhi;
      replace (a + 4) with ahi in nhi by lia
    end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Theorem za_prefix_s : forall Rb l M MD T (u p q n zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS1 = u -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = 262144 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + 208 <= 140737488355328 -> u mod 16 = 0 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= zc ->
  ZSEP (p + STATE_SIZE <= q \/ q + n <= p) -> ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p) ->
  rom_ok M -> mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  mem_arr 1 R_segs M q n fin ->
  mem_u64 R_segs M (u + -32) BUF -> mem_u64 R_segs M (u + -24) (u + 168) -> mem_u64 R_segs M (u + -16) (u + 176) ->
  mem_u64 R_segs M (u + -8) RA_II ->
  mem_u64 R_segs M u q -> mem_u32 R_segs M (u + 8) 0 ->
  mem_u64 R_segs M (u + 64) A_ZCALLOC -> mem_u64 R_segs M (u + 72) A_ZCFREE -> mem_u64 R_segs M (u + 80) 0 ->
  (forall R' M' (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z),
     zget R' kSP = u ->
     zget R' kS0 = u + 176 -> zget R' kS1 = u + 168 -> zget R' kS2 = 4294967295 -> zget R' kS3 = 0 -> zget R' kS4 = 0 ->
     zget R' kS5 = s5 -> zget R' kGP = gp -> zget R' kTP = tp ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     rom_ok M' -> mem_wr R_segs M' (u + -1024) 1232 -> mem_wr R_segs M' p STATE_SIZE -> mem_arr 1 R_segs M' q n fin ->
     mem_u64 R_segs M' u q -> mem_u32 R_segs M' (u + 8) n -> mem_u64 R_segs M' (u + 24) BUF -> mem_u32 R_segs M' (u + 32) 262144 ->
     mem_u64 R_segs M' (u + 56) p -> mem_u64 R_segs M' (u + 64) A_ZCALLOC -> mem_u64 R_segs M' (u + 72) A_ZCFREE -> mem_u64 R_segs M' (u + 80) 0 ->
     mem_u64 R_segs M' p u -> mem_u32 R_segs M' (p + 8) HEAD -> mem_u32 R_segs M' (p + 12) 0 ->
     mem_u32 R_segs M' (p + 16) 5 -> mem_u32 R_segs M' (p + 28) (-1) -> mem_u64 R_segs M' (p + 56) 0 ->
     mem_u32 R_segs M' (p + 68) 15 -> mem_u32 R_segs M' (p + 72) 0 -> mem_u32 R_segs M' (p + 76) 0 -> mem_u32 R_segs M' (p + 80) 0 ->
     mem_u64 R_segs M' (p + 88) 0 -> mem_u64 R_segs M' (p + 96) 0 -> mem_u32 R_segs M' (p + 104) 0 ->
     mem_u32 R_segs M' (p + 108) vlen -> mem_u32 R_segs M' (p + 112) vofs -> mem_u32 R_segs M' (p + 116) vext ->
     mem_u64 R_segs M' (p + 120) (p + 1384) -> mem_u64 R_segs M' (p + 128) (p + 1384) ->
     mem_u32 R_segs M' (p + 136) vlb -> mem_u32 R_segs M' (p + 140) vdb ->
     mem_u32 R_segs M' (p + 144) vnc -> mem_u32 R_segs M' (p + 148) vnl -> mem_u32 R_segs M' (p + 152) vnd -> mem_u32 R_segs M' (p + 156) vsh ->
     mem_u64 R_segs M' (p + 160) (p + 1384) -> mem_u32 R_segs M' (p + 7160) 1 ->
     0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
     0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
     mpostL R_segs M M' [(u + -80, 48); (u, 112); (p, STATE_SIZE)] ->
     realizes R_segs (zcfg R_segs L_CALL2 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin
         Hh Lsp Ls1 La0 Ls3 Ls4 Lgp Ltp Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Sprom
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 K.
  zkeysb. unfold L_ZA, L_CALL2, RA_II in *. cbv [STATE_SIZE FRA ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF HEAD DATA_LO DATA_LEN] in *.
  pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M [(u + -80, 48); (u, 112); (p, 7176)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X [(u + -80, 48); (u, 112); (p, 7176)]) M) by (apply mpostL_refl).
  (* inflateInit_ after zalloc: the state pointer is not NULL; memset(p + 8, 0, 7168) *)
  zbr Rfd false.                      (* 150f0 beqz a0 *)
  zstep Rfd.                          (* 150f4 mv s0,a0 *)
  zstep Rfd.                          (* 150f8 addi a0,a0,8 *)
  zstep Rfd.                          (* 150fc li a2,7 *)
  tstep1 Rfd.                         (* 15100 slli a2,a2,10 *)
  zstep Rfd.                          (* 15104 li a1,0 *)
  zstep Rfd.                          (* 15108 jal memset *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc) ?Mx _) _ =>
    eapply (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.I7S.SMemsetOk.memset7168_ok R lc Mx MD T (p + 8) 86408 Hh) end.
  - zreg. - zreg. - zreg. - zreg. - reflexivity.
  - eapply mem_wr_sub; [exact Wp | lia | lia].
  - lia. - lia.
  - Z.to_euclidean_division_equations; lia.
  - intros M1 R1 HP HZ HW1 E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
    zimps. apply mpost_mpostL1 in HP. zreattachL HP.
    (* the fields memset leaves zero and nothing below stores over *)
    pose proof (mz_u64 M1 (p + 8) 7168 80 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z88.
    pose proof (mz_u32 M1 (p + 8) 7168 100 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z108.
    pose proof (mz_u32 M1 (p + 8) 7168 104 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z112.
    pose proof (mz_u32 M1 (p + 8) 7168 108 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z116.
    pose proof (mz_u32 M1 (p + 8) 7168 128 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z136.
    pose proof (mz_u32 M1 (p + 8) 7168 132 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z140.
    pose proof (mz_u32 M1 (p + 8) 7168 136 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z144.
    pose proof (mz_u32 M1 (p + 8) 7168 140 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z148.
    pose proof (mz_u32 M1 (p + 8) 7168 144 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z152.
    pose proof (mz_u32 M1 (p + 8) 7168 148 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z156.
    replace (p + 8 + 80) with (p + 88) in Z88 by lia.
    replace (p + 8 + 100) with (p + 108) in Z108 by lia. replace (p + 8 + 104) with (p + 112) in Z112 by lia.
    replace (p + 8 + 108) with (p + 116) in Z116 by lia. replace (p + 8 + 128) with (p + 136) in Z136 by lia.
    replace (p + 8 + 132) with (p + 140) in Z140 by lia. replace (p + 8 + 136) with (p + 144) in Z144 by lia.
    replace (p + 8 + 140) with (p + 148) in Z148 by lia. replace (p + 8 + 144) with (p + 152) in Z152 by lia.
    replace (p + 8 + 148) with (p + 156) in Z156 by lia.
    clear HZ.
    (* back in inflateInit_: state->strm, mode = HEAD, strm->state; wrap 5, wbits 15; inflateReset *)
    tstep1 Rfd.                       (* 1510c lui a0,0x4 *)
    zstep Rfd.                        (* 15110 mv a1,s1 *)
    zstep Rfd.                        (* 15114 ld a2,64(s1) *)
    zstep Rfd.                        (* 15118 addi a0,a0,-204 *)
    zstep Rfd.                        (* 1511c sd s1,0(s0) *)
    zstep Rfd.                        (* 15120 sw a0,8(s0) *)
    zstep Rfd.                        (* 15124 sd s0,56(s1) *)
    zbr Rfd false.                    (* 15128 beqz a2 *)
    zstep Rfd.                        (* 1512c li a0,5 *)
    zstep Rfd.                        (* 15130 li a2,15 *)
    tstep1 Rfd.                       (* 15134 slli a0,a0,32 *)
    tstep1 Rfd.                       (* 15138 slli a2,a2,32 *)
    zstep Rfd.                        (* 1513c addi a0,a0,5 *)
    zstep Rfd.                        (* 15140 addi a2,a2,15 *)
    zstep Rfd.                        (* 15144 sd a0,16(s0) *)
    zstep Rfd.                        (* 15148 sd a2,64(s0) *)
    split64 (p + 16) (p + 20) W16 W20. split64 (p + 64) (p + 68) W64 W68.
    zstep Rfd.                        (* 1514c mv a0,a1 *)
    zstep Rfd.                        (* 15150 jal inflateReset *)
    (* inflateReset (0x14f0c): frame 32; the state checks *)
    zstep Rfd.                        (* 14f0c addi sp,sp,-32 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* sd ra, s0, s1, s2 *)
    zstep Rfd.                        (* 14f20 mv s0,a0 *)
    zstep Rfd.                        (* 14f24 li a0,-2 *)
    zbr Rfd false.                    (* 14f28 beqz s0 *)
    zstep Rfd. zbr Rfd false.         (* ld a1,64(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a2,72(s0); beqz a2 *)
    zstep Rfd. zbr Rfd false.         (* ld s2,56(s0); beqz s2 *)
    zstep Rfd. zbr Rfd true.          (* ld a1,0(s2); beq a1,s0 *)
    zstep Rfd.                        (* 14f64 lw a1,8(s2) *)
    tstep1 Rfd.                       (* 14f68 lui a3,0xffffc *)
    zstep Rfd.                        (* 14f6c addi s1,a3,204 *)
    zstep Rfd.                        (* 14f70 addw a1,a1,s1 *)
    zstep Rfd.                        (* 14f74 li a3,31 *)
    zbr Rfd false.                    (* 14f78 bltu a3,a1 *)
    zstep Rfd.                        (* 14f7c lw a3,64(s2) *)
    zstep Rfd.                        (* 14f80 lw a1,68(s2) *)
    zbr Rfd true.                     (* 14f84 beq a1,a3: the window size is unchanged *)
    zstep Rfd.                        (* 14fc8 lw a1,20(s2) *)
    zstep Rfd.                        (* 14fcc sw a1,16(s2) *)
    zstep Rfd.                        (* 14fd0 sd zero,72(s2) *)
    zstep Rfd.                        (* 14fd4 sw zero,80(s2) *)
    (* the keep-reset part, inline *)
    zstep Rfd. zbr Rfd false.         (* ld a1,72(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a1,56(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a2,0(a1); bne a2,s0 *)
    zstep Rfd.                        (* 14ff0 lw a2,8(a1) *)
    zstep Rfd.                        (* 14ff4 addw a2,a2,s1 *)
    zstep Rfd.                        (* 14ff8 li a3,31 *)
    zbr Rfd false.                    (* 14ffc bltu a3,a2 *)
    zstep Rfd.                        (* 15000 sd zero,48(a1) *)
    zstep Rfd.                        (* 15004 sd zero,16(s0) *)
    zstep Rfd.                        (* 15008 sd zero,40(s0) *)
    zstep Rfd.                        (* 1500c sd zero,48(s0) *)
    zstep Rfd.                        (* 15010 lwu a0,16(a1) *)
    tstep1 Rfd.                       (* 15014 lui a2,0x2 *)
    zstep Rfd.                        (* 15018 addiw a2,a2,-1032 *)
    zstep Rfd.                        (* 1501c add a2,a1,a2 *)
    zstep Rfd.                        (* 15020 sw zero,88(s0) *)
    zbr Rfd false.                    (* 15024 beqz a0 *)
    zstep Rfd.                        (* 15028 andi a0,a0,1 *)
    zstep Rfd.                        (* 1502c sd a0,96(s0) *)
    zstep Rfd.                        (* 15030 li a0,0 *)
    tstep1 Rfd.                       (* 15034 lui a3,0x4 *)
    zstep Rfd.                        (* 15038 li a4,-1 *)
    zstep Rfd.                        (* 1503c addi a5,a1,1384 *)
    zstep Rfd.                        (* 15040 sd a5,160(a1) *)
    zstep Rfd.                        (* 15044 sd zero,96(a1) *)
    zstep Rfd.                        (* 15048 sw zero,104(a1) *)
    zstep Rfd.                        (* 1504c sd a5,120(a1) *)
    zstep Rfd.                        (* 15050 sd a5,128(a1) *)
    tstep1 Rfd.                       (* 15054 lui a5,0x8 *)
    zstep Rfd.                        (* 15058 addiw a3,a3,-204 *)
    tstep1 Rfd.                       (* 1505c slli a4,a4,32 *)
    zstep Rfd.                        (* 15060 sd a3,8(a1) *)
    zstep Rfd.                        (* 15064 sd a4,24(a1) *)
    zstep Rfd.                        (* 15068 sw a5,32(a1) *)
    zstep Rfd.                        (* 1506c sd zero,56(a1) *)
    zstep Rfd.                        (* 15070 addi a4,a4,1 *)
    zstep Rfd.                        (* 15074 sd a4,0(a2) *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra, s0, s1, s2 *)
    zstep Rfd.                        (* 15088 addi sp,sp,32 *)
    zret Rfd.                         (* 1508c ret *)
    (* inflateInit_ returns Z_OK *)
    zbr Rfd true.                     (* 15154 beqz a0 *)
    zstep Rfd.                        (* 151c8 li a3,0 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra, s0, s1, s2 *)
    zstep Rfd.                        (* 151dc addi sp,sp,32 *)
    zstep Rfd.                        (* 151e0 mv a0,a3 *)
    zret Rfd.                         (* 151e4 ret *)
    (* uncompress2_z: next_out = BUF, avail_out = 0, max = 2^32 - 1; the first refills *)
    zbr Rfd false.                    (* 14dc0 bnez a0 *)
    zstep Rfd.                        (* 14dc4 or a0,s2,s4 *)
    zbr Rfd true.                     (* 14dc8 bnez a0 *)
    zstep Rfd.                        (* 14dd0 sd s2,24(sp) *)
    zstep Rfd.                        (* 14dd4 sw zero,32(sp) *)
    zstep Rfd.                        (* 14dd8 li a1,-1 *)
    tstep1 Rfd.                       (* 14ddc srli s2,a1,32 *)
    zbr Rfd true.                     (* 14de0 beqz zero *)
    zstep Rfd.                        (* 14e00 mv a0,s4 *)
    zbr Rfd true.                     (* 14e04 bltu s4,s2 *)
    zstep Rfd.                        (* 14e0c sw a0,32(sp) *)
    zstep Rfd.                        (* 14e10 sub s4,s4,a0 *)
    zstep Rfd.                        (* 14e14 lw a0,8(sp) *)
    zbr Rfd false.                    (* 14e18 bnez a0 *)
    zstep Rfd.                        (* 14e1c mv a0,s3 *)
    zbr Rfd true.                     (* 14e20 bltu s3,s2 *)
    zstep Rfd.                        (* 14e28 sw a0,8(sp) *)
    zstep Rfd.                        (* 14e2c sub s3,s3,a0 *)
    (* at L_CALL2: the K facts *)
    split64 (p + 8) (p + 12) C8 C12. split64 (p + 24) (p + 28) C24 C28. split64 (p + 72) (p + 76) C72 C76.
    split64 (p + 7160) (p + 7164) C7160 C7164.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (K R' Mx 0 0 0 0 0 0 0 0 0) end;
      first [ zreg | assumption | exact HAG | lia
            | lazymatch goal with |- mem_u32 _ _ _ _ => idtac | |- mem_u64 _ _ _ _ => idtac end;
              match goal with H : mem_u32 R_segs ?My ?a ?v |- mem_u32 R_segs ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H
                                       | (eapply (mem_u32_relit _ _ _ _ H); reflexivity)]
                            | H : mem_u64 R_segs ?My ?a ?v |- mem_u64 R_segs ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H] end
            | match goal with |- ?G => idtac "KSIDE" G end ].
Qed.
End FXG.
End S_U2A.


