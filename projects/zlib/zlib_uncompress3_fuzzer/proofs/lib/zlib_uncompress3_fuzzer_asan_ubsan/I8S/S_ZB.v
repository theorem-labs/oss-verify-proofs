(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require SBase S_Entry S_U2C SMemsetOk. (* 1.4: S_ZAw Requires SMemsetOk (inflateInit_'s memset) *)

Module S_U2A.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Definition L_ZA : Z := 86484.              (* 0x150f0: inflateInit_ after jalr zalloc *)
Definition L_CALL2 : Z := 85756.           (* 0x14e30: uncompress2_z, mv a0,sp before the first jal inflate *)
Definition RA_II : Z := 85644.             (* 0x14dc0: uncompress2_z after jal inflateInit_ *)

End FXG.
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Lemma mem_u32_relit : forall M a e e', mem_u32 R_segs M a e -> e mod 4294967296 = e' mod 4294967296 -> mem_u32 R_segs M a e'.
Proof.
  intros M a e e' H E. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

(* 1.4: uncompress2_z tests dest | left (`or a0,s2,s4; bnez a0`): nonzero when dest is *)
Lemma lor_nz_u64 : forall d o, 1 <= d < 18446744073709551616 -> 0 <= o < 18446744073709551616 ->
  Z.lor d o <> 0 /\ 0 <= Z.lor d o < 18446744073709551616.
Proof.
  intros d o Hd Ho. split; [| split].
  - intros E. apply Z.lor_eq_0_iff in E. lia.
  - apply Z.lor_nonneg. lia.
  - assert (P : 0 < Z.lor d o).
    { assert (N : 0 <= Z.lor d o) by (apply Z.lor_nonneg; lia).
      assert (Z : Z.lor d o <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia). lia. }
    change 18446744073709551616 with (2 ^ 64). apply Z.log2_lt_pow2; [exact P |].
    rewrite Z.log2_lor by lia.
    assert (Ld : Z.log2 d < 64) by (apply Z.log2_lt_pow2; [lia | change (2 ^ 64) with 18446744073709551616; lia]).
    destruct (Z.eq_dec o 0) as [E0 | N0].
    + subst o. change (Z.log2 0) with 0. lia.
    + assert (Lo : Z.log2 o < 64) by (apply Z.log2_lt_pow2; [lia | change (2 ^ 64) with 18446744073709551616; lia]). lia.
Qed.

Theorem za_prefix_s : forall Rb l M MD T (u p q n zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (dest osz : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS1 = u -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = osz -> 0 <= osz <= 262144 -> 1 <= dest < two64 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + 208 <= 140737488355328 -> u mod 16 = 0 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= zc ->
  ZSEP (p + STATE_SIZE <= q \/ q + n <= p) -> ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p) ->
  rom_ok M -> mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  mem_arr 1 R_segs M q n fin ->
  mem_u64 R_segs M (u + -32) dest -> mem_u64 R_segs M (u + -24) (u + 168) -> mem_u64 R_segs M (u + -16) (u + 176) ->
  mem_u64 R_segs M (u + -8) RA_II ->
  mem_u64 R_segs M u q -> mem_u32 R_segs M (u + 8) 0 ->
  mem_u64 R_segs M (u + 64) A_ZCALLOC -> mem_u64 R_segs M (u + 72) A_ZCFREE -> mem_u64 R_segs M (u + 80) 0 ->
  (forall R' M' (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z),
     zget R' kSP = u ->
     zget R' kS0 = u + 176 -> zget R' kS1 = u + 168 -> zget R' kS2 = 4294967295 -> zget R' kS3 = 0 -> zget R' kS4 = 0 ->
     zget R' kS5 = s5 -> zget R' kGP = gp -> zget R' kTP = tp ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     rom_ok M' -> mem_wr R_segs M' (u + -1024) 1232 -> mem_wr R_segs M' p STATE_SIZE -> mem_arr 1 R_segs M' q n fin ->
     mem_u64 R_segs M' u q -> mem_u32 R_segs M' (u + 8) n -> mem_u64 R_segs M' (u + 24) dest -> mem_u32 R_segs M' (u + 32) osz ->
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
  intros Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin dest osz
         Hh Lsp Ls1 La0 Ls3 Ls4 Hosz Hdest Lgp Ltp Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
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
    eapply (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.SMemsetOk.memset7168_ok R lc Mx MD T (p + 8) 86512 Hh) end.
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
    (* 1.4: dest | left is nonzero because dest (the harness buffer) is; left may be 0 *)
    pose proof (lor_nz_u64 dest osz ltac:(lia) ltac:(lia)) as (HORnz & HORr).
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

Module S_ZA.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.SBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_Entry.S_Loop OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Ret OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_Entry OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Uw OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Leave OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Inflate S_U2A OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Lemma le_cell_range : forall k bs i, 0 < k <= 8 -> 0 <= le_cell k bs i < 2 ^ (8 * k).
Proof.
  intros k bs i Hk. unfold le_cell.
  pose proof (bytes_le_to_Z_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs))) as H0.
  pose proof (bytes_le_to_Z_bound (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs))) as H1.
  pose proof (firstn_le_length (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)) as Hl.
  assert (2 ^ (8 * Z.of_nat (length (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma mem_wr_arrk_exists : forall k M base n,
  0 < k <= 8 -> 0 <= n -> 0 <= base -> base + k * n <= two64 ->
  mem_wr R_segs M base (k * n) ->
  exists f, mem_arr k R_segs M base n f /\ (forall i, 0 <= f i < 2 ^ (8 * k)).
Proof.
  intros k M base n Hk Hn Hb Hbn W.
  destruct (mem_wr_readable R_segs wr_rd_R M base (k * n) W ltac:(lia)) as (bs & Hbs & Hlen).
  exists (le_cell k bs). split.
  - apply (mem_arr_of_bytes R_segs k M base n bs Hbs); lia.
  - intros i. apply le_cell_range. exact Hk.
Qed.

Section ZA.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Variable zm : bool. Variable osz : Z.
Hypothesis HOSZ : if zm then osz = 0 else 1 <= osz /\ osz <= 262144.
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Definition st_init (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z) : ist :=
  IST HEAD 0 (-1) 0 0 0 0 osz 0 vlen vofs vext (CDyn 0) (CDyn 0) vlb vdb vnc vnl vnd vsh 0 0 0.

Lemma ainv_init : forall (lf cf : Z -> Z) vlen vofs vext vlb vdb vnc vnl vnd vsh W0 ra,
  (forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536) -> (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) ->
  0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
  0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
  ainv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz 0 0 0 W0 ra) (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf.
Proof.
  intros lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh W0 ra Hlf Hcf R1 R2 R3 R4 R5 R6 R7 R8 R9.
  pose proof two64_eq as TW64. assert (Hosz : 0 <= osz <= 262144) by (clear - HOSZ; destruct zm; lia_std).
  unfold ainv, RNG, WIN, MODE, st_init, cxc; icx_cbn. cbv [N_CODES N_LENS WIN_SIZE]. cbv [N_CODES N_LENS] in Hlf, Hcf.
  split; [| split].
  - split_conj; first [assumption | lia_std | change (2 ^ 0) with 1; lia_std].
  - split; [intros _; split; reflexivity | intros C; exfalso; exact (C eq_refl)].
  - split_conj.
    + left. reflexivity.
    + intros _. split; [left; reflexivity | reflexivity].
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. unfold codes_liveP. cbv [LEN_ LIT HEAD]. lia_std.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros [E|E]; exfalso; revert E; cbv; discriminate.
Qed.

Theorem za_cps : forall Rb l M,
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS1 = u -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = osz -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  rom_ok M -> mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  mem_arr 1 R_segs M q n fin ->
  mem_u64 R_segs M (u + -32) (ob u zm) -> mem_u64 R_segs M (u + -24) (u + 168) -> mem_u64 R_segs M (u + -16) (u + 176) ->
  mem_u64 R_segs M (u + -8) RA_II ->
  mem_u64 R_segs M (u) q -> mem_u32 R_segs M (u + 8) 0 ->
  mem_u64 R_segs M (u + 64) A_ZCALLOC -> mem_u64 R_segs M (u + 72) A_ZCFREE -> mem_u64 R_segs M (u + 80) 0 ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M zm osz 0 ->
  KZW u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc zm osz 0 ->
  realizes R_segs (zcfg R_segs L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M Lsp Ls1 La0 Ls3 Ls4 Ls5 Lgp Ltp Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 HZE2 HZW.
  pose proof two64_eq as TW64. assert (Hosz : 0 <= osz <= 262144) by (clear - HOSZ; destruct zm; lia_std).
  assert (Hob : 1 <= ob u zm < two64) by (unfold ob; clear - Hu0 Hzimg Hu1; destruct zm; cbv [BUF FRA DATA_LO DATA_LEN] in *; lia_std).
  assert (Hwph : wok p q n zc 0).
  { unfold wok, ZSEP. cbv [WIN_SIZE ]. pose proof Hzimg as Hz'. cbv [DATA_LO DATA_LEN] in Hz'. split_conj; try lia_std; try (left; reflexivity). reflexivity. }
  eapply (za_prefix_s Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin (ob u zm) osz Hh); try eassumption.
  intros R' M' vlen vofs vext vlb vdb vnc vnl vnd vsh.
  intros Gsp Gs0 Gs1 Gs2 Gs3 Gs4 Gs5 Ggp Gtp Gs6 Gs7 Gs8 Gs9 Gs10 Gs11
         ROM' Wstk' Wp' Hin' T8 T16 T32 T40 T64 T72 T80 T88
         P0 P8 P12 P16 P24 P48 P56 P60 P64 P68 P72 P80 P88 P92 P96 P100 P104 P112 P120 P124 P128 P132 P136 P140 P144 P7144
         Rlen Rofs Rext Rlb Rdb Rnc Rnl Rnd Rsh HP.
  zkeys. unfold ZSEP in *. cbv [STATE_SIZE FRA ROM_LO_ALL BUF A_ZCALLOC A_ZCFREE HEAD] in *.
  destruct (mem_wr_arrk_exists 2 M' (p + 168) 320 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (lf & Hlens & Hlf).
  destruct (mem_wr_arrk_exists 4 M' (p + 1384) 1444 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (cf & Hcodes & Hcf).
  change (2 ^ (8 * 2)) with 65536 in Hlf. change (2 ^ (8 * 4)) with 4294967296 in Hcf.
  pose proof (ainv_init lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh (8 * (n - 0) + 0 + (osz - 0)) RA_C2
                ltac:(intros i _; apply Hlf) ltac:(intros i _; apply Hcf) Rlen Rofs Rext Rlb Rdb Rnc Rnl Rnd Rsh) as AI.
  assert (HZE1 : KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M zm osz 0) by (intros R1 M1; intros; exfalso; lia_std).
  eapply (pcall_all u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
            Spq Spob Sobq Sprom zm osz HOSZ Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
            A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
            A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH 0 Hwph HZE2 HZE1 HZW
            (M2v n osz (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) + 1) false R' M' (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf).
  - exact AI.
  - lia.
  - unfold u2regs. zkeys. split_conj; assumption.
  - unfold e_mem, cxc, st_init, i_cst, i_hooks, st_at, st_rest, strm_at, cp_addr, wsz; icx_cbn. cbv [STATE_SIZE o_codes BUF A_ZCALLOC A_ZCFREE N_LENS N_CODES].
    cbn [Z.eqb].
    assert (Wob : mem_wr R_segs M' (ob u zm) osz).
    { unfold ob in *. clear - HOSZ Wstk' Hu0 Hzimg Hu1 TW64. destruct zm; cbv [BUF FRA DATA_LO DATA_LEN] in *.
      - eapply mem_wr_sub; [apply buf_writable | cbv [BUF]; lia_std | cbv [BUF BUF_N]; lia_std].
      - eapply mem_wr_sub; [apply buf_writable | cbv [BUF]; lia_std | cbv [BUF BUF_N]; lia_std]. }
    split_conj; try assumption;
      first [ exact Wob
            | intros i Hi; exfalso; lia_std
            | match goal with H : mem_u64 R_segs ?My ?a ?v |- mem_u64 R_segs ?My ?a ?v' => replace v' with v by lia_std; exact H
                            | H : mem_u32 R_segs ?My ?a ?v |- mem_u32 R_segs ?My ?a ?v' => replace v' with v by lia_std; exact H end
            | match goal with |- ?G => idtac "EMSIDE" G end ].
  - eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M (fp_u2 u p zm osz 0)) HP).
    intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; cbn [Z.eqb]; ranges_within_tac.
Qed.
End ZA.
End FXG.
End S_ZA.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require RefMemcpyLib FuzzMem S8MemcpyBase S8Memcpy S8AdlerBase S8AdlerIface S8Adler S8AdlerApart.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require S8LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require ModelRel ItCovIface ItCovMain.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require ZStep.

Module S_It0.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ModelRel OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItCovIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItCovMain.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZStep OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.
Definition lensA (lf : Z -> Z) : arr := arr_init N_LENS lf.
Definition tblA (cf : Z -> Z) : arr := arr_init N_CODES cf.
Definition workA (wf : Z -> Z) : arr := arr_init N_WORK wf.

Section Model.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).

  Definition cntK (k : Z) : arr := itm_count_k (lensA lf) lens_ofs k.
  Definition cntA : arr := itm_count (lensA lf) lens_ofs codes.
  Definition mxA : Z := itm_max cntA.
  Definition mnA : Z := itm_min cntA mxA.
  Definition rootA : Z := itm_root bits mxA mnA.
  Definition offsA : arr := itm_offs cntA.
  Definition work1A : arr := itm_work (lensA lf) lens_ofs codes offsA (workA wf).
  Definition resA : Z * arr * Z * Z * arr :=
    inflate_table ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf).
End Model.


Record itc (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z)
           (p pb sp ret FR zc : Z) : Prop := ITC {
  C_lf    : forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536;
  C_cf    : forall i, 0 <= i < N_CODES -> 0 <= cf i < two32;
  C_wf    : forall i, 0 <= i < N_WORK -> 0 <= wf i < 65536;
  C_ofs   : 0 <= lens_ofs;
  C_ofs2  : lens_ofs + codes <= N_LENS;
  C_codes : 0 <= codes;
  C_codes2 : codes <= 288;
  C_lens15 : forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 15;
  C_tyC   : ty = CODES -> codes <= 19 /\ bits = 7 /\ (forall s, 0 <= s < codes -> lf (lens_ofs + s) <= 7);
  C_tyD   : ty = DISTS -> codes <= 32;
  C_bits  : 1 <= bits;
  C_bits2 : bits <= 15;
  C_nx    : 0 <= nx;
  C_room  : nx + it_room ty <= N_CODES;
  C_pb    : pb = p + o_lenbits \/ pb = p + o_distbits;
  C_pal   : p mod 16 = 0;
  C_p0    : 0 < p;
  C_pceil : p + STATE_SIZE <= zc;
  C_sp    : zc + FR <= sp;
  C_zrom  : DEXT_ADDR + 64 <= zc;
  C_sp2   : sp <= 140737488355328;
  C_spal  : sp mod 16 = 0;
  C_prom  : p + STATE_SIZE <= ROM_LO_ALL \/ DEXT_ADDR + 64 <= p;
  C_ret   : Z.land ret (-2) = ret;
  C_ret2  : 0 <= ret < two64 }.

End FXG.
Ltac open_itc C :=
  destruct C as [Hlf Hcf Hwf Hofs Hofs2 Hcodes Hcodes2 Hlens15 HtyC HtyD Hbits Hbits2 Hnx Hroom
                 Hpb Hpal Hp0 Hpceil Hsp Hzrom Hsp2 Hspal Hprom Hret Hret2];
  cbv [N_LENS N_CODES N_WORK STATE_SIZE o_lenbits o_distbits ROM_LO_ALL DEXT_ADDR] in
    Hlf, Hcf, Hwf, Hofs2, Hcodes2, Hroom, Hpb, Hpceil, Hsp, Hzrom, Hprom;
  lazymatch type of Hpb with ?P => change (ZSEP P) in Hpb end;
  lazymatch type of Hprom with ?P => change (ZSEP P) in Hprom end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.


Section Safe.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret FR zc : Z).
  Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret FR zc.

  Lemma lensA_get : forall i, arr_get (lensA lf) i = lf i.
  Proof using. intros. apply arr_get_init. Qed.
  Lemma workA_get : forall i, arr_get (workA wf) i = wf i.
  Proof using. intros. apply arr_get_init. Qed.
  Lemma tblA_get : forall i, arr_get (tblA cf) i = cf i.
  Proof using. intros. apply arr_get_init. Qed.

  Lemma it_safe_ok : it_safe ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) = true.
  Proof using C zc FR ret sp pb p.
    destruct C.
    apply it_safe_true; unfold lensA, tblA, workA; rewrite ?arr_len_init.
    all: cbv [N_WORK N_LENS N_CODES] in *; try lia.
    - intros s Hs. rewrite arr_get_init. pose proof (C_lf0 (lens_ofs + s) ltac:(lia)).
      pose proof (C_lens16 s Hs). lia.
    - intros H. dand (C_tyC0 H) as (A & B & D). split; [exact A|]. split; [exact B|].
      intros s Hs. rewrite arr_get_init. apply D. exact Hs.
    - exact C_tyD0.
  Qed.
End Safe.


Lemma wrap16_small : forall z, 0 <= z < 65536 -> wrap16 z = z.
Proof. intros z Hz. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. exact Hz. Qed.

Lemma cntK_le : forall lf lens_ofs k i, 0 <= k -> k < 65536 -> 0 <= arr_get (cntK lf lens_ofs k) i <= k.
Proof.
  intros lf lens_ofs k i Hk Hk2. unfold cntK.
  remember (Z.to_nat k) as n eqn:Hn. replace k with (Z.of_nat n) in * by lia. clear Hk Hn. revert i.
  induction n as [|n IH]; intros i.
  - rewrite itm_count_k_0 by lia. rewrite it_zero_count_spec. lia.
  - assert (Hn : Z.of_nat n < 65536) by lia.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite itm_count_k_step by lia. cbv zeta.
    rewrite arr_get_set. destruct (_ && _).
    + specialize (IH Hn (arr_get (lensA lf) (lens_ofs + Z.of_nat n))). rewrite wrap16_small by lia. lia.
    + specialize (IH Hn i). lia.
Qed.

Lemma cntK_len : forall lf lens_ofs k, arr_len (cntK lf lens_ofs k) = 16.
Proof. intros. unfold cntK. apply itm_count_k_len. Qed.

Lemma cntA_eq : forall lf lens_ofs codes, cntA lf lens_ofs codes = cntK lf lens_ofs codes.
Proof. intros. unfold cntA, cntK. apply itm_count_eq. Qed.

Lemma cntK_step : forall lf lens_ofs k, 0 <= k -> k < 65535 ->
  cntK lf lens_ofs (k + 1) = arr_set (cntK lf lens_ofs k) (lf (lens_ofs + k)) (arr_get (cntK lf lens_ofs k) (lf (lens_ofs + k)) + 1).
Proof.
  intros lf lens_ofs k Hk Hk2. unfold cntK at 1. rewrite itm_count_k_step by lia. cbv zeta. fold (cntK lf lens_ofs k).
  unfold lensA at 1 2. rewrite !arr_get_init.
  pose proof (cntK_le lf lens_ofs k (lf (lens_ofs + k)) Hk ltac:(lia)).
  rewrite wrap16_small by lia. reflexivity.
Qed.

Lemma mx_range : forall c, 0 <= itm_max c <= 15.
Proof. intros c. rewrite itm_max_rec. pose proof (find_max_rec_spec c 16 15 ltac:(lia) ltac:(cbn; lia)) as (A & _). exact A. Qed.

Lemma mx_found : forall c k, 1 <= k <= 15 ->
  (forall j, k < j <= 15 -> arr_get c j = 0) -> arr_get c k <> 0 -> itm_max c = k.
Proof.
  intros c k Hk Hz Hnz. rewrite itm_max_rec.
  pose proof (find_max_rec_spec c 16 15 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_max_rec c 16 15) in *.
  destruct (Z.lt_trichotomy r k) as [L | [E | G]]; [| exact E |].
  - exfalso. apply Hnz. apply C. lia.
  - exfalso. destruct B as [B | B]; [lia|]. apply B. apply Hz. lia.
Qed.

Lemma mx_zero : forall c, (forall j, 1 <= j <= 15 -> arr_get c j = 0) -> itm_max c = 0.
Proof.
  intros c Hz. rewrite itm_max_rec.
  pose proof (find_max_rec_spec c 16 15 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_max_rec c 16 15) in *. destruct (Z.eq_dec r 0) as [E|NE]; [exact E|].
  destruct B as [B | B]; [exact B|]. exfalso. apply B. apply Hz. lia.
Qed.

Lemma mn_range : forall c mx, 1 <= mx <= 15 -> 1 <= itm_min c mx <= mx.
Proof.
  intros c mx Hmx. rewrite itm_min_rec by lia.
  pose proof (find_min_rec_spec c mx 16 1 ltac:(lia) ltac:(cbn; lia)) as (A & _). exact A.
Qed.

Lemma mn_found : forall c mx m, 1 <= mx <= 15 -> 1 <= m < mx ->
  (forall j, 1 <= j < m -> arr_get c j = 0) -> arr_get c m <> 0 -> itm_min c mx = m.
Proof.
  intros c mx m Hmx Hm Hz Hnz. rewrite itm_min_rec by lia.
  pose proof (find_min_rec_spec c mx 16 1 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_min_rec c mx 16 1) in *.
  destruct (Z.lt_trichotomy r m) as [L | [E | G]]; [| exact E |].
  - exfalso. destruct B as [B | B]; [lia|]. apply B. apply Hz. lia.
  - exfalso. apply Hnz. apply C. lia.
Qed.

Lemma mn_all : forall c mx, 1 <= mx <= 15 ->
  (forall j, 1 <= j < mx -> arr_get c j = 0) -> itm_min c mx = mx.
Proof.
  intros c mx Hmx Hz. rewrite itm_min_rec by lia.
  pose proof (find_min_rec_spec c mx 16 1 ltac:(lia) ltac:(cbn; lia)) as (A & B & C). cbv zeta in *.
  set (r := find_min_rec c mx 16 1) in *. destruct (Z.eq_dec r mx) as [E|NE]; [exact E|].
  destruct B as [B | B]; [exact B|]. exfalso. apply B. apply Hz. lia.
Qed.


Fixpoint lzk (c : arr) (k : nat) : Z :=
  match k with O => 1 | S k' => 2 * lzk c k' - arr_get c (Z.of_nat k) end.
Definition LZ (c : arr) (k : Z) : Z := lzk c (Z.to_nat k).

Lemma LZ_S : forall c k, 0 <= k -> LZ c (k + 1) = 2 * LZ c k - arr_get c (k + 1).
Proof.
  intros c k Hk. unfold LZ. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  cbn [lzk]. f_equal. f_equal. lia.
Qed.

Lemma left_rec_adv : forall c (m : nat) (n : nat) k,
  0 <= k -> k + Z.of_nat m <= 15 -> (m <= n)%nat ->
  (forall j, k < j <= k + Z.of_nat m -> 0 <= LZ c j) ->
  left_rec c n (k + 1) (LZ c k) = left_rec c (n - m) (k + Z.of_nat m + 1) (LZ c (k + Z.of_nat m)).
Proof.
  intros c m. induction m as [|m IH]; intros n k Hk Hm Hn Hpos.
  - cbn [Z.of_nat]. rewrite !Z.add_0_r. replace (n - 0)%nat with n by lia. reflexivity.
  - destruct n as [|n]; [lia|]. rewrite left_rec_S.
    destruct (Z.leb_spec (k + 1) MAXBITS); [|unfold MAXBITS in *; lia].
    rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
    replace (LZ c k * 2 - arr_get c (k + 1)) with (LZ c (k + 1)) by (rewrite LZ_S by lia; lia).
    pose proof (Hpos (k + 1) ltac:(lia)) as P1.
    destruct (Z.ltb_spec (LZ c (k + 1)) 0); [lia|].
    cbn [Nat.sub]. replace (k + Z.of_nat (S m)) with (k + 1 + Z.of_nat m) by lia.
    apply IH; try lia. intros j Hj. apply Hpos. lia.
Qed.

Lemma left_check_some : forall c, (forall j, 1 <= j <= 15 -> 0 <= LZ c j) -> it_left_check c = Some (LZ c 15).
Proof.
  intros c Hpos. rewrite it_left_check_rec.
  change (left_rec c 16 1 1) with (left_rec c 16 (0 + 1) (LZ c 0)).
  rewrite (left_rec_adv c 15 16 0); try lia; [| intros; apply Hpos; lia].
  cbn [Nat.sub Z.of_nat]. reflexivity.
Qed.

Lemma left_check_none : forall c k, 1 <= k <= 15 ->
  (forall j, 1 <= j < k -> 0 <= LZ c j) -> LZ c k < 0 -> it_left_check c = None.
Proof.
  intros c k Hk Hpos Hneg. rewrite it_left_check_rec.
  change (left_rec c 16 1 1) with (left_rec c 16 (0 + 1) (LZ c 0)).
  rewrite (left_rec_adv c (Z.to_nat (k - 1)) 16 0); try lia; [| intros; apply Hpos; lia].
  replace (0 + Z.of_nat (Z.to_nat (k - 1))) with (k - 1) by lia.
  replace (16 - Z.to_nat (k - 1))%nat with (S (16 - Z.to_nat k))%nat by lia.
  rewrite left_rec_S. destruct (Z.leb_spec (k - 1 + 1) MAXBITS); [|unfold MAXBITS in *; lia].
  rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
  replace (LZ c (k - 1) * 2 - arr_get c (k - 1 + 1)) with (LZ c k).
  2:{ replace k with (k - 1 + 1) at 1 by lia. rewrite LZ_S by lia. lia. }
  destruct (Z.ltb_spec (LZ c k) 0); [reflexivity | lia].
Qed.

Lemma LZ_bound : forall c k N, 0 <= N -> (forall j, 0 <= arr_get c j <= N) -> 0 <= k <= 15 ->
  - 65536 * N <= LZ c k <= 32768.
Proof.
  intros c k N HN Hc Hk. unfold LZ. remember (Z.to_nat k) as n eqn:Hn.
  assert (Hn15 : (n <= 15)%nat) by lia. clear Hn Hk k.
  assert (G : - (2 ^ Z.of_nat n - 1) * N <= lzk c n <= 2 ^ Z.of_nat n).
  { induction n as [|n IH].
    - cbn. lia.
    - cbn [lzk]. specialize (IH ltac:(lia)). pose proof (Hc (Z.of_nat (S n))).
      replace (2 ^ Z.of_nat (S n)) with (2 * 2 ^ Z.of_nat n) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia. }
  assert (2 ^ Z.of_nat n <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2 ^ 15) with 32768 in *.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma zext32_x2 : forall c, 0 <= c < 2147483648 ->
  Z.shiftr ((Z.shiftl c 32) mod 18446744073709551616) 31 = 2 * c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (2 * 2 ^ 31). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma zext32_id : forall c, 0 <= c < 4294967296 ->
  Z.shiftr ((Z.shiftl c 32) mod 18446744073709551616) 32 = c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia). apply Z.div_mul. lia.
Qed.
Lemma zext32_x4 : forall c, 0 <= c < 1073741824 ->
  Z.shiftr ((Z.shiftl c 32) mod 18446744073709551616) 30 = 4 * c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Lemma zext16_id : forall c, 0 <= c < 65536 ->
  Z.shiftr ((Z.shiftl c 48) mod 18446744073709551616) 48 = c.
Proof.
  intros c Hc. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 48) with 281474976710656; lia). apply Z.div_mul. lia.
Qed.

Lemma LZ_0 : forall c, LZ c 0 = 1.
Proof. reflexivity. Qed.
Lemma LZ_1 : forall c, LZ c 1 = 2 - arr_get c 1.
Proof. intros c. change 1 with (0 + 1) at 1. rewrite LZ_S by lia. rewrite LZ_0. reflexivity. Qed.

Lemma LZ_S' : forall c k, 1 <= k -> LZ c k = 2 * LZ c (k - 1) - arr_get c k.
Proof.
  intros c k Hk. replace k with (k - 1 + 1) at 1 by lia. rewrite LZ_S by lia. f_equal. f_equal. lia.
Qed.

Fixpoint osk (c : arr) (n : nat) : Z :=
  match n with O => 0 | S n' => osk c n' + arr_get c (Z.of_nat n) end.
Definition OZ (c : arr) (k : Z) : Z := osk c (Z.to_nat (k - 1)).

Lemma OZ_1 : forall c, OZ c 1 = 0.
Proof. reflexivity. Qed.
Lemma OZ_S : forall c k, 1 <= k -> OZ c (k + 1) = OZ c k + arr_get c k.
Proof.
  intros c k Hk. unfold OZ. replace (Z.to_nat (k + 1 - 1)) with (S (Z.to_nat (k - 1))) by lia.
  cbn [osk]. f_equal. f_equal. lia.
Qed.
Lemma OZ_S' : forall c k, 2 <= k -> OZ c k = OZ c (k - 1) + arr_get c (k - 1).
Proof. intros c k Hk. replace k with (k - 1 + 1) at 1 by lia. apply OZ_S. lia. Qed.

Lemma OZ_range : forall c N k, 0 <= N -> (forall j, 0 <= arr_get c j <= N) -> 1 <= k ->
  0 <= OZ c k <= (k - 1) * N.
Proof.
  intros c N k HN Hc Hk. unfold OZ. remember (Z.to_nat (k - 1)) as n eqn:Hn.
  replace (k - 1) with (Z.of_nat n) by lia. clear Hn Hk k.
  induction n as [|n IH]; [cbn; lia|]. cbn [osk]. pose proof (Hc (Z.of_nat (S n))). lia.
Qed.

Lemma offs_spec : forall c, (forall j, 0 <= arr_get c j <= 288) ->
  forall k, 1 <= k <= 15 -> arr_get (itm_offs c) k = OZ c k.
Proof.
  intros c Hc. rewrite itm_offs_eq. unfold MAXBITS.
  assert (G : forall n : nat, (n <= 14)%nat -> forall k, 1 <= k <= 1 + Z.of_nat n ->
             arr_get (itm_offs_k c (1 + Z.of_nat n)) k = OZ c k).
  { induction n as [|n IH]; intros Hn k Hk.
    - cbn [Z.of_nat Z.add] in *. replace k with 1 by lia. rewrite itm_offs_k_1.
      rewrite arr_get_set_same by (rewrite arr_len_make; lia). rewrite OZ_1. reflexivity.
    - replace (1 + Z.of_nat (S n)) with (1 + Z.of_nat n + 1) in * by lia.
      rewrite itm_offs_k_step by lia. cbv zeta.
      destruct (Z.eq_dec k (1 + Z.of_nat n + 1)) as [->|Hne].
      + rewrite arr_get_set_same by (rewrite itm_offs_k_len; lia).
        rewrite IH by lia. rewrite OZ_S by lia.
        pose proof (OZ_range c 288 (1 + Z.of_nat n) ltac:(lia) Hc ltac:(lia)). pose proof (Hc (1 + Z.of_nat n)).
        apply wrap16_small. lia.
      + rewrite arr_get_set_other by lia. apply IH; lia. }
  intros k Hk. change 15 with (1 + Z.of_nat 14). apply G; lia.
Qed.

Lemma sort_ok_at : forall lens lens_ofs codes offs work WN i,
  it_sort_ok lens lens_ofs codes offs WN = true -> 0 <= i < codes ->
  arr_get lens (lens_ofs + i) <> 0 ->
  0 <= arr_get (fst (itm_sort_k lens lens_ofs i offs work)) (arr_get lens (lens_ofs + i)) < WN.
Proof.
  intros lens lens_ofs codes offs work WN i Hok Hi Hnz. rewrite it_sort_ok_eq in Hok.
  pose proof (itm_sort_ok_k_le lens lens_ofs offs WN codes (i + 1) ltac:(lia) Hok) as H1.
  exact (proj2 (itm_sort_ok_k_inv lens lens_ofs offs work WN i ltac:(lia) H1) Hnz).
Qed.

Lemma sort_k_skip : forall lens lens_ofs i offs work, 0 <= i -> arr_get lens (lens_ofs + i) = 0 ->
  itm_sort_k lens lens_ofs (i + 1) offs work = itm_sort_k lens lens_ofs i offs work.
Proof.
  intros lens lens_ofs i offs work Hi Hz. rewrite itm_sort_k_step by lia.
  destruct (itm_sort_k lens lens_ofs i offs work) as [o w]. cbn [sort_body]. rewrite Hz. reflexivity.
Qed.
Lemma sort_k_take : forall lens lens_ofs i offs work, 0 <= i -> arr_get lens (lens_ofs + i) <> 0 ->
  itm_sort_k lens lens_ofs (i + 1) offs work =
  (let ow := itm_sort_k lens lens_ofs i offs work in
   let l := arr_get lens (lens_ofs + i) in
   let o := arr_get (fst ow) l in
   (arr_set (fst ow) l (wrap16 (o + 1)), arr_set (snd ow) o (wrap16 i))).
Proof.
  intros lens lens_ofs i offs work Hi Hnz. rewrite itm_sort_k_step by lia.
  destruct (itm_sort_k lens lens_ofs i offs work) as [o w]. cbn [sort_body fst snd].
  destruct (Z.eqb_spec (arr_get lens (lens_ofs + i)) 0); [lia|]. reflexivity.
Qed.

Lemma sort_k_work_range : forall lens lens_ofs k offs work n,
  (forall i, 0 <= i < n -> 0 <= arr_get work i < 65536) ->
  forall i, 0 <= i < n -> 0 <= arr_get (snd (itm_sort_k lens lens_ofs k offs work)) i < 65536.
Proof.
  intros lens lens_ofs k offs work n B. unfold itm_sort_k.
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. exact B.
  - apply (forZ_ind (fun _ ow => forall i, 0 <= i < n -> 0 <= arr_get (snd ow) i < 65536)); [| exact B | lia].
    intros j [o w] _ H i Hi. cbn [sort_body snd] in *.
    destruct (negb _); cbn [snd]; [|apply H; exact Hi]. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H; exact Hi].
Qed.

Lemma sort_k_len : forall lens lens_ofs k offs work,
  arr_len (fst (itm_sort_k lens lens_ofs k offs work)) = arr_len offs /\
  arr_len (snd (itm_sort_k lens lens_ofs k offs work)) = arr_len work.
Proof. intros. apply itm_sort_k_len. Qed.

Lemma offsA_len : forall lf lens_ofs codes, arr_len (offsA lf lens_ofs codes) = 16.
Proof. intros. unfold offsA. rewrite itm_offs_eq. apply itm_offs_k_len. Qed.
Lemma workA_len : forall wf, arr_len (workA wf) = 288.
Proof. intros. unfold workA. apply arr_len_init. Qed.

Fixpoint allr (f : Z -> Z) (lo hi : Z) (n : nat) : bool :=
  match n with O => true | S n' => (lo <=? f (Z.of_nat n')) && (f (Z.of_nat n') <? hi) && allr f lo hi n' end.
Lemma allr_spec : forall f lo hi n, allr f lo hi n = true -> forall j, 0 <= j < Z.of_nat n -> lo <= f j < hi.
Proof.
  intros f lo hi n. induction n as [|n IH]; intros H j Hj; [lia|].
  cbn [allr] in H. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  destruct (Z.eq_dec j (Z.of_nat n)) as [->|]; [lia|]. apply IH; [exact H2 | lia].
Qed.
Lemma lbase_range : forall j, 0 <= j < 31 -> 0 <= arr_get lbase_a j < 65536.
Proof. apply (allr_spec (arr_get lbase_a) 0 65536 31). vm_compute. reflexivity. Qed.
Lemma lext_range : forall j, 0 <= j < 31 -> 0 <= arr_get lext_a j < 65536.
Proof. apply (allr_spec (arr_get lext_a) 0 65536 31). vm_compute. reflexivity. Qed.
Lemma dbase_range : forall j, 0 <= j < 32 -> 0 <= arr_get dbase_a j < 65536.
Proof. apply (allr_spec (arr_get dbase_a) 0 65536 32). vm_compute. reflexivity. Qed.
Lemma dext_range : forall j, 0 <= j < 32 -> 0 <= arr_get dext_a j < 65536.
Proof. apply (allr_spec (arr_get dext_a) 0 65536 32). vm_compute. reflexivity. Qed.

Section Trip.
  Variables (x : ItCtx) (st : ItSt).
  Definition tr_hb : Z := t_len st - t_drop st.
  Definition tr_w : Z := arr_get (t_work st) (t_sym st).
  Definition tr_ov : Z * Z :=
    let ty := x_ty x in let w := tr_w in
    if w + 1 <? it_match ty then (0, w)
    else if it_match ty <=? w then (wrap8 (it_extra ty (t_work st) (w - it_match ty)), it_base ty (t_work st) (w - it_match ty))
    else (96, 0).
  Definition tr_op : Z := fst tr_ov.
  Definition tr_val : Z := snd tr_ov.
  Definition tr_here : Z := code_pack tr_op (wrap8 tr_hb) tr_val.
  Definition tr_incr : Z := shl32 1 tr_hb.
  Definition tr_fill : Z := shl32 1 (t_curr st).
  Definition tr_tbl1 : arr := it_fill tr_here tr_incr (t_huff st) (t_drop st) (t_next st) tr_fill (t_tbl st).
  Definition tr_incr2 : Z := it_incr_back (t_huff st) (t_len st).
  Definition tr_huff : Z := if negb (tr_incr2 =? 0) then Z.land (t_huff st) (tr_incr2 - 1) + tr_incr2 else 0.
  Definition tr_sym : Z := wrap32 (t_sym st + 1).
  Definition tr_c : Z := wrap16 (arr_get (t_count st) (t_len st) - 1).
  Definition tr_count : arr := arr_set (t_count st) (t_len st) tr_c.
  Definition tr_brk : bool := (tr_c =? 0) && (t_len st =? x_max x).
  Definition tr_len : Z := if (tr_c =? 0) && negb (t_len st =? x_max x)
                           then arr_get (x_lens x) (x_lens_ofs x + arr_get (t_work st) tr_sym) else t_len st.
  Definition tr_st1 : ItSt := mkItSt tr_huff tr_sym tr_len (t_next st) (t_curr st) (t_drop st) (t_low st) (t_used st)
                                     tr_fill tr_count tr_tbl1 (t_work st).
  Definition tr_sub : bool := (x_root x <? tr_len) && negb (Z.land tr_huff (x_mask x) =? t_low st).
  Definition tr_drop : Z := if t_drop st =? 0 then x_root x else t_drop st.
  Definition tr_next : Z := t_next st + tr_fill.
  Definition tr_curr : Z := it_subtable_curr tr_count tr_len tr_drop (x_max x).
  Definition tr_used : Z := wrap32 (t_used st + Z.shiftl 1 tr_curr).
  Definition tr_st2 : ItSt := mkItSt tr_huff tr_sym tr_len tr_next tr_curr tr_drop (t_low st) tr_used
                                     tr_fill tr_count tr_tbl1 (t_work st).
  Definition tr_low : Z := Z.land tr_huff (x_mask x).
  Definition tr_tbl2 : arr := arr_set tr_tbl1 (x_table x + tr_low) (code_pack tr_curr (x_root x) (tr_next - x_table x)).
  Definition tr_st3 : ItSt := mkItSt tr_huff tr_sym tr_len tr_next tr_curr tr_drop tr_low tr_used
                                     tr_fill tr_count tr_tbl2 (t_work st).

  Lemma it_step_eq : it_step x st =
    if tr_brk then ItBreak tr_st1
    else if tr_sub then (if it_not_enough (x_ty x) tr_used then ItFail tr_st2 else ItCont tr_st3)
    else ItCont tr_st1.
  Proof using.
    unfold it_step, tr_st1, tr_st2, tr_st3, tr_brk, tr_sub, tr_used, tr_curr, tr_next, tr_drop, tr_low, tr_tbl2,
      tr_len, tr_count, tr_c, tr_sym, tr_huff, tr_incr2, tr_tbl1, tr_fill, tr_incr, tr_here, tr_op, tr_val, tr_ov, tr_w, tr_hb.
    cbv zeta.
    destruct (arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x));
      [| destruct (it_match (x_ty x) <=? arr_get (t_work st) (t_sym st))]; cbn [fst snd]; reflexivity.
  Qed.
End Trip.

End FXG.
Ltac split_all := repeat match goal with |- _ /\ _ => split end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Definition BOX (P : Prop) : Prop := P.
End FXG.
Ltac box H := lazymatch type of H with ?P => change (BOX P) in H end.
Ltac unbox H := unfold BOX in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Definition tr_hd (st : ItSt) : Z := Z.shiftr (t_huff st) (t_drop st).
Definition fill_body (here incr hd next : Z) (ft : Z * arr) : bool * (Z * arr) :=
  let '(fill, tbl) := ft in
  let fill' := wrap32 (fill - incr) in
  let tbl' := arr_set tbl (next + (hd + fill')) here in
  if negb (fill' =? 0) then (true, (fill', tbl')) else (false, (fill', tbl')).
Lemma it_fill_eq : forall here incr huff drop next fill tbl,
  it_fill here incr huff drop next fill tbl = snd (loopZ fill (fill_body here incr (Z.shiftr huff drop) next) (fill, tbl)).
Proof. reflexivity. Qed.
Lemma fill_last : forall here incr hd next n f t, 0 < n -> wrap32 (f - incr) = 0 ->
  loopZ n (fill_body here incr hd next) (f, t) = (0, arr_set t (next + (hd + 0)) here).
Proof.
  intros here incr hd next n f t Hn H0. rewrite loopZ_step by lia. cbn [fill_body]. rewrite H0. cbn [Z.eqb negb]. reflexivity.
Qed.
Lemma fill_more : forall here incr hd next n f t, 0 < n -> wrap32 (f - incr) <> 0 ->
  loopZ n (fill_body here incr hd next) (f, t) =
  loopZ (n - 1) (fill_body here incr hd next) (wrap32 (f - incr), arr_set t (next + (hd + wrap32 (f - incr))) here).
Proof.
  intros here incr hd next n f t Hn H0. rewrite loopZ_step at 1 by lia. cbn [fill_body].
  destruct (Z.eqb_spec (wrap32 (f - incr)) 0); [lia|]. cbn [negb]. reflexivity.
Qed.
Lemma shl32_1 : forall k, 0 <= k <= 15 -> shl32 1 k = 2 ^ k.
Proof. intros k Hk. exact (itm_used_pow2 k Hk). Qed.
Lemma wrap32_small : forall z, 0 <= z < 4294967296 -> wrap32 z = z.
Proof. intros z Hz. unfold wrap32. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb.
  pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as Hal.
  rewrite Z.lor_ldiff_and in Hal.
  assert (Hand : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  rewrite Hand in Hal.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia_std). lia_std.
Qed.
Lemma land_le_r : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof. intros. rewrite Z.land_comm. apply land_le_l; assumption. Qed.
Lemma shiftr1_half : forall c m, 0 <= c < 2 ^ Z.of_nat (S m) -> 0 <= Z.shiftr c 1 < 2 ^ Z.of_nat m.
Proof.
  intros c m Hc. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hc by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma wrap16_mod : forall z, wrap16 z = z mod 65536.
Proof. intros z. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma swrap16_cases : forall c, 0 <= c < 65536 ->
  (c < 32768 /\ bv_swrap 16 c = c) \/ (32768 <= c /\ bv_swrap 16 c = c - 65536).
Proof.
  intros c Hc. unfold bv_swrap, bv_wrap. change (bv_half_modulus 16) with 32768. change (bv_modulus 16) with 65536.
  destruct (Z_lt_le_dec c 32768).
  - left. rewrite Z.mod_small by lia. lia.
  - right. replace (c + 32768) with ((c - 32768) + 1 * 65536) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Lemma negshift48_mod : forall n, -32769 <= n <= -1 ->
  (n * 281474976710656) mod 18446744073709551616 = (n + 65536) * 281474976710656.
Proof.
  intros n Hn. replace (n * 281474976710656) with ((n + 65536) * 281474976710656 + (-1) * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Definition incr_body (huff : Z) (incr : Z) : bool * Z :=
  if negb (Z.land huff incr =? 0) then (true, Z.shiftr incr 1) else (false, incr).
Lemma it_incr_back_eq : forall huff len, it_incr_back huff len = loopZ 32 (incr_body huff) (shl32 1 (len - 1)).
Proof. reflexivity. Qed.
Lemma incr_last : forall huff n c, 0 < n -> Z.land huff c = 0 -> loopZ n (incr_body huff) c = c.
Proof. intros huff n c Hn H0. rewrite loopZ_step by lia. unfold incr_body. rewrite H0. cbv beta iota. reflexivity. Qed.
Lemma incr_more : forall huff n c, 0 < n -> Z.land huff c <> 0 ->
  loopZ n (incr_body huff) c = loopZ (n - 1) (incr_body huff) (Z.shiftr c 1).
Proof.
  intros huff n c Hn H0. rewrite loopZ_step at 1 by lia. unfold incr_body at 1.
  destruct (Z.eqb_spec (Z.land huff c) 0); [lia|]. cbv beta iota. reflexivity.
Qed.
Lemma incr_range : forall huff n c, 0 <= c -> 0 <= loopZ n (incr_body huff) c <= c.
Proof.
  intros huff n. destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
  2:{ intros. rewrite loopZ_le0 by lia. lia. }
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia. clear n Hn Hm.
  induction m as [|m IH]; intros c Hc.
  - rewrite loopZ_le0 by lia. lia.
  - destruct (Z.eq_dec (Z.land huff c) 0) as [E|E].
    + rewrite incr_last by lia. lia.
    + rewrite incr_more by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      assert (0 <= Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      specialize (IH (Z.shiftr c 1) ltac:(lia)). lia.
Qed.

Definition curr_body (count : arr) (drop max : Z) (cl : Z * Z) : bool * (Z * Z) :=
  let '(curr, lft) := cl in
  if wrap32 (curr + drop) <? max then
    let lft' := lft - arr_get count (wrap32 (curr + drop)) in
    if lft' <=? 0 then (false, (curr, lft')) else (true, (wrap32 (curr + 1), Z.shiftl lft' 1))
  else (false, (curr, lft)).
Lemma it_subtable_curr_eq : forall count len drop max,
  it_subtable_curr count len drop max =
  fst (loopZ 16 (curr_body count drop max) (wrap32 (len - drop), swrap32 (Z.shiftl 1 (wrap32 (len - drop))))).
Proof. reflexivity. Qed.
Lemma curr_stop_ge : forall count drop max n curr lft, 0 < n -> 0 <= curr + drop < 4294967296 -> max <= curr + drop ->
  loopZ n (curr_body count drop max) (curr, lft) = (curr, lft).
Proof.
  intros count drop max n curr lft Hn Hr Hge. rewrite loopZ_step by lia. unfold curr_body at 1.
  rewrite wrap32_small by lia. destruct (Z.ltb_spec (curr + drop) max); [lia|]. reflexivity.
Qed.
Lemma curr_stop_le : forall count drop max n curr lft, 0 < n -> 0 <= curr + drop < 4294967296 -> curr + drop < max ->
  lft - arr_get count (curr + drop) <= 0 ->
  loopZ n (curr_body count drop max) (curr, lft) = (curr, lft - arr_get count (curr + drop)).
Proof.
  intros count drop max n curr lft Hn Hr Hlt Hle. rewrite loopZ_step by lia. unfold curr_body at 1.
  rewrite wrap32_small by lia. destruct (Z.ltb_spec (curr + drop) max); [|lia].
  destruct (Z.leb_spec (lft - arr_get count (curr + drop)) 0); [|lia]. reflexivity.
Qed.
Lemma curr_more : forall count drop max n curr lft, 0 < n -> 0 <= curr + drop < 4294967295 -> 0 <= curr -> curr + drop < max ->
  0 <= drop -> max <= 65536 ->
  0 < lft - arr_get count (curr + drop) ->
  loopZ n (curr_body count drop max) (curr, lft) =
  loopZ (n - 1) (curr_body count drop max) (curr + 1, Z.shiftl (lft - arr_get count (curr + drop)) 1).
Proof.
  intros count drop max n curr lft Hn Hr Hc Hlt Hd Hm Hgt. rewrite loopZ_step at 1 by lia. unfold curr_body at 1.
  rewrite wrap32_small by lia. destruct (Z.ltb_spec (curr + drop) max); [|lia].
  destruct (Z.leb_spec (lft - arr_get count (curr + drop)) 0); [lia|]. rewrite wrap32_small by lia. reflexivity.
Qed.

Lemma curr_result_range : forall count drop max n curr lft,
  0 <= curr -> 0 <= drop -> max <= 65536 -> 0 < n -> curr + drop < 4294967296 ->
  curr <= fst (loopZ n (curr_body count drop max) (curr, lft)) /\
  (curr + drop <= max -> fst (loopZ n (curr_body count drop max) (curr, lft)) <= max - drop) /\
  (max <= curr + drop -> fst (loopZ n (curr_body count drop max) (curr, lft)) = curr).
Proof.
  intros count drop max n. intros curr lft Hc Hd Hmx Hn Hcd.
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia_std. assert (Hm1 : (1 <= m)%nat) by lia_std. clear n Hn Hm.
  revert curr lft Hc Hcd. induction m as [|m IH]; intros curr lft Hc Hcd; [lia_std|].
  destruct (Z_lt_le_dec (curr + drop) max).
  - destruct (Z_lt_le_dec 0 (lft - arr_get count (curr + drop))).
    + rewrite curr_more by lia_std. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia_std.
      destruct m as [|m'].
      * rewrite loopZ_le0 by lia_std. cbn [fst]. lia_std.
      * specialize (IH ltac:(lia_std) (curr + 1) (Z.shiftl (lft - arr_get count (curr + drop)) 1) ltac:(lia_std) ltac:(lia_std)). lia_std.
    + rewrite curr_stop_le by lia_std. cbn [fst]. lia_std.
  - rewrite curr_stop_ge by lia_std. cbn [fst]. lia_std.
Qed.

Lemma it_fill_len_tr : forall x st, arr_len (tr_tbl1 x st) = arr_len (t_tbl st).
Proof. intros. unfold tr_tbl1. apply it_fill_len. Qed.

Lemma code_pack_range : forall op bits val, 0 <= code_pack op bits val < 4294967296.
Proof.
  intros. unfold code_pack.
  pose proof (wrap16_range val) as A. change (2 ^ 16) with 65536 in A.
  assert (W8 : forall z, 0 <= wrap8 z < 256).
  { intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia_std. apply Z.mod_pos_bound. lia_std. }
  pose proof (W8 op). pose proof (W8 bits). lia_std.
Qed.
Lemma fill_get_cases : forall here incr hd next n f t j,
  arr_get (snd (loopZ n (fill_body here incr hd next) (f, t))) j = here \/
  arr_get (snd (loopZ n (fill_body here incr hd next) (f, t))) j = arr_get t j.
Proof.
  intros here incr hd next n. destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
  2:{ intros. rewrite loopZ_le0 by lia_std. cbn [snd]. right. reflexivity. }
  remember (Z.to_nat n) as m eqn:Hm. replace n with (Z.of_nat m) by lia_std. clear n Hn Hm.
  induction m as [|m IH]; intros f t j.
  - rewrite loopZ_le0 by lia_std. right. reflexivity.
  - destruct (Z.eq_dec (wrap32 (f - incr)) 0) as [E|E].
    + rewrite fill_last by first [lia_std | exact E]. cbn [snd]. rewrite arr_get_set. destruct (_ && _); [left | right]; reflexivity.
    + rewrite fill_more by first [lia_std | exact E]. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia_std.
      destruct (IH (wrap32 (f - incr)) (arr_set t (next + (hd + wrap32 (f - incr))) here) j) as [A|A]; [left; exact A|].
      rewrite arr_get_set in A. destruct (_ && _); [left | right]; exact A.
Qed.
Lemma tr_tbl1_range : forall x st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 -> 0 <= arr_get (tr_tbl1 x st) j < 4294967296.
Proof.
  intros x st H j Hj. unfold tr_tbl1. rewrite it_fill_eq.
  destruct (fill_get_cases (tr_here x st) (tr_incr st) (Z.shiftr (t_huff st) (t_drop st)) (t_next st) (tr_fill st) (tr_fill st) (t_tbl st) j) as [A|A]; rewrite A.
  - unfold tr_here. apply code_pack_range.
  - apply H. exact Hj.
Qed.
Lemma tr_tbl2_range : forall x st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 -> 0 <= arr_get (tr_tbl2 x st) j < 4294967296.
Proof.
  intros x st H j Hj. unfold tr_tbl2. rewrite arr_get_set. destruct (_ && _); [apply code_pack_range | apply tr_tbl1_range; assumption].
Qed.
Lemma tr_count_range0 : forall st, (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) ->
  forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536.
Proof.
  intros st H j Hj. unfold tr_count. rewrite arr_get_set. destruct (_ && _); [|apply H; exact Hj].
  pose proof (wrap16_range (arr_get (t_count st) (t_len st) - 1)) as W. change (2 ^ 16) with 65536 in W. unfold tr_c. lia_std.
Qed.

Lemma trip_ok_facts : forall x WN LN TN st, it_trip_ok x WN LN TN st = true ->
  0 <= t_sym st < WN /\ 1 <= t_len st <= 15 /\ 0 <= t_drop st <= t_len st /\
  t_len st - t_drop st <= t_curr st <= 15 /\ 0 <= t_huff st < 65536 /\ 0 <= t_next st /\
  0 <= t_used st < 65536 /\ 0 <= t_min st < 65536 /\
  0 <= tr_w st < 65536 /\
  (it_match (x_ty x) <= tr_w st -> tr_w st - it_match (x_ty x) < it_ext_len (x_ty x) WN) /\
  t_next st + Z.shiftr (t_huff st) (t_drop st) + Z.shiftl 1 (t_curr st) - Z.shiftl 1 (t_len st - t_drop st) < TN /\
  (tr_c st = 0 -> t_len st <> x_max x ->
     t_sym st + 1 < WN /\ 0 <= arr_get (t_work st) (t_sym st + 1) /\
     0 <= x_lens_ofs x + arr_get (t_work st) (t_sym st + 1) < LN /\
     1 <= arr_get (x_lens x) (x_lens_ofs x + arr_get (t_work st) (t_sym st + 1)) <= 15) /\
  (forall st', it_step x st = ItCont st' -> (t_low st' <> t_low st \/ t_next st' <> t_next st) ->
     0 <= x_table x + t_low st' < TN /\ 1 <= t_curr st' <= 15 /\ t_next st <= t_next st').
Proof.
  intros x WN LN TN st H. unfold it_trip_ok in H. cbv zeta in H. fold (tr_w st) in H. fold (tr_c st) in H.
  repeat match goal with G : (_ && _) = true |- _ => apply andb_prop in G as [? ?] end.
  repeat match goal with
  | G : (_ <=? _) = true |- _ => apply Z.leb_le in G
  | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G
  end.
  split_all; try lia.
  - intros Hm. match goal with G : (if tr_w st + 1 <? _ then _ else _) = true |- _ =>
      destruct (Z.ltb_spec (tr_w st + 1) (it_match (x_ty x))); [lia|];
      destruct (Z.leb_spec (it_match (x_ty x)) (tr_w st)); [|lia]; apply Z.ltb_lt in G; exact G end.
  - intros Hc Hne. match goal with G : (if (tr_c st =? 0) && _ then _ else _) = true |- _ =>
      rewrite Hc in G; cbn [Z.eqb] in G;
      destruct (Z.eqb_spec (t_len st) (x_max x)); [lia|]; cbn [negb andb] in G; cbv zeta in G;
      repeat (apply andb_prop in G as [G ?Y]) end.
    repeat match goal with
    | G : (_ <=? _) = true |- _ => apply Z.leb_le in G
    | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G
    end. lia.
  - intros st' Hs Hch. match goal with G : match it_step x st with _ => _ end = true |- _ =>
      rewrite Hs in G;
      destruct (Z.eqb_spec (t_low st') (t_low st)); destruct (Z.eqb_spec (t_next st') (t_next st)); cbn [negb orb] in G; try lia;
      repeat (apply andb_prop in G as [G ?W]) end.
    all: repeat match goal with
      | G : (_ <=? _) = true |- _ => apply Z.leb_le in G
      | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G
      end; lia.
Qed.

Section Res.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).
  Let cnt := cntA lf lens_ofs codes.
  Let mx := mxA lf lens_ofs codes.
  Let mn := mnA lf lens_ofs codes.
  Let rt := rootA lf lens_ofs codes bits.
  Let w1 := work1A lf lens_ofs codes wf.
  Let X := itm_ctx ty (lensA lf) lens_ofs nx rt mx.
  Let st0 := itm_st0 mn nx rt cnt (tblA cf) w1.
  Let R := resA ty lf lens_ofs codes nx bits cf wf.

  Lemma res_phases : R =
    (if mx =? 0 then (0, arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0), nx + 2, 1, workA wf)
     else if itm_reject ty mx (it_left_check cnt) then (-1, tblA cf, nx, bits, workA wf)
     else if it_not_enough ty (itm_used rt) then (1, tblA cf, nx, bits, w1)
     else match it_loop X codes st0 with
          | inr st => (1, t_tbl st, nx, bits, t_work st)
          | inl st => (0, (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st),
                       nx + t_used st, rt, t_work st)
          end).
  Proof using.
    unfold R, resA. rewrite inflate_table_phases. cbv zeta.
    fold cnt. unfold mxA in mx. fold mx. unfold mnA in mn. fold mn. unfold rootA in rt. fold rt.
    unfold work1A, offsA in w1. fold w1. fold X. fold st0. reflexivity.
  Qed.
End Res.


End FXG.
Ltac destr_conj H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "F" in destruct H as [H1 H]; destr_conj H1; destr_conj H
  | _ => idtac
  end.
Ltac split_conj := repeat match goal with |- _ /\ _ => split end.
Ltac zkeys := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6
                   o_strm o_mode o_last o_wrap o_havedict o_flags o_dmax o_check o_total o_head o_wbits
                   o_wsize o_whave o_wnext o_window o_hold o_bits o_length o_offset o_extra o_lencode
                   o_distcode o_lenbits o_distbits o_ncode o_nlen o_ndist o_shave o_next o_lens o_work
                   o_codes o_sane o_back o_was STATE_SIZE N_LENS N_WORK N_CODES WIN_SIZE
                   ORDER_ADDR LENFIX_ADDR DISTFIX_ADDR LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR JTAB_ADDR MOD31_ADDR
                   FRA ROM_LO_ALL] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

End FXG.
Ltac zregv := cbv [zget_l kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                  kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6];
             cbn [alookup Pos.eqb]; rewrite ?zget_zupd; cbv [zget_l]; cbn [alookup Pos.eqb];
             zrefold_getl; zbase.
Ltac zreg := zregv; first [ reflexivity | assumption | OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.zarith_goal; lia ].
Ltac hyp := lazymatch goal with |- ?G => match goal with Hh : G |- _ => exact Hh end end.
End S_It0.

Module S_It1.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.
Import S_It0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

End FXG.
Ltac zmem_transport_loop_S_ZB M a bs :=
  repeat match goal with
  | H : mem_arr ?k ?segs M ?base ?n ?f |- _ =>
      first [ apply (mem_arr_frame segs k M base n f a bs) in H; [|unfold zdisj; zlen_norm; zlia]
            | idtac "WARNING: mem_arr fact dropped at store" a base; clear H ]
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 8;
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 4;
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 2;
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 1;
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      zrng_ensure a' (Z.of_nat (length bs'));
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_frame M a bs) in H; [| zlia | zlen_norm; zlia | unfold ROM_LO, ROM_HI; zdisj_tac]
            | idtac "WARNING: rom_ok dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | idtac "WARNING: framed fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | idtac "WARNING: framed2 fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stableL ?Fr _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; in_some_tac]
            | idtac "WARNING: framedL fact dropped at store" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.
End FXG.
Ltac zmem_transport M a bs ::=
  zxfer_pre a bs;
  zmem_transport_loop_S_ZB M a bs;
  zxfer_post a.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Definition A_ITABLE : Z := 95848.

Lemma mem_arr2_zero16 : forall M a,
  0 <= a -> a + 32 <= two64 ->
  mem_u64 R_segs M a 0 -> mem_u64 R_segs M (a + 8) 0 -> mem_u64 R_segs M (a + 16) 0 -> mem_u64 R_segs M (a + 24) 0 ->
  mem_arr 2 R_segs M a 16 (fun _ => 0).
Proof.
  intros M a Ha Ha2 H0 H1 H2 H3.
  apply mem_arr_of_elems; [lia | lia | lia | lia |].
  intros i Hi. change (Z.to_nat 2) with 2%nat.
  assert (E : forall b j, mem_u64 R_segs M b 0 -> 0 <= j < 4 -> mem_is R_segs M (b + 2 * j) (Z_to_le_bytes 2 0)).
  { intros b j Hb Hj. unfold mem_u64 in Hb.
    pose proof (mem_is_sub R_segs M b (Z_to_le_bytes 8 0) (2 * j) 2 Hb ltac:(lia) ltac:(cbn; lia)) as X.
    unfold mem_is. cbn [length Z_to_le_bytes]. rewrite X.
    assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct J as [-> | [-> | [-> | ->]]]; reflexivity. }
  assert (C : i < 4 \/ (4 <= i < 8) \/ (8 <= i < 12) \/ 12 <= i) by lia.
  destruct C as [C | [C | [C | C]]].
  - apply (E a i H0). lia.
  - replace (a + 2 * i) with (a + 8 + 2 * (i - 4)) by lia. apply (E (a + 8) (i - 4) H1). lia.
  - replace (a + 2 * i) with (a + 16 + 2 * (i - 8)) by lia. apply (E (a + 16) (i - 8) H2). lia.
  - replace (a + 2 * i) with (a + 24 + 2 * (i - 12)) by lia. apply (E (a + 24) (i - 12) H3). lia.
Qed.

Section Prologue.

Lemma it_prologue_s : forall Rb l M MD T (sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = sp -> zget_l Rb l kRA = v1 -> zget_l Rb l kGP = v4 -> zget_l Rb l kTP = v5 ->
  zget_l Rb l kS0 = v8 -> zget_l Rb l kS1 = v9 ->
  zget_l Rb l kA0 = v10 -> zget_l Rb l kA1 = v11 -> zget_l Rb l kA2 = v12 -> zget_l Rb l kA3 = v13 ->
  zget_l Rb l kA4 = v14 -> zget_l Rb l kA5 = v15 ->
  zget_l Rb l kS2 = v18 -> zget_l Rb l kS3 = v19 ->
  zget_l Rb l kS4 = v20 -> zget_l Rb l kS5 = v21 -> zget_l Rb l kS6 = v22 -> zget_l Rb l kS7 = v23 ->
  zget_l Rb l kS8 = v24 -> zget_l Rb l kS9 = v25 -> zget_l Rb l kS10 = v26 -> zget_l Rb l kS11 = v27 ->
  192 <= sp -> sp <= 140737488355328 ->
  mem_wr R_segs M (sp - 192) 192 ->
  (forall R' M',
     zget_l R' [] kSP = sp + -192 -> zget_l R' [] kGP = v4 -> zget_l R' [] kTP = v5 ->
     zget_l R' [] kA0 = v10 -> zget_l R' [] kA1 = v11 -> zget_l R' [] kA2 = v12 -> zget_l R' [] kA3 = v13 ->
     zget_l R' [] kA4 = v14 -> zget_l R' [] kA5 = v15 ->
     mpost R_segs M M' (sp + -192) sp 0 0 ->
     mem_wr R_segs M' (sp - 192) 192 ->
     mem_u64 R_segs M' (sp + -8) v1 -> mem_u64 R_segs M' (sp + -16) v8 -> mem_u64 R_segs M' (sp + -24) v9 ->
     mem_u64 R_segs M' (sp + -32) v18 -> mem_u64 R_segs M' (sp + -40) v19 -> mem_u64 R_segs M' (sp + -48) v20 ->
     mem_u64 R_segs M' (sp + -56) v21 -> mem_u64 R_segs M' (sp + -64) v22 -> mem_u64 R_segs M' (sp + -72) v23 ->
     mem_u64 R_segs M' (sp + -80) v24 -> mem_u64 R_segs M' (sp + -88) v25 -> mem_u64 R_segs M' (sp + -96) v26 ->
     mem_u64 R_segs M' (sp + -104) v27 ->
     mem_arr 2 R_segs M' (sp + -136) 16 (fun _ => 0) ->
     realizes R_segs (zcfg R_segs 95920 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 95848 (zupd Rb l) M MD) T.
Proof using.
  intros Rb l M MD T sp v1 v4 v5 v8 v9 v10 v11 v12 v13 v14 v15 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
         Hh LSP LRA LGP LTP L8 L9 L10 L11 L12 L13 L14 L15 L18 L19 L20 L21 L22 L23 L24 L25 L26 L27 Hsp Hsp2 Wf K.
  zkeys. idtac.
  pose proof (mpost_stable R_segs M (sp + -192) sp 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -192) sp 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  do 13 (zstep Rfd).
  do 4 (zstep Rfd).
  lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => eapply (K R Mx) end.
  all: try zreg.
  all: try assumption.
  apply mem_arr2_zero16; [lia | rewrite two64_eq; lia | assumption | | | ].
  all: match goal with |- mem_u64 _ _ ?a 0 => zfold; assumption end.
Qed.
End Prologue.

Definition pregs (p lens_ofs codes pb sp vgp vtp tyv : Z) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\
  zget_l R l kA0 = tyv /\ zget_l R l kA1 = p + 168 + 2 * lens_ofs /\ zget_l R l kA2 = codes /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.

End FXG.
Ltac open_pregs H := unfold pregs in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in let d := fresh "LA0" in
  let e := fresh "LA1" in let f := fresh "LA2" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & d & e & f & g & h & i).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.
End FXG.
Ltac clear_regs := repeat match goal with H : zget _ _ = _ |- _ => clear H | H : zget_l _ _ _ = _ |- _ => clear H end.
Ltac close_pregs := unfold pregs; split_conj; zreg.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Section S7IT.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cnt i := (arr_get (cntK lf lens_ofs i)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).


Lemma cA_range : forall j, 0 <= cA j <= codes.
Proof using C zc ret sp pb p wf cf bits nx ty. intros j. destruct C. rewrite cntA_eq. pose proof (cntK_le lf lens_ofs codes j ltac:(lia) ltac:(lia)). lia. Qed.

Lemma count_loop_s : forall fuel i Rb l M MD T,
  (Z.to_nat (codes - i) <= fuel)%nat -> 0 <= i < codes ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kT0 = p + 168 + 2 * lens_ofs + 2 * i -> zget_l Rb l kA6 = p + 168 + 2 * lens_ofs + 2 * codes ->
  zget_l Rb l kA7 = sp + -136 ->
  mem_wr R_segs M (sp - 192) 192 ->
  mem_arr 2 R_segs M (p + 168) 320 lf ->
  mem_arr 2 R_segs M (sp + -136) 16 (cnt i) ->
  (forall R' M',
     PR R' [] -> zget_l R' [] kA7 = sp + -136 ->
     mpost R_segs M M' (sp + -136) (sp + -104) 0 0 ->
     mem_wr R_segs M' (sp - 192) 192 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf ->
     mem_arr 2 R_segs M' (sp + -136) 16 (cnt codes) ->
     realizes R_segs (zcfg R_segs 95976 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 95944 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP LT0 LA6 LA7 Wf Hlens Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HCr1 : forall j, 0 <= j < 16 -> -32768 <= cnt i j < 32768).
  { intros j _. pose proof (cntK_le lf lens_ofs i j ltac:(lia) ltac:(lia)). lia. }
  pose proof (mpost_stable R_segs M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  zrebase.
  tstep Rfd.
  tstep Rfd.
  tstep Rfd. zsetreg (2 * lf (lens_ofs + i)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  tstep Rfd.
  tstep Rfd.
  tstep Rfd.
  tstore_arr Rfd Hcnt (lf (lens_ofs + i)).
  apply mem_arr_arr_set in Hcnt; [|rewrite cntK_len; lia].
  rewrite <- (cntK_step lf lens_ofs i) in Hcnt by lia.
  destruct (Z.eq_dec (i + 1) codes) as [Hend|Hmore].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => eapply (K R Mx) end.
    all: try first [close_pregs | zreg | assumption].
    rewrite <- Hend. exact Hcnt.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (i + 1) Rx [] Mx MD T) end.
    all: try first [lia | assumption | close_pregs | zreg].
    intros R' M'. intros. eapply K; try eassumption.
    eapply mpost_trans; [exact HAG | assumption].
Qed.

Lemma count_phase_s : forall Rb l M MD T,
  0 < codes -> m_halted MD = None -> PR Rb l ->
  mem_wr R_segs M (sp - 192) 192 ->
  mem_arr 2 R_segs M (p + 168) 320 lf ->
  mem_arr 2 R_segs M (sp + -136) 16 (fun _ => 0) ->
  (forall R' M',
     PR R' [] -> zget_l R' [] kA7 = sp + -136 ->
     mpost R_segs M M' (sp + -136) (sp + -104) 0 0 ->
     mem_wr R_segs M' (sp - 192) 192 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf ->
     mem_arr 2 R_segs M' (sp + -136) 16 cA ->
     realizes R_segs (zcfg R_segs 95976 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 95920 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T Hc0 Hh HP Wf Hlens Hcnt K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (Hcnt0 : mem_arr 2 R_segs M (sp + -136) 16 (cnt 0)).
  { eapply mem_arr_ext; [exact Hcnt|]. intros j Hj. cbn beta. unfold cntK. rewrite itm_count_k_0 by lia.
    rewrite it_zero_count_spec. reflexivity. }
  clear Hcnt. zrebase.
  zbr Rfd false.
  zstep Rfd. zstep Rfd. zsetreg (2 * codes) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
    eapply (count_loop_s (Z.to_nat codes) 0 Rx [] Mx MD T) end.
  all: try first [lia | assumption | close_pregs | zreg].
  all: intros; rewrite cntA_eq in K; eapply K; eassumption.
Qed.

Definition Kmax (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> zget_l R' [] kT0 = mx -> zget_l R' [] kT2 = cA 15 ->
    2 <= mx -> realizes R_segs (zcfg R_segs 96256 (zupd R' []) M MD) T.
Definition Klow (bitsv : Z) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA7 = bitsv -> (forall j, 2 <= j <= 15 -> cA j = 0) ->
    realizes R_segs (zcfg R_segs 97564 (zupd R' []) M MD) T.

Lemma max_stage_2 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 2 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96240 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 2) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 2) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KL Rx) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 2) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 2); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 2); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_3 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 3 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96220 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 3) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 3) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_2 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 3) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 3); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 3); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_4 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 4 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96200 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 4) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 4) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_3 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 4) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 4); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 4); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_5 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 5 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96180 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 5) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 5) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_4 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 5) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 5); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 5); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_6 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 6 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96160 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 6) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 6) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_5 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 6) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 6); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 6); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_7 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 7 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96140 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 7) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 7) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_6 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 7) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 7); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 7); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_8 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 8 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96120 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 8) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 8) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_7 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 8) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 8); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 8); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_9 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 9 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96100 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 9) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 9) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_8 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 9) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 9); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 9); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_10 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 10 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96080 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 10) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 10) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_9 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 10) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 10); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 10); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_11 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 11 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96060 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 11) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 11) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_10 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 11) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 11); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 11); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_12 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 12 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96040 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 12) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 12) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_11 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 12) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 12); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 12); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_13 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 13 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96020 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 13) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 13) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_12 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 13) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 13); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 13); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_stage_14 : forall Rb l M MD T bitsv,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bitsv ->
  (forall j, 14 < j <= 15 -> cA j = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kmax bitsv M MD T -> Klow bitsv M MD T ->
  realizes R_segs (zcfg R_segs 96000 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  intros Rb l M MD T bitsv Hh HP LA7 Hz Hcnt KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 14) as HRk.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 14) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_13 Rx [] M MD T bitsv) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. destruct (Z.eq_dec jj 14) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 14); [lia | exact Hz | exact NZ].
    + zregv. symmetry. apply Hz. lia.
    + unfold mxA. rewrite (mx_found _ 14); [lia | lia | exact Hz | exact NZ].
Qed.

Lemma max_entry_s : forall Rb l M MD T av,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 R_segs M (sp + -136) 16 cA -> mem_u32 R_segs M pb bits ->
  Kmax bits M MD T -> Klow bits M MD T ->
  realizes R_segs (zcfg R_segs 95976 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T av Hh HP LA7 Hcnt HB32 KF KL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 15) as HRk.
  zrebase.
  tstep Rfd.
  zstep Rfd. zsetreg bits ltac:(symmetry; apply swrap32_small; lia).
  destruct (Z.eq_dec (cA 15) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_14 Rx [] M MD T bits) end.
    all: try first [assumption | close_pregs | zreg].
    intros jj Hjj. replace jj with 15 by lia. exact Z0.
  - zbr Rfd false. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. symmetry. unfold mxA. apply (mx_found _ 15); [lia | intros; lia | exact NZ].
    + unfold mxA. rewrite (mx_found _ 15); [lia | lia | intros; lia | exact NZ].
Qed.

#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).

Definition Kleft (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT3 = (if mx =? 1 then 0 else 1) -> zget_l R' [] kT2 = cA 15 -> 1 <= mx ->
    realizes R_segs (zcfg R_segs 96316 (zupd R' []) M MD) T.
Definition Kmax0 (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> mx = 0 -> realizes R_segs (zcfg R_segs 97600 (zupd R' []) M MD) T.

Lemma mxmn_facts : 1 <= mx -> 1 <= mn <= mx /\ mx <= 15 /\ 1 <= rt <= 15 /\ mn <= rt /\
  rt = (let r := (if bits <? mx then bits else mx) in if mn <? r then r else mn).
Proof using C zc ret sp pb p wf cf nx ty.
  intros H1. pose proof C as C'. open_itc C'. pose proof (mx_range (cntA lf lens_ofs codes)) as MR.
  pose proof (mn_range (cntA lf lens_ofs codes) mx ltac:(unfold mxA in *; lia)) as NR.
  unfold rootA, itm_root. unfold mnA in *. unfold mxA in *.
  set (mxv := itm_max (cntA lf lens_ofs codes)) in *. set (mnv := itm_min (cntA lf lens_ofs codes) mxv) in *.
  destruct (Z.ltb_spec mxv bits); destruct (Z.ltb_spec bits mxv); try lia_std;
    destruct (Z.ltb_spec mxv mnv); destruct (Z.ltb_spec bits mnv); destruct (Z.ltb_spec mnv mxv); destruct (Z.ltb_spec mnv bits); cbv zeta; lia_std.
Qed.

Lemma min_loop_s : forall fuel m Rb l M MD T r7,
  (Z.to_nat (mx - m) <= fuel)%nat -> 1 <= m < mx -> 2 <= mx <= 15 ->
  (forall jj, 1 <= jj < m -> cA jj = 0) ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kT1 = m -> zget_l Rb l kA6 = sp + -136 + 2 * m -> zget_l Rb l kT4 = mx - m ->
  zget_l Rb l kT0 = mx -> zget_l Rb l kA7 = r7 -> zget_l Rb l kT3 = 1 -> zget_l Rb l kT2 = cA 15 ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  (forall R', PR R' [] -> zget_l R' [] kT1 = mn -> zget_l R' [] kT0 = mx -> zget_l R' [] kA7 = r7 ->
     zget_l R' [] kT3 = 1 -> zget_l R' [] kT2 = cA 15 ->
     realizes R_segs (zcfg R_segs 96308 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 96280 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx.
  induction fuel as [|fuel IH]; intros m Rb l M MD T r7 Hfuel Hm Hmx2 Hz Hh HP LT1 LA6 LT4 LT0 LA7 LT3 LT2 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range m) as HRm.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA m) 0) as [Z0|NZ].
  - zbr Rfd false.
    zstep Rfd. zsetreg (m + 1) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zstep Rfd.
    destruct (Z.eq_dec (m + 1) mx) as [Hlast|Hmore].
    + zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try first [assumption | close_pregs | zreg].
      zregv. symmetry. unfold mnA. apply mn_all; [lia|].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (m + 1) Rx [] M MD T r7) end.
      all: try first [lia | assumption | close_pregs | zreg].
      intros jj Hjj. destruct (Z.eq_dec jj m) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try first [assumption | close_pregs | zreg].
    zregv. symmetry. unfold mnA. apply mn_found; [lia | lia | exact Hz | exact NZ].
Qed.

Lemma rootmin_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits -> zget_l Rb l kT0 = mx -> zget_l Rb l kT2 = cA 15 ->
  2 <= mx ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kleft M MD T ->
  realizes R_segs (zcfg R_segs 96256 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T Hh HP LA7 LT0 LT2 Hmx2 Hcnt KL.
  pose proof C as C'. open_itc C'.
  pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
  assert (STEP : forall r7, r7 = (if bits <? mx then bits else mx) -> 1 <= r7 <= 15 ->
    forall Rx lx, m_halted MD = None -> PR Rx lx -> zget_l Rx lx kA7 = r7 -> zget_l Rx lx kT0 = mx -> zget_l Rx lx kT2 = cA 15 ->
    realizes R_segs (zcfg R_segs 96264 (zupd Rx lx) M MD) T).
  { intros r7 Hr7 Hr7b Rx lx Hh' HP' XA7 XT0 XT2. open_pregs HP'. zkeys. zrebase.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx' _ _) _ => eapply (min_loop_s (Z.to_nat mx) 1 Rx' [] M MD T r7) end.
    all: try first [lia | assumption | close_pregs | zreg].
    intros R' HP2 YT1 YT0 YA7 YT3 YT2. open_pregs HP2. zkeys. zrebase.
    destruct (Z.ltb_spec mn r7).
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Ry _ _) _ => eapply (KL Ry) end.
      all: try first [assumption | close_pregs | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia.
    - zbr Rfd false. zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Ry _ _) _ => eapply (KL Ry) end.
      all: try first [assumption | close_pregs | zreg].
      + zregv. rewrite RTEQ. cbv zeta. subst r7. destruct (Z.ltb_spec mn (if bits <? mx then bits else mx)); lia.
      + zregv. destruct (Z.eqb_spec mx 1); lia. }
  open_pregs HP. zkeys. zrebase.
  destruct (Z.ltb_spec bits mx).
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (STEP bits _ _ Rx []) end.
    all: try first [assumption | close_pregs | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  - zbr Rfd false. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (STEP mx _ _ Rx []) end.
    all: try first [assumption | close_pregs | zreg].
    all: destruct (Z.ltb_spec bits mx); lia.
  Unshelve. all: lia.
Qed.

Lemma maxlow_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = bits ->
  (forall jj, 2 <= jj <= 15 -> cA jj = 0) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA ->
  Kleft M MD T -> Kmax0 M MD T ->
  realizes R_segs (zcfg R_segs 97564 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T Hh HP LA7 Hz Hcnt KL K0.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range j); lia).
  pose proof (cA_range 1) as HR1. pose proof (Hz 15 ltac:(lia)) as Z15.
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (cA 1) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K0 Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold mxA. apply mx_zero. intros jj Hjj. destruct (Z.eq_dec jj 1) as [->|]; [exact Z0 | apply Hz; lia].
  - zbr Rfd false.
    assert (MX1 : mx = 1) by (unfold mxA; apply (mx_found _ 1); [lia | intros jj Hjj; apply Hz; lia | exact NZ]).
    pose proof (mxmn_facts ltac:(lia)) as (MN1 & MX15 & RT & MNRT & RTEQ).
    zstep Rfd. zstep Rfd.
    zstep Rfd. zbool.
    zstep Rfd. zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KL Rx) end.
    all: try first [assumption | close_pregs | zreg].
    + zregv. rewrite RTEQ, MX1. cbv zeta. destruct (Z.ltb_spec bits 1); destruct (Z.ltb_spec mn 1); destruct (Z.ltb_spec mn bits); lia.
    + zregv. rewrite MX1. reflexivity.
Qed.

Lemma count_phase0_s : forall Rb l M MD T av,
  codes = 0 -> m_halted MD = None -> PR Rb l -> zget_l Rb l kA7 = av ->
  mem_arr 2 R_segs M (sp + -136) 16 (fun _ => 0) -> mem_u32 R_segs M pb bits ->
  Kmax0 M MD T ->
  realizes R_segs (zcfg R_segs 95920 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  intros Rb l M MD T av Hc0 Hh HP LA7 Hcnt HB32 K0.
  pose proof C as C'. open_itc C'.
  assert (ZALL : forall jj, cA jj = 0).
  { intros jj. rewrite cntA_eq, Hc0. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (MX0 : mx = 0) by (unfold mxA; apply mx_zero; intros; apply ZALL).
  assert (Hcnt' : mem_arr 2 R_segs M (sp + -136) 16 cA).
  { eapply mem_arr_ext; [exact Hcnt|]. intros jj Hjj. cbn beta. symmetry. apply ZALL. }
  open_pregs HP. zkeys. zrebase.
  zbr Rfd true.
  zstep Rfd. zsetreg bits ltac:(symmetry; apply swrap32_small; lia).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (max_stage_14 Rx [] M MD T bits) end.
  all: try first [assumption | close_pregs | zreg].
  - intros; apply ZALL.
  - intros R' _ _ _ _ Hmx. exfalso. lia.
  - intros R' HP' XA7 _. eapply maxlow_s; try eassumption.
    + intros; apply ZALL.
    + intros R'' _ _ _ _ _ _ Hmx. exfalso. lia.
Qed.
End S7IT.
End FXG.
End S_It1.

Module S_It2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.
Import S_It0 S_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Section S7IT2.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation L k := (LZ (cntA lf lens_ofs codes) k).
#[local] Abbreviation KLEFT := (Kleft ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation offsAr := (offsA lf lens_ofs codes).
#[local] Abbreviation SKo i := (fst (itm_sort_k (lensA lf) lens_ofs i (offsA lf lens_ofs codes) (workA wf))).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation SKw i := (snd (itm_sort_k (lensA lf) lens_ofs i (offsA lf lens_ofs codes) (workA wf))).

Lemma cty_codes : (cty ty =? 0) = codetype_eqb ty CODES.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; reflexivity. Qed.

Definition Kneg (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kA6 = -1 ->
    itm_reject ty mx (it_left_check cntAr) = true -> 1 <= mx ->
    realizes R_segs (zcfg R_segs 97500 (zupd R' []) M MD) T.

Definition Koffs (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
    zget_l R' [] kT4 = cA 1 -> zget_l R' [] kT5 = cA 2 -> zget_l R' [] kT6 = cA 3 -> zget_l R' [] kS0 = cA 4 ->
    zget_l R' [] kS1 = cA 5 -> zget_l R' [] kS2 = cA 6 -> zget_l R' [] kS3 = cA 7 -> zget_l R' [] kS4 = cA 8 ->
    zget_l R' [] kS5 = cA 9 -> zget_l R' [] kS6 = cA 10 -> zget_l R' [] kS7 = cA 11 -> zget_l R' [] kS8 = cA 12 ->
    zget_l R' [] kS9 = cA 13 -> zget_l R' [] kS10 = cA 14 ->
    1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
    realizes R_segs (zcfg R_segs 96580 (zupd R' []) M MD) T.

Lemma left_s : forall M MD T,
  m_halted MD = None -> mem_arr 2 R_segs M (sp + -136) 16 cA -> Kneg M MD T -> Koffs M MD T -> KLEFT M MD T.
Proof using C zc ret wf cf nx.
  intros M MD T Hh Hcnt KN KO. unfold Kleft. intros Rb HP LT0 LT1 LA7 LT3 LT2 Hmx.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HCr : forall j, 0 <= j < 16 -> 0 <= cA j < 65536) by (intros j _; pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j); lia).
  assert (HRa : forall j, 0 <= cA j <= codes) by (intros j; apply (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j)).
  assert (LB : forall j, 0 <= j <= 15 -> -18874368 <= L j <= 32768).
  { intros j Hj. pose proof (LZ_bound cntAr j codes ltac:(lia) HRa Hj). lia. }
  assert (PP0 : forall j, 1 <= j <= 0 -> 0 <= L j) by (intros; lia).
  pose proof (HRa 1) as HR1. pose proof (HRa 15) as HR15.
  zrebase.
  tstep Rfd. zstep Rfd. zstep Rfd.
  destruct (Z.ltb_spec 2 (cA 1)) as [F1|P1].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 1); [reflexivity | lia | intros; lia | rewrite LZ_1; lia]. }
  zbr Rfd false.
  assert (PP1 : forall j, 1 <= j <= 1 -> 0 <= L j) by (intros j Hj; replace j with 1 by lia; rewrite LZ_1; lia). clear PP0.
  pose proof (LB 1 ltac:(lia)) as LB1. pose proof (LB 2 ltac:(lia)) as LB2. pose proof (HRa 2) as HR2.
  zstep Rfd. zsetreg (2 * cA 1) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. tstep Rfd.
  zstep Rfd. zsetreg (2 * L 1) ltac:(rewrite swrap32_small by lia; rewrite LZ_1; lia).
  zstep Rfd. zstep Rfd. zsetreg (2 * L 1) ltac:(symmetry; apply zext16_id; rewrite LZ_1; lia).
  zstep Rfd. zsetreg (L 2) ltac:(rewrite (LZ_S' cntAr 2) by lia; reflexivity).
  destruct (Z.ltb_spec (L 2) 0) as [F2|P2].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 2); [reflexivity | lia | intros; apply PP1; lia | exact F2]. }
  zbr Rfd false.
  assert (PP2 : forall j, 1 <= j <= 2 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 2) as [->|]; [exact P2 | apply PP1; lia]). clear PP1 P1.

  pose proof (LB 3 ltac:(lia)) as LB3. pose proof (HRa 3) as HR3. clear LB1.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 2) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 3) ltac:(rewrite (LZ_S' cntAr 3) by lia; reflexivity).
  destruct (Z.ltb_spec (L 3) 0) as [F3|P3].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 3); [reflexivity | lia | intros; apply PP2; lia | exact F3]. }
  zbr Rfd false.
  assert (PP3 : forall j, 1 <= j <= 3 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 3) as [->|]; [exact P3 | apply PP2; lia]). clear PP2 P2.
  pose proof (LB 4 ltac:(lia)) as LB4. pose proof (HRa 4) as HR4. clear LB2.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 3) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 4) ltac:(rewrite (LZ_S' cntAr 4) by lia; reflexivity).
  destruct (Z.ltb_spec (L 4) 0) as [F4|P4].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 4); [reflexivity | lia | intros; apply PP3; lia | exact F4]. }
  zbr Rfd false.
  assert (PP4 : forall j, 1 <= j <= 4 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 4) as [->|]; [exact P4 | apply PP3; lia]). clear PP3 P3.
  pose proof (LB 5 ltac:(lia)) as LB5. pose proof (HRa 5) as HR5. clear LB3.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 4) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 5) ltac:(rewrite (LZ_S' cntAr 5) by lia; reflexivity).
  destruct (Z.ltb_spec (L 5) 0) as [F5|P5].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 5); [reflexivity | lia | intros; apply PP4; lia | exact F5]. }
  zbr Rfd false.
  assert (PP5 : forall j, 1 <= j <= 5 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 5) as [->|]; [exact P5 | apply PP4; lia]). clear PP4 P4.
  pose proof (LB 6 ltac:(lia)) as LB6. pose proof (HRa 6) as HR6. clear LB4.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 5) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 6) ltac:(rewrite (LZ_S' cntAr 6) by lia; reflexivity).
  destruct (Z.ltb_spec (L 6) 0) as [F6|P6].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 6); [reflexivity | lia | intros; apply PP5; lia | exact F6]. }
  zbr Rfd false.
  assert (PP6 : forall j, 1 <= j <= 6 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 6) as [->|]; [exact P6 | apply PP5; lia]). clear PP5 P5.
  pose proof (LB 7 ltac:(lia)) as LB7. pose proof (HRa 7) as HR7. clear LB5.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 6) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 7) ltac:(rewrite (LZ_S' cntAr 7) by lia; reflexivity).
  destruct (Z.ltb_spec (L 7) 0) as [F7|P7].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 7); [reflexivity | lia | intros; apply PP6; lia | exact F7]. }
  zbr Rfd false.
  assert (PP7 : forall j, 1 <= j <= 7 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 7) as [->|]; [exact P7 | apply PP6; lia]). clear PP6 P6.
  pose proof (LB 8 ltac:(lia)) as LB8. pose proof (HRa 8) as HR8. clear LB6.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 7) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 8) ltac:(rewrite (LZ_S' cntAr 8) by lia; reflexivity).
  destruct (Z.ltb_spec (L 8) 0) as [F8|P8].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 8); [reflexivity | lia | intros; apply PP7; lia | exact F8]. }
  zbr Rfd false.
  assert (PP8 : forall j, 1 <= j <= 8 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 8) as [->|]; [exact P8 | apply PP7; lia]). clear PP7 P7.
  pose proof (LB 9 ltac:(lia)) as LB9. pose proof (HRa 9) as HR9. clear LB7.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 8) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 9) ltac:(rewrite (LZ_S' cntAr 9) by lia; reflexivity).
  destruct (Z.ltb_spec (L 9) 0) as [F9|P9].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 9); [reflexivity | lia | intros; apply PP8; lia | exact F9]. }
  zbr Rfd false.
  assert (PP9 : forall j, 1 <= j <= 9 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 9) as [->|]; [exact P9 | apply PP8; lia]). clear PP8 P8.
  pose proof (LB 10 ltac:(lia)) as LB10. pose proof (HRa 10) as HR10. clear LB8.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 9) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 10) ltac:(rewrite (LZ_S' cntAr 10) by lia; change (10 - 1) with 9; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 10) 0) as [F10|P10].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 10); [reflexivity | lia | intros; apply PP9; lia | exact F10]. }
  zbr Rfd false.
  assert (PP10 : forall j, 1 <= j <= 10 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 10) as [->|]; [exact P10 | apply PP9; lia]). clear PP9 P9.
  pose proof (LB 11 ltac:(lia)) as LB11. pose proof (HRa 11) as HR11. clear LB9.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 10) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 11) ltac:(rewrite (LZ_S' cntAr 11) by lia; change (11 - 1) with 10; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 11) 0) as [F11|P11].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 11); [reflexivity | lia | intros; apply PP10; lia | exact F11]. }
  zbr Rfd false.
  assert (PP11 : forall j, 1 <= j <= 11 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 11) as [->|]; [exact P11 | apply PP10; lia]). clear PP10 P10.
  pose proof (LB 12 ltac:(lia)) as LB12. pose proof (HRa 12) as HR12. clear LB10.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 11) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 12) ltac:(rewrite (LZ_S' cntAr 12) by lia; change (12 - 1) with 11; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 12) 0) as [F12|P12].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 12); [reflexivity | lia | intros; apply PP11; lia | exact F12]. }
  zbr Rfd false.
  assert (PP12 : forall j, 1 <= j <= 12 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 12) as [->|]; [exact P12 | apply PP11; lia]). clear PP11 P11.
  pose proof (LB 13 ltac:(lia)) as LB13. pose proof (HRa 13) as HR13. clear LB11.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 12) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 13) ltac:(rewrite (LZ_S' cntAr 13) by lia; change (13 - 1) with 12; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 13) 0) as [F13|P13].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 13); [reflexivity | lia | intros; apply PP12; lia | exact F13]. }
  zbr Rfd false.
  assert (PP13 : forall j, 1 <= j <= 13 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 13) as [->|]; [exact P13 | apply PP12; lia]). clear PP12 P12.
  pose proof (LB 14 ltac:(lia)) as LB14. pose proof (HRa 14) as HR14. clear LB12.
  tstep Rfd.
  zstep Rfd. zsetreg (2 * L 13) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd. zsetreg (L 14) ltac:(rewrite (LZ_S' cntAr 14) by lia; change (14 - 1) with 13; symmetry; apply swrap32_small; lia).
  destruct (Z.ltb_spec (L 14) 0) as [F14|P14].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 14); [reflexivity | lia | intros; apply PP13; lia | exact F14]. }
  zbr Rfd false.
  assert (PP14 : forall j, 1 <= j <= 14 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 14) as [->|]; [exact P14 | apply PP13; lia]). clear PP13 P13.
  pose proof (LB 15 ltac:(lia)) as LB15. clear LB13.
  zstep Rfd. zsetreg (2 * L 14) ltac:(rewrite swrap32_small by (rewrite Z.shiftl_mul_pow2 by lia; lia); rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (E15 : L 15 = 2 * L 14 - cA 15) by (rewrite (LZ_S' cntAr 15) by lia; change (15 - 1) with 14; reflexivity).
  destruct (Z.ltb_spec (2 * L 14) (cA 15)) as [F15|P15].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite (left_check_none cntAr 15); [reflexivity | lia | intros; apply PP14; lia | lia]. }
  zbr Rfd false.
  assert (PP15 : forall j, 1 <= j <= 15 -> 0 <= L j) by (intros j Hj; destruct (Z.eq_dec j 15) as [->|]; [lia | apply PP14; lia]). clear PP14 P14.
  assert (HLC : it_left_check cntAr = Some (L 15)) by (apply left_check_some; exact PP15).
  destruct (Z.eq_dec (2 * L 14) (cA 15)) as [Z15|NZ15].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KO Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite HLC. replace (0 <? L 15) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  zbr Rfd false.
  assert (L15P : 0 < L 15) by lia.
  assert (CTR : 0 <= cty ty <= 2) by (clear; destruct ty; cbn; lia_std).
  zstep Rfd. zsetreg (Z.b2z (cty ty =? 0)) ltac:(rewrite (Z.mod_small (cty ty)) by lia_std; destruct (Z.eqb_spec (cty ty) 0); destruct (Z.ltb_spec (cty ty) 1); cbn [Z.b2z]; lia_std).
  zstep Rfd. zsetreg (Z.b2z ((cty ty =? 0) || negb (mx =? 1))) ltac:(destruct (cty ty =? 0); destruct (mx =? 1); reflexivity).
  destruct ((cty ty =? 0) || negb (mx =? 1)) eqn:RJ.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KN Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite HLC, <- cty_codes, RJ. replace (0 <? L 15) with true by (symmetry; apply Z.ltb_lt; lia_std). reflexivity.
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KO Rx) end.
    all: try first [assumption | close_pregs | zreg].
    unfold itm_reject. rewrite HLC, <- cty_codes, RJ. apply Bool.andb_false_r.
Qed.

Lemma offs_s : forall M MD T,
  m_halted MD = None -> mem_wr R_segs M (sp - 192) 192 ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) 0 0 ->
     mem_arr 2 R_segs M' (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
     1 <= mx -> itm_reject ty mx (it_left_check cntAr) = false ->
     realizes R_segs (zcfg R_segs 96692 (zupd R' []) M' MD) T) ->
  Koffs M MD T.
Proof using C zc ret wf cf nx.
  intros M MD T Hh Wf K. unfold Koffs.
  intros Rb HP LT0 LT1 LA7 LT4 LT5 LT6 LS0 LS1 LS2 LS3 LS4 LS5 LS6 LS7 LS8 LS9 LS10 Hmx HRJ.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  assert (HRa : forall j, 0 <= cA j <= 288) by (intros j; pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j); lia).
  pose proof (mpost_stable R_segs M (sp + -166) (sp + -136) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -166) (sp + -136) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd. zsetreg (OZ cntAr 3) ltac:(rewrite (OZ_S' cntAr 3) by lia; change (3 - 1) with 2; rewrite (OZ_S' cntAr 2) by lia; change (2 - 1) with 1; rewrite OZ_1; lia).
  zstep Rfd. zsetreg (OZ cntAr 4) ltac:(rewrite (OZ_S' cntAr 4) by lia; change (4 - 1) with 3; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (OZ cntAr 5) ltac:(rewrite (OZ_S' cntAr 5) by lia; change (5 - 1) with 4; lia).
  zstep Rfd. zsetreg (OZ cntAr 6) ltac:(rewrite (OZ_S' cntAr 6) by lia; change (6 - 1) with 5; lia).
  zstep Rfd. zsetreg (OZ cntAr 7) ltac:(rewrite (OZ_S' cntAr 7) by lia; change (7 - 1) with 6; lia).
  zstep Rfd. zsetreg (OZ cntAr 8) ltac:(rewrite (OZ_S' cntAr 8) by lia; change (8 - 1) with 7; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (OZ cntAr 9) ltac:(rewrite (OZ_S' cntAr 9) by lia; change (9 - 1) with 8; lia).
  zstep Rfd. zsetreg (OZ cntAr 10) ltac:(rewrite (OZ_S' cntAr 10) by lia; change (10 - 1) with 9; lia).
  zstep Rfd. zsetreg (OZ cntAr 11) ltac:(rewrite (OZ_S' cntAr 11) by lia; change (11 - 1) with 10; lia).
  zstep Rfd. zsetreg (OZ cntAr 12) ltac:(rewrite (OZ_S' cntAr 12) by lia; change (12 - 1) with 11; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (OZ cntAr 13) ltac:(rewrite (OZ_S' cntAr 13) by lia; change (13 - 1) with 12; lia).
  zstep Rfd. zsetreg (OZ cntAr 14) ltac:(rewrite (OZ_S' cntAr 14) by lia; change (14 - 1) with 13; lia).
  zstep Rfd. zsetreg (OZ cntAr 15) ltac:(rewrite (OZ_S' cntAr 15) by lia; change (15 - 1) with 14; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  all: try first [assumption | close_pregs | zreg].
  unfold mem_u16 in *.
  apply mem_arr_of_elems; [lia | lia | lia | rewrite two64_eq; lia |].
  intros i Hi. change (Z.to_nat 2) with 2%nat. cbn beta.

  assert (CS : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14) by lia.
  unfold offsA. rewrite (offs_spec cntAr HRa) by lia.
  destruct CS as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]; rewrite E; clear E Hi.
  - replace (sp + -166 + 2 * 0) with (sp + -166) by lia. change (0 + 1) with 1. replace (OZ cntAr 1) with 0 by reflexivity. assumption.
  - replace (sp + -166 + 2 * 1) with (sp + -164) by lia. change (1 + 1) with 2. replace (OZ cntAr 2) with (cA 1) by (rewrite (OZ_S' cntAr 2) by lia; change (2 - 1) with 1; rewrite OZ_1; lia). assumption.
  - replace (sp + -166 + 2 * 2) with (sp + -162) by lia. change (2 + 1) with 3. idtac. assumption.
  - replace (sp + -166 + 2 * 3) with (sp + -160) by lia. change (3 + 1) with 4. idtac. assumption.
  - replace (sp + -166 + 2 * 4) with (sp + -158) by lia. change (4 + 1) with 5. idtac. assumption.
  - replace (sp + -166 + 2 * 5) with (sp + -156) by lia. change (5 + 1) with 6. idtac. assumption.
  - replace (sp + -166 + 2 * 6) with (sp + -154) by lia. change (6 + 1) with 7. idtac. assumption.
  - replace (sp + -166 + 2 * 7) with (sp + -152) by lia. change (7 + 1) with 8. idtac. assumption.
  - replace (sp + -166 + 2 * 8) with (sp + -150) by lia. change (8 + 1) with 9. idtac. assumption.
  - replace (sp + -166 + 2 * 9) with (sp + -148) by lia. change (9 + 1) with 10. idtac. assumption.
  - replace (sp + -166 + 2 * 10) with (sp + -146) by lia. change (10 + 1) with 11. idtac. assumption.
  - replace (sp + -166 + 2 * 11) with (sp + -144) by lia. change (11 + 1) with 12. idtac. assumption.
  - replace (sp + -166 + 2 * 12) with (sp + -142) by lia. change (12 + 1) with 13. idtac. assumption.
  - replace (sp + -166 + 2 * 13) with (sp + -140) by lia. change (13 + 1) with 14. idtac. assumption.
  - replace (sp + -166 + 2 * 14) with (sp + -138) by lia. change (14 + 1) with 15. idtac. assumption.
Qed.
Lemma sort_loop_s : forall fuel i Rb l M MD T,
  (Z.to_nat (codes - i) <= fuel)%nat -> 0 <= i < codes ->
  m_halted MD = None -> PR Rb l ->
  zget_l Rb l kA6 = i -> zget_l Rb l kT3 = p + 168 + 2 * lens_ofs + 2 * i -> zget_l Rb l kT2 = sp + -168 ->
  zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true ->
  mem_wr R_segs M (sp - 192) 192 -> mem_wr R_segs M p 7176 ->
  mem_arr 2 R_segs M (p + 168) 320 lf ->
  mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get (SKo i) (j + 1)) ->
  mem_arr 2 R_segs M (p + 808) 288 (arr_get (SKw i)) ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf ->
     mem_arr 2 R_segs M' (p + 808) 288 (arr_get (SKw codes)) ->
     realizes R_segs (zcfg R_segs 96776 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96732 (zupd Rb l) M MD) T.
Proof using C zc ret cf nx.
  induction fuel as [|fuel IH]; intros i Rb l M MD T Hfuel Hi Hh HP LA6 LT3 LT2 LT0 LT1 LA7 SOK Wf Wp Hlens Hoffs Hwork K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys.
  pose proof (Hlens15 i ltac:(lia)) as Hl15. pose proof (Hlf (lens_ofs + i) ltac:(lia)) as Hl16.
  assert (HOr : forall j, 0 <= j < 16 -> 0 <= arr_get (SKo i) j < 65536) by (intros j _; unfold offsA; apply itm_sort_k_offs_range).
  pose proof (mpost_stable R_segs M (sp + -166) (sp + -136) (p + 808) (p + 1384) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -166) (sp + -136) (p + 808) (p + 1384)) M) by (apply mpost_refl).
  assert (J : forall RJ MJ, PR RJ [] ->
    zget_l RJ [] kA6 = i -> zget_l RJ [] kT3 = p + 168 + 2 * lens_ofs + 2 * i -> zget_l RJ [] kT2 = sp + -168 ->
    zget_l RJ [] kT0 = mx -> zget_l RJ [] kT1 = mn -> zget_l RJ [] kA7 = rt ->
    mpost R_segs M MJ (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
    mem_wr R_segs MJ (sp - 192) 192 -> mem_wr R_segs MJ p 7176 ->
    mem_arr 2 R_segs MJ (p + 168) 320 lf ->
    mem_arr 2 R_segs MJ (sp + -166) 15 (fun j => arr_get (SKo (i + 1)) (j + 1)) ->
    mem_arr 2 R_segs MJ (p + 808) 288 (arr_get (SKw (i + 1))) ->
    realizes R_segs (zcfg R_segs 96720 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HPJ JA6 JT3 JT2 JT0 JT1 JA7 HPO WfJ WpJ HlensJ HoffsJ HworkJ.
    clear HAG Hoffs Hwork Wf Wp Hlens.
    open_pregs HPJ. zkeys. zrebase.
    zstep Rfd. zstep Rfd.
    destruct (Z.eq_dec (i + 1) codes) as [Hend|Hmore].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx MJ) end.
      all: try first [assumption | close_pregs | zreg].
      rewrite Hend in HworkJ. exact HworkJ.
    - zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (i + 1) Rx [] MJ MD T) end.
      all: try first [lia | assumption | close_pregs | zreg].
      intros R' M'. intros. eapply K; try eassumption.
      eapply mpost_trans; [exact HPO | assumption]. }
  zrebase.
  tstep Rfd.
  destruct (Z.eq_dec (lf (lens_ofs + i)) 0) as [Z0|NZ].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J Rx M) end.
    all: try first [assumption | close_pregs | zreg].
    + rewrite sort_k_skip; [exact Hoffs | lia | rewrite lensA_get; exact Z0].
    + rewrite sort_k_skip; [exact Hwork | lia | rewrite lensA_get; exact Z0].
  - zbr Rfd false.
    pose proof (sort_ok_at (lensA lf) lens_ofs codes offsAr (workA wf) 288 i SOK ltac:(lia) ltac:(rewrite lensA_get; exact NZ)) as HO.
    rewrite lensA_get in HO.
    zstep Rfd. zsetreg (2 * lf (lens_ofs + i)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep Rfd.
    tstep Rfd.
    zsetreg (arr_get (SKo i) (lf (lens_ofs + i))) ltac:(f_equal; lia).
    zstep Rfd.
    zstep Rfd. zsetreg (2 * arr_get (SKo i) (lf (lens_ofs + i))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    tstore_arr Rfd Hoffs (lf (lens_ofs + i) - 1).
    zstep Rfd.
    tstore_arr Rfd Hwork (arr_get (SKo i) (lf (lens_ofs + i))).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J Rx Mx) end.
    all: try first [assumption | close_pregs | zreg].
    + eapply mem_arr_ext; [exact Hoffs|]. intros j Hj. cbn beta.
      rewrite sort_k_take by (try lia; rewrite lensA_get; exact NZ). cbv zeta. rewrite lensA_get. cbn [fst].
      unfold zfupd. rewrite arr_get_set. unfold arr_inb. rewrite (proj1 (sort_k_len _ _ _ _ _)), offsA_len.
      rewrite wrap16_small by lia.
      destruct (Z.eqb_spec j (lf (lens_ofs + i) - 1)); destruct (Z.eqb_spec (lf (lens_ofs + i)) (j + 1)); cbn [andb]; try lia.
      destruct (Z.leb_spec 0 (lf (lens_ofs + i))); destruct (Z.ltb_spec (lf (lens_ofs + i)) 16); cbn [andb]; lia.
    + apply mem_arr_arr_set in Hwork; [| rewrite (proj2 (sort_k_len _ _ _ _ _)), workA_len; lia].
      eapply mem_arr_ext; [exact Hwork|]. intros j Hj. cbn beta.
      rewrite sort_k_take by (try lia; rewrite lensA_get; exact NZ). cbv zeta. rewrite lensA_get. cbn [snd].
      rewrite (wrap16_small i) by lia. reflexivity.
Qed.

Lemma sort_phase_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  1 <= mx -> it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true ->
  mem_wr R_segs M (sp - 192) 192 -> mem_wr R_segs M p 7176 ->
  mem_arr 2 R_segs M (p + 168) 320 lf ->
  mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get offsAr (j + 1)) ->
  mem_arr 2 R_segs M (p + 808) 288 wf ->
  (forall R' M', PR R' [] -> zget_l R' [] kT0 = mx -> zget_l R' [] kT1 = mn -> zget_l R' [] kA7 = rt ->
     mpost R_segs M M' (sp + -166) (sp + -136) (p + 808) (p + 1384) ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf ->
     mem_arr 2 R_segs M' (p + 808) 288 (arr_get work1Ar) ->
     realizes R_segs (zcfg R_segs 96776 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96692 (zupd Rb l) M MD) T.
Proof using C zc ret cf nx.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 Hmx SOK Wf Wp Hlens Hoffs Hwork K.
  pose proof C as C'. open_itc C'.
  assert (Hc0 : 0 < codes).
  { destruct (Z.eq_dec codes 0) as [E|]; [|lia]. exfalso. enough (mx = 0) by lia. unfold mxA. apply mx_zero.
    intros j _. rewrite cntA_eq, E. unfold cntK. rewrite itm_count_k_0 by lia. apply it_zero_count_spec. }
  assert (Hoffs0 : mem_arr 2 R_segs M (sp + -166) 15 (fun j => arr_get (SKo 0) (j + 1))).
  { rewrite itm_sort_k_0 by lia. cbn [fst]. exact Hoffs. }
  assert (Hwork0 : mem_arr 2 R_segs M (p + 808) 288 (arr_get (SKw 0))).
  { rewrite itm_sort_k_0 by lia. cbn [snd]. eapply mem_arr_ext; [exact Hwork|]. intros j _. symmetry. apply workA_get. }
  clear Hoffs Hwork. open_pregs HP. zkeys. zrebase.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd. zstep Rfd. zsetreg codes ltac:(symmetry; apply zext32_id; lia).
  zstep Rfd. zstep Rfd. zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (sort_loop_s (Z.to_nat codes) 0 Rx [] M MD T) end.
  all: try first [lia | assumption | close_pregs | zreg].
Qed.

End S7IT2.
End FXG.
End S_It2.

Module S_It3.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.
Import S_It0 S_It1.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Definition lowS (z : Z) : Z := if z =? 4294967295 then -1 else z.

Definition EXA (ty : codetype) (p : Z) : Z := match ty with CODES => p + 808 | LENS => 67232 | DISTS => 67358 end.
Definition BSA (ty : codetype) (p : Z) : Z := match ty with CODES => p + 808 | LENS => 67170 | DISTS => 67294 end.
Definition EXAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => EXA ty p end.
Definition BSAn (ty : codetype) (p : Z) : Z := match ty with CODES => 0 | _ => BSA ty p end.
Lemma EXAn_ne : forall ty p, ty <> CODES -> EXAn ty p = EXA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Lemma BSAn_ne : forall ty p, ty <> CODES -> BSAn ty p = BSA ty p. Proof. intros [] p H; [congruence|reflexivity|reflexivity]. Qed.
Definition NE (ty : codetype) : Z := match ty with CODES => 288 | LENS => 31 | DISTS => 32 end.
Definition isL (ty : codetype) : Z := match ty with LENS => 1 | _ => 0 end.
Definition isD (ty : codetype) : Z := match ty with DISTS => 1 | _ => 0 end.

Lemma NE_ext_len : forall ty, NE ty = it_ext_len ty 288.
Proof. destruct ty; reflexivity. Qed.


Lemma pow2_le15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof.
  intros k Hk. split. - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia. - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.
Lemma sllw_1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl 1 (k mod 32)) = 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l. pose proof (pow2_le15 k Hk). apply swrap32_small. lia.
Qed.
Lemma sllw_m1 : forall k, 0 <= k <= 15 -> bv_swrap 32 (Z.shiftl (-1) (k mod 32)) = - 2 ^ k.
Proof.
  intros k Hk. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. pose proof (pow2_le15 k Hk).
  rewrite swrap32_small by lia. lia.
Qed.
Lemma srlw_small : forall a b, 0 <= a < 2147483648 -> 0 <= b < 32 ->
  bv_swrap 32 (Z.shiftr (a mod 4294967296) (b mod 32)) = Z.shiftr a b.
Proof.
  intros a b Ha Hb. rewrite !Z.mod_small by lia.
  assert (0 <= Z.shiftr a b <= a).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  apply swrap32_small. lia.
Qed.
Lemma mul_S_sub : forall a m, a * Z.of_nat (S m) - a = a * Z.of_nat m.
Proof. intros. rewrite Nat2Z.inj_succ. ring. Qed.
Lemma mul_S_ge : forall a m, 0 <= a -> a <= a * Z.of_nat (S m).
Proof. intros. rewrite Nat2Z.inj_succ. nia. Qed.

Lemma wrap8_mod : forall z, wrap8 z = z mod 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Section S7IT3.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).

Definition pregs6 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp /\
  zget_l R l kA1 = p + 168 + 2 * lens_ofs /\
  zget_l R l kA3 = p + 160 /\ zget_l R l kA4 = pb /\ zget_l R l kA5 = p + 808.
Ltac open_pregs6 H := unfold pregs6 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & e & g & h & i).
Ltac close_pregs6 := unfold pregs6; split_conj; zreg.

Definition cregs (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kA2 = it_match ty /\
  zget_l R l kT3 = EXA ty p /\ zget_l R l kT4 = BSA ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition cregsN (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\ zget_l R l kA0 = it_match ty /\
  zget_l R l kT3 = EXAn ty p /\ zget_l R l kT2 = BSAn ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition cregsB (R : tree Z) (l : list (positive * Z)) : Prop :=
  pregs6 R l /\ zget_l R l kA7 = rt /\ zget_l R l kT0 = mx /\
  zget_l R l kT3 = EXAn ty p /\ zget_l R l kT2 = BSAn ty p /\ zget_l R l kS2 = 1 /\ zget_l R l kS3 = -1 /\
  zget_l R l kS4 = 2 ^ rt - 1 /\ zget_l R l kS5 = sp + -136.
Definition sregs (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT6 = t_sym st /\ zget_l R l kT1 = t_len st /\ zget_l R l kA6 = t_drop st /\ zget_l R l kT5 = t_used st /\
  zget_l R l kS1 = t_huff st /\ zget_l R l kS0 = p + 1384 + 4 * t_next st /\ zget_l R l kA2 = 2 ^ t_curr st /\
  zget_l R l kS7 = lowS (t_low st).
Definition cmem (M : mem) : Prop :=
  mem_wr R_segs M (sp - 192) 192 /\ mem_wr R_segs M p 7176 /\
  mem_arr 2 R_segs M (p + 168) 320 lf /\
  mem_arr 2 R_segs M (p + 808) 288 (arr_get work1Ar) /\
  mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) /\
  mem_u64 R_segs M (sp + -184) (isD ty) /\ mem_u64 R_segs M (sp + -176) (isL ty) /\
  mem_arr 2 R_segs M (EXA ty p) (NE ty) (it_extra ty work1Ar) /\ mem_arr 2 R_segs M (BSA ty p) (NE ty) (it_base ty work1Ar).
Definition smem (st : ItSt) (M : mem) : Prop :=
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get (t_count st)) /\
  mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (t_tbl st)).
Definition spure (st : ItSt) : Prop :=
  t_work st = work1Ar /\ ZSEP (t_low st = 4294967295 \/ 0 <= t_low st < 32768) /\ ZSEP (t_drop st = 0 \/ t_drop st = rt) /\
  0 <= t_next st /\ nx <= t_next st /\
  (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) /\
  (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) /\
  arr_len (t_count st) = 16 /\ arr_len (t_tbl st) = 1444.

Ltac open_cregs H :=
  unfold cregsN in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LA2" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  dand H as (hp & a & b & c & d & e & f & g & h & i); open_pregs6 hp.
Ltac open_sregs H :=
  unfold sregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let c := fresh "LA6" in let d := fresh "LT5" in
  let e := fresh "LS1" in let f := fresh "LS0" in let g := fresh "LT2" in let h := fresh "LS7" in
  dand H as (a & b & c & d & e & f & g & h).
Ltac open_cmem H :=
  unfold cmem in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "HslD" in let g := fresh "HslL" in let h := fresh "Hext" in let i := fresh "Hbase" in
  dand H as (a & b & c & d & e & f & g & h & i).
Ltac open_smem H :=
  unfold smem in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in dand H as (a & b).
Ltac open_spure H :=
  unfold spure in H;
  let a := fresh "WK" in let b := fresh "LOWR" in let b2 := fresh "DROPR" in let c := fresh "NX0" in let d := fresh "NX1" in
  let e := fresh "HCr" in let f := fresh "HTr" in let g := fresh "CL" in let h := fresh "TL" in
  dand H as (a & b & b2 & c & d & e & f & g & h).
Ltac close_cregs := unfold cregsN; split_conj; try close_pregs6; zreg.
Ltac close_sregs := unfold sregs; split_conj; zreg.
Ltac kauto := first
  [ assumption
  | lazymatch goal with
    | |- cregsN _ _ => close_cregs
    | |- sregs (tr_st1 _ _) _ _ => fail
    | |- sregs _ _ _ => close_sregs
    | |- pregs6 _ _ => close_pregs6
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].

Lemma work1_range : forall j, 0 <= j < 288 -> 0 <= arr_get work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx ty.
  intros j Hj. pose proof C as C'. open_itc C'. unfold work1A. rewrite itm_work_eq.
  apply (sort_k_work_range _ _ _ _ _ 288); [|exact Hj]. intros i Hi. rewrite workA_get. apply Hwf. exact Hi.
Qed.

Lemma rt_facts : 1 <= mx -> 1 <= rt <= 15 /\ mn <= rt <= mx /\ 1 <= mn.
Proof using C zc ret sp pb p wf cf nx ty.
  intros H. pose proof (mxmn_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C H) as (A & B & D & E & F). cbv zeta in F.
  destruct (Z.ltb_spec bits mx); [destruct (Z.ltb_spec mn bits) | destruct (Z.ltb_spec mn mx)]; lia_std.
Qed.

Lemma mx15 : 0 <= mx <= 15.
Proof using. unfold mxA. apply mx_range. Qed.

Lemma xaddr_facts :
  ZSEP (p + 7160 <= EXA ty p \/ EXA ty p + 2 * NE ty <= p + 1384) /\
  ZSEP (p + 7160 <= BSA ty p \/ BSA ty p + 2 * NE ty <= p + 1384) /\
  0 <= EXA ty p /\ EXA ty p + 2 * NE ty <= zc /\
  0 <= BSA ty p /\ BSA ty p + 2 * NE ty <= zc /\ 0 < NE ty <= 288.
Proof using C ret sp pb wf cf bits nx codes lens_ofs lf.
  pose proof C as C'. open_itc C'. unfold ZSEP in *. destruct ty; cbn [EXA BSA NE]; lia_std.
Qed.
Ltac xaddr := pose proof xaddr_facts as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma base_range : forall j, 0 <= j < NE ty -> 0 <= it_base ty work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx.
  intros j Hj. pose proof (work1_range j) as W.
  destruct ty; cbn [it_base NE] in *; [apply W; lia_std | apply lbase_range; lia_std | apply dbase_range; lia_std].
Qed.
Lemma ext_range : forall j, 0 <= j < NE ty -> 0 <= it_extra ty work1Ar j < 65536.
Proof using C zc ret sp pb p cf bits nx.
  intros j Hj. pose proof (work1_range j) as W.
  destruct ty; cbn [it_extra NE] in *; [apply W; lia_std | apply lext_range; lia_std | apply dext_range; lia_std].
Qed.

Lemma here_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> cmem M -> spure st ->
  0 <= t_sym st < 288 -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall R', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS10 = tr_op X st -> zget_l R' [] kS9 = tr_val X st ->
     realizes R_segs (zcfg R_segs 97060 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 96984 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HU Hsym Hw Hwm HcB K.
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. open_cmem HM. open_spure HU. zkeys. xaddr.
  pose proof work1_range as HWr. pose proof base_range as HBr. pose proof ext_range as HEr.
  assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia).
  unfold tr_w in Hw, Hwm. rewrite WK in Hw, Hwm. box Hwm. clear HtyC HtyD LOWR DROPR.
  zrebase.
  zstep Rfd. zstep Rfd. zsetreg (2 * t_sym st) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  tstep Rfd.
  zstep Rfd.
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)) as [Cw1|Cw1'].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto.
    + zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
    + zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite WK. destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [reflexivity | lia].
  - zbr Rfd true.
    destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))) as [Cw2|Cw2'].
    + zbr Rfd true.
      unbox Hwm. specialize (Hwm Cw2).
      assert (Hty : ty <> CODES) by (intro HH; specialize (HcB HH); unfold tr_w in HcB; rewrite WK in HcB; lia).
      rewrite (EXAn_ne _ _ Hty) in LT3. rewrite (BSAn_ne _ _ Hty) in LT4.
      zstep Rfd. zsetreg (arr_get work1Ar (t_sym st) - it_match ty) ltac:(symmetry; apply swrap32_small; lia).
      zstep Rfd. zstep Rfd. zsetreg (2 * (arr_get work1Ar (t_sym st) - it_match ty)) ltac:(symmetry; apply zext32_x2; lia).
      zstep Rfd. zstep Rfd.
      tstep Rfd.
      tstep Rfd.
      rewrite <- (EXAn_ne _ _ Hty) in LT3. rewrite <- (BSAn_ne _ _ Hty) in LT4.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. cbn [fst]. symmetry. apply wrap8_mod.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [|lia]. reflexivity.
    + zbr Rfd false.
      zstep Rfd. zstep Rfd. zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto.
      * zregv. unfold tr_op, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
      * zregv. unfold tr_val, tr_ov, tr_w. cbn [x_ty itm_ctx]. rewrite ?WK.
        destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [lia|].
        destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); [lia|]. reflexivity.
Qed.
Lemma entry_write : forall M base n f i op hbits val a0 a1 a2,
  mem_arr 4 R_segs M base i f ->
  mem_arr 4 R_segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u8 R_segs M a0 op -> mem_u8 R_segs M a1 hbits -> mem_u16 R_segs M a2 val ->
  a0 = base + 4 * i -> a1 = a0 + 1 -> a2 = a0 + 2 ->
  0 <= i < n -> base + 4 * n <= two64 -> 0 <= base ->
  0 <= op < 256 -> 0 <= hbits < 256 -> 0 <= val < 65536 ->
  mem_arr 4 R_segs M base n (zfupd f i (code_pack op hbits val)).
Proof using.
  intros M base n f i op hbits val a0 a1 a2 H1 H2 Ho Hb Hv -> -> -> Hi Hn Hb0 Ro Rb Rv.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  apply mem_arr4_pack; try assumption; rewrite ?two64_eq in *; lia.
Qed.

Lemma fill_loop_s : forall trips f t n st Rb l M MD T,
  f = 2 ^ tr_hb st * Z.of_nat trips -> (1 <= trips)%nat -> Z.of_nat trips <= n ->
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l ->
  zget_l Rb l kS6 = f -> zget_l Rb l kS11 = - 2 ^ tr_hb st -> zget_l Rb l kRA = tr_hd st - 2 ^ tr_hb st ->
  zget_l Rb l kS10 = tr_op X st -> zget_l Rb l kS8 = tr_hb st -> zget_l Rb l kS9 = tr_val X st ->
  0 <= tr_hb st <= 15 -> 0 <= t_next st -> 0 <= tr_hd st -> t_next st + tr_hd st + f - 2 ^ tr_hb st < 1444 ->
  0 <= tr_op X st < 256 -> 0 <= tr_val X st < 65536 ->
  mem_wr R_segs M p 7176 -> mem_arr 4 R_segs M (p + 1384) 1444 (arr_get t) -> arr_len t = 1444 ->
  (forall R' M', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS8 = tr_hb st ->
     mpost R_segs M M' (p + 1384) (p + 7160) 0 0 ->
     mem_wr R_segs M' p 7176 ->
     mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get (snd (loopZ n (fill_body (tr_here X st) (2 ^ tr_hb st) (tr_hd st) (t_next st)) (f, t)))) ->
     realizes R_segs (zcfg R_segs 97120 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97080 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction trips as [|trips IH]; intros f t n st Rb l M MD T Hf Htr Hn Hh HC HS LS6 LS11 LRA LS10 LS8 LS9 Hhb Hnx0 Hhd Hfit Rop Rval Wp Htbl TL K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. zkeys.
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI.
  set (I := 2 ^ tr_hb st) in *.
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  assert (Hf1 : I <= f) by (rewrite Hf; apply mul_S_ge; lia).
  assert (W1 : wrap32 (f - I) = f - I) by (apply wrap32_small; lia).
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) Htbl ltac:(lia)) as [HT1 HT2].
  clear Htbl. zrebase.
  zstep Rfd. zsetreg (f - I) ltac:(symmetry; apply swrap32_small; lia).
  zstep Rfd. zsetreg (tr_hd st + (f - I)) ltac:(lia).
  zstep Rfd. zstep Rfd. zsetreg (4 * (tr_hd st + (f - I))) ltac:(symmetry; apply zext32_x4; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_op X st), Hb : mem_u8 _ _ _ (tr_hb st), Hv : mem_u16 _ _ _ (tr_val X st) |- _ =>
    pose proof (entry_write Mc (p + 1384) 1444 (arr_get t) (t_next st + tr_hd st + (f - I)) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) Rop ltac:(lia) Rval) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
  assert (EH : code_pack (tr_op X st) (tr_hb st) (tr_val X st) = tr_here X st).
  { unfold tr_here. rewrite (wrap8_mod (tr_hb st)). rewrite Z.mod_small by lia. reflexivity. }
  rewrite EH in Htbl. clear EH.
  replace (t_next st + tr_hd st + (f - I)) with (t_next st + (tr_hd st + wrap32 (f - I))) in Htbl by lia.
  zstep Rfd.
  destruct (Z.eq_dec (f - I) 0) as [Hz|Hnz].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
    all: try kauto.
    rewrite fill_last by first [lia | rewrite W1; exact Hz]. cbn [snd]. rewrite W1, Hz in Htbl. exact Htbl.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (IH (f - I) (arr_set t (t_next st + (tr_hd st + wrap32 (f - I))) (tr_here X st)) (n - 1) st Rx [] Mx MD T) end.
    all: try kauto.
    all: try (rewrite Hf; apply mul_S_sub).
    all: try (rewrite arr_len_set; exact TL).
    all: try (destruct trips; [cbn in Hf; exfalso; lia | lia]).
    intros R' M'. intros. eapply K; try eassumption.
    * eapply mpost_trans; [exact HAG | assumption].
    * rewrite fill_more by first [lia | rewrite W1; exact Hnz]. subst I. rewrite W1 in *. assumption.
Qed.

Lemma op_val_range : forall st, t_work st = work1Ar -> 0 <= tr_w st < 65536 ->
  (it_match ty <= tr_w st -> tr_w st - it_match ty < NE ty) ->
  0 <= tr_op X st < 256 /\ 0 <= tr_val X st < 65536.
Proof using C zc ret sp pb p cf.
  intros st WK Fw Fwm. assert (MT : 0 <= it_match ty <= 257) by (clear; destruct ty; cbn; lia_std).
  unfold tr_op, tr_val, tr_ov. cbn [x_ty itm_ctx]. unfold tr_w in *. rewrite WK in Fw, Fwm. rewrite WK.
  destruct (Z.ltb_spec (arr_get work1Ar (t_sym st) + 1) (it_match ty)); [cbn [fst snd]; lia_std|].
  destruct (Z.leb_spec (it_match ty) (arr_get work1Ar (t_sym st))); cbn [fst snd]; [|lia_std].
  split; [rewrite wrap8_mod; apply Z.mod_pos_bound; lia_std | apply base_range; lia_std].
Qed.

Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

Lemma fill_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l ->
  zget_l Rb l kS10 = tr_op X st -> zget_l Rb l kS9 = tr_val X st ->
  spure st -> it_trip_ok X 288 320 1444 st = true ->
  mem_wr R_segs M p 7176 -> mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (t_tbl st)) ->
  (forall R' M', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS8 = tr_hb st ->
     mpost R_segs M M' (p + 1384) (p + 7160) 0 0 -> mem_wr R_segs M' p 7176 ->
     mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
     realizes R_segs (zcfg R_segs 97120 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97060 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS10 LS9 HU TOK Wp Htbl K.
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. open_spure HU. zkeys.
  trip_facts TOK.
  unbox Fwm. pose proof (op_val_range st WK Fw Fwm) as [Rop Rval].
  clear Fwm Flook Fcont LOWR DROPR Hprom HtyC HtyD Hlf Hcf Hwf HCr HTr.
  assert (Ehb : tr_hb st = t_len st - t_drop st) by reflexivity.
  assert (Hhb : 0 <= tr_hb st <= 15) by lia.
  assert (Hhd : 0 <= tr_hd st <= t_huff st).
  { unfold tr_hd. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (t_drop st) ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]. }
  pose proof (pow2_le15 (tr_hb st) Hhb) as PI. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PF.
  pose proof (pow2_le15 (t_curr st - tr_hb st) ltac:(lia)) as PQ.
  assert (EQ : 2 ^ t_curr st = 2 ^ tr_hb st * 2 ^ (t_curr st - tr_hb st)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  zrebase.
  zstep Rfd. zsetreg (tr_hb st) ltac:(rewrite Ehb; symmetry; apply swrap32_small; lia).
  zstep Rfd. zsetreg (- 2 ^ tr_hb st) ltac:(symmetry; apply sllw_m1; lia).
  zstep Rfd. zsetreg (tr_hd st) ltac:(unfold tr_hd; symmetry; apply srlw_small; lia).
  zstep Rfd. zsetreg (tr_hd st - 2 ^ tr_hb st) ltac:(lia).
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (fill_loop_s (Z.to_nat (2 ^ (t_curr st - tr_hb st))) (2 ^ t_curr st) (t_tbl st) (2 ^ t_curr st) st Rx [] M MD T) end.
  all: try kauto.
  - rewrite Z2Nat.id by lia. exact EQ.
  - lia.
  - rewrite Z2Nat.id by lia. apply Z.pow_le_mono_r; lia.
  - lia.
  - intros R' M'. intros. eapply K; try eassumption.
    unfold tr_tbl1. rewrite it_fill_eq. unfold tr_incr, tr_fill. rewrite !shl32_1 by lia. assumption.
Qed.

Lemma incr_loop_s : forall m c n st Rb l M MD T,
  0 <= c < 2 ^ Z.of_nat m -> Z.of_nat m < n -> c < 65536 ->
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> zget_l Rb l kS8 = tr_hb st ->
  zget_l Rb l kS6 = c -> 0 <= t_huff st < 65536 ->
  (forall R', cregsN R' [] -> sregs st R' [] -> zget_l R' [] kS8 = tr_hb st ->
     zget_l R' [] kS9 = loopZ n (incr_body (t_huff st)) c ->
     realizes R_segs (zcfg R_segs 97148 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 97128 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf nx.
  induction m as [|m IH]; intros c n st Rb l M MD T Hc Hn Hc2 Hh HC HS LS8 LS6 Hhuff K.
  -
    cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Hc. assert (E : c = 0) by lia. rewrite E in *. clear E Hc Hc2.
    pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf.
    zrebase. zstep Rfd. zstep Rfd. zsetreg 0 ltac:(rewrite Z.land_0_l; reflexivity).
    zstep Rfd. zsetreg 0 ltac:(reflexivity). zstep Rfd. zsetreg 0 ltac:(reflexivity).
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto. zregv. symmetry. apply incr_last; [lia | apply Z.land_0_r].
  - pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf.
    assert (HA : 0 <= Z.land c (t_huff st) <= c) by (split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).
    pose proof (shiftr1_half c m Hc) as HH.
    assert (HH2 : Z.shiftr c 1 <= c) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; apply Z.div_le_upper_bound; lia).
    zrebase.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zsetreg (Z.land c (t_huff st)) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zsetreg (Z.shiftr c 1) ltac:(transitivity (c / 2 ^ 1); [rewrite Z.shiftr_div_pow2 by lia; reflexivity | symmetry; apply srliw_small; lia]).
    destruct (Z.eq_dec (Z.land c (t_huff st)) 0) as [Z0|NZ].
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto. zregv. symmetry. apply incr_last; [lia | rewrite Z.land_comm; exact Z0].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (IH (Z.shiftr c 1) (n - 1) st Rx [] M MD T) end.
      all: try kauto. all: try lia.
      intros R' HC' HS' L8 L9. eapply K; try eassumption. rewrite incr_more; [exact L9 | lia | rewrite Z.land_comm; exact NZ].
Qed.

Ltac close_cmem := unfold cmem; split_conj; assumption.
Ltac close_smem := unfold smem; split_conj; assumption.
Ltac close_sregs1 EL := unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.

Definition Kst1 (pc : Z) (brk : bool) (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', cregsN R' [] -> sregs (tr_st1 X st) R' [] -> zget_l R' [] kS8 = tr_hb st ->
    mpost R_segs M M' (sp + -136) (sp + -104) 0 0 -> cmem M' -> smem (tr_st1 X st) M' ->
    tr_brk X st = brk ->
    realizes R_segs (zcfg R_segs pc (zupd R' []) M' MD) T.

Lemma count_s : forall st Rb l M MD T,
  m_halted MD = None -> cregsN Rb l -> sregs st Rb l -> zget_l Rb l kS8 = tr_hb st ->
  cmem M -> spure st -> it_trip_ok X 288 320 1444 st = true ->
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get (t_count st)) ->
  mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) ->
  Kst1 97248 false st M MD T -> Kst1 97440 true st M MD T ->
  realizes R_segs (zcfg R_segs 97120 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS8 HM HU TOK Hcnt Htbl KS KB.
  pose proof C as C'. open_itc C'. open_cregs HC. open_sregs HS. open_cmem HM. open_spure HU. zkeys. xaddr.
  trip_facts TOK. clear Fcont Fwm Hprom HtyC HtyD Hcf Hwf DROPR.
  pose proof work1_range as HWr.
  pose proof (mpost_stable R_segs M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL.
  zrebase.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ (t_len st - 1)) ltac:(symmetry; apply sllw_1; lia).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
    eapply (incr_loop_s (Z.to_nat (t_len st)) (2 ^ (t_len st - 1)) 32 st Rx [] M MD T) end.
  all: try kauto.
  { rewrite Z2Nat.id by lia. split; [lia|]. apply Z.pow_lt_mono_r; lia. }
  { lia. }
  { assert (2 ^ (t_len st - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
  clear HST HAG. clear_regs. intros R1 HC HS L8 L9.
  assert (EI : loopZ 32 (incr_body (t_huff st)) (2 ^ (t_len st - 1)) = tr_incr2 st).
  { unfold tr_incr2. rewrite it_incr_back_eq, shl32_1 by lia. reflexivity. }
  pose proof (incr_range (t_huff st) 32 (2 ^ (t_len st - 1)) ltac:(lia)) as IR.
  rewrite EI in L9, IR. clear EI.
  assert (I14 : 2 ^ (t_len st - 1) <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
  set (v1 := Z.land (tr_incr2 st - 1) (t_huff st) + tr_incr2 st).
  assert (HL : 0 <= Z.land (tr_incr2 st - 1) (t_huff st) <= t_huff st).
  { destruct (Z.eq_dec (tr_incr2 st) 0) as [E0|NE0].
    - rewrite E0. change (0 - 1) with (-1). rewrite Z.land_m1_l. lia.
    - split; [apply Z.land_nonneg; lia | apply land_le_r; lia]. }
  assert (EH : tr_huff st = Z.land (Z.b2z (tr_incr2 st =? 0) + -1) v1).
  { unfold tr_huff, v1. destruct (Z.eqb_spec (tr_incr2 st) 0) as [E0|NE0]; cbn [Z.b2z negb Z.add].
    - symmetry. apply Z.land_0_l.
    - rewrite Z.land_m1_l. rewrite Z.land_comm. reflexivity. }
  set (c0 := arr_get (t_count st) (t_len st)).
  pose proof (HCr (t_len st) ltac:(lia)) as HC0. fold c0 in HC0.
  assert (ESY : tr_sym st = t_sym st + 1) by (unfold tr_sym; apply wrap32_small; lia).
  pose proof mx15 as MXR.
  pose proof (mpost_stable R_segs M (sp + -136) (sp + -104) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -136) (sp + -104) 0 0) M) by (apply mpost_refl).
  open_cregs HC. open_sregs HS. zkeys. zrebase.
  zstep Rfd. zsetreg (Z.b2z (tr_incr2 st =? 0))
    ltac:(rewrite (Z.mod_small (tr_incr2 st)) by lia; destruct (Z.eqb_spec (tr_incr2 st) 0); destruct (Z.ltb_spec (tr_incr2 st) 1); cbn [Z.b2z]; lia).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 * t_len st) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd. zsetreg v1 ltac:(unfold v1; symmetry; apply swrap32_small; lia).
  zstep Rfd.
  tstep Rfd.
  fold c0. set (c0s := bv_swrap 16 c0) in *.
  pose proof (swrap16_cases c0 HC0) as HS16. fold c0s in HS16.
  assert (HSR : -32768 <= c0s <= c0) by (destruct HS16; lia). box HS16.
  zstep Rfd. zsetreg (-281474976710656) ltac:(reflexivity).
  zstep Rfd.
  zstep Rfd. zsetreg (tr_huff st) ltac:(exact EH).
  zstep Rfd.
  zstep Rfd. zsetreg ((c0s + -1) * 281474976710656) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 48) with 281474976710656; lia).
  zstep Rfd. zsetreg (tr_sym st) ltac:(unfold tr_sym; apply wrap32_small; lia).
  zstep Rfd.
  time tstore_arr Rfd Hcnt (t_len st).
  assert (Hcnt' : forall Mq, mem_arr 2 R_segs Mq (sp + -136) 16 (zfupd (arr_get (t_count st)) (t_len st) (c0s + -1)) ->
                             mem_arr 2 R_segs Mq (sp + -136) 16 (arr_get (tr_count st))).
  { intros Mq Hq. eapply mem_arr_ext_mod; [exact Hq|]. intros j Hj. unfold tr_count, zfupd, tr_c. fold c0.
    change (cell_mod 2) with 65536. rewrite arr_get_set. unfold arr_inb. rewrite CL.
    destruct (Z.eqb_spec j (t_len st)) as [Ej|NEj].
    - subst j. rewrite Z.eqb_refl. destruct (Z.leb_spec 0 (t_len st)); destruct (Z.ltb_spec (t_len st) 16); cbn [andb]; try lia.
      rewrite wrap16_mod. rewrite Z.mod_mod by lia. unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B; [f_equal; lia|].
      replace (c0 - 65536 + -1) with ((c0 - 1) + (-1) * 65536) by lia. rewrite Z_mod_plus_full. reflexivity.
    - destruct (Z.eqb_spec (t_len st) j); [lia|]. cbn [andb]. reflexivity. }
  apply Hcnt' in Hcnt. clear Hcnt'.
  assert (EC : tr_c st = (c0 - 1) mod 65536) by (unfold tr_c; fold c0; apply wrap16_mod).
  destruct (Z.eq_dec c0 1) as [C1|NC1].
  - assert (C1s : c0s = 1) by (unbox HS16; destruct HS16; lia).
    zbr Rfd false.
    assert (EC0 : tr_c st = 0) by (rewrite EC, C1; reflexivity).
    destruct (Z.eq_dec (t_len st) mx) as [LM|NLM].
    + zbr Rfd true.
      assert (EL : tr_len X st = t_len st).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [reflexivity | lia]. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KB Rx Mx) end.
      all: try kauto.
      * close_sregs1 EL.
      * close_cmem.
      * unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_eq. exact LM.
    + zbr Rfd false.
      unbox Flook. dand (Flook EC0 NLM) as (W1 & W2 & W3 & W4). rewrite WK in W2, W3, W4. rewrite lensA_get in W4. rewrite <- ESY in W1, W2, W3, W4.
      zstep Rfd. zstep Rfd. zsetreg (2 * tr_sym st) ltac:(symmetry; apply zext32_x2; lia).
      zstep Rfd.
      tstep Rfd.
      zstep Rfd. zsetreg (2 * arr_get work1Ar (tr_sym st)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep Rfd.
      tstep Rfd.
      assert (EL : tr_len X st = lf (lens_ofs + arr_get work1Ar (tr_sym st))).
      { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx]. rewrite EC0. destruct (Z.eqb_spec (t_len st) mx); [lia|].
        cbn [andb negb]. rewrite WK. apply lensA_get. }
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end.
      all: try kauto.
      * close_sregs1 EL.
      * close_cmem.
      * unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
      * unfold tr_brk. cbn [x_max itm_ctx]. rewrite EC0. cbn [Z.eqb andb]. apply Z.eqb_neq. exact NLM.
  - assert (HNZ : ((c0s + -1) * 281474976710656) mod 18446744073709551616 <> 0).
    { unbox HS16. destruct HS16 as [[A B]|[A B]]; rewrite B.
      - destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia].
      - rewrite negshift48_mod by lia. lia. }
    zbr Rfd true.
    assert (ECN : tr_c st <> 0).
    { rewrite EC. destruct (Z.eq_dec c0 0) as [E0|NE0]; [rewrite E0; cbv; discriminate | rewrite Z.mod_small by lia; lia]. }
    assert (EL : tr_len X st = t_len st).
    { unfold tr_len. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity]. }
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KS Rx Mx) end.
    all: try kauto.
    * close_sregs1 EL.
    * close_cmem.
    * unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    * unfold tr_brk. destruct (Z.eqb_spec (tr_c st) 0); [lia | reflexivity].
Qed.
End S7IT3.

End FXG.
Ltac open_pregs6 H := unfold pregs6 in H;
  let a := fresh "LSP" in let b := fresh "LGP" in let c := fresh "LTP" in
  let e := fresh "LA1" in let g := fresh "LA3" in let h := fresh "LA4" in
  let i := fresh "LA5" in dand H as (a & b & c & e & g & h & i).
Ltac close_pregs6 := unfold pregs6; split_conj; zreg.
Ltac open_cregs H :=
  unfold cregsN in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in let c := fresh "LA2" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  dand H as (hp & a & b & c & d & e & f & g & h & i); open_pregs6 hp.
Ltac open_sregs H :=
  unfold sregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let c := fresh "LA6" in let d := fresh "LT5" in
  let e := fresh "LS1" in let f := fresh "LS0" in let g := fresh "LT2" in let h := fresh "LS7" in
  dand H as (a & b & c & d & e & f & g & h).
Ltac open_cmem H :=
  unfold cmem in H;
  let a := fresh "Wf" in let b := fresh "Wp" in let c := fresh "Hlens" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "HslD" in let g := fresh "HslL" in let h := fresh "Hext" in let i := fresh "Hbase" in
  dand H as (a & b & c & d & e & f & g & h & i).
Ltac open_smem H :=
  unfold smem in H; let a := fresh "Hcnt" in let b := fresh "Htbl" in dand H as (a & b).
Ltac open_spure H :=
  unfold spure in H;
  let a := fresh "WK" in let b := fresh "LOWR" in let b2 := fresh "DROPR" in let c := fresh "NX0" in let d := fresh "NX1" in
  let e := fresh "HCr" in let f := fresh "HTr" in let g := fresh "CL" in let h := fresh "TL" in
  dand H as (a & b & b2 & c & d & e & f & g & h).
Ltac open_cregsB H :=
  unfold cregsB in H;
  let hp := fresh "HP" in let a := fresh "LA7" in let b := fresh "LT0" in
  let d := fresh "LT3" in let e := fresh "LT4" in let f := fresh "LS2" in let g := fresh "LS3" in
  let h := fresh "LS4" in let i := fresh "LS5" in
  dand H as (hp & a & b & d & e & f & g & h & i); open_pregs6 hp.
Ltac close_cregsB := unfold cregsB; split_conj; try close_pregs6; zreg.
Ltac close_cregs := unfold cregsN; split_conj; try close_pregs6; zreg.
Ltac close_sregs := unfold sregs; split_conj; zreg.
Ltac close_cmem := unfold cmem; split_conj; assumption.
Ltac close_smem := unfold smem; split_conj; assumption.
Ltac close_sregs1 EL := unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]; rewrite ?EL; split_conj; zreg.
Ltac kauto := first
  [ assumption
  | lazymatch goal with
    | |- cregsN _ _ _ _ _ _ _ _ _ _ _ _ => close_cregs
    | |- cregsB _ _ _ _ _ _ _ _ _ _ _ _ => close_cregsB
    | |- sregs _ (tr_st1 _ _) _ _ => fail
    | |- sregs _ _ _ _ => close_sregs
    | |- pregs6 _ _ _ _ _ _ _ _ => close_pregs6
    | |- pregs _ _ _ _ _ _ _ _ _ _ => close_pregs
    | |- zget_l _ _ _ = _ => zreg
    | |- zget _ _ = _ => zreg
    | |- m_halted _ = _ => assumption
    end ].
Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain.

Module PIc_mod.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.
Definition PIc (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (st : ItSt) : Prop :=
  ty = CODES -> exists j, 0 <= j < N (lensA lf) lens_ofs codes /\
    IS ty (lensA lf) lens_ofs codes (rootA lf lens_ofs codes bits) nx j st.

Section PI.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).
Hypothesis Hc : 0 <= codes <= 288.
Hypothesis Hl : forall s, 0 <= s < codes -> 0 <= arr_get (lensA lf) (lens_ofs + s) <= 15.
Hypothesis HtyC' : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get (lensA lf) (lens_ofs + s) <= 7.
Hypothesis Hb : 1 <= bits <= 15.
Hypothesis Hmx : 1 <= mxA lf lens_ofs codes.
Hypothesis Hrj : itm_reject ty (mxA lf lens_ofs codes) (it_left_check (cntA lf lens_ofs codes)) = false.

Lemma Hmx' : max (lensA lf) lens_ofs codes <> 0.
Proof. intro H. change (mxA lf lens_ofs codes = 0) in H. lia. Qed.

Lemma pic_complete : ty = CODES -> kraft (lensA lf) lens_ofs codes 15 = 2 ^ 15.
Proof.
  intros Ety. pose proof (left_eq (lensA lf) lens_ofs codes Hc Hl) as LE.
  change (it_left_check (cntA lf lens_ofs codes)) with (it_left_check (count (lensA lf) lens_ofs codes)) in Hrj.
  rewrite LE in Hrj. unfold itm_reject in Hrj.
  destruct (Z.ltb_spec (2 ^ 15) (kraft (lensA lf) lens_ofs codes 15)); [discriminate|].
  rewrite Ety in Hrj. cbn [codetype_eqb orb andb] in Hrj.
  destruct (Z.ltb_spec 0 (2 ^ 15 - kraft (lensA lf) lens_ofs codes 15)); [discriminate | lia].
Qed.

Lemma pic_init : it_not_enough ty (itm_used (rootA lf lens_ofs codes bits)) = false ->
  PIc ty lf lens_ofs codes nx bits
    (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros Hne Ety. pose proof (N_range (lensA lf) lens_ofs codes Hc Hl) as NR.
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  pose proof (CN (lensA lf) lens_ofs codes Hc Hl Hmx) as N1.
  exists 0. split; [lia|].
  assert (HU : itm_used (rootA lf lens_ofs codes bits) = 2 ^ rootA lf lens_ofs codes bits).
  { exact (used_eq (lensA lf) lens_ofs codes bits Hc Hl Hb Hmx'). }
  rewrite HU in Hne.
  exact (IS0' ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) Hc Hl Hb ltac:(rewrite workA_len; lia) Hmx' Hne).
Qed.

Lemma pic_step : forall st st', PIc ty lf lens_ofs codes nx bits st ->
  it_step (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)) st = ItCont st' ->
  PIc ty lf lens_ofs codes nx bits st'.
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros st st' HP Hs Ety. destruct (HP Ety) as (j & Hj & HIS).
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  change (it_step (itm_ctx ty (lensA lf) lens_ofs nx (itm_root bits (max (lensA lf) lens_ofs codes) (min (lensA lf) lens_ofs codes)) (max (lensA lf) lens_ofs codes)) st = ItCont st') in Hs.
  rewrite (ctx_eq ty (lensA lf) lens_ofs codes nx bits Hc Hl Hb Hmx') in Hs.
  pose proof (trip ty (lensA lf) lens_ofs codes Hc Hl Hmx (pic_complete Ety) (rootA lf lens_ofs codes bits)
                (Hroot (lensA lf) lens_ofs codes bits Hc Hl Hb Hmx') nx (fun _ => C19) j st Hj HIS) as TP.
  unfold trip_post in TP. match type of TP with context [it_step ?c st] => assert (Hs2 : it_step c st = ItCont st') by exact Hs; rewrite Hs2 in TP end. destruct TP as (HjN & _ & HIS' & _).
  exists (j + 1). split; [lia | exact HIS'].
Qed.

Lemma pic_w : forall st, PIc ty lf lens_ofs codes nx bits st -> ty = CODES ->
  arr_get (t_work st) (t_sym st) < 20.
Proof using Hc Hl HtyC' Hb Hmx Hrj.
  intros st HP Ety. destruct (HP Ety) as (j & Hj & HIS).
  pose proof (HtyC19 ty (lensA lf) lens_ofs codes bits HtyC' Ety) as C19.
  destruct HIS as (Hsym & _ & _ & _ & _ & Hw & _).
  rewrite Hsym, (Hw j Hj). pose proof (LWr (lensA lf) lens_ofs codes Hc j Hj). lia.
Qed.
End PI.
End FXG.
End PIc_mod.

End S_It3.

Module S_It4.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.
Import S_It0 S_It1 S_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Section S7IT4.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregsN ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation CRB := (cregsB ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs p).
#[local] Abbreviation CM := (cmem ty lf lens_ofs codes nx wf p sp).
#[local] Abbreviation SM := (smem p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

Definition uregs (st : ItSt) (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kT6 = tr_sym st /\ zget_l R l kT1 = tr_len X st /\
  zget_l R l kS1 = tr_huff st /\ zget_l R l kS0 = p + 1384 + 4 * t_next st /\ zget_l R l kA2 = 2 ^ t_curr st /\
  zget_l R l kS8 = tr_low X st.
Ltac open_uregs H :=
  unfold uregs in H;
  let a := fresh "LT6" in let b := fresh "LT1" in let d := fresh "LS1" in
  let e := fresh "LS0" in let f := fresh "LT2" in let g := fresh "LS8" in
  dand H as (a & b & d & e & f & g).
Ltac close_uregs := unfold uregs; split_conj; zreg.
Ltac kauto4 := first
  [ assumption
  | lazymatch goal with
    | |- uregs _ _ _ => close_uregs
    | |- _ => kauto
    end ].
Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma curr_loop_s : forall m curr lft n (cnt : arr) st Rb l M MD T,
  mx - (curr + rt) <= Z.of_nat m -> Z.of_nat m < n -> 1 <= mx ->
  1 <= curr -> curr + rt < mx -> 0 < lft <= 2 ^ curr ->
  (forall j, 0 <= j < 16 -> 0 <= arr_get cnt j < 65536) ->
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kT5 = t_used st -> zget_l Rb l kS9 = rt ->
  zget_l Rb l kS10 = curr + rt -> zget_l Rb l kA6 = lft -> zget_l Rb l kS7 = mx - rt ->
  mem_arr 2 R_segs M (sp + -136) 16 (arr_get cnt) ->
  (forall R', CR R' [] -> uregs st R' [] -> zget_l R' [] kT5 = t_used st -> zget_l R' [] kS9 = rt ->
     zget_l R' [] kS7 = fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     zget_l R' [] kA6 = 2 ^ fst (loopZ n (curr_body cnt rt mx) (curr, lft)) ->
     realizes R_segs (zcfg R_segs 97340 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 97292 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf.
  induction m as [|m IH]; intros curr lft n cnt st Rb l M MD T Hm Hn Hmx Hc1 Hcm Hl HCR Hh HC HUr LT5 LS9 LS10 LA6 LS7 Hcnt K.
  { exfalso. lia. }
  pose proof C as C'. open_itc C'. open_cregs HC. open_uregs HUr. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C ltac:(lia)) as (RT1 & RT2 & RT3).
  assert (P14 : 2 ^ curr <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P14.
  pose proof (HCR (curr + rt) ltac:(lia)) as HCc.
  zrebase.
  zstep Rfd. zstep Rfd. zsetreg (2 * (curr + rt)) ltac:(symmetry; apply zext32_x2; lia).
  zstep Rfd.
  tstep Rfd.
  zstep Rfd. zsetreg (lft - arr_get cnt (curr + rt)) ltac:(symmetry; apply swrap32_small; lia).
  destruct (Z_lt_le_dec 0 (lft - arr_get cnt (curr + rt))) as [GT|LE].
  - zbr Rfd false.
    zstep Rfd. zsetreg (curr + rt + 1) ltac:(symmetry; apply swrap32_small; lia).
    zstep Rfd. zsetreg (2 * (lft - arr_get cnt (curr + rt))) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
    destruct (Z_lt_le_dec (curr + rt + 1) mx) as [MORE|DONE].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
        eapply (IH (curr + 1) (2 * (lft - arr_get cnt (curr + rt))) (n - 1) cnt st Rx [] M MD T) end.
      all: try kauto4.
      all: try lia.
      * rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
      * intros R' HC' HU' L5 L9 L7 L6. eapply K; try eassumption.
        all: rewrite curr_more by lia; rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia;
             replace ((lft - arr_get cnt (curr + rt)) * 2) with (2 * (lft - arr_get cnt (curr + rt))) by lia; assumption.
    + zbr Rfd false.
      zstep Rfd.
      zstep Rfd. zsetreg (2 ^ (mx - rt)) ltac:(symmetry; apply sllw_1; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
      all: try kauto4.
      * zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. lia.
      * zregv. rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. f_equal. lia.
  - zbr Rfd true.
    zstep Rfd. zsetreg curr ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd. zsetreg (2 ^ curr) ltac:(symmetry; apply sllw_1; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
    all: try kauto4.
    * zregv. rewrite curr_stop_le by lia. reflexivity.
    * zregv. rewrite curr_stop_le by lia. reflexivity.
Qed.

Lemma ne_facts : (isL ty = 0 \/ isL ty = 1) /\ (isD ty = 0 \/ isD ty = 1) /\ isL ty + isD ty <= 1 /\
  (forall u, it_not_enough ty u = (if isL ty =? 1 then 852 <? u else if isD ty =? 1 then 592 <? u else false)).
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; repeat split; try lia_std; intros; reflexivity. Qed.
Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof using. destruct b; reflexivity. Qed.
Lemma land1_b2z : forall b, Z.land 1 (Z.b2z b) = Z.b2z b.
Proof using. destruct b; reflexivity. Qed.
Lemma lowS_small : forall z, 0 <= z < 4294967295 -> lowS z = z.
Proof using. intros z Hz. unfold lowS. destruct (Z.eqb_spec z 4294967295); [lia_std | reflexivity]. Qed.

Definition Kbody3 (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R' M', CR R' [] -> SR (tr_st3 X st) R' [] ->
     mpost R_segs M M' (p + 1384) (p + 7160) 0 0 -> CM M' -> SM (tr_st3 X st) M' ->
     tr_sub X st = true -> it_not_enough ty (tr_used X st) = false ->
     1 <= tr_curr X st <= 15 -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st ->
     realizes R_segs (zcfg R_segs 96984 (zupd R' []) M' MD) T.
Definition Kfail (st : ItSt) (M : mem) (MD : Model) (T : TSet) : Prop :=
  forall R', CR R' [] -> zget_l R' [] kA6 = 1 -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = true ->
     realizes R_segs (zcfg R_segs 97500 (zupd R' []) M MD) T.

Lemma link_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kS7 = tr_curr X st ->
  zget_l Rb l kT5 = tr_used X st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> it_not_enough ty (tr_used X st) = false -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3 st M MD T ->
  realizes R_segs (zcfg R_segs 97388 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LS7 LT5 HM HSM HP TOK Hbrk Hsub Hne Hmx HLOW HDR K3.
  pose proof C as C'. open_itc C'. open_cregs HC. open_uregs HU. open_cmem HM. open_smem HSM. open_spure HP. zkeys. xaddr.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  trip_facts TOK. clear Flook Fwm LOWR DROPR Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  assert (HST3 : it_step X st = ItCont (tr_st3 X st)).
  { rewrite it_step_eq. rewrite Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity. }
  unbox Fcont. dand (Fcont (tr_st3 X st) HST3) as (Flow3 & Fcurr3 & Fnext3).
  { right. cbn [t_next tr_st3]. unfold tr_next, tr_fill. rewrite shl32_1 by lia. pose proof (pow2_le15 (t_curr st) ltac:(lia)). lia. }
  cbn [t_low t_curr t_next tr_st3] in Flow3, Fcurr3, Fnext3. clear Fcont HST3.
  assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
  pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC. pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (Hroom3 : t_next st < 1444).
  { pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
    assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
    assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia. }
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (4 * 2 ^ t_curr st) ltac:(symmetry; apply zext32_x4; lia).
  zstep Rfd. zsetreg (p + 1384 + 4 * tr_next st) ltac:(rewrite ENX; lia).
  zstep Rfd. zsetreg (4 * tr_low X st) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep Rfd.
  zstep Rfd. zsetreg (4 * (tr_next st - nx)) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (tr_next st - nx) ltac:(rewrite srli_small by lia; change (2 ^ 2) with 4; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Ho : mem_u8 _ ?Mc _ (tr_curr X st), Hb : mem_u8 _ _ _ rt, Hv : mem_u16 _ _ _ (tr_next st - nx) |- _ =>
    pose proof (entry_write Mc (p + 1384) 1444 (arr_get (tr_tbl1 X st)) (nx + tr_low X st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Ho Hb Hv HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite it_fill_len_tr; lia].
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ tr_curr X st) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (tr_low X st) ltac:(rewrite swrap32_small by lia; lia).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K3 Rx Mx) end.
  all: try kauto4.
  all: lazymatch goal with
       | |- sregs _ _ _ _ => unfold sregs; cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st3]; rewrite HDR;
                             rewrite (lowS_small (tr_low X st)) by lia; split_conj; zreg
       | |- cmem _ _ _ _ _ _ _ _ _ => close_cmem
       | |- smem _ _ _ _ => unfold smem; cbn [t_count t_tbl tr_st3]; split; [exact Hcnt|]; unfold tr_tbl2; cbn [x_table x_root itm_ctx]; exact Htbl
       | |- _ => lia
       end.
Qed.

Lemma enough_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kT5 = t_used st ->
  zget_l Rb l kS7 = tr_curr X st -> zget_l Rb l kA6 = 2 ^ tr_curr X st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  0 <= tr_low X st < 32768 -> tr_drop X st = rt -> 1 <= tr_curr X st <= 15 ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 97340 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LT5 LS7 LA6 HM HSM HP TOK Hbrk Hsub Hmx HLOW HDR HCU K3 KF.
  pose proof C as C'. open_itc C'. open_cmem HM. open_spure HP. zkeys.
  trip_facts TOK. clear Flook Fwm Fcont Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3.
  assert (EU : tr_used X st = t_used st + 2 ^ tr_curr X st).
  { unfold tr_used. rewrite Z.shiftl_1_l. apply wrap32_small. lia. }
  pose proof ne_facts as (IL & ID & ILD & NE').
  assert (JD : forall RJ, CR RJ [] -> uregs st RJ [] -> zget_l RJ [] kS9 = rt -> zget_l RJ [] kT5 = tr_used X st ->
            zget_l RJ [] kS7 = tr_curr X st -> zget_l RJ [] kA6 = 1 -> (isL ty = 1 -> tr_used X st < 853) ->
            realizes R_segs (zcfg R_segs 97368 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ J9 J5 J7 J6 HL. open_cregs HCJ. open_uregs HUJ. zkeys. zrebase.
    zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 593)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
    zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
    zstep Rfd.
    destruct ID as [ID0|ID1].
    - zstep Rfd. zsetreg 0 ltac:(rewrite ID0; symmetry; apply Z.land_0_l).
      zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_s st Rx [] M MD T) end.
      all: try kauto4. all: try assumption. all: try lia.
      + unfold cmem; split_conj; assumption.
      + unfold spure; split_conj; assumption.
      + rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [apply Z.ltb_ge; lia|]. rewrite ID0. reflexivity.
    - zstep Rfd. zsetreg (Z.b2z (593 <=? tr_used X st)) ltac:(rewrite ID1; symmetry; apply land1_b2z).
      destruct (Z.leb_spec 593 (tr_used X st)) as [GE|LT].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
        all: try kauto4. rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [destruct IL; lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
      + zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (link_s st Rx [] M MD T) end.
        all: try kauto4. all: try assumption. all: try lia.
        * unfold cmem; split_conj; assumption.
        * unfold spure; split_conj; assumption.
        * rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [apply Z.ltb_ge; lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_ge. lia. }
  open_cregs HC. open_uregs HU. zkeys. zrebase.
  zstep Rfd. zsetreg (tr_used X st) ltac:(rewrite EU, swrap32_small by lia; lia).
  zstep Rfd. zsetreg (Z.b2z (tr_used X st <? 853)) ltac:(rewrite (Z.mod_small (tr_used X st)) by lia; reflexivity).
  zstep Rfd. zsetreg (Z.b2z (853 <=? tr_used X st)) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
  zstep Rfd.
  destruct IL as [IL0|IL1].
  - zstep Rfd. zsetreg 0 ltac:(rewrite IL0; symmetry; apply Z.land_0_l).
    zstep Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JD Rx) end.
    all: try kauto4. intros; lia.
  - zstep Rfd. zsetreg (Z.b2z (853 <=? tr_used X st)) ltac:(rewrite IL1; symmetry; apply land1_b2z).
    zstep Rfd.
    destruct (Z.leb_spec 853 (tr_used X st)) as [GE|LT].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KF Rx) end.
      all: try kauto4. rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (JD Rx) end.
      all: try kauto4. intros; lia.
Qed.

Ltac zbr_by bv tac :=
  let pc := zpc in Rfd pc ltac:(fun F E D => eapply (zu_branch_b bv); [exact F | exact E | exact D | zhalted | znorm; tac | ]; cbv iota; znorm).

Lemma tr_count_range : forall st, (forall j, 0 <= j < 16 -> 0 <= arr_get (t_count st) j < 65536) ->
  forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536.
Proof using.
  intros st H j Hj. unfold tr_count. rewrite arr_get_set. destruct (_ && _); [|apply H; exact Hj].
  pose proof (wrap16_range (arr_get (t_count st) (t_len st) - 1)) as W. change (2 ^ 16) with 65536 in W. unfold tr_c. lia_std.
Qed.

Lemma currsz_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> uregs st Rb l -> zget_l Rb l kS9 = rt -> zget_l Rb l kT5 = t_used st ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> tr_sub X st = true -> 1 <= mx ->
  1 <= tr_len X st <= 15 -> rt < tr_len X st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 97272 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HU LS9 LT5 HM HSM HP TOK Hbrk Hsub Hmx TLR RTL HLOW HDR K3 KF.
  pose proof C as C'. open_itc C'. open_smem HSM. open_spure HP. zkeys.
  cbn [t_count t_tbl tr_st1] in Hcnt, Htbl.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  pose proof (tr_count_range st HCr) as HCr1.
  set (c0 := tr_len X st - rt). assert (Ec0 : c0 = tr_len X st - rt) by reflexivity.
  pose proof (pow2_le15 c0 ltac:(lia)) as PC0.
  assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
  { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
    fold c0. rewrite Z.shiftl_1_l, swrap32_id by lia. reflexivity. }
  pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (CR1 & CR2 & CR3).
  rewrite <- ETC in CR1, CR2, CR3.
  open_cregs HC. open_uregs HU. zkeys. zrebase.
  zstep Rfd. zsetreg c0 ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zsetreg (2 ^ c0) ltac:(symmetry; apply sllw_1; lia).
  destruct (Z_lt_le_dec (tr_len X st) mx) as [LT|GE].
  - zbr Rfd false.
    zstep Rfd. zsetreg (mx - rt) ltac:(rewrite swrap32_small by lia; lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
      eapply (curr_loop_s 15%nat c0 (2 ^ c0) 16 (tr_count st) st Rx [] M MD T) end.
    all: try kauto4. all: try lia.
    intros R' HC' HU' L5 L9 L7 L6. rewrite <- ETC in L7, L6. specialize (CR2 ltac:(lia)).
    eapply enough_s; try eassumption; try lia.
    + unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
  - zbr Rfd true.
    assert (ETC0 : tr_curr X st = c0) by (apply CR3; lia).
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (enough_s st Rx [] M MD T) end.
    all: try kauto4. all: try (rewrite ETC0; zreg). all: try lia.
    + unfold smem. cbn [t_count t_tbl tr_st1]. split; assumption.
    + unfold spure. split_conj; assumption.
Qed.

Lemma sub_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR (tr_st1 X st) Rb l ->
  CM M -> SM (tr_st1 X st) M -> SP st -> it_trip_ok X 288 320 1444 st = true ->
  tr_brk X st = false -> 1 <= mx ->
  (forall R', CR R' [] -> SR (tr_st1 X st) R' [] -> tr_sub X st = false ->
     realizes R_segs (zcfg R_segs 96984 (zupd R' []) M MD) T) ->
  Kbody3 st M MD T -> Kfail st M MD T ->
  realizes R_segs (zcfg R_segs 97248 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HSM HP TOK Hbrk Hmx K1 K3 KF.
  pose proof C as C'. open_itc C'. open_spure HP. zkeys.
  clear Hprom HtyC HtyD Hcf Hwf Hlens15.
  pose proof (mx15 lf lens_ofs codes) as MXR. pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  trip_facts TOK. clear Fwm Fcont.
  pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  assert (TLR : 1 <= tr_len X st <= 15).
  { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx].
    destruct (Z.eqb_spec (tr_c st) 0) as [E0|NE0]; [|cbn [andb]; lia].
    destruct (Z.eqb_spec (t_len st) mx) as [EM|NEM]; cbn [andb negb]; [lia|].
    unbox Flook. dand (Flook E0 NEM) as (W1 & W2 & W3 & W4).
    replace (tr_sym st) with (t_sym st + 1) by (unfold tr_sym; symmetry; apply wrap32_small; lia). exact W4. }
  clear Flook.
  assert (HHF : 0 <= tr_huff st).
  { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
    pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
    rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
    destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
    assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
  assert (HLOW : 0 <= tr_low X st < 32768).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia.
    split; [apply Z.land_nonneg; lia|]. eapply Z.le_lt_trans; [apply land_le_r; lia | lia]. }
  assert (ELOW : Z.land (tr_huff st) (2 ^ rt - 1) = tr_low X st).
  { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia. reflexivity. }
  assert (HDR : tr_drop X st = rt).
  { unfold tr_drop. cbn [x_root itm_ctx]. unbox DROPR. destruct DROPR as [D0|D1]; rewrite D0 || rewrite D1; [reflexivity|].
    destruct (Z.eqb_spec rt 0); lia. }
  assert (J68 : forall RJ, CR RJ [] -> uregs st RJ [] -> zget_l RJ [] kA6 = t_drop st -> zget_l RJ [] kT5 = t_used st ->
            tr_sub X st = true -> realizes R_segs (zcfg R_segs 97260 (zupd RJ []) M MD) T).
  { intros RJ HCJ HUJ JA6 JT5 Hsub.
    assert (RTL : rt < tr_len X st).
    { unfold tr_sub in Hsub. apply andb_prop in Hsub as [H1 _]. cbn [x_root itm_ctx] in H1. apply Z.ltb_lt in H1. exact H1. }
    open_cregs HCJ. open_uregs HUJ. zkeys. zrebase.
    zstep Rfd.
    unbox DROPR. destruct DROPR as [D0|D1].
    - zbr Rfd true.
      eapply currsz_s; try eassumption; try lia. all: try kauto4.
      + unfold spure; split_conj; try assumption. unfold ZSEP. lia.
    - zbr Rfd false.
      zstep Rfd.
      eapply currsz_s; try eassumption; try lia. all: try kauto4.
      + unfold spure; split_conj; try assumption. unfold ZSEP. lia. }
  open_cregs HC. open_sregs HS. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1] in LT6, LT1, LA6, LT5, LS1, LS0, LT2, LS7.
  zkeys. zrebase.
  destruct (Z_lt_le_dec rt (tr_len X st)) as [SUB1|NOSUB1].
  - zbr Rfd false.
    zstep Rfd. zsetreg (tr_low X st) ltac:(exact (eq_sym ELOW)).
    unbox LOWR. destruct LOWR as [LM|LSM].
    +
      unfold lowS in LS7. rewrite LM in LS7. cbn in LS7.
      zbr_by false ltac:(cbv beta iota delta [zcond]; rewrite (mod_small_u64 (tr_low X st)) by lia;
                         try change ((-1) mod 18446744073709551616) with 18446744073709551615; apply Z.eqb_neq; lia).
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J68 Rx) end.
      all: try kauto4.
      unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, LM.
      replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (Z.eqb_spec (tr_low X st) 4294967295); [lia | reflexivity].
    + rewrite (lowS_small (t_low st)) in LS7 by lia.
      destruct (Z.eq_dec (tr_low X st) (t_low st)) as [EQL|NEL].
      * zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
        all: try kauto4.
        -- unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. rewrite (lowS_small (t_low st)) by lia. split_conj; zreg.
        -- unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, EQL, Z.eqb_refl. cbn [negb]. apply Bool.andb_false_r.
      * zbr Rfd false.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J68 Rx) end.
        all: try kauto4.
        unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW.
        replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.eqb_spec (tr_low X st) (t_low st)); [lia | reflexivity].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K1 Rx) end.
    all: try kauto4.
    + unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low tr_st1]. split_conj; zreg.
    + unfold tr_sub. cbn [x_root itm_ctx]. replace (rt <? tr_len X st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End S7IT4.
End FXG.
End S_It4.

Module S_It5.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.
Import S_It0 S_It1 S_It3 S_It4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Section S7IT5.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregsN ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation CRB := (cregsB ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs p).
#[local] Abbreviation CM := (cmem ty lf lens_ofs codes nx wf p sp).
#[local] Abbreviation SM := (smem p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).

Definition rsL : list (Z * Z) := [(sp + -136, 32); (p + 1384, 5776)].

Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Lemma cmem_mpost : forall M M' lo hi,
  CM M -> mpost R_segs M M' lo hi 0 0 ->
  ((lo = p + 1384 /\ hi = p + 7160) \/ (lo = sp + -136 /\ hi = sp + -104)) -> CM M'.
Proof using C zc ret pb cf bits.
  intros M M' lo hi HM [HA HW] Hr. pose proof C as C'. open_itc C'. xaddr. unfold ZSEP in *. open_cmem HM.
  unfold cmem. split_conj.
  - apply HW. exact Wf.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact HslD | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact HslL | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hext | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hbase | lia_std | lia_std].
Qed.

Lemma cnt_mpost : forall M M' f, mem_arr 2 R_segs M (sp + -136) 16 f -> mpost R_segs M M' (p + 1384) (p + 7160) 0 0 ->
  mem_arr 2 R_segs M' (sp + -136) 16 f.
Proof using C zc ret pb wf cf bits nx codes lens_ofs lf ty.
  intros M M' f H [HA HW]. pose proof C as C'. open_itc C'.
  eapply mem_arr_magree; [exact HA | exact H | lia_std | lia_std].
Qed.

Lemma mpostL_of_tbl : forall M M', mpost R_segs M M' (p + 1384) (p + 7160) 0 0 -> mpostL R_segs M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 R_segs M M M' rsL _ _ _ _ (mpostL_refl R_segs M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. right. left. lia.
Qed.
Lemma mpostL_of_cnt : forall M M', mpost R_segs M M' (sp + -136) (sp + -104) 0 0 -> mpostL R_segs M M' rsL.
Proof using.
  intros M M' HP. pose proof (framed_mpostL_trans2 R_segs M M M' rsL _ _ _ _ (mpostL_refl R_segs M rsL) HP) as H.
  apply H; [left | right; lia]. cbn. left. lia.
Qed.

Lemma spure_st1 : forall st, SP st -> SP (tr_st1 X st).
Proof using.
  intros st HP. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st1]. split_conj; try assumption.
  - apply tr_count_range0. exact HCr.
  - apply tr_tbl1_range. exact HTr.
  - unfold tr_count. rewrite arr_len_set. exact CL.
  - rewrite it_fill_len_tr. exact TL.
Qed.
Lemma spure_st3 : forall st, SP st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st -> SP (tr_st3 X st).
Proof using.
  intros st HP HL HD HN. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st3]. split_conj; try assumption.
  - unfold ZSEP. right. exact HL.
  - unfold ZSEP. right. exact HD.
  - lia_std.
  - lia_std.
  - apply tr_count_range0. exact HCr.
  - apply tr_tbl2_range. exact HTr.
  - unfold tr_count. rewrite arr_len_set. exact CL.
  - unfold tr_tbl2. rewrite arr_len_set. rewrite it_fill_len_tr. exact TL.
Qed.

Lemma trip_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> CM M -> SM st M -> SP st ->
  it_trip_ok X 288 320 1444 st = true -> 1 <= mx ->
  (ty = CODES -> tr_w st < it_match ty) ->
  (forall st' R' M', it_step X st = ItCont st' -> CR R' [] -> SR st' R' [] ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      realizes R_segs (zcfg R_segs 96984 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItBreak st' -> CR R' [] -> SR st' R' [] -> zget_l R' [] kS8 = t_len st' - t_drop st' ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> SP st' ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes R_segs (zcfg R_segs 97440 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_step X st = ItFail st' -> CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL R_segs M M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes R_segs (zcfg R_segs 97500 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96984 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS HM HSM HP TOK Hmx HcB KC KB KF.
  pose proof HP as HP'. open_spure HP'. open_smem HSM.
  pose proof TOK as TOK'. trip_facts TOK'. unbox Fwm.
  eapply here_s; try eassumption; try lia.
  intros R1 HC1 HS1 L10 L9.
  eapply fill_s; try eassumption.
  { open_cmem HM. assumption. }
  intros R2 M2 HC2 HS2 L8 HPO1 Wp2 Htbl2.
  pose proof (cmem_mpost M M2 _ _ HM HPO1 ltac:(left; split; reflexivity)) as HM2.
  pose proof (cnt_mpost M M2 _ Hcnt HPO1) as Hcnt2.
  eapply count_s; try eassumption.
  -
    intros R3 M3 HC3 HS3 L8' HPO2 HM3 HSM3 Hbrk.
    eapply sub_s; try eassumption.
    +
      intros R4 HC4 HS4 Hsub. eapply (KC (tr_st1 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * apply spure_st1. exact HP.
    +
      intros R4 M4 HC4 HS4 HPO3 HM4 HSM4 Hsub Hne HCU HLOW HDR HNX. eapply (KC (tr_st3 X st) R4 M4); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 |].
        eapply mpostL_trans; [apply mpostL_of_cnt; exact HPO2 | apply mpostL_of_tbl; exact HPO3].
      * apply spure_st3; assumption.
    +
      intros R4 HC4 LA6 Hsub Hne. eapply (KF (tr_st2 X st) R4 M3); try assumption.
      * rewrite it_step_eq, Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite Hne. reflexivity.
      * eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2].
      * cbn [t_tbl tr_st2]. apply tr_tbl1_range. exact HTr.
  -
    intros R3 M3 HC3 HS3 L8' HPO2 HM3 HSM3 Hbrk.
    assert (EL : tr_len X st = t_len st).
    { unfold tr_brk in Hbrk. apply andb_prop in Hbrk as [B1 B2]. unfold tr_len. rewrite B1.
      cbn [x_max itm_ctx] in *. rewrite B2. reflexivity. }
    assert (HHF : 0 <= tr_huff st).
    { unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
      pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
      rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
      destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
      assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1)) by (apply Z.land_nonneg; lia). lia. }
    eapply (KB (tr_st1 X st) R3 M3); try assumption.
    all: try (rewrite it_step_eq, Hbrk; reflexivity).
    all: try (cbn [t_len t_drop tr_st1]; rewrite EL; first [exact L8' | lia]).
    all: try (eapply mpostL_trans; [apply mpostL_of_tbl; exact HPO1 | apply mpostL_of_cnt; exact HPO2]).
    all: try (apply spure_st1; exact HP).
    all: cbn [t_used t_huff tr_st1]; first [exact HHF | lia].
Qed.

Lemma main_loop_s : forall (PI : ItSt -> Prop),
  (forall st, PI st -> ty = CODES -> tr_w st < it_match ty) ->
  (forall st st', PI st -> it_step X st = ItCont st' -> PI st') ->
  forall k st Rb l M0 M MD T,
  it_loop_ok k X 288 320 1444 st = true -> 1 <= mx -> PI st ->
  m_halted MD = None -> CR Rb l -> SR st Rb l -> CM M -> SM st M -> SP st ->
  mpostL R_segs M0 M rsL ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inl st' ->
      CR R' [] -> SR st' R' [] -> zget_l R' [] kS8 = t_len st' - t_drop st' ->
      mpostL R_segs M0 M' rsL -> CM M' -> SM st' M' -> SP st' ->
      (t_huff st' <> 0 -> 0 <= t_next st' + t_huff st' < 1444) ->
      0 <= t_len st' - t_drop st' <= 15 -> 0 <= t_used st' < 65536 -> 0 <= t_huff st' ->
      realizes R_segs (zcfg R_segs 97440 (zupd R' []) M' MD) T) ->
  (forall st' R' M', it_loop_n X (Z.of_nat k) st = inr st' ->
      CR R' [] -> zget_l R' [] kA6 = 1 ->
      mpostL R_segs M0 M' rsL -> CM M' -> SM st' M' -> t_work st' = work1Ar ->
      (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st') j < 4294967296) ->
      realizes R_segs (zcfg R_segs 97500 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96984 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros PI HI1 HI2. induction k as [|k IH]; intros st Rb l M0 M MD T HOK Hmx PIs Hh HC HS HM HSM HP HPL KB KF.
  { cbn [it_loop_ok] in HOK. discriminate. }
  rewrite it_loop_ok_S in HOK. apply andb_prop in HOK as [TOK REST].
  eapply trip_s; try eassumption.
  - exact (HI1 _ PIs).
  - intros st' R' M' Hstep HC' HS' HPO HM' HSM' HP'. rewrite Hstep in REST.
    eapply (IH st' R' [] M0 M' MD T); try eassumption.
    + eapply HI2; eassumption.
    + eapply mpostL_trans; eassumption.
    + intros st'' R'' M'' Hl. eapply KB. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
    + intros st'' R'' M'' Hl. eapply KF. rewrite it_loop_n_step by lia. rewrite Hstep.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. exact Hl.
  - intros st' R' M' Hstep HC' HS' L8 HPO HM' HSM' HP' B1 B2 B3. rewrite Hstep in REST.
    eapply KB; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
    + intros Hne. destruct (Z.eqb_spec (t_huff st') 0); [lia_std|]. cbn [negb] in REST.
      apply andb_prop in REST as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia_std.
  - intros st' R' M' Hstep HC' LA6 HPO HM' HSM' HW HTR. eapply KF; try eassumption.
    + rewrite it_loop_n_step by lia. rewrite Hstep. reflexivity.
    + eapply mpostL_trans; eassumption.
Qed.
End S7IT5.
End FXG.
End S_It5.

Module S_It6.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.
Import S_It0 S_It1 S_It3.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Section S7IT6.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation PR6 := (pregs6 lens_ofs p pb sp vgp vtp).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation CR := (cregsN ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation CRB := (cregsB ty lf lens_ofs codes bits p pb sp vgp vtp).
#[local] Abbreviation SR := (sregs p).
#[local] Abbreviation CM := (cmem ty lf lens_ofs codes nx wf p sp).
#[local] Abbreviation SM := (smem p sp).
#[local] Abbreviation SP := (spure lf lens_ofs codes nx bits wf).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).

Ltac xaddr := pose proof (xaddr_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C) as (XS1 & XS2 & XA1 & XA2 & XB1 & XB2 & XN).

Definition pregs3 (R : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l R l kSP = sp + -192 /\ zget_l R l kGP = vgp /\ zget_l R l kTP = vtp.
Ltac close_pregs3 := unfold pregs3; split_conj; zreg.

Lemma ne_pow : forall k, 1 <= k <= 15 ->
  it_not_enough ty (itm_used k) = match ty with CODES => false | _ => negb (k <=? 9) end.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf.
  intros k Hk. rewrite itm_used_pow2 by lia_std. unfold it_not_enough, ENOUGH_LENS, ENOUGH_DISTS.
  assert (E : forall b : bool, (if b then true else false) = b) by (destruct b; reflexivity).
  destruct ty; [reflexivity| |].
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 9) with 512 in *. lia_std.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 10) with 1024 in *. lia_std.
  - destruct (Z.leb_spec k 9); cbn [negb].
    + apply Z.ltb_ge. assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 9) with 512 in *. lia_std.
    + apply Z.ltb_lt. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia_std). change (2 ^ 10) with 1024 in *. lia_std.
Qed.

Lemma init_s : forall Rb l M MD T,
  m_halted MD = None -> PR6 Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt ->
  zget_l Rb l kA0 = it_match ty -> zget_l Rb l kT3 = EXAn ty p -> zget_l Rb l kT2 = BSAn ty p ->
  1 <= mx -> CM M -> SM st0 M ->
  (forall R', CR R' [] -> SR st0 R' [] -> realizes R_segs (zcfg R_segs 96984 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 96932 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 LA2 LT3 LT4 Hmx HM HSM K.
  pose proof C as C'. open_itc C'. open_pregs6 HP. open_cmem HM. zkeys. clear Hprom HtyC HtyD Hpb.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3). pose proof (pow2_le15 rt ltac:(lia)) as PRT.
  zrebase.
  zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (2 ^ rt - 1) ltac:(rewrite swrap32_small by lia; lia).
  zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd. zsetreg (2 ^ rt) ltac:(symmetry; apply sllw_1; lia).
  zstep Rfd. zsetreg (-1) ltac:(reflexivity).
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  - close_cregs.
  - unfold sregs. cbn [t_sym t_len t_drop t_used t_huff t_next t_curr t_low itm_st0]. rewrite itm_used_pow2 by lia.
    unfold lowS. cbn [Z.eqb Pos.eqb]. split_conj; zreg.
Qed.

Ltac kfix := unfold EXAn, BSAn, EXA, BSA; match goal with H : ty = _ |- _ => rewrite H end; cbv iota; kauto.
Lemma ty_cases :
  (ty = CODES /\ cty ty = 0 /\ it_match ty = 20 /\ EXA ty p = p + 808 /\ BSA ty p = p + 808 /\ NE ty = 288 /\ isL ty = 0 /\ isD ty = 0)
  \/ (ty = LENS /\ cty ty = 1 /\ it_match ty = 257 /\ EXA ty p = 67232 /\ BSA ty p = 67170 /\ NE ty = 31 /\ isL ty = 1 /\ isD ty = 0)
  \/ (ty = DISTS /\ cty ty = 2 /\ it_match ty = 0 /\ EXA ty p = 67358 /\ BSA ty p = 67294 /\ NE ty = 32 /\ isL ty = 0 /\ isD ty = 1).
Proof using C zc ret sp pb wf cf bits nx codes lens_ofs lf. destruct ty; [left | right; left | right; right]; repeat split; reflexivity. Qed.

Lemma spure_st0 : 1 <= mx -> SP st0.
Proof using C zc ret sp pb p ty.
  intros Hmx. pose proof C as C'. open_itc C'. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl itm_st0]. split_conj.
  - reflexivity.
  - unfold ZSEP. left. reflexivity.
  - unfold ZSEP. left. reflexivity.
  - lia_std.
  - lia_std.
  - intros j Hj. pose proof (cA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C j). lia_std.
  - intros j Hj. rewrite tblA_get. apply Hcf. exact Hj.
  - rewrite cntA_eq. apply cntK_len.
  - unfold tblA. apply arr_len_init.
Qed.

Lemma switch_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> zget_l Rb l kT0 = mx -> zget_l Rb l kT1 = mn -> zget_l Rb l kA7 = rt -> 1 <= mx ->
  mem_wr R_segs M (sp - 192) 192 -> mem_wr R_segs M p 7176 ->
  mem_arr 2 R_segs M (p + 168) 320 lf -> mem_arr 2 R_segs M (p + 808) 288 (arr_get work1Ar) ->
  mem_arr 2 R_segs M (sp + -136) 16 cA -> mem_arr 4 R_segs M (p + 1384) 1444 cf ->
  mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) ->
  mem_arr 2 R_segs M 67170 31 (arr_get lbase_a) -> mem_arr 2 R_segs M 67232 31 (arr_get lext_a) ->
  mem_arr 2 R_segs M 67294 32 (arr_get dbase_a) -> mem_arr 2 R_segs M 67358 32 (arr_get dext_a) ->
  (forall R' M', CR R' [] -> SR st0 R' [] -> mpost R_segs M M' (sp + -184) (sp + -168) 0 0 ->
     CM M' -> SM st0 M' -> SP st0 -> it_not_enough ty (itm_used rt) = false ->
     realizes R_segs (zcfg R_segs 96984 (zupd R' []) M' MD) T) ->
  (forall R' M', PR6 R' [] -> zget_l R' [] kA6 = 1 -> mpost R_segs M M' (sp + -184) (sp + -168) 0 0 ->
     it_not_enough ty (itm_used rt) = true ->
     realizes R_segs (zcfg R_segs 97500 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 96776 (zupd Rb l) M MD) T.
Proof using C zc ret.
  intros Rb l M MD T Hh HP LT0 LT1 LA7 Hmx Wf Wp Hlens Hwork Hcnt Htbl Hnext Hlb Hle Hdb Hde KBODY KFAIL.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. xaddr. clear HtyC HtyD.
  pose proof (rt_facts _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx) as (RT1 & RT2 & RT3).
  pose proof (spure_st0 Hmx) as HSP.
  assert (HSM : forall Mq, mem_arr 2 R_segs Mq (sp + -136) 16 cA -> mem_arr 4 R_segs Mq (p + 1384) 1444 cf -> SM st0 Mq).
  { intros Mq A B. unfold smem. cbn [t_count t_tbl itm_st0]. split; [exact A|].
    eapply mem_arr_ext; [exact B|]. intros j _. symmetry. apply tblA_get. }
  pose proof (ne_pow rt ltac:(lia)) as NE.
  pose proof (mpost_stable R_segs M (sp + -184) (sp + -168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (sp + -184) (sp + -168) 0 0) M) by (apply mpost_refl).
  zrebase.
  destruct ty_cases as [(Ety & E0 & EM & EX & EB & EN & EL & ED) | [(Ety & E0 & EM & EX & EB & EN & EL & ED) | (Ety & E0 & EM & EX & EB & EN & EL & ED)]];
    rewrite E0 in LA0.
  -
    zstep Rfd. zbr Rfd false. zstep Rfd. zbr Rfd false. zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    eapply init_s; try eassumption; try lia.
    all: try kfix.
    all: try kauto.
    all: lazymatch goal with
         | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
         | |- smem _ _ _ _ => apply HSM; assumption
         | |- _ => idtac
         end.
    intros R' HC' HS'. eapply KBODY; try assumption.
    + unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
    + apply HSM; assumption.
    + rewrite NE, Ety. reflexivity.
  -
    zstep Rfd. zbr Rfd false. zstep Rfd. zbr Rfd true. zstep Rfd.
    destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KFAIL Rx M) end.
      all: try kauto. all: try exact HAG.
      rewrite NE, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
    + zbr Rfd false.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      eapply init_s; try eassumption; try lia.
      all: try kfix.
      all: try kauto.
      all: lazymatch goal with
           | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
           | |- smem _ _ _ _ => apply HSM; assumption
           | |- _ => idtac
           end.
      intros R' HC' HS'. eapply KBODY; try assumption.
      * unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
      * apply HSM; assumption.
      * rewrite NE, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
  -
    zstep Rfd. zbr Rfd true. zstep Rfd. zstep Rfd.
    destruct (Z_lt_le_dec 9 rt) as [BIG|OK].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KFAIL Rx Mx) end.
      all: try kauto. all: try exact HAG.
      rewrite NE, Ety. destruct (Z.leb_spec rt 9); [lia | reflexivity].
    + zbr Rfd false.
      zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
      eapply init_s; try eassumption; try lia.
      all: try kfix.
      all: try kauto.
      all: lazymatch goal with
           | |- cmem _ _ _ _ _ _ _ _ _ => unfold cmem; rewrite EX, EB, EN, EL, ED, Ety; split_conj; assumption
           | |- smem _ _ _ _ => apply HSM; assumption
           | |- _ => idtac
           end.
      intros R' HC' HS'. eapply KBODY; try assumption.
      * unfold cmem. rewrite EX, EB, EN, EL, ED, Ety. split_conj; assumption.
      * apply HSM; assumption.
      * rewrite NE, Ety. destruct (Z.leb_spec rt 9); [reflexivity | lia].
Qed.

Lemma entry_write2 : forall M base n f i lo a0 a2,
  mem_arr 4 R_segs M base i f ->
  mem_arr 4 R_segs M (base + 4 * (i + 1)) (n - (i + 1)) (fun j => f (i + 1 + j)) ->
  mem_u16 R_segs M a0 lo -> mem_u16 R_segs M a2 0 ->
  a0 = base + 4 * i -> a2 = a0 + 2 -> 0 <= i < n -> base + 4 * n <= two64 -> 0 <= base -> 0 <= lo < 65536 ->
  mem_arr 4 R_segs M base n (zfupd f i lo).
Proof using.
  intros M base n f i lo a0 a2 H1 H2 Hlo Hhi -> -> Hi Hn Hb Rlo.
  eapply mem_arr4_fill; [exact H1 | | exact H2 | lia | lia].
  change 4%nat with (2 + 2)%nat. rewrite Z_to_le_bytes_add. unfold mem_u16 in *.
  apply mem_is_app; [exact Hlo | | rewrite two64_eq in *; lia | rewrite !length_Z_to_le_bytes; cbn; rewrite two64_eq in *; lia].
  rewrite length_Z_to_le_bytes. change (Z.of_nat 2) with 2.
  replace (Z.shiftr lo (8 * 2)) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia). exact Hhi.
Qed.

Definition slots (M : mem) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : Z) : Prop :=
  mem_u64 R_segs M (sp + -8) v1 /\ mem_u64 R_segs M (sp + -16) v8 /\ mem_u64 R_segs M (sp + -24) v9 /\
  mem_u64 R_segs M (sp + -32) v18 /\ mem_u64 R_segs M (sp + -40) v19 /\ mem_u64 R_segs M (sp + -48) v20 /\
  mem_u64 R_segs M (sp + -56) v21 /\ mem_u64 R_segs M (sp + -64) v22 /\ mem_u64 R_segs M (sp + -72) v23 /\
  mem_u64 R_segs M (sp + -80) v24 /\ mem_u64 R_segs M (sp + -88) v25 /\ mem_u64 R_segs M (sp + -96) v26 /\
  mem_u64 R_segs M (sp + -104) v27.

Lemma epilogue_s : forall Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  m_halted MD = None -> zget_l Rb l kSP = sp + -192 -> zget_l Rb l kA6 = v ->
  slots M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> Z.land v1 (-2) = v1 -> 0 <= v1 < two64 ->
  (forall R', zget_l R' [] kA0 = v -> zget_l R' [] kSP = sp -> zget_l R' [] kRA = v1 ->
     zget_l R' [] kS0 = v8 -> zget_l R' [] kS1 = v9 -> zget_l R' [] kS2 = v18 -> zget_l R' [] kS3 = v19 ->
     zget_l R' [] kS4 = v20 -> zget_l R' [] kS5 = v21 -> zget_l R' [] kS6 = v22 -> zget_l R' [] kS7 = v23 ->
     zget_l R' [] kS8 = v24 -> zget_l R' [] kS9 = v25 -> zget_l R' [] kS10 = v26 -> zget_l R' [] kS11 = v27 ->
     zget_l R' [] kGP = zget_l Rb l kGP -> zget_l R' [] kTP = zget_l Rb l kTP ->
     realizes R_segs (zcfg R_segs v1 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs 97500 (zupd Rb l) M MD) T.
Proof using C zc ret pb p wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T v v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hh LSP LA6 HSL Hev Hv1 K.
  remember (zget_l Rb l kGP) as vgp' eqn:EG. remember (zget_l Rb l kTP) as vtp' eqn:ET. symmetry in EG, ET.
  pose proof C as C'. open_itc C'. zkeys. clear Hprom HtyC HtyD Hpb Hlf Hcf Hwf Hlens15.
  unfold slots in HSL. dand HSL as (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
  zrebase.
  zstep Rfd.
  do 13 (zstep Rfd).
  zstep Rfd.
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end.
  all: zreg.
Qed.

Lemma setbits_s : forall Rb l M MD T rv,
  m_halted MD = None -> pregs3 Rb l -> zget_l Rb l kA4 = pb -> zget_l Rb l kA7 = rv -> mem_wr R_segs M p 7176 ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpost R_segs M M' pb (pb + 4) 0 0 -> mem_u32 R_segs M' pb rv ->
     realizes R_segs (zcfg R_segs 97500 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97492 (zupd Rb l) M MD) T.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros Rb l M MD T rv Hh HP LA4 LA7 Wp K.
  pose proof C as C'. open_itc C'. unfold pregs3 in HP. dand HP as (LSP & LGP & LTP). zkeys. clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15. unfold ZSEP in Hpb.
  pose proof (mpost_stable R_segs M pb (pb + 4) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X pb (pb + 4) 0 0) M) by (apply mpost_refl).
  zrebase.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx) end.
  all: try kauto. all: try close_pregs3. all: exact HAG.
Qed.

Lemma it_room_ge : 128 <= it_room ty.
Proof using C zc ret sp pb p wf cf bits nx codes lens_ofs lf. destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia_std. Qed.

Definition rsT : list (Z * Z) := [(p + 1384, 5776); (p + 160, 8); (pb, 4)].

Lemma break_tail_s : forall st Rb l M MD T,
  m_halted MD = None -> CR Rb l -> SR st Rb l -> zget_l Rb l kS8 = t_len st - t_drop st ->
  CM M -> SM st M -> SP st ->
  0 <= t_len st - t_drop st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_huff st ->
  (t_huff st <> 0 -> 0 <= t_next st + t_huff st < 1444) ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1384) 1444
       (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                 else t_tbl st)) ->
     mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * (nx + t_used st)) -> mem_u32 R_segs M' pb rt ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 2 R_segs M' (p + 808) 288 (arr_get work1Ar) ->
     realizes R_segs (zcfg R_segs 97500 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97440 (zupd Rb l) M MD) T.
Proof using C zc ret cf.
  intros st Rb l M MD T Hh HC HS LS8 HM HSM HP Hhb Hused Hhuff Hfit K.
  pose proof C as C'. open_itc C'. open_cmem HM. open_smem HSM. open_spure HP. zkeys. xaddr.
  clear Hprom HtyC HtyD Hlf Hcf Hwf Hlens15 LOWR DROPR.
  assert (J80 : forall RJ MJ, CRB RJ [] -> zget_l RJ [] kT5 = t_used st ->
            mpost R_segs M MJ (p + 1384) (p + 7160) 0 0 ->
            mem_arr 4 R_segs MJ (p + 1384) 1444
              (arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)
                        else t_tbl st)) ->
            mem_wr R_segs MJ (sp - 192) 192 -> mem_wr R_segs MJ p 7176 ->
            mem_arr 2 R_segs MJ (p + 168) 320 lf -> mem_arr 2 R_segs MJ (p + 808) 288 (arr_get work1Ar) ->
            mem_u64 R_segs MJ (p + 160) (p + 1384 + 4 * nx) ->
            realizes R_segs (zcfg R_segs 97472 (zupd RJ []) MJ MD) T).
  { intros RJ MJ HCJ JT5 HPO HtblJ WfJ WpJ HlensJ HworkJ HnextJ.
    clear Hcnt Htbl Wf Wp Hlens Hwork Hnext HslD HslL Hext Hbase. open_cregsB HCJ. zkeys.
    pose proof (mpost_stable R_segs MJ (p + 160) (p + 168) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
    assert (HAG : framed (fun X => mpost R_segs MJ X (p + 160) (p + 168) 0 0) MJ) by (apply mpost_refl).
    zrebase.
    zstep Rfd.
    zstep Rfd. zstep Rfd. zsetreg (4 * t_used st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd. zsetreg (p + 1384 + 4 * (nx + t_used st)) ltac:(lia).
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_s Rx [] Mx MD T rt Hh) end.
    all: try kauto. all: try close_pregs3.
    intros R' M' HP' LA6 HPO2 Hbits'.
    destruct HPO2 as [HA2 HW2].
    eapply K; try eassumption.
    -
      pose proof (framed_mpostL_trans2 R_segs M M MJ rsT _ _ _ _ (mpostL_refl R_segs M rsT) HPO ltac:(left; cbn; left; lia) ltac:(right; lia)) as F1.
      pose proof (framed_mpostL_trans2 R_segs M MJ _ rsT _ _ _ _ F1 HAG ltac:(left; cbn; right; left; lia) ltac:(right; lia)) as F2.
      exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ F2 (conj HA2 HW2) ltac:(left; cbn; right; right; left; lia) ltac:(right; lia)).
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_u64_magree; [exact HA2 | eassumption | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    - apply HW2. assumption.
    - apply HW2. assumption.
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
    - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia]. }
  pose proof (mpost_stable R_segs M (p + 1384) (p + 7160) 0 0 ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpost R_segs M X (p + 1384) (p + 7160) 0 0) M) by (apply mpost_refl).
  open_cregs HC. open_sregs HS. zkeys. zrebase.
  destruct (Z.eq_dec (t_huff st) 0) as [H0|HN0].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J80 Rx M) end.
    all: try kauto. all: try assumption.
    rewrite H0. cbn [Z.eqb negb]. exact Htbl.
  - zbr Rfd false.
    specialize (Hfit HN0).
    destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
    zstep Rfd. zstep Rfd. zsetreg (4 * t_huff st) ltac:(symmetry; apply zext32_x4; lia).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    match goal with
    | Ho : mem_u8 _ ?Mc _ 64, Hb : mem_u8 _ _ _ (t_len st - t_drop st), Hv : mem_u16 _ _ _ 0 |- _ =>
      pose proof (entry_write Mc (p + 1384) 1444 (arr_get (t_tbl st)) (t_next st + t_huff st) _ _ _ _ _ _ HT1 HT2 Ho Hb Hv
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Htbl;
      clear Ho Hb Hv HT1 HT2
    end.
    apply mem_arr_arr_set in Htbl; [| rewrite TL; lia].
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J80 Rx Mx) end.
    all: try kauto. all: try assumption.
    destruct (Z.eqb_spec (t_huff st) 0); [lia|]. cbn [negb]. exact Htbl.
Qed.

Lemma max0_s : forall Rb l M MD T,
  m_halted MD = None -> PR Rb l -> mx = 0 ->
  mem_wr R_segs M p 7176 -> mem_arr 4 R_segs M (p + 1384) 1444 cf -> mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) ->
  mem_wr R_segs M (sp - 192) 192 -> mem_arr 2 R_segs M (p + 168) 320 lf -> mem_arr 2 R_segs M (p + 808) 288 wf ->
  (forall R' M', pregs3 R' [] -> zget_l R' [] kA6 = 0 -> mpostL R_segs M M' rsT ->
     mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0))) ->
     mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * (nx + 2)) -> mem_u32 R_segs M' pb 1 ->
     mem_wr R_segs M' (sp - 192) 192 -> mem_wr R_segs M' p 7176 ->
     mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 2 R_segs M' (p + 808) 288 wf ->
     realizes R_segs (zcfg R_segs 97500 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs 97600 (zupd Rb l) M MD) T.
Proof using C zc ret bits.
  intros Rb l M MD T Hh HP Hmx0 Wp Htbl Hnext Wf Hlens Hwork K.
  pose proof C as C'. open_itc C'. open_pregs HP. zkeys. clear Hprom HtyC HtyD Hlf Hwf Hlens15.
  pose proof it_room_ge as HRG.
  assert (Htbl' : mem_arr 4 R_segs M (p + 1384) 1444 (arr_get (tblA cf))).
  { eapply mem_arr_ext; [exact Htbl|]. intros j _. symmetry. apply tblA_get. }
  clear Htbl.
  pose proof (mpostL_stable R_segs M rsT ltac:(cbn; unfold ZSEP in Hpb; rewrite two64_eq; lia)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X rsT) M) by (apply mpostL_refl).
  destruct (arr4_hole R_segs M (p + 1384) 1444 (arr_get (tblA cf)) nx Htbl' ltac:(lia)) as [HT1 HT2]. clear Htbl'.
  zrebase.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2 Mc (p + 1384) 1444 (arr_get (tblA cf)) nx 320 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  destruct (arr4_hole R_segs _ (p + 1384) 1444 _ (nx + 1) Htbl ltac:(lia)) as [HT1 HT2]. clear Htbl.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  match goal with
  | Hlo : mem_u16 _ ?Mc _ 320, Hhi : mem_u16 _ _ _ 0 |- _ =>
    pose proof (entry_write2 Mc (p + 1384) 1444 _ (nx + 1) 320 _ _ HT1 HT2 Hlo Hhi
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite two64_eq; lia) ltac:(lia) ltac:(lia)) as Htbl;
    clear Hlo Hhi HT1 HT2
  end.
  apply mem_arr_arr_set in Htbl; [| rewrite arr_len_set; unfold tblA; rewrite arr_len_init; cbv [N_CODES]; lia].
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (setbits_s Rx [] Mx MD T 1 Hh) end.
  all: try kauto. all: try close_pregs3.
  intros R' M' HP' LA6 HPO2 Hbits'. destruct HPO2 as [HA2 HW2].
  eapply K; try eassumption.
  - exact (framed_mpostL_trans2 R_segs M _ M' rsT _ _ _ _ HAG (conj HA2 HW2) ltac:(left; cbn; right; right; left; lia) ltac:(right; lia)).
  - eapply mem_arr_magree; [exact HA2 | | unfold ZSEP in Hpb; lia | lia].
    change (code_pack 64 1 0) with 320. exact Htbl.
  - eapply mem_u64_magree; [exact HA2 | | lia | rewrite two64_eq; lia | unfold ZSEP in Hpb; lia | lia].
    match goal with H : mem_u64 _ _ (p + 160) ?v |- _ => replace (p + 1384 + 4 * (nx + 2)) with v by lia; exact H end.
  - apply HW2. assumption.
  - apply HW2. assumption.
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
  - eapply mem_arr_magree; [exact HA2 | eassumption | unfold ZSEP in Hpb; lia | lia].
Qed.
End S7IT6.
End FXG.
End S_It6.

Module S_It7.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.Inftrees OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InftreesCoverage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ItableModel.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.Base.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ZArr4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ISpecs OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.ITac.
Import S_It0 S_It1 S_It2 S_It3 S_It4 S_It5 S_It6.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Section S7IT7.
Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z) (p pb sp ret vgp vtp zc : Z).
Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc.

#[local] Abbreviation PR := (pregs p lens_ofs codes pb sp vgp vtp (cty ty)).
#[local] Abbreviation cA := (arr_get (cntA lf lens_ofs codes)).
#[local] Abbreviation cntAr := (cntA lf lens_ofs codes).
#[local] Abbreviation mx := (mxA lf lens_ofs codes).
#[local] Abbreviation mn := (mnA lf lens_ofs codes).
#[local] Abbreviation rt := (rootA lf lens_ofs codes bits).
#[local] Abbreviation offsAr := (offsA lf lens_ofs codes).
#[local] Abbreviation work1Ar := (work1A lf lens_ofs codes wf).
#[local] Abbreviation X := (itm_ctx ty (lensA lf) lens_ofs nx (rootA lf lens_ofs codes bits) (mxA lf lens_ofs codes)).
#[local] Abbreviation st0 := (itm_st0 (mnA lf lens_ofs codes) nx (rootA lf lens_ofs codes bits) (cntA lf lens_ofs codes) (tblA cf) (work1A lf lens_ofs codes wf)).

Definition FP : list (Z * Z) := [(sp - 192, 192); (p + 160, 8); (pb, 4); (p + 808, 576); (p + 1384, 5776)].
Definition FPS : list (Z * Z) := [(sp + -192, 88); (p + 160, 8); (pb, 4); (p + 808, 576); (p + 1384, 5776)].

Definition pf (M : mem) : Prop :=
  mem_wr R_segs M p 7176 /\ mem_arr 2 R_segs M (p + 168) 320 lf /\ mem_arr 4 R_segs M (p + 1384) 1444 cf /\
  mem_arr 2 R_segs M (p + 808) 288 wf /\ mem_u64 R_segs M (p + 160) (p + 1384 + 4 * nx) /\ mem_u32 R_segs M pb bits /\
  mem_arr 2 R_segs M 67170 31 (arr_get lbase_a) /\ mem_arr 2 R_segs M 67232 31 (arr_get lext_a) /\
  mem_arr 2 R_segs M 67294 32 (arr_get dbase_a) /\ mem_arr 2 R_segs M 67358 32 (arr_get dext_a).
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  dand H as (a & b & c & d & e & f & g & h & i & j).

Lemma pf_frame : forall M M' lo hi, pf M -> mpost R_segs M M' lo hi 0 0 -> zc <= lo -> pf M'.
Proof using C ret sp codes lens_ofs ty.
  intros M M' lo hi HP [HA HW] Hlo. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb. open_pf HP. unfold pf. split_conj.
  - apply HW. exact Wp.
  - eapply mem_arr_magree; [exact HA | exact Hlens | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Htabl | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hwork | lia_std | lia_std].
  - eapply mem_u64_magree; [exact HA | exact Hnext | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_u32_magree; [exact HA | exact Hbcell | lia_std | rewrite two64_eq; lia_std | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hlb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hle | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hdb | lia_std | lia_std].
  - eapply mem_arr_magree; [exact HA | exact Hde | lia_std | lia_std].
Qed.

Lemma slots_fps : forall M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  slots sp M v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 -> mpostL R_segs M M' FPS ->
  slots sp M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M' v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 HS [HA HW]. pose proof C as C'. open_itc C'. unfold ZSEP in Hpb.
  unfold slots in *. destr_conj HS. split_conj.
  all: eapply mem_u64_magreeL; [exact HA | eassumption | lia_std | rewrite two64_eq; lia_std | cbn; lia_std].
Qed.


Lemma acc2 : forall M0 M M' a1 b1 a2 b2,
  framed (fun X => mpostL R_segs M0 X FPS) M -> mpost R_segs M M' a1 b1 a2 b2 ->
  in_some a1 (b1 - a1) FPS \/ b1 <= a1 -> in_some a2 (b2 - a2) FPS \/ b2 <= a2 ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using. intros. eapply framed_mpostL_trans2; eassumption. Qed.
Lemma accL : forall M0 M M', framed (fun X => mpostL R_segs M0 X FPS) M -> mpostL R_segs M M' (rsL p sp) ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.
Lemma accT : forall M0 M M', framed (fun X => mpostL R_segs M0 X FPS) M -> mpostL R_segs M M' (rsT p pb) ->
  framed (fun X => mpostL R_segs M0 X FPS) M'.
Proof using.
  intros M0 M M' HF HP. eapply framed_mpostL_trans; [exact HF | exact HP |].
  intros x Hx. cbn in *. lia_std.
Qed.

Lemma safe_sort : mx <> 0 -> itm_reject ty mx (it_left_check cntAr) = false ->
  it_sort_ok (lensA lf) lens_ofs codes offsAr 288 = true /\
  (it_not_enough ty (itm_used rt) = false -> it_loop_ok (Z.to_nat (codes + 1)) X 288 320 1444 st0 = true).
Proof using C zc ret sp pb p.
  intros Hmx Hrj.
  pose proof (it_safe_sort ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ C)) as S.
  cbv zeta in S. unfold mxA, cntA, rootA, mnA, mxA, cntA, offsA, work1A, offsA, cntA in *.
  specialize (S Hmx Hrj). destruct S as [S1 S2].
  unfold workA, lensA, tblA in S1, S2 |- *. rewrite !arr_len_init in S1, S2. cbv [N_WORK N_LENS N_CODES] in S1, S2 |- *.
  split; [exact S1 | intros Hne; exact (proj2 (proj2 (S2 Hne)))].
Qed.

Lemma fin_fp : forall M M1 M', mpost R_segs M M1 (sp + -192) sp 0 0 -> mpostL R_segs M1 M' FPS -> mpostL R_segs M M' FP.
Proof using C zc ret wf cf bits nx codes lens_ofs lf ty.
  intros M M1 M' HP [HA HW]. pose proof C as C'. open_itc C'.
  pose proof (framed_mpostL_trans2 R_segs M M M1 FP _ _ _ _ (mpostL_refl R_segs M FP) HP ltac:(left; cbn; left; lia_std) ltac:(right; lia_std)) as [A1 W1].
  split; [| intros a n Hw; apply HW; apply W1; exact Hw].
  intros x Hx. rewrite (HA x); [apply A1; exact Hx|]. cbn in Hx |- *. lia_std.
Qed.

Lemma cA_zero : codes = 0 -> forall j, arr_get cntAr j = 0.
Proof using. intros Hc j. rewrite cntA_eq, Hc. unfold cntK. rewrite itm_count_k_0 by lia_std. apply it_zero_count_spec. Qed.

Lemma tbl_max0_range : forall j, 0 <= j < 1444 ->
  0 <= arr_get (arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0)) j < 4294967296.
Proof using C zc ret sp pb p wf bits codes lens_ofs lf ty.
  intros j Hj. pose proof C as C'. open_itc C'.
  rewrite !arr_get_set. destruct (_ && _); [apply code_pack_range|]. destruct (_ && _); [apply code_pack_range|].
  rewrite tblA_get. apply Hcf. exact Hj.
Qed.
Lemma tbl_brk_range : forall st, (forall j, 0 <= j < 1444 -> 0 <= arr_get (t_tbl st) j < 4294967296) ->
  forall j, 0 <= j < 1444 ->
  0 <= arr_get (if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st) j < 4294967296.
Proof using.
  intros st H j Hj. destruct (negb _); [|apply H; exact Hj]. rewrite arr_get_set. destruct (_ && _); [apply code_pack_range | apply H; exact Hj].
Qed.
Lemma tblA_range : forall j, 0 <= j < 1444 -> 0 <= arr_get (tblA cf) j < 4294967296.
Proof using C zc ret sp pb p wf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite tblA_get. apply Hcf. exact Hj. Qed.
Lemma workA_range : forall j, 0 <= j < 288 -> 0 <= arr_get (workA wf) j < 65536.
Proof using C zc ret sp pb p cf bits nx codes lens_ofs lf ty. intros j Hj. pose proof C as C'. open_itc C'. rewrite workA_get. apply Hwf. exact Hj. Qed.
End S7IT7.

End FXG.
Ltac open_pf H :=
  unfold pf in H;
  let a := fresh "Wp" in let b := fresh "Hlens" in let c := fresh "Htabl" in let d := fresh "Hwork" in
  let e := fresh "Hnext" in let f := fresh "Hbcell" in let g := fresh "Hlb" in let h := fresh "Hle" in
  let i := fresh "Hdb" in let j := fresh "Hde" in
  dand H as (a & b & c & d & e & f & g & h & i & j).
Ltac zkeys_all := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Theorem itable_s : itable_spec_at R_segs A_ITABLE 192.
Proof.
  unfold itable_spec_at, A_ITABLE.
  intros Rb l M MD T ty p lens_ofs codes nx bits pb sp ret zc lf cf wf.
  intros Hh LA0 LA1 LA2 LA3 LA4 LA5 LSP LRA Hret Hret2 Hpb Hpal Hp0 Hpceil Hsp Hzrom Hsp2 Hspal Hprom
         Wf0 Wp0 Hlens0 Htab0 Hwork0 Hnext0 Hbits0 Hlb0 Hle0 Hdb0 Hde0 Rlf Rcf Rwf
         Hofs Hofs2 Hc0 Hc288 Hl15 HtyC HtyD Hb1 Hb15 Hnx Hroom K.
  cbv [o_lens o_next o_work o_codes N_LENS N_CODES N_WORK STATE_SIZE LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR
       o_lenbits o_distbits ROM_LO_ALL it_fp] in *.
  set (vgp := zget_l Rb l kGP). set (vtp := zget_l Rb l kTP).
  assert (C : itc ty lf lens_ofs codes nx bits cf wf p pb sp ret 192 zc).
  { constructor; cbv [N_LENS N_CODES N_WORK STATE_SIZE o_lenbits o_distbits ROM_LO_ALL DEXT_ADDR]; try assumption; try lia_std. }
  assert (PF0 : pf lf nx bits cf wf p pb M) by (unfold pf; split_conj; assumption).
  assert (FIN : forall R' M' rv (T' W' : arr) tab' b',
    resA ty lf lens_ofs codes nx bits cf wf = (rv, T', tab', b', W') ->
    zget_l R' [] kSP = sp + -192 -> zget_l R' [] kGP = vgp -> zget_l R' [] kTP = vtp -> zget_l R' [] kA6 = rv ->
    slots sp M' ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9)
          (zget_l Rb l kS10) (zget_l Rb l kS11) ->
    mpostL R_segs M M' (FP p pb sp) ->
    mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 4 R_segs M' (p + 1384) 1444 (arr_get T') -> mem_arr 2 R_segs M' (p + 808) 288 (arr_get W') ->
    (forall i, 0 <= i < 1444 -> 0 <= arr_get T' i < 4294967296) -> (forall i, 0 <= i < 288 -> 0 <= arr_get W' i < 65536) ->
    mem_u64 R_segs M' (p + 160) (p + 1384 + 4 * tab') -> mem_u32 R_segs M' pb b' ->
    realizes R_segs (zcfg R_segs 97500 (zupd R' []) M' MD) T).
  { intros R' M' rv T' W' tab' b' ER LSP' LGP' LTP' LA6' HSL HPL Hlens' Htab' Hwork' RT RW Hnext' Hbits'.
    eapply (epilogue_s ty lf lens_ofs codes nx bits cf wf p pb sp ret zc C R' [] M' MD T rv ret); try eassumption.
    intros R'' FA0 FSP FRA FS0 FS1 FS2 FS3 FS4 FS5 FS6 FS7 FS8 FS9 FS10 FS11 FGP FTP.
    assert (RES : it_ret (resA ty lf lens_ofs codes nx bits cf wf) = rv /\ it_tbl (resA ty lf lens_ofs codes nx bits cf wf) = T' /\
                  it_table (resA ty lf lens_ofs codes nx bits cf wf) = tab' /\ it_bits (resA ty lf lens_ofs codes nx bits cf wf) = b' /\
                  it_work (resA ty lf lens_ofs codes nx bits cf wf) = W').
    { rewrite ER. repeat split; reflexivity. }
    unfold resA, lensA, tblA, workA in RES. cbv [N_LENS N_CODES N_WORK] in RES. dand RES as (E1 & E2 & E3 & E4 & E5).
    assert (RV3 : rv = 0 \/ rv = 1 \/ rv = -1).
    { pose proof (res_phases ty lf lens_ofs codes nx bits cf wf) as PH. rewrite ER in PH.
      destruct (mxA lf lens_ofs codes =? 0); [injection PH; intros; lia_std|].
      destruct (itm_reject _ _ _); [injection PH; intros; lia_std|].
      destruct (it_not_enough _ _); [injection PH; intros; lia_std|].
      destruct (it_loop _ _ _); injection PH; intros; lia_std. }
    eapply (K R'' M' (arr_get T') (arr_get W')); cbv zeta; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
    all: try (intros; reflexivity).
    unfold kept_eq. cbv [zget_l alookup] in FSP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FGP, FTP.
    rewrite FSP, FGP, FTP, FS0, FS1, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11. subst vgp vtp.
    repeat split; first [reflexivity | symmetry; assumption | assumption]. }
  pose proof (it_safe_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ C) as SAFE.
  eapply (it_prologue_s Rb l M MD T sp ret vgp vtp (zget_l Rb l kS0) (zget_l Rb l kS1) (cty ty) (p + 168 + 2 * lens_ofs) codes (p + 160) pb (p + 808)
            (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4) (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7)
            (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11) Hh); try assumption; try reflexivity; try lia.
  intros R1 M1 QSP QGP QTP QA0 QA1 QA2 QA3 QA4 QA5 HPO1 Wf1 S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27 Hcnt0.
  assert (HSL1 : slots sp M1 ret (zget_l Rb l kS0) (zget_l Rb l kS1) (zget_l Rb l kS2) (zget_l Rb l kS3) (zget_l Rb l kS4)
          (zget_l Rb l kS5) (zget_l Rb l kS6) (zget_l Rb l kS7) (zget_l Rb l kS8) (zget_l Rb l kS9) (zget_l Rb l kS10) (zget_l Rb l kS11))
    by (unfold slots; split_conj; assumption).
  clear S1 S8 S9 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27.
  pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M M1 _ _ PF0 HPO1 ltac:(lia)) as PF1.
  assert (HAGS1 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M1) by (apply mpostL_refl).
  assert (PR1 : pregs p lens_ofs codes pb sp vgp vtp (cty ty) R1 []) by (unfold pregs; split_conj; assumption).
  assert (KC : forall Mc, pf lf nx bits cf wf p pb Mc -> mem_wr R_segs Mc (sp - 192) 192 -> mem_arr 2 R_segs Mc (sp + -136) 16 (arr_get (cntA lf lens_ofs codes)) ->
            framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) Mc ->
            Kleft ty lf lens_ofs codes bits p pb sp vgp vtp Mc MD T /\ Kmax0 ty lf lens_ofs codes p pb sp vgp vtp Mc MD T).
  { intros Mc PFc Wfc Hcntc HAGc. pose proof PFc as PFc'. unfold pf in PFc'.
    dand PFc' as (Wpc & Hlens1 & Htabl0 & Hwork1 & Hnext1 & Hbcell0 & Hlb1 & Hle1 & Hdb1 & Hde1). split.
    -
      apply (left_s ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Hcntc).
      +
        unfold Kneg. intros R' HP' LA6 Hrj Hmx1. open_pregs HP'.
        eapply (FIN R' Mc (-1) (tblA cf) (workA wf) nx bits); try eassumption.
        * rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj. reflexivity.
        * eapply slots_fps; [exact C | exact HSL1 | exact HAGc].
        * eapply fin_fp; [exact C | exact HPO1 | exact HAGc].
        * eapply mem_arr_ext; [exact Htabl0|]. intros; symmetry; apply tblA_get.
        * eapply mem_arr_ext; [exact Hwork1|]. intros; symmetry; apply workA_get.
        * apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
        * apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      +
        apply (offs_s ty lf lens_ofs codes nx bits cf wf p pb sp ret vgp vtp zc C Mc MD T Hh Wfc).
        intros R3 M3 HP3 LT0 LT1 LA7 HPO3 Hoffs Hmx1 Hrj.
        assert (Hmx0 : mxA lf lens_ofs codes <> 0) by lia.
        destruct (safe_sort _ _ _ _ _ _ _ _ _ _ _ _ _ C Hmx0 Hrj) as [SOK LOOPOK].
        pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C Mc M3 _ _ PFc HPO3 ltac:(lia)) as PF3.
        dand PF3 as (Wp3 & Hlens3 & Htab3 & Hwork3 & Hnext3 & Hbits3 & Hlb3 & Hle3 & Hdb3 & Hde3).
        assert (HAG3 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M3) by (eapply acc2; [exact HAGc | exact HPO3 | left; cbn; left; lia | right; lia]).
        assert (Wf3 : mem_wr R_segs M3 (sp - 192) 192) by (destruct HPO3 as [_ HW]; apply HW; exact Wfc).
        eapply (sort_phase_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M3 MD T Hh HP3 LT0 LT1 LA7 Hmx1 SOK Wf3 Wp3 Hlens3 Hoffs Hwork3).
        intros R4 M4 HP4 LT0' LT1' LA7' HPO4 Wf4 Wp4 Hlens4 Hwork4.
        destruct HPO4 as [HA4 HW4]. unfold ZSEP in Hprom, Hpb.
        assert (HAG4 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M4) by (eapply acc2; [exact HAG3 | exact (conj HA4 HW4) | left; cbn; left; lia | left; cbn; right; right; right; left; lia]).
        assert (Htab4 : mem_arr 4 R_segs M4 (p + 1384) 1444 cf) by (eapply mem_arr_magree; [exact HA4 | exact Htab3 | lia | lia]).
        assert (Hnext4 : mem_u64 R_segs M4 (p + 160) (p + 1384 + 4 * nx)) by (eapply mem_u64_magree; [exact HA4 | exact Hnext3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hbits4 : mem_u32 R_segs M4 pb bits) by (eapply mem_u32_magree; [exact HA4 | exact Hbits3 | lia | rewrite two64_eq; lia | lia | lia]).
        assert (Hlb4 : mem_arr 2 R_segs M4 67170 31 (arr_get lbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hlb3 | lia | lia]).
        assert (Hle4 : mem_arr 2 R_segs M4 67232 31 (arr_get lext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hle3 | lia | lia]).
        assert (Hdb4 : mem_arr 2 R_segs M4 67294 32 (arr_get dbase_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hdb3 | lia | lia]).
        assert (Hde4 : mem_arr 2 R_segs M4 67358 32 (arr_get dext_a)) by (eapply mem_arr_magree; [exact HA4 | exact Hde3 | lia | lia]).
        assert (Hcnt4 : mem_arr 2 R_segs M4 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
        { eapply mem_arr_magree; [exact HA4 | | lia | lia]. destruct HPO3 as [HA3 _]. eapply mem_arr_magree; [exact HA3 | exact Hcntc | lia | lia]. }
        clear HA4 HW4 Htab3 Hnext3 Hbits3 Hlb3 Hle3 Hdb3 Hde3 Hwork3 Hlens3 Wp3 Htabl0 Hnext1 Hbcell0 Hlb1 Hle1 Hdb1 Hde1 Hwork1 Hlens1 Wpc.
        eapply (switch_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R4 [] M4 MD T Hh HP4 LT0' LT1' LA7' Hmx1 Wf4 Wp4 Hlens4 Hwork4 Hcnt4 Htab4 Hnext4 Hlb4 Hle4 Hdb4 Hde4).
        *
          intros R5 M5 HC5 HS5 HPO5 HM5 HSM5 HSP5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          assert (Hbits5 : mem_u32 R_segs M5 pb bits).
          { destruct HPO5 as [HA5 _]. eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia]. }
          specialize (LOOPOK Hne).
          assert (PHc : 0 <= codes <= 288) by lia.
          assert (PHl : forall s, 0 <= s < codes -> 0 <= arr_get (lensA lf) (lens_ofs + s) <= 15).
          { intros s Hs. rewrite lensA_get. pose proof (Rlf (lens_ofs + s) ltac:(lia)). pose proof (Hl15 s Hs). lia. }
          assert (PHt : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get (lensA lf) (lens_ofs + s) <= 7).
          { intros E. destruct (HtyC E) as (A & B & D). repeat split; try assumption. intros s Hs. rewrite lensA_get. apply D. exact Hs. }
          assert (PHb : 1 <= bits <= 15) by lia.
          assert (PHI1 : forall st, PIc_mod.PIc ty lf lens_ofs codes nx bits st -> ty = CODES -> tr_w st < it_match ty).
          { intros st0 HPI Ety. unfold tr_w. assert (EM : it_match ty = 20) by (rewrite Ety; reflexivity). rewrite EM. exact (PIc_mod.pic_w ty lf lens_ofs codes nx bits PHc PHl PHt PHb Hmx1 Hrj st0 HPI Ety). }
          eapply (main_loop_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C (PIc_mod.PIc ty lf lens_ofs codes nx bits) PHI1
                    (PIc_mod.pic_step ty lf lens_ofs codes nx bits PHc PHl PHt PHb Hmx1 Hrj)
                    (Z.to_nat (codes + 1)) _ R5 [] M5 M5 MD T LOOPOK Hmx1
                    (PIc_mod.pic_init ty lf lens_ofs codes nx bits cf wf PHc PHl PHt PHb Hmx1 Hrj Hne)
                    Hh HC5 HS5 HM5 HSM5 HSP5 (mpostL_refl _ _ _)).
          --
             intros st' R6 M6 HL HC6 HS6 L8 HPL6 HM6 HSM6 HSP6 Hfit B1 B2 B3.
             assert (HAG6 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             eapply (break_tail_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C st' R6 [] M6 MD T Hh HC6 HS6 L8 HM6 HSM6 HSP6 B1 B2 B3 Hfit).
             intros R7 M7 HP7 LA6 HPT7 Htbl7 Hnext7 Hbits7 Wf7 Wp7 Hlens7 Hwork7.
             assert (HAG7 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M7) by (eapply accT; [exact HAG6 | exact HPT7]).
             unfold pregs3 in HP7. dand HP7 as (P1 & P2 & P3).
             pose proof HSP6 as HSP6'. unfold spure in HSP6'. dand HSP6' as (WK6 & _ & _ & _ & _ & _ & HTR6 & _ & _).
             eapply (FIN R7 M7 0 _ (t_work st') (nx + t_used st') (rootA lf lens_ofs codes bits)); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG7].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG7].
             ++ rewrite WK6. exact Hwork7.
             ++ apply tbl_brk_range. exact HTR6.
             ++ rewrite WK6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          --
             intros st' R6 M6 HL HC6 LA6 HPL6 HM6 HSM6 HW6 HTR6.
             assert (HAG6 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M6) by (eapply accL; [exact HAG5 | exact HPL6]).
             unfold cregsN in HC6. dand HC6 as (HP6 & _). unfold pregs6 in HP6. dand HP6 as (P1 & P2 & P3 & _).
             unfold cmem in HM6. dand HM6 as (Wf6 & Wp6 & Hlens6 & Hwork6 & Hnext6 & _).
             unfold smem in HSM6. dand HSM6 as (Hcnt6 & Htbl6).
             assert (Hbits6 : mem_u32 R_segs M6 pb bits).
             { destruct HPL6 as [HA6 _]. eapply mem_u32_magreeL; [exact HA6 | exact Hbits5 | lia | rewrite two64_eq; lia | cbn; lia]. }
             eapply (FIN R6 M6 1 (t_tbl st') (t_work st') nx bits); try eassumption.
             ++ rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne.
                rewrite it_loop_is_n. replace (codes + 1) with (Z.of_nat (Z.to_nat (codes + 1))) by lia. rewrite HL. reflexivity.
             ++ eapply slots_fps; [exact C | exact HSL1 | exact HAG6].
             ++ eapply fin_fp; [exact C | exact HPO1 | exact HAG6].
             ++ rewrite HW6. exact Hwork6.
             ++ rewrite HW6. apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
        *
          intros R5 M5 HP5 LA6 HPO5 Hne.
          assert (HAG5 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M5) by (eapply acc2; [exact HAG4 | exact HPO5 | left; cbn; left; lia | right; lia]).
          destruct HPO5 as [HA5 HW5].
          unfold pregs6 in HP5. dand HP5 as (P1 & P2 & P3 & _).
          eapply (FIN R5 M5 1 (tblA cf) (work1A lf lens_ofs codes wf) nx bits); try eassumption.
          -- rewrite res_phases. destruct (Z.eqb_spec (mxA lf lens_ofs codes) 0); [lia|]. rewrite Hrj, Hne. reflexivity.
          -- eapply slots_fps; [exact C | exact HSL1 | exact HAG5].
          -- eapply fin_fp; [exact C | exact HPO1 | exact HAG5].
          -- eapply mem_arr_magree; [exact HA5 | exact Hlens4 | lia | lia].
          -- eapply mem_arr_magree; [exact HA5 | | lia | lia]. eapply mem_arr_ext; [exact Htab4|]. intros; symmetry; apply tblA_get.
          -- eapply mem_arr_magree; [exact HA5 | exact Hwork4 | lia | lia].
          -- apply (tblA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          -- apply (work1_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
          -- eapply mem_u64_magree; [exact HA5 | exact Hnext4 | lia | rewrite two64_eq; lia | lia | lia].
          -- eapply mem_u32_magree; [exact HA5 | exact Hbits4 | lia | rewrite two64_eq; lia | lia | lia].
    -
      unfold Kmax0. intros R' HP' Hmx0.
      eapply (max0_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R' [] Mc MD T Hh HP' Hmx0 Wpc Htabl0 Hnext1 Wfc Hlens1 Hwork1).
      intros R2 M2 HP2 LA6 HPT2 Htbl2 Hnext2 Hbits2 Wf2 Wp2 Hlens2 Hwork2.
      assert (HAG2 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M2) by (eapply accT; [exact HAGc | exact HPT2]).
      unfold pregs3 in HP2. dand HP2 as (P1 & P2 & P3).
      eapply (FIN R2 M2 0 _ (workA wf) (nx + 2) 1); try eassumption.
      + rewrite res_phases. rewrite Hmx0. reflexivity.
      + eapply slots_fps; [exact C | exact HSL1 | exact HAG2].
      + eapply fin_fp; [exact C | exact HPO1 | exact HAG2].
      + eapply mem_arr_ext; [exact Hwork2|]. intros; symmetry; apply workA_get.
      + apply (tbl_max0_range _ _ _ _ _ _ _ _ _ _ _ _ _ C).
      + apply (workA_range _ _ _ _ _ _ _ _ _ _ _ _ _ C). }
  pose proof PF1 as PF1'. unfold pf in PF1'. dand PF1' as (Wp1 & HlensM1 & HtabM1 & HworkM1 & HnextM1 & HbitsM1 & _).
  destruct (Z.eq_dec codes 0) as [Cz|Cnz].
  -
    assert (HcntA : mem_arr 2 R_segs M1 (sp + -136) 16 (arr_get (cntA lf lens_ofs codes))).
    { eapply mem_arr_ext; [exact Hcnt0|]. intros; symmetry; apply cA_zero; exact Cz. }
    destruct (KC M1 PF1 Wf1 HcntA HAGS1) as [_ KM0].
    eapply (count_phase0_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T _ Cz Hh PR1 eq_refl Hcnt0 HbitsM1 KM0).
  - eapply (count_phase_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R1 [] M1 MD T ltac:(lia) Hh PR1 Wf1 HlensM1 Hcnt0).
    intros R2 M2 PR2 QA7 HPO2 Wf2 Hlens2 Hcnt2.
    pose proof (pf_frame _ _ _ _ _ _ _ _ _ _ _ _ _ C M1 M2 _ _ PF1 HPO2 ltac:(lia)) as PF2.
    assert (HAG2 : framed (fun Xm => mpostL R_segs M1 Xm (FPS p pb sp)) M2) by (eapply acc2; [exact HAGS1 | exact HPO2 | left; cbn; left; lia | right; lia]).
    destruct (KC M2 PF2 Wf2 Hcnt2 HAG2) as [KL KM0].
    pose proof PF2 as PF2'. unfold pf in PF2'. dand PF2' as (_ & _ & _ & _ & _ & HbitsM2 & _).
    eapply (max_entry_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R2 [] M2 MD T _ Hh PR2 QA7 Hcnt2 HbitsM2).
    + unfold Kmax. intros R3 HP3 LA7 LT0 LT2 Hmx2.
      eapply (rootmin_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 LT0 LT2 Hmx2 Hcnt2 KL).
    + unfold Klow. intros R3 HP3 LA7 HZ.
      eapply (maxlow_s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C R3 [] M2 MD T Hh HP3 LA7 HZ Hcnt2 KL KM0).
Qed.
End FXG.
End S_It7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_Fast7.

Module S_Tok.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Frame OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Hoare.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.S8MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.S8Memcpy OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.S8AdlerBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.S8AdlerIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.S8Adler OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.S8AdlerApart.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.S8LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.SBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_LeaveA S_U2A OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C S_It7 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_Fast7.S_Fast1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_Fast7.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.


Lemma w64_lit : forall z (w : word), bv_unsigned w = z -> w64 z = w.
Proof. intros z w <-. apply w64_of_word. Qed.

Lemma msteps_memcpy_S8 : msteps_memcpy R_segs A_MEMCPY.
Proof.
  intros mem0 dst src n bs rom Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd regs ret Hret H1 H10 H11 H12.
  unfold A_MEMCPY. rewrite (w64_lit 131564 (0x201ec%bv : word)) by reflexivity.
  apply (ref_memcpy mem0 dst src n bs rom); try assumption.
  constructor; assumption.
Qed.
Theorem memcpy_ok : memcpy_spec_s.
Proof. unfold memcpy_spec_s. apply memcpy_glue. apply msteps_memcpy_S8. Qed.

Lemma img_ok_of_rom_ok : forall m, rom_ok m -> img_ok m.
Proof.
  intros m H. apply (img_ok_of_range m ROM_LO ROM_HI).
  - apply rom_hyp_of_okG; [cbv [ROM_LO]; lia_std | rewrite two64_eq; cbv [ROM_HI]; lia_std | exact H].
  - cbv [ROM_LO RO_LO]. lia_std.
  - cbv [ROM_HI RO_HI]. lia_std.
Qed.
Lemma msteps_adler32_S8 : msteps_adler32A R_segs A_ADLER32 FR_AD rom_ok.
Proof.
  intros regs m rom retw usp a adr v len. unfold A_ADLER32, FR_AD. rewrite (w64_lit 95836 (0x1765c%bv : word)) by reflexivity.
  intros. eapply (s8_adler32_apart regs m rom retw usp a adr v len); try eassumption. apply img_ok_of_rom_ok. assumption.
Qed.
Theorem adler32_ok : adler32_spec_s.
Proof. unfold adler32_spec_s. apply adler32A_glue; [cbv [FR_AD]; lia_std | apply msteps_adler32_S8]. Qed.

Lemma msteps_adler32_null_S8 : msteps_adler32_null0 R_segs A_ADLER32.
Proof.
  intros regs m rom retw. unfold A_ADLER32. rewrite (w64_lit 95836 (0x1765c%bv : word)) by reflexivity.
  exact (s8_adler32_null regs m rom retw).
Qed.
Theorem adler32_null_ok : adler32_null_spec_s.
Proof. unfold adler32_null_spec_s. apply adler32_null0_glue. apply msteps_adler32_null_S8. Qed.

Theorem itable_ok : itable_spec_s.
Proof. exact itable_s. Qed.
Theorem ifast_ok : ifast_spec_s.
Proof. exact ifast_s. Qed.

Section Local.
Variable P : word -> Prop.
Variables M M' : mem.
Hypothesis AG : forall x, P x -> M' x = M x.

Lemma mem_is_local : forall a bs,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> P x) ->
  0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  mem_is R_segs M a bs -> mem_is R_segs M' a bs.
Proof.
  intros a bs HP Ha Hn H. unfold mem_is in *.
  destruct bs as [|b bs']; [exact H|].
  assert (Ha' : bv_unsigned (w64 a) = a).
  { rewrite w64_unsigned, mod_small_u64; [reflexivity|]. cbn [length] in Hn. lia_std. }
  rewrite (rdn_ext R_segs (length (b :: bs')) M' M (w64 a)); [exact H | |].
  - rewrite Ha'. rewrite <- two64_eq. exact Hn.
  - intros x Hx. apply AG. apply HP. rewrite Ha' in Hx. exact Hx.
Qed.

Lemma mem_u64_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 8 -> P x) -> 0 <= a -> a + 8 <= two64 ->
  mem_u64 R_segs M a v -> mem_u64 R_segs M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u64 in *.
  apply (mem_is_local a (Z_to_le_bytes 8 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_u32_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 4 -> P x) -> 0 <= a -> a + 4 <= two64 ->
  mem_u32 R_segs M a v -> mem_u32 R_segs M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u32 in *.
  apply (mem_is_local a (Z_to_le_bytes 4 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_arr_local : forall k base n f,
  (forall x : word, base <= bv_unsigned x < base + k * n -> P x) ->
  mem_arr k R_segs M base n f -> mem_arr k R_segs M' base n f.
Proof.
  intros k base n f HP (A & B & C & D & H). split; [exact A | split; [exact B | split; [exact C | split; [exact D |]]]].
  intros i Hi. eapply mem_is_local; [ | nia | rewrite length_Z_to_le_bytes; nia | apply H; exact Hi].
  intros x Hx. apply HP. rewrite length_Z_to_le_bytes in Hx. nia.
Qed.

Lemma i_frame_local : forall cx,
  (forall x : word, c_u cx + -224 <= bv_unsigned x < c_u cx -> P x) ->
  0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  i_frame cx M -> i_frame cx M'.
Proof.
  intros cx HP Hu1 Hu2 H. unfold i_frame in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25).
  repeat split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma i_hooks_local : forall cx,
  (forall x : word, c_u cx + 64 <= bv_unsigned x < c_u cx + 80 -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 ->
  i_hooks cx M -> i_hooks cx M'.
Proof.
  intros cx HP Hu1 Hu2 [A B].
  split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma i_cst_local : forall cx,
  (forall x : word, (c_u cx + 56 <= bv_unsigned x < c_u cx + 88) \/ (c_p cx <= bv_unsigned x < c_p cx + 7164) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  i_cst R_segs cx M -> i_cst R_segs cx M'.
Proof.
  intros cx HP Hu1 Hu2 Hp1 Hp2 H. unfold i_cst, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma st_at_local : forall cx st,
  (forall x : word, c_p cx + 8 <= bv_unsigned x < c_p cx + 168 -> P x) ->
  0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  st_at R_segs cx st M -> st_at R_segs cx st M'.
Proof.
  intros cx st HP Hp1 Hp2 H. unfold st_at, st_rest, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma strm_at_local : forall cx st,
  (forall x : word, (c_u cx <= bv_unsigned x < c_u cx + 36) \/ (c_p cx + 96 <= bv_unsigned x < c_p cx + 108) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  strm_at R_segs cx st M -> strm_at R_segs cx st M'.
Proof.
  intros cx st HP Hu1 Hu2 Hp1 Hp2 H. unfold strm_at, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
End Local.

Definition cxw (u p q n s5 s6 s7 s8 s9 s10 s11 zc : Z) (zm : bool) (osz cin0 cout0 W0 ra : Z) : ictx :=
  cxc u p q n 0 0 s5 s6 s7 s8 s9 s10 s11 zc zm osz 0 cin0 cout0 W0 ra.

Definition tok_mem (cx : ictx) (st : ist) (rv : Z) (lf cf : Z -> Z) (M : mem) : Prop :=
  mem_u64 R_segs M (c_u cx + -232) L_UW_RET /\ mem_u64 R_segs M (c_u cx + -240) (c_p cx) /\
  mem_u64 R_segs M (c_u cx + -248) rv /\ mem_u64 R_segs M (c_u cx + -256) (c_n cx - t_cin st) /\
  mem_u64 R_segs M (c_u cx + -264) (c_osz cx - t_cout st) /\ mem_u64 R_segs M (c_u cx + -272) (t_out st - (c_osz cx - t_cout st)) /\
  i_frame cx M /\ i_cst R_segs cx M /\ i_hooks cx M /\
  st_at R_segs cx st M /\ strm_at R_segs cx st M /\
  mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf /\ mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf.

Definition tok_pure (u p q n s5 s6 s7 s8 s9 s10 s11 zc : Z) (zm : bool) (osz cin0 cout0 W0 ra s11v : Z) (st : ist) (lf cf : Z -> Z) : Prop :=
  (ra = RA_C1 \/ ra = RA_C2) /\ 0 <= cin0 <= n /\ 0 <= cout0 <= osz /\ (if zm then osz = 0 else 1 <= osz /\ osz <= 262144) /\
  0 <= s5 < two64 /\ 0 <= s6 < two64 /\ 0 <= s7 < two64 /\ 0 <= s8 < two64 /\ 0 <= s9 < two64 /\ 0 <= s10 < two64 /\ 0 <= s11 < two64 /\
  0 <= s11v < two64 /\
  sinv (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc zm osz cin0 cout0 W0 ra) st lf cf /\ cout0 < t_cout st /\ t_mode st <= DONE /\
  zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc.

(* 1.4: register order (the 1.4 allocation), with uncompress3's output buffer and size (ob, osz) *)
Definition tok_regs (u p q n : Z) (zm : bool) (osz cin0 s11v : Z) (st : ist) : list Z :=
  [ob u zm + t_cout st; t_out st - (osz - t_cout st); 1; p; t_out st - (osz - t_cout st); n - cin0;
   osz - t_cout st; t_hold st; t_bits st; t_out st; s11v; q + t_cin st].

Definition zwtok_S8 (zm : bool) : ZWINV := fun u p q n zc sE sW M =>
  exists (osz s5 s6 s7 s8 s9 s10 s11 cin0 cout0 W0 ra rv s11v : Z) (st : ist) (lf cf : Z -> Z),
    sE = [s5; s6; s7; s8; s9; s10; s11] /\ sW = tok_regs u p q n zm osz cin0 s11v st /\
    tok_pure u p q n s5 s6 s7 s8 s9 s10 s11 zc zm osz cin0 cout0 W0 ra s11v st lf cf /\
    tok_mem (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc zm osz cin0 cout0 W0 ra) st rv lf cf M.

Theorem zw_local : forall zm : bool, zw_local_stmt_S8 (zwtok_S8 zm).
Proof.
  intros zm u p q n zc sE sW M M' AG H.
  dand H as (osz & s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & rv & s11v & st & lf & cf & EsE & EsW & PURE & TM).
  exists osz, s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra, rv, s11v, st, lf, cf.
  split; [exact EsE | split; [exact EsW | split; [exact PURE |]]].
  pose proof two64_eq as TW64.
  assert (HL : zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc).
  { unfold tok_pure in PURE. destr_conj PURE. split_conj; assumption. }
  clear PURE EsE EsW. cbv [FRA STATE_SIZE] in HL. dand HL as (Hu0 & Hu1 & Hp0 & Hp1).
  unfold tok_mem, cxw, cxc, ob in *. icx_cbn.
  dand TM as (T1 & T2 & T3 & T4 & T5 & T6 & FRM & CST & HK & SAT & STRM & Hlens & Hcodes).
  unfold in_fpw_S8, S8_ZWD, S8_INFL_N, S8_BUF, S8_BUF_N in AG.
  split_conj.
  all: first [ eapply (mem_u64_local _ M M' AG); [ | | | eassumption]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_frame_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_hooks_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_cst_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (st_at_local _ M M' AG); [ | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (strm_at_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE BUF]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (mem_arr_local _ M M' AG); [ | eassumption]; cbv [N_LENS N_CODES]; intros x Hx; lia_std
             | match goal with |- ?G => idtac "LOCSIDE" G end ].
Qed.
End FXG.
End S_Tok.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_Entry.S_Loop. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require Import S_Entry. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Uw. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_LeaveA. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Leave. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_Inflate. Import S_U2A. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S.S_U2C.S_U2B. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.I8S Require Import S_U2C. Import S_ZA. Import S_Tok.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Lemma sinv_rewin : forall u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc (zm : bool) osz w cin0 cout0 W0 ra st lf cf wh wn,
  sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz 0 cin0 cout0 W0 ra) st lf cf ->
  w <> 0 -> 0 <= wh -> wh <= WIN_SIZE -> 0 <= wn -> wn < WIN_SIZE -> (wh < WIN_SIZE -> wn = wh) ->
  sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz w cin0 cout0 W0 ra) (set_win st wh wn) lf cf.
Proof.
  intros u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz w cin0 cout0 W0 ra st lf cf wh wn (R & W & P & Mo) Hw H1 H2 H3 H4 H5.
  destruct st; unfold sinv, set_win, RNG, WIN, PROG, MODE, Wm, tables_live, ctable_live, cxc in *; cbn -[Z.add Z.mul Z.sub Z.pow] in *.
  split; [| split; [| split; [exact P | exact Mo]]].
  - destr_conj R. split_conj; try assumption; lia_std.
  - split; [intros E; exfalso; exact (Hw E) | intros _; split_conj; assumption].
Qed.

Lemma wok0 : forall p q n zc, DATA_LO + DATA_LEN <= zc -> wok p q n zc 0.
Proof.
  intros p q n zc Hz. unfold wok, ZSEP. cbv [WIN_SIZE]. cbv [DATA_LO DATA_LEN] in Hz.
  split_conj; try lia_std; try (left; reflexivity). reflexivity.
Qed.

Section ZB.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Variable zm : bool. Variable osz : Z.
Hypothesis HOSZ : if zm then osz = 0 else 1 <= osz /\ osz <= 262144.
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.
Variable w : Z.
Hypothesis Hw : wok p q n zc w.
Variables (site : bool) (cin0 cout0 W0 rv : Z) (st : ist) (lf cf : Z -> Z).
Hypothesis Hcin0 : 0 <= cin0 <= n.
Hypothesis Hcout0 : 0 <= cout0 <= osz.
Hypothesis SI : sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz 0 cin0 cout0 W0 (ra_site site)) st lf cf.
Hypothesis Hcc : cout0 < t_cout st.

Ltac lia_std ::= lia_std_stock.
Lemma ob_wr : forall M0, mem_wr R_segs M0 (u + -1024) 1232 -> mem_wr R_segs M0 (ob u zm) osz.
Proof.
  clear SI Hcc. intros M0 W. pose proof two64_eq as TW64. pose proof Hu0 as U0. pose proof Hzimg as UZ. generalize HOSZ. unfold ob.
  destruct zm; intros HO; cbv [BUF FRA DATA_LO DATA_LEN] in U0, UZ |- *.
  - eapply mem_wr_sub; [apply buf_writable | cbv [BUF]; lia_std | cbv [BUF BUF_N]; lia_std].
  - eapply mem_wr_sub; [apply buf_writable | cbv [BUF]; lia_std | cbv [BUF BUF_N]; lia_std].
Qed.
Ltac lia_std ::= lia_std_fast.
Local Ltac ob_open8 :=
  pose proof (ob_facts u p q n zc Hu0 Hzimg Hp0 Hp1 Hn0 Hqn Spq Spob Sobq zm osz HOSZ) as (Ob1 & Ob2 & Ob3 & Ob4 & Ob5 & Sobp & Sobq2 & Sobu & Sobw);
  pose proof (Sobw w Hw) as Sobw0; clear Sobw;
  cbv [STATE_SIZE FRA WIN_SIZE ROMHI_S] in Ob4, Ob5;
  assert (Sobs : ZSEP (ob u zm + osz <= u + -224 + -48 \/ u + -224 <= ob u zm)) by (clear - Sobu Ob2; unfold ZSEP in *; cbv [FRA] in Sobu; lia_std).

Local Ltac open_zb :=
  zkeysb; unfold L_UW_RET, L_RET, L_ZB, T_ZE1, T_ZE2, RA2 in *;
  cbv [STATE_SIZE FRA WIN_SIZE ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *;
  pose proof two64_eq as TW64.

Theorem zb_cps : forall Rb l M,
  zget_l Rb l kSP = u + -272 -> zget_l Rb l kA0 = w ->
  zget_l Rb l kS0 = ob u zm + t_cout st -> zget_l Rb l kS1 = t_out st - (osz - t_cout st) ->
  zget_l Rb l kS2 = 1 -> zget_l Rb l kS3 = p -> zget_l Rb l kS4 = t_out st - (osz - t_cout st) ->
  zget_l Rb l kS5 = n - cin0 -> zget_l Rb l kS6 = osz - t_cout st -> zget_l Rb l kS7 = t_hold st ->
  zget_l Rb l kS8 = t_bits st -> zget_l Rb l kS9 = t_out st -> zget_l Rb l kS11 = q + t_cin st ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  rom_ok M -> mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  (w <> 0 -> mem_wr R_segs M w WIN_SIZE) ->
  mem_arr 1 R_segs M q n fin ->
  tok_mem (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz 0 cin0 cout0 W0 (ra_site site)) st rv lf cf M ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M zm osz w ->
  KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M zm osz w ->
  realizes R_segs (zcfg R_segs L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M Lsp La0 Ls0 Ls1 Ls2 Ls3 Ls4 Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 Lgp Ltp ROM Wstk Wp Ww Hin TM HZE2 HZE1.
  pose proof Hw as Hw'. dand Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn.
  assert (RF : 0 <= cin /\ cin <= n /\ 0 <= cout /\ cout <= osz /\ osz - cout <= out /\ out <= osz /\ out - (osz - cout) <= cout).
  { clear -RNG_. unfold RNG, cxc in RNG_. icx_cbn. destr_conj RNG_. split_conj; assumption. }
  clear RNG_. dand RF as (Rci0 & Rci1 & Rco0 & Rco1 & Rou0 & Rou1 & Rou2).
  dand TM as (T1 & T2 & T3 & T4 & T5 & T6 & FRM & CST & HK & SAT & STRM & Hlens & Hcodes).
  unfold cxc in *. icx_cbn.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. unfold wsz in CST'. icx_cbn. cbn [Z.eqb] in CST'.
  dand CST' as (C64 & C88 & Cp0 & Cp16 & Cp48 & Cp56 & Cp60 & Cp72 & Cp7144).
  open_zb. ob_open8.
  destruct (mem_wr_arr_exists_R M (ob u zm) osz (ob_wr M Wstk) ltac:(lia_std) ltac:(lia_std) ltac:(rewrite ?two64_eq; lia_std)) as (fo & HOB & Hfo).
  assert (T1' : mem_u64 R_segs M (u + -224 + -8) 94036) by (replace (u + -224 + -8) with (u + -232) by lia_std; exact T1).
  assert (T2' : mem_u64 R_segs M (u + -224 + -16) p) by (replace (u + -224 + -16) with (u + -240) by lia_std; exact T2).
  assert (T3' : mem_u64 R_segs M (u + -224 + -24) rv) by (replace (u + -224 + -24) with (u + -248) by lia_std; exact T3).
  assert (T4' : mem_u64 R_segs M (u + -224 + -32) (n - cin)) by (replace (u + -224 + -32) with (u + -256) by lia_std; exact T4).
  assert (T5' : mem_u64 R_segs M (u + -224 + -40) (osz - cout)) by (replace (u + -224 + -40) with (u + -264) by lia_std; exact T5).
  assert (T6' : mem_u64 R_segs M (u + -224 + -48) (out - (osz - cout))) by (replace (u + -224 + -48) with (u + -272) by lia_std; exact T6).
  clear T1 T2 T3 T4 T5 T6.
  eapply (uw_resume_s MEMCPY Rb l M MD T p (ob u zm) osz w cout (out - (osz - cout)) (u + -224) 94036
            p rv (n - cin) (osz - cout) (out - (osz - cout)) zc fo Hh).
  all: lazymatch goal with
       | |- forall R' M', w = 0 -> _ => idtac
       | |- forall R' M' whave' wnext', _ => idtac
       | |- ZSEP _ => first [ assumption | exact Sobs | exact Sobp | exact Sobw0 | unfold ZSEP; lia_std ]
       | |- mem_u64 _ _ _ _ => assumption
       | |- mem_u32 _ _ _ _ => assumption
       | |- mem_arr _ _ _ _ _ _ => exact HOB
       | |- mem_wr _ _ _ _ => first [ assumption | eapply mem_wr_sub; [exact Wstk | lia_std | lia_std] ]
       | |- _ -> mem_wr _ _ _ _ => exact Ww
       | |- forall i, _ -> _ => intros i _; apply Hfo
       | |- _ => first [ zreg | assumption | reflexivity | lia_std
                       | match goal with |- ?G => idtac "UWSIDE" G end ]
       end.
  -
    intros R' M' Wz. intros. zimps. zkeys.
    clear SAT STRM Hlens Hcodes HOB Hfo CST Cp60 Cp72 T1' T2' T3' T4' T5' T6'.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom zm osz HOSZ
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 0 cin0 cout0 W0 (ra_site site) (wok0 p q n zc Hzimg) Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX0.
    pose proof CX0 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    match goal with HP : mpostL R_segs M M' _ |- _ =>
      pose proof HP as HPw; zreattachL HP end.
    clear SEP.
    pose proof (mpostL_stable R_segs M [(u + -1024, 1024); (u, 112); (p, 7176); (ob u zm, osz)] ltac:(ranges_ok_tac)) as HST.
    assert (HAG : framed (fun X => mpostL R_segs M X [(u + -1024, 1024); (u, 112); (p, 7176); (ob u zm, osz)]) M').
    { eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M _) HPw).
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac. }
    clear HPw.
    pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
    dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & _ & _ & Q72 & _).
    rewrite Wz in *.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (ret_s _ R9 [] Mx MD T (-4) CX0 Hh) end.
    + unfold s_regs_ret, cxc, Kra; icx_cbn; zkeys; cbn [Pos.eqb]; split_conj; zreg.
    + exact FRM.
    + intros R9 HB.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        eapply (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 Hn0 Hqn Spq Spob Sobq zm osz HOSZ 0 (wok0 p q n zc Hzimg) HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl R_segs M (fp_u2 u p zm osz 0)) R9 Mx (-4) 16210) end.
      * cbv. discriminate.
      * exact HB.
      * unfold s_std, i_cst, wsz, cxc; icx_cbn; cbn [Z.eqb]; split_conj; try assumption.
        all: first [ apply ob_wr; assumption | intros i Hi; exfalso; lia_std | match goal with |- ?G => idtac "STDSIDE" G end ].
      * unfold cxc; icx_cbn. assumption.
      * unfold reach; cbv [HEAD DICTID MEM]; lia_std.
      * unfold fp_call, fp_loop, wsz, cxc; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE]; cbn [Z.eqb app].
        eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M _) HAG).
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac.
  -
    intros R' M' whave' wnext' Wnz. intros. zimps. zkeys.
    specialize (Ww Wnz).
    pose proof SAT as SAT'. destruct SAT' as [Hmode SREST']. unfold st_rest, cxc in SREST'. icx_cbn. destr_conj SREST'. clear SAT.
    unfold cxc in Hmode; icx_cbn.
    clear Cp60 Cp72 CST HOB Hfo T1' T2' T3' T4' T5' T6'.
    repeat match goal with
           | H : mem_u32 R_segs M (p + 76) _ |- _ => clear H
           | H : mem_u32 R_segs M (p + 80) _ |- _ => clear H
           end.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom zm osz HOSZ
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 w cin0 cout0 W0 (ra_site site) Hw Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX1.
    pose proof CX1 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    lazymatch goal with HP : mpostL R_segs M M' ?rs |- _ =>
      pose proof HP as HPw; unfold uw_res_fp in HP; cbv [WIN_SIZE] in HP;
      lazymatch type of HP with mpostL _ _ _ ?rs' =>
        apply (mem_arr_magreeL R_segs 1 M M' rs' q n fin (proj1 HP)) in Hin;
        [| pose proof Spq as D1; pose proof W5 as D2; unfold ZSEP in D1, D2; clear SEP;
           zconj_norm; repeat split; first [ exact I | lia_std ] ]
      end;
      zreattachL HP end.
    clear SEP.
    assert (HZW : KZW u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc zm osz w) by (unfold KZW; intros; exfalso; lia_std).
    assert (OBLOW1 : c_ob (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz w cin0 cout0 W0 (ra_site site)) + c_osz (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz w cin0 cout0 W0 (ra_site site))
                  <= c_u (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz w cin0 cout0 W0 (ra_site site)) - FRA \/ c_u (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz w cin0 cout0 W0 (ra_site site)) + 7 <= c_ob (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc zm osz w cin0 cout0 W0 (ra_site site))).
    { clear - Sobu. unfold ZSEP in Sobu. unfold cxc; icx_cbn; exact Sobu. }
    pose proof (pcall_all u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
                  Spq Spob Sobq Sprom zm osz HOSZ Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
                  A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
                  A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH w Hw HZE2 HZE1 HZW) as PC.
    pose proof (u2_krl u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 Hn0 Hn1 Hqn Spq Spob Sobq zm osz HOSZ w Hw HZE2 HZE1
                  _ (PC _) site cin0 cout0 W0 M Hcin0 Hcout0 (Z.le_refl _) (mpostL_refl R_segs M (fp_u2 u p zm osz w))) as HKRL.
    pose proof (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 Hn0 Hqn Spq Spob Sobq zm osz HOSZ w Hw HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl R_segs M (fp_u2 u p zm osz w))) as HKRX.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_uwret_s _ fin MD T M CX1 Hh HKRL HKRX R9 [] Mx
                (set_win (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) whave' wnext')
                rv 0 lf cf) end.
    all: first [ eapply sinv_rewin; [exact SI | exact Wnz | assumption ..]
               | unfold cxc; icx_cbn; zreg
               | unfold set_win, cxc; icx_cbn; zreg
               | left; reflexivity
               | unfold s_std, i_cst, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [WIN_SIZE]; split_conj;
                 first [ assumption | apply ob_wr; assumption | match goal with |- ?G => idtac "STDSIDE1" G end ]
               | unfold st_at, st_rest, set_win, cxc; icx_cbn; split_conj; assumption
               | unfold strm_at, set_win, cxc; icx_cbn; unfold strm_at, cxc in STRM; icx_cbn; exact STRM
               | assumption
               | unfold fp_call, fp_loop, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE]; cbn [app];
                 eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M _) HPw);
                 intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold uw_res_fp; cbv [WIN_SIZE]; ranges_within_tac
               | match goal with |- ?G => idtac "LVSIDE" G end ].
Qed.
End ZB.
End FXG.
