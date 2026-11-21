(* reloc-zl14c *)
(* (uncompress 1.4 UBSan): the za walk is new code at 1.4, the plain build's I7SW/S_ZAw.v
   za_prefix_s moved to the UBSan image. inflateInit_ (from the zalloc return, 0x1520c) memsets the WHOLE state
   (memset(p, 0, 7176), TMemsetOk.memset7176_ok; the size rides in s1 over the zalloc call), checks the state's
   alignment (UBSan), stores strm->state / state->strm / mode, wrap 5 and wbits 15, then calls the one 1.4
   inflateReset (0x15018; with its UBSan alignment checks; window unchanged, keep-reset inline); inflateInit_ returns
   0 to uncompress2_z (0x14e94), which sets next_out = BUF, avail_out = BUF_N, avail_in = n (len and left fall to 0,
   s2 = max) and reaches the first inflate call (0x14f04). The fields memset leaves zero are handed on as 0.
   uncompress2_z keeps s0 .. s4 (destLen, sourceLen, dest / max, len, left); s5 .. s11 ride through. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* (uncompress 1.4 UBSan): the za walk is new code at 1.4, the plain build's I7SW/S_ZAw.v
   za_prefix_s moved to the UBSan image. inflateInit_ (from the zalloc return, 0x15150) memsets the WHOLE state
   (memset(p, 0, 7176), TMemsetOk.memset7176_ok; the size rides in s1 over the zalloc call), checks the state's
   alignment (UBSan), stores strm->state / state->strm / mode, wrap 5 and wbits 15, then calls the one 1.4
   inflateReset (0x14f5c; with its UBSan alignment checks; window unchanged, keep-reset inline); inflateInit_ returns
   0 to uncompress2_z (0x14dfc), which sets next_out = BUF, avail_out = BUF_N, avail_in = n (len and left fall to 0,
   s2 = max) and reaches the first inflate call (0x14e6c). The fields memset leaves zero are handed on as 0.
   uncompress2_z keeps s0 .. s4 (destLen, sourceLen, dest / max, len, left); s5 .. s11 ride through. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U Require Import TBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U Require TMemsetOk.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_ZA : Z := 86492.              (* 0x15150: inflateInit_ after jalr zalloc *)
Definition L_CALL2 : Z := 85716.           (* 0x14e6c: uncompress2_z, mv a0,sp before the first jal inflate *)
Definition RA_II : Z := 85604.             (* 0x14dfc: uncompress2_z after jal inflateInit_ *)

(* generalize the value just written to the head register *)
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.

(* a u32 fact read back at an equal-mod-2^32 literal *)
Lemma mem_u32_relit {RCa1 : RunCtx}  : forall M a e e', mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> e mod 4294967296 = e' mod 4294967296 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e'.
Proof.
  intros M a e e' H E. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

(* a u32 / u64 zero inside a memset region *)
Lemma mz_u32 {RCa1 : RunCtx}  : forall M a len off, mem_zero (run_segments R_segs rc_inp rc_sp rc_mb) M a len -> 0 <= off -> off + 4 <= len -> 0 <= a + off ->
  a + off + 4 <= two64 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u32, mem_is. change (length (Z_to_le_bytes 4 0)) with 4%nat.
  rewrite (mem_zero_sub (run_segments R_segs rc_inp rc_sp rc_mb) M a len off 4 Hz) by lia. reflexivity.
Qed.
Lemma mz_u64 {RCa1 : RunCtx}  : forall M a len off, mem_zero (run_segments R_segs rc_inp rc_sp rc_mb) M a len -> 0 <= off -> off + 8 <= len -> 0 <= a + off ->
  a + off + 8 <= two64 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u64, mem_is. change (length (Z_to_le_bytes 8 0)) with 8%nat.
  rewrite (mem_zero_sub (run_segments R_segs rc_inp rc_sp rc_mb) M a len off 8 Hz) by lia. reflexivity.
Qed.

(* split the u64 fact at a (on the current memory) into its two u32 halves *)
Ltac split64 a ahi nlo nhi :=
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mx a _ |- _ =>
      pose proof (mem_u64_lo32 _ _ _ _ H) as nlo; pose proof (mem_u64_hi32 _ _ _ _ H) as nhi; cbn in nhi;
      replace (a + 4) with ahi in nhi by lia
    end
  end.

Theorem za_prefix_t {RCa1 : RunCtx}  : forall Rb l M MD T (u p q n zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS2 = u -> zget_l Rb l kS1 = 7176 -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = 262144 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + 208 <= 140737488355328 -> u mod 16 = 0 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= zc ->
  ZSEP (p + STATE_SIZE <= q \/ q + n <= p) -> ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_T <= p) ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -32) BUF -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -24) (u + 168) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -16) (u + 176) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA_II ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M u q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) 0 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  (forall R' M' (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z),
     zget R' kSP = u ->
     zget R' kS0 = u + 176 -> zget R' kS1 = u + 168 -> zget R' kS2 = 4294967295 -> zget R' kS3 = 0 -> zget R' kS4 = 0 ->
     zget R' kS5 = s5 -> zget R' kGP = gp -> zget R' kTP = tp ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     rom_ok M' -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p STATE_SIZE -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' u q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 8) n -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 24) BUF -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 32) 262144 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' p u -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 8) HEAD -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 12) 0 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 16) 5 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 28) (-1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 56) 0 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) 0 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) 0 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) 0 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 96) 0 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 104) 0 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 108) vlen -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 112) vofs -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 116) vext ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 120) (p + 1384) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 128) (p + 1384) ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 136) vlb -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 140) vdb ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 144) vnc -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 148) vnl -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 152) vnd -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 156) vsh ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 160) (p + 1384) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 7160) 1 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 7164) 4294967295 ->
     0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
     0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + -80, 48); (u, 112); (p, STATE_SIZE)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CALL2 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin
         Hh Lsp Ls2 Ls1 La0 Ls3 Ls4 Lgp Ltp Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Sprom
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 K.
  zkeysb. unfold L_ZA, L_CALL2, RA_II in *. cbv [STATE_SIZE FRA ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF HEAD DATA_LO DATA_LEN] in *.
  pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(u + -80, 48); (u, 112); (p, 7176)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(u + -80, 48); (u, 112); (p, 7176)]) M) by (apply mpostL_refl).
  (* inflateInit_ after zalloc: the state pointer is not NULL; memset(p, 0, 7176) *)
  zbr Rfd false.                      (* 15150 beqz a0 *)
  zstep Rfd.                          (* 15154 mv s0,a0 *)
  zstep Rfd.                          (* 15158 li a1,0 *)
  zstep Rfd.                          (* 1515c mv a2,s1 *)
  zstep Rfd.                          (* 15160 jal memset *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc) ?Mx _) _ =>
    eapply (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U.TMemsetOk.memset7176_ok R lc Mx MD T p 86512 Hh) end.
  - zreg. - zreg. - zreg. - zreg. - reflexivity.
  - eapply mem_wr_sub; [exact Wp | lia | lia].
  - lia. - lia.
  - Z.to_euclidean_division_equations; lia.
  - intros M1 R1 HP HZ HW1 E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
    zimps. apply mpost_mpostL1 in HP. zreattachL HP.
    (* the fields memset leaves zero and nothing below stores over *)
    pose proof (mz_u64 M1 p 7176 88 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z88.
    pose proof (mz_u32 M1 p 7176 108 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z108.
    pose proof (mz_u32 M1 p 7176 112 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z112.
    pose proof (mz_u32 M1 p 7176 116 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z116.
    pose proof (mz_u32 M1 p 7176 136 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z136.
    pose proof (mz_u32 M1 p 7176 140 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z140.
    pose proof (mz_u32 M1 p 7176 144 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z144.
    pose proof (mz_u32 M1 p 7176 148 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z148.
    pose proof (mz_u32 M1 p 7176 152 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z152.
    pose proof (mz_u32 M1 p 7176 156 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z156.
    clear HZ.
    (* back in inflateInit_: the UBSan alignment check, strm->state, state->strm, mode = HEAD; wrap 5, wbits 15 *)
    zstep Rfd. zalign.                (* 15164 and a0,s0,7 *)
    zstep Rfd.                        (* 15168 sd s0,56(s2) *)
    zbr Rfd false.                    (* 1516c bnez a0 *)
    zstep Rfd.                        (* 15170 mv a1,s2 *)
    zstep Rfd.                        (* 15174 ld a0,64(s2) *)
    tstep1 Rfd.                       (* 15178 lui a2,0x4 *)
    zstep Rfd.                        (* 1517c addi a2,a2,-204 *)
    zstep Rfd.                        (* 15180 sd s2,0(s0) *)
    zstep Rfd.                        (* 15184 sw a2,8(s0) *)
    zbr Rfd false.                    (* 15188 beqz a0 *)
    zstep Rfd.                        (* 1518c li a0,5 *)
    zstep Rfd.                        (* 15190 li a2,15 *)
    tstep1 Rfd.                       (* 15194 slli a0,a0,32 *)
    tstep1 Rfd.                       (* 15198 slli a2,a2,32 *)
    zstep Rfd.                        (* 1519c addi a0,a0,5 *)
    zstep Rfd.                        (* 151a0 addi a2,a2,15 *)
    zstep Rfd.                        (* 151a4 sd a0,16(s0) *)
    zstep Rfd.                        (* 151a8 sd a2,64(s0) *)
    split64 (p + 16) (p + 20) W16 W20. split64 (p + 64) (p + 68) W64 W68.
    zstep Rfd.                        (* 151ac mv a0,a1 *)
    zstep Rfd.                        (* 151b0 jal inflateReset *)
    (* inflateReset (0x14f5c): frame 32; the strm / state checks with UBSan's alignment traps *)
    zstep Rfd.                        (* 14f5c addi sp,sp,-32 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* sd ra, s0, s1, s2 *)
    zstep Rfd.                        (* 14f70 mv s0,a0 *)
    zstep Rfd.                        (* 14f74 li a0,-2 *)
    zbr Rfd false.                    (* 14f78 beqz s0 *)
    zstep Rfd. zalign.                (* 14f7c and a1,s0,7 *)
    zbr Rfd false.                    (* 14f80 bnez a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a1,64(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a2,72(s0); beqz a2 *)
    zstep Rfd. zbr Rfd false.         (* ld s2,56(s0); beqz s2 *)
    zstep Rfd. zalign.                (* 14f9c and a1,s2,7 *)
    zbr Rfd false.                    (* 14fa0 bnez a1 *)
    zstep Rfd. zbr Rfd true.          (* ld a1,0(s2); beq a1,s0 *)
    zstep Rfd.                        (* 14fc4 lw a1,8(s2) *)
    tstep1 Rfd.                       (* 14fc8 lui a3,0xffffc *)
    zstep Rfd.                        (* 14fcc addi s1,a3,204 *)
    zstep Rfd.                        (* 14fd0 addw a1,a1,s1 *)
    zstep Rfd.                        (* 14fd4 li a3,31 *)
    zbr Rfd false.                    (* 14fd8 bltu a3,a1 *)
    zstep Rfd.                        (* 14fdc lw a3,64(s2) *)
    zstep Rfd.                        (* 14fe0 lw a1,68(s2) *)
    zbr Rfd true.                     (* 14fe4 beq a1,a3: the window size is unchanged *)
    zstep Rfd.                        (* 15008 lw a1,20(s2) *)
    zstep Rfd.                        (* 1500c sd zero,72(s2) *)
    zstep Rfd.                        (* 15010 ld a2,64(s0) *)
    zstep Rfd.                        (* 15014 sw a1,16(s2) *)
    zstep Rfd.                        (* 15018 sw zero,80(s2) *)
    (* the keep-reset part, inline *)
    zbr Rfd false.                    (* 1501c beqz a2 *)
    zstep Rfd. zbr Rfd false.         (* ld a1,72(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a1,56(s0); beqz a1 *)
    zstep Rfd. zalign.                (* 15030 and a2,a1,7 *)
    zbr Rfd false.                    (* 15034 bnez a2 *)
    zstep Rfd. zbr Rfd false.         (* ld a2,0(a1); bne a2,s0 *)
    zstep Rfd.                        (* 15040 lw a2,8(a1) *)
    zstep Rfd.                        (* 15044 addw a2,a2,s1 *)
    zstep Rfd.                        (* 15048 li a3,31 *)
    zbr Rfd false.                    (* 1504c bltu a3,a2 *)
    tstep1 Rfd.                       (* 15050 lui a2,0x2 *)
    zstep Rfd.                        (* 15054 sd zero,48(a1) *)
    zstep Rfd.                        (* 15058 lwu a0,16(a1) *)
    zstep Rfd.                        (* 1505c addiw a2,a2,-1032 *)
    zstep Rfd.                        (* 15060 add a2,a1,a2 *)
    zstep Rfd.                        (* 15064 sd zero,16(s0) *)
    zstep Rfd.                        (* 15068 sd zero,40(s0) *)
    zstep Rfd.                        (* 1506c sd zero,48(s0) *)
    zstep Rfd.                        (* 15070 sw zero,88(s0) *)
    zbr Rfd false.                    (* 15074 beqz a0 *)
    zstep Rfd.                        (* 15078 andi a0,a0,1 *)
    zstep Rfd.                        (* 1507c sd a0,96(s0) *)
    zstep Rfd.                        (* 15080 li a0,0 *)
    tstep1 Rfd.                       (* 15084 lui a3,0x4 *)
    zstep Rfd.                        (* 15088 li a4,-1 *)
    zstep Rfd.                        (* 1508c addi a5,a1,1384 *)
    zstep Rfd.                        (* 15090 sd a5,160(a1) *)
    zstep Rfd.                        (* 15094 sd zero,96(a1) *)
    zstep Rfd.                        (* 15098 sw zero,104(a1) *)
    zstep Rfd.                        (* 1509c sd a5,120(a1) *)
    zstep Rfd.                        (* 150a0 sd a5,128(a1) *)
    tstep1 Rfd.                       (* 150a4 lui a5,0x8 *)
    zstep Rfd.                        (* 150a8 addiw a3,a3,-204 *)
    tstep1 Rfd.                       (* 150ac slli a4,a4,32 *)
    zstep Rfd.                        (* 150b0 sd a3,8(a1) *)
    zstep Rfd.                        (* 150b4 sd a4,24(a1) *)
    zstep Rfd.                        (* 150b8 sw a5,32(a1) *)
    zstep Rfd.                        (* 150bc sd zero,56(a1) *)
    zstep Rfd.                        (* 150c0 addi a4,a4,1 *)
    zstep Rfd.                        (* 150c4 sd a4,0(a2) *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra, s0, s1, s2 *)
    zstep Rfd.                        (* 150d8 addi sp,sp,32 *)
    zret Rfd.                         (* 150dc ret *)
    (* inflateInit_ returns Z_OK *)
    zbr Rfd true.                     (* 151b4 beqz a0 *)
    zstep Rfd.                        (* 15224 li a3,0 *)
    zstep Rfd.                        (* 15228 mv a0,a3 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra, s0, s1, s2 *)
    zstep Rfd.                        (* 1523c addi sp,sp,32 *)
    zret Rfd.                         (* 15240 ret *)
    (* uncompress2_z: next_out = BUF, avail_out = 0, max = 2^32 - 1; the first refills *)
    zbr Rfd false.                    (* 14dfc bnez a0 *)
    zstep Rfd.                        (* 14e00 or a0,s2,s4 *)
    zbr Rfd true.                     (* 14e04 bnez a0 *)
    zstep Rfd.                        (* 14e0c sd s2,24(sp) *)
    zstep Rfd.                        (* 14e10 sw zero,32(sp) *)
    zstep Rfd.                        (* 14e14 li a1,-1 *)
    tstep1 Rfd.                       (* 14e18 srli s2,a1,32 *)
    zbr Rfd true.                     (* 14e1c beqz zero *)
    zstep Rfd.                        (* 14e3c mv a0,s4 *)
    zbr Rfd true.                     (* 14e40 bltu s4,s2 *)
    zstep Rfd.                        (* 14e48 sw a0,32(sp) *)
    zstep Rfd.                        (* 14e4c sub s4,s4,a0 *)
    zstep Rfd.                        (* 14e50 lw a0,8(sp) *)
    zbr Rfd false.                    (* 14e54 bnez a0 *)
    zstep Rfd.                        (* 14e58 mv a0,s3 *)
    zbr Rfd true.                     (* 14e5c bltu s3,s2 *)
    zstep Rfd.                        (* 14e64 sw a0,8(sp) *)
    zstep Rfd.                        (* 14e68 sub s3,s3,a0 *)
    (* at L_CALL2: the K facts *)
    split64 (p + 8) (p + 12) C8 C12. split64 (p + 24) (p + 28) C24 C28. split64 (p + 72) (p + 76) C72 C76.
    split64 (p + 7160) (p + 7164) C7160 C7164.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (K R' Mx 0 0 0 0 0 0 0 0 0) end;
      first [ zreg | assumption | exact HAG | lia
            | lazymatch goal with |- mem_u32 _ _ _ _ => idtac | |- mem_u64 _ _ _ _ => idtac end;
              match goal with H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H
                                       | (eapply (mem_u32_relit _ _ _ _ H); reflexivity)]
                            | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H] end
            | match goal with |- ?G => idtac "KSIDE" G end ].
Qed.
