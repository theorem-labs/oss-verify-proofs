(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require ITree Nodes Decode SysStep RegsEquiv Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Decode OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.SysStep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim StrFun Stdio.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_memset F_memcpy Startup_glue.

Module Startup_B.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require ITree Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
Export OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac.Layout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_memset F_memcpy Startup_glue Rnd.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Notation psegs := Image.psegs.

Ltac sfinish :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.


Definition memsetZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Lemma memset_specZ : forall (A n c : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells psegs m A [CB (Z.to_nat n) junk] ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  (0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
  evt psegs (memsetZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x27930) fc None m (seg_rom psegs)).
Proof.
  intros until junk. intros DST MI -> -> -> Hc Hn Hl.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
  intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.

Definition memcpyZ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' A [CB (Z.to_nat n) src]
    /\ bytes_at psegs m' S src.

Lemma memcpy_specZ : forall (A S n : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at psegs m S src ->
  length src = Z.to_nat n ->
  rw_cells psegs m A [CB (Z.to_nat n) junk] ->
  (S + n <= A \/ A + n <= S)%Z ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  (0 <= n < 2^64)%Z -> (A < 2^64)%Z -> (S < 2^64)%Z ->
  evt psegs (memcpyZ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A S n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2752c) fc None m (seg_rom psegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI -> -> -> Hn HA HS.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec; [| | | | exact MI]; rewrite ?EA, ?ES, ?En; [exact SRC | exact LEN | exact DST | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite EA, ES, En in PO. exact PO.
Qed.

Definition init_ssp_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo R : Z) (g : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x5a700); (0x3a480, 0x3a488)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' RGUARD [C8 (guard_of g)]
    /\ rw_cells psegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
    /\ rw_cells psegs m' RTD (rtd_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 (guard_of g) x10 x11)
    /\ bytes_at psegs m' R (le8 g).

Lemma init_ssp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo R : Z) (g : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 : word) (junk : list byte),
  stk psegs m lo (bv_unsigned sp) ->
  bytes_at psegs m R (le8 g) ->
  rw_cells psegs m RGUARD [CB 8 junk] ->
  rw_cells psegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
  rw_cells psegs m RTD (td_cells x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11) ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 R ->
  (lo <= bv_unsigned sp - 16)%Z -> (0x5b000 <= lo)%Z -> (bv_unsigned sp <= R)%Z ->
  evt psegs (init_ssp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R g x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2046c) fc None m (seg_rom psegs)).
Proof.
  intros until junk. intros ST RND GU GG TDC MI -> -> LO LOLO SPR.
  unfold td_cells in TDC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0x5a700); (0x3a480, 0x3a488)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
  carve_frame 16%nat ST.
  lstep. lstep. lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  do 4 lstep.
  lstep. call (memcpy_specZ RGUARD R 8); [exact RND | reflexivity | exact GU | lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
  rename PC into GU. clear RND. rename POST into RND. change (Z.to_nat 8) with 8%nat in GU. try rename MI0 into MI.
  lstep. lstep. lstep. lstep.
  apply (rw_cells_recast psegs _ _ _ [C8 (guard_of g)]) in GU;
    [| cbn; repeat split; exact I | cbn [cells_bytes cbytes]; rewrite !app_nil_r, le8_guard_of; reflexivity | reflexivity].
  lstep. lstep. lstep.
  do 2 lstep. release_frame FR ST (bv_unsigned sp). lstep.
  unfold init_ssp_post, rtd_cells. sfinish.
Qed.


Definition auxv20 (rnd uid hw : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10;
   Z_to_bv 64 16; hw; Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
   Z_to_bv 64 25; rnd; z64; z64].

(* the auxv
   [StackLayout.auxv_entries] lays at 727298f3 for this image: ARCH_DLINFO's ten entries, [create_elf_tables]'
   sixteen, the CONFIG_RSEQ pair when the launch's kernel has it, and AT_NULL.  Keys and the image's own PhdrInfo
   are literal; every other value is the launch's. *)
Definition pauxv (la : LaunchAuxv) (hw ent uid gid rnd efn : word) : list word :=
  [Z_to_bv 64 33; la_sysinfo_ehdr la;
   Z_to_bv 64 40; cw_l1i_size (la_cache la); Z_to_bv 64 41; cw_l1i_geom (la_cache la);
   Z_to_bv 64 42; cw_l1d_size (la_cache la); Z_to_bv 64 43; cw_l1d_geom (la_cache la);
   Z_to_bv 64 44; cw_l2_size (la_cache la); Z_to_bv 64 45; cw_l2_geom (la_cache la);
   Z_to_bv 64 46; cw_l3_size (la_cache la); Z_to_bv 64 47; cw_l3_geom (la_cache la);
   Z_to_bv 64 51; la_minsigstksz la;
   Z_to_bv 64 16; hw; Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 17; Z_to_bv 64 100;
   Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10;
   Z_to_bv 64 7; z64; Z_to_bv 64 8; z64; Z_to_bv 64 9; ent;
   Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 13; gid; Z_to_bv 64 14; gid;
   Z_to_bv 64 23; z64; Z_to_bv 64 25; rnd; Z_to_bv 64 31; efn]
  ++ (if la_rseq la then [Z_to_bv 64 27; Z_to_bv 64 28; Z_to_bv 64 28; Z_to_bv 64 32] else [])
  ++ [z64; z64].

Lemma pauxv_length : forall la hw ent uid gid rnd efn,
  length (pauxv la hw ent uid gid rnd efn) = (2 * auxv_count (la_rseq la))%nat.
Proof. intros. unfold pauxv. destruct (la_rseq la); reflexivity. Qed.

Lemma pauxv_auxv_words : forall la ent sp top argv envp execfn uid gid hw,
  auxv_words la Src_zlib_example_small_fuzzer_repro.M.phdrs ent sp top argv envp execfn uid gid hw
  = pauxv la hw ent uid gid (Z_to_bv 64 (rnd_addr (la_rseq la) sp argv envp)) (Z_to_bv 64 (xfn_base top argv envp execfn)).
Proof. intros. unfold auxv_words, auxv_entries, pauxv. destruct (la_rseq la); reflexivity. Qed.

Lemma envp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at psegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt psegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1fb88) fc None m (seg_rom psegs)) ->
  evt psegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1fb7c) fc None m (seg_rom psegs)).
Proof.
  induction ws as [|w ws IH]; intros until rest; intros NZ B HQ.
  - cbn [u64s app] in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite app_length, length_le8 in BB.
    pose proof (rd_u64 psegs m A z64 rest (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    cbn [length Z.of_nat] in HQ. exact_evt HQ.
  - cbn [u64s app] in B. rewrite <- app_assoc in B.
    pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite !app_length, !length_le8 in BB.
    apply Forall_cons_iff in NZ. destruct NZ as [NZw NZ].
    pose proof (rd_u64 psegs m A w _ (Z_to_bv 64 A) B eq_refl) as RD.
    zstep. clear RD. zstep. zstep. if_true.
    apply bytes_at_app in B. destruct B as [_ B]. rewrite length_le8 in B.
    eapply (IH Q); [exact NZ | exact B |].
    cbn [length] in HQ. exact_evt HQ.
Qed.
End Startup_B.


Module Startup_A.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require ITree Nodes Decode SysStep RegsEquiv Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Decode OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.SysStep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac Startup_glue.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup.Startup_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Local Open Scope bv_scope.
Import ITree.Exc.

Notation psegs := Image.psegs.


Definition init_tls_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (sysinfo auxvp page_size : word) (m : word -> option byte) (t : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x3a3c8, 0x5a498); (0x5a4a0, 0x5a4d0); (RLIBC, 0x5a780)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' RTD (td_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) sysinfo (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x3a440) (Z_to_bv 64 0x5a750) (Z_to_bv 64 0x3a4a0) z64)
    /\ rw_cells psegs m' RLIBC (libc_cells (Z_to_bv 8 1) auxvp (Z_to_bv 64 224) (Z_to_bv 64 8) page_size)
    /\ rw_cells psegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells psegs m' RSYSINFO [C8 sysinfo]
    /\ rw_cells psegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells psegs m' RGOT_DYNAMIC [C8 z64]
    /\ (0 < t < 4194304)%Z.

Lemma init_tls_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sysinfo page_size auxvp : word),
  stk psegs m lo (bv_unsigned sp) ->
  rw_cells psegs m (bv_unsigned a0 + 24) [C8 (Z_to_bv 64 0x10040); C8 (Z_to_bv 64 56); C8 (Z_to_bv 64 10)] ->
  rw_cells psegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
  rw_cells psegs m RLIBC (libc_cells (Z_to_bv 8 0) auxvp z64 z64 page_size) ->
  rw_cells psegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
  rw_cells psegs m RSYSINFO [C8 sysinfo] ->
  rw_cells psegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
  rw_cells psegs m RGOT_DYNAMIC [C8 z64] ->
  mem_inv psegs m ->
  (lo <= bv_unsigned sp - 64)%Z -> (0x5b000 <= lo)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned a0 + 48 <= 2^64)%Z ->
  impl psegs (at_node psegs) (enode NSetTid dec_set_tid)
       (epost (init_tls_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo sysinfo auxvp page_size m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1fe64) fc None m (seg_rom psegs)).
Proof.
  intros until auxvp. intros ST AUX TDC LC MT SI DS GD MI LO LOLO A0LO A0HI.
  unfold td_cells, libc_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x3a3c8, 0x5a498); (0x5a4a0, 0x5a4d0); (RLIBC, 0x5a780)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  apply impl_enode.
  carve_frame 64%nat ST.
  steps_to 0x1ff3c%Z.
  steps_to 0x200c0%Z.
  step_ecall.
  split. { at_node_solve. }
  intros rsp t Hdec. apply dec_set_tid_Some in Hdec. destruct Hdec as [-> Ht].
  unfold eff0. sys_nret.
  steps_to 0x20110%Z.
  release_frame FR ST (bv_unsigned sp). astep.
  unfold init_tls_post, td_cells, libc_cells. unfold PID_MAX_ENVELOPE in Ht; cbn in Ht. sys_finish; lia.
Qed.

End Startup_A.


Module Startup_C.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Cells.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require ITree Nodes Decode SysStep RegsEquiv Image.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Arr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Cells.Bytes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.ITree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Nodes OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Decode OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.SysStep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.RegsEquiv OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Image.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import StrFun.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Str_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_memset F_memcpy Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Rnd.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup.Startup_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup.Startup_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call psegs m mm MU WM end end.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Local Open Scope bv_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].

Notation psegs := Image.psegs.


Section InitLibc.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (R : Z) (g : word) (uid hw : word) (P : Z) (s : list byte)
            (pn0 pnf0 hw0 env0 : word) (gjunk : list byte)
            (la : LaunchAuxv) (ent gid efn : word).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x5a498); (0x3a3c8, 0x5a498); (0x5a4a0, 0x5a4d0);
                 (RGUARD, 0x5a700); (RPROGNAME, 0x5a718); (RLIBC, 0x5a788)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition init_libc_post : Z -> machine_state -> Prop :=
    fun t ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pg m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' RTD (rtd_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 t) z64 (Z_to_bv 64 2)
                                (Z_to_bv 64 0x3a440) (Z_to_bv 64 0x5a750) (guard_of g) (Z_to_bv 64 0x3a4a0) z64)
    /\ rw_cells psegs m' RLIBC (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
    /\ rw_cells psegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells psegs m' RSYSINFO [C8 z64]
    /\ rw_cells psegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
    /\ rw_cells psegs m' RHWCAP [C8 hw]
    /\ rw_cells psegs m' RENVIRON [C8 (Z_to_bv 64 E)]
    /\ rw_cells psegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells psegs m' RGUARD [C8 (guard_of g)]
    /\ rw_cells psegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x5a710); C8 (Z_to_bv 64 RPROGNAME)]
    /\ rw_cells psegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
    /\ rw_cells psegs m' RGOT_DYNAMIC [C8 z64]
    /\ bytes_at psegs m' E (u64s eps ++ le8 z64 ++ u64s (pauxv la hw ent uid gid (Z_to_bv 64 R) efn))
    /\ bytes_at psegs m' P (s ++ [Z_to_bv 8 0])
    /\ bytes_at psegs m' R (le8 g)
    /\ (0 < t < 4194304)%Z.

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x5b000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  Definition pn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists pg m',
    ms' = MS (mkR (Z_to_bv 64 0x1fb70) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
                  (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47) z64 x14 x15 x16 x17
                  (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x1fc4c) fc None m' (seg_rom psegs)
    /\ munch [(RPROGNAME, 0x5a710)]%Z m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  Lemma pn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(RPROGNAME, 0x5a710)]%Z m0 mm -> wmono psegs m0 mm -> mem_inv psegs mm ->
    bytes_at psegs mm P (s ++ [Z_to_bv 8 0]) ->
    rw_cells psegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt psegs (pn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x1fb70) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1fc40) fc None mm (seg_rom psegs)).
  Proof.
    induction k as [|k IH]; intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg Hk Hj MU WM MI STR G2.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length s)%nat with 0%nat by lia. reflexivity. }
      pose proof (u8ro_read psegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_false. zstep. if_false.
      replace (Z_to_bv 64 (P + j)) with (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) by (f_equal; lia).
      unfold pn_post. finish2. all: eassumption.
    - pose proof (bytes_at_bound _ _ _ _ STR) as BB. rewrite app_length in BB. cbn [length] in BB.
      destruct (nth_error s (Z.to_nat (j - 1))) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
      assert (Hn : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
      pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ Hb)) as NZb. cbn in NZb.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      pose proof (u8ro_read psegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD. zstep. if_cases K.
      + lstep. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
      + zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. zstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        eapply (IH (j + 1)%Z); try eassumption; lia.
  Qed.

  Ltac scan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  (* sem727: a key at or above AUX_CNT (the cache words, AT_MINSIGSTKSZ): bgeu skips the store and the
     loop loads the next key (the donor's skip_it). *)
  Ltac skip_it AUXB ki :=
    lstep; if_true; ldaux AUXB ki; lstep; astep.

  Lemma init_libc_spec : forall tp a0 a1,
    stk psegs m lo (bv_unsigned sp) ->
    bytes_at psegs m E (u64s eps ++ le8 z64 ++ u64s (pauxv la hw ent uid gid (Z_to_bv 64 R) efn)) ->
    bytes_at psegs m P (s ++ [Z_to_bv 8 0]) ->
    bytes_at psegs m R (le8 g) ->
    rw_cells psegs m RPROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells psegs m RHWCAP [C8 hw0] ->
    rw_cells psegs m RENVIRON [C8 env0] ->
    rw_cells psegs m RSYSINFO [C8 z64] ->
    rw_cells psegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
    rw_cells psegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells psegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
    rw_cells psegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells psegs m RGUARD [CB 8 gjunk] ->
    rw_cells psegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x5a710); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells psegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
    rw_cells psegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv psegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl psegs (at_node psegs) (enode NSetTid dec_set_tid) (epost init_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1fb44) fc None m (seg_rom psegs)).
  Proof.
    (* sem727: the walk is the same for both kernels up to the CONFIG_RSEQ pair, which only a CONFIG_RSEQ
       kernel lays; the two cases are walked separately (the donor's split). *)
    destruct (la_rseq la) eqn:RS.
    - intros tp a0 a1 ST ENV STR RND G2 HW ENVC SI LC TDC MT DS GU GOT3 GG GD MI -> ->.
      unfold td_cells, libc_cells in *.
      pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. rewrite pauxv_length, RS in EB. cbn [auxv_count] in EB.
      pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
      pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
      pose proof (bv_unsigned_in_range 64 hw) as RHW. unfold bv_modulus in RHW. cbn in RHW.
      iprefix.
      carve_frame 384%nat ST.
      zidle_begin sp 384%Z MUz WMz.
      do 9 lstep.
      zidle_end MUz WMz.
      do 1 lstep.
    apply (rw_cells_split_CB psegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
      change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
      replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
      replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
      lstep. call (memset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
      rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
      apply (rw_cells_recast psegs _ _ _ (repeat (C8 z64) 38)) in AUX;
        [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
    lstep. lstep. lstep.
      eapply (envp_count_loop eps); [exact EPS | exact ENV |].
    lstep. lstep. lstep.
      pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
      apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
      replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
      unfold pauxv in AUXB. rewrite RS in AUXB. cbn [app] in AUXB.
      ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
    scan_it AUXB 1%nat 2%nat.
      skip_it AUXB 4%nat. skip_it AUXB 6%nat. skip_it AUXB 8%nat. skip_it AUXB 10%nat. skip_it AUXB 12%nat.
      skip_it AUXB 14%nat. skip_it AUXB 16%nat. skip_it AUXB 18%nat. skip_it AUXB 20%nat.
      scan_it AUXB 21%nat 22%nat. scan_it AUXB 23%nat 24%nat. scan_it AUXB 25%nat 26%nat. scan_it AUXB 27%nat 28%nat.
      scan_it AUXB 29%nat 30%nat. scan_it AUXB 31%nat 32%nat. scan_it AUXB 33%nat 34%nat. scan_it AUXB 35%nat 36%nat.
      scan_it AUXB 37%nat 38%nat. scan_it AUXB 39%nat 40%nat. scan_it AUXB 41%nat 42%nat. scan_it AUXB 43%nat 44%nat.
      scan_it AUXB 45%nat 46%nat. scan_it AUXB 47%nat 48%nat. scan_it AUXB 49%nat 50%nat. scan_it AUXB 51%nat 52%nat.
      (* The CONFIG_RSEQ pair: AT_RSEQ_FEATURE_SIZE and AT_RSEQ_ALIGN are below AUX_CNT. *)
      scan_it AUXB 53%nat 54%nat. scan_it AUXB 55%nat 56%nat.

      steps_to 0x1fc00%Z.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.

      steps_to 0x1fc40%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (pn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
      rename POST into G2. try rename MI0 into MI.

      apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
      apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
      cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
      replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
      replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
      lstep. lstep.
      name_sp sp (-384)%Z. name_sp sp (-336)%Z.
      icallk (init_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
      all: lazymatch goal with
           | |- forall _, _ => ipost psegs; unname_sp; unname_sp
           | |- _ => unname_sp; unname_sp;
                     first [ hyp_by_addr | reflexivity | lia
                           | lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
                               replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
           end.
      rename PC into ST. unfold td_cells, libc_cells in *.

      lstep. lstep.
      call_sp (init_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R g).
      all: lazymatch goal with
           | |- evt _ _ _ => idtac
           | |- ?g => first [ hyp_by_addr | reflexivity | lia ]
           end.
      match goal with H : stk _ _ _ _ |- _ => rename H into ST end.

      do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
      do 5 lstep.
      join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
      release_frame FRlo ST (bv_unsigned sp).
      lstep.
      unfold init_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
      all: hyp_by_addr.
    - intros tp a0 a1 ST ENV STR RND G2 HW ENVC SI LC TDC MT DS GU GOT3 GG GD MI -> ->.
      unfold td_cells, libc_cells in *.
      pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8 in EB. rewrite pauxv_length, RS in EB. cbn [auxv_count] in EB.
      pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
      pose proof (bytes_at_bound _ _ _ _ RND) as RB. rewrite length_le8 in RB.
      pose proof (bv_unsigned_in_range 64 hw) as RHW. unfold bv_modulus in RHW. cbn in RHW.
      iprefix.
      carve_frame 384%nat ST.
      zidle_begin sp 384%Z MUz WMz.
      do 9 lstep.
      zidle_end MUz WMz.
      do 1 lstep.

      apply (rw_cells_split_CB psegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
      change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
      replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
      replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
      lstep. call (memset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
      rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
      apply (rw_cells_recast psegs _ _ _ (repeat (C8 z64) 38)) in AUX;
        [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.

      lstep. lstep. lstep.
      eapply (envp_count_loop eps); [exact EPS | exact ENV |].

      lstep. lstep. lstep.
      pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
      apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
      replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
      unfold pauxv in AUXB. rewrite RS in AUXB. cbn [app] in AUXB.
      ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.

      scan_it AUXB 1%nat 2%nat.
      skip_it AUXB 4%nat. skip_it AUXB 6%nat. skip_it AUXB 8%nat. skip_it AUXB 10%nat. skip_it AUXB 12%nat.
      skip_it AUXB 14%nat. skip_it AUXB 16%nat. skip_it AUXB 18%nat. skip_it AUXB 20%nat.
      scan_it AUXB 21%nat 22%nat. scan_it AUXB 23%nat 24%nat. scan_it AUXB 25%nat 26%nat. scan_it AUXB 27%nat 28%nat.
      scan_it AUXB 29%nat 30%nat. scan_it AUXB 31%nat 32%nat. scan_it AUXB 33%nat 34%nat. scan_it AUXB 35%nat 36%nat.
      scan_it AUXB 37%nat 38%nat. scan_it AUXB 39%nat 40%nat. scan_it AUXB 41%nat 42%nat. scan_it AUXB 43%nat 44%nat.
      scan_it AUXB 45%nat 46%nat. scan_it AUXB 47%nat 48%nat. scan_it AUXB 49%nat 50%nat. scan_it AUXB 51%nat 52%nat.
    steps_to 0x1fc00%Z.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
      astep. if_cases K; zify_cond K; [|exfalso; lia]. clear K.
    steps_to 0x1fc40%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (pn_loop (length s) 1 mm mm); [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact STR | exact G2 | ] end.
      rename POST into G2. try rename MI0 into MI.
    apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUXa AUX].
      apply (proj1 (rw_cells_app _ _ _ [_;_;_] _)) in AUX. destruct AUX as [AUX3 AUXb].
      cbn [cells_size csize Nat.add] in AUX3, AUXb. change (Z.of_nat 24) with 24%Z in *.
      replace (bv_unsigned sp + -336 + 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
      replace (bv_unsigned sp + -336 + 24 + 24)%Z with (bv_unsigned sp + -288)%Z in AUXb by lia.
      lstep. lstep.
      name_sp sp (-384)%Z. name_sp sp (-336)%Z.
      icallk (init_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
      all: lazymatch goal with
           | |- forall _, _ => ipost psegs; unname_sp; unname_sp
           | |- _ => unname_sp; unname_sp;
                     first [ hyp_by_addr | reflexivity | lia
                           | lazymatch goal with |- rw_cells _ _ (?b + -336 + 24)%Z _ =>
                               replace (b + -336 + 24)%Z with (b + -312)%Z by lia; hyp_by_addr end ]
           end.
      rename PC into ST. unfold td_cells, libc_cells in *.
    lstep. lstep.
      call_sp (init_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R g).
      all: lazymatch goal with
           | |- evt _ _ _ => idtac
           | |- ?g => first [ hyp_by_addr | reflexivity | lia ]
           end.
      match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    do 3 lstep. if_false. lstep. lstep. lstep. if_false. lstep. lstep. if_true.
      do 5 lstep.
      join2 FRlo AUXa. join2 FRlo AUX3. join2 FRlo AUXb. join2 FRlo FRhi.
      release_frame FRlo ST (bv_unsigned sp).
      lstep.
      unfold init_libc_post, td_cells, rtd_cells, libc_cells in *. sys_finish; try lia.
      all: hyp_by_addr.
  Qed.
End InitLibc.
End Startup_C.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Exit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_tac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Str_memset.InitMem OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_memcpy OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup.Startup_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup.Startup_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Startup.Startup_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Exit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Export Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_example_small_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].

Notation psegs := Image.psegs.


Section AtMain.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word).
  Context {RN__ : RunRnd}.
  Notation usp0 := (bv_unsigned sp0).

  Definition crt_written : list (Z * Z) :=
    [(0x2a330, 0x2a331); (0x3a3c0, 0x5a498); (0x3a3c8, 0x5a498); (0x5a4a0, 0x5a4d0); (0x5a6f8, 0x5a700); (0x5a708, 0x5a788)]%Z.

  (* the entry block the launch laid at [sp0], [Run.entry_stack_image] of the run
     (727298f3's build_stack_bytes: the auxv's launch fields, the entry, the block's top, the exec name, the gid). *)
  Definition img_at : list byte :=
    build_stack_bytes run_la Src_zlib_example_small_fuzzer_repro.M.phdrs
      (Z_to_bv 64 (Z.of_N Src_zlib_example_small_fuzzer_repro.M.init_pc)) sp0 (ed_top run_draw)
      argv envp run_execfn uid run_gid run_hw run_draw.

  Definition at_main : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                      (t P0 : Z) (pg : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x1fe60) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x3a490)
                 t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x15948) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             bvmap_empty (Z_to_bv 64 0x15948) (Z_to_bv 32 0) None m' (seg_rom psegs)
    /\ mem_inv psegs m'
    /\ stk psegs m' (usp0 - 6144513) (usp0 + -48)
    /\ rw_cells psegs m' 0x3a3c8 [C8 (Z_to_bv 64 0x3a3c8); C8 (Z_to_bv 64 0x3a3c8); C8 (Z_to_bv 64 0x3a3c8); C8 z64; C4 (Z_to_bv 64 t)]
    /\ rw_cells psegs m' 0x3a3ec [C4 z64]
    /\ rw_cells psegs m' 0x3a3f0 [C4 (Z_to_bv 64 2); CB 76 (repeat (Z_to_bv 8 0) 76); C8 (Z_to_bv 64 0x3a440);
                                 CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 0x5a750); CB 24 (repeat (Z_to_bv 8 0) 24); C8 rr_guard;
                                 C8 (Z_to_bv 64 0x3a4a0); CB 16 (repeat (Z_to_bv 8 0) 16); C8 z64; CB 112 (repeat (Z_to_bv 8 0) 112)]
    /\ rw_cells psegs m' 0x5a718 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64]
    /\ rw_cells psegs m' 0x5a720 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 z64; C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 z64;
                                 C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]
    /\ rw_cells psegs m' 0x5a498 [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
    /\ rw_cells psegs m' 0x5a700 [C8 z64]
    /\ rw_cells psegs m' 0x5a708 [C8 pg; C8 (Z_to_bv 64 P0)]
    /\ rw_cells psegs m' 0x5a780 [C8 run_hw]
    /\ rw_cells psegs m' 0x3a3c0 [C8 (Z_to_bv 64 (envp_addr sp0 argv))]
    /\ rw_cells psegs m' 0x2a320 [C4 (Z_to_bv 64 0x20000)]
    /\ rw_cells psegs m' 0x5a6f8 [C8 rr_guard]
    /\ rw_cells psegs m' 0x29080 [C8 z64]
    /\ rw_cells psegs m' 0x29088 [C8 (Z_to_bv 64 0x15948); C8 (Z_to_bv 64 0x1fb40); C8 (Z_to_bv 64 0x202a8); C8 z64]
    /\ rw_cells psegs m' 0x290a8 [C8 (Z_to_bv 64 0x201dc); C8 z64]
    /\ rw_cells psegs m' 0x290b8 [C8 (Z_to_bv 64 0x29068)]
    /\ rw_cells psegs m' 0x290c0 [C8 z64]
    /\ rw_cells psegs m' 0x290d0 [C8 (Z_to_bv 64 0x28fb8)]
    /\ rw_cells psegs m' 0x290d8 [C8 (Z_to_bv 64 0x3a3c0); C8 (Z_to_bv 64 0x5a710); C8 (Z_to_bv 64 0x5a708)]
    /\ rw_cells psegs m' 0x290f0 [C8 (Z_to_bv 64 0x28f10); C8 (Z_to_bv 64 0x28f08)]
    /\ rw_cells psegs m' 0x29100 [C8 (Z_to_bv 64 0x5a6f8)]
    /\ rw_cells psegs m' 0x29108 [C8 (Z_to_bv 64 0x28f18); C8 (Z_to_bv 64 0x28f10)]
    /\ rw_cells psegs m' 0x28f08 [C8 (Z_to_bv 64 0x15844)]
    /\ rw_cells psegs m' 0x28f10 [C8 (Z_to_bv 64 0x158b8)]
    /\ rw_cells psegs m' 0x29068 [C8 (Z_to_bv 64 0x2a140)]
    /\ rw_cells psegs m' 0x2a330 [C1 (Z_to_bv 8 1)]
    /\ rw_cells psegs m' 0x2a378 [C1 (Z_to_bv 8 0)]
    /\ rw_cells psegs m' 0x5a6f0 [C4 z64]
    /\ rw_cells psegs m' 0x2a318 [C8 (Z_to_bv 64 0x2a230)]
    /\ rw_cells psegs m' 0x2a228 [C8 (Z_to_bv 64 0x2a140)]
    /\ rw_cells psegs m' 0x5ab38 [C8 z64]
    /\ rw_cells psegs m' 0x5ab48 [C8 z64]
    /\ stdout_file m' stdout_init
    /\ stderr_file m'
    /\ bytes_at psegs m' usp0 img_at
    /\ wr_at psegs m' usp0 (Z.of_nat (length img_at))
    /\ nth_error (argv_ptrs (ed_top run_draw) argv envp run_execfn) 0 = Some (Z_to_bv 64 P0)
    /\ (forall a : word, (0x28000 <= bv_unsigned a < 0x5b000)%Z -> outside crt_written (bv_unsigned a) -> m' a = None)
    /\ (0 < t < 4194304)%Z.
End AtMain.


Ltac img_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells psegs m A cs);
  [ apply (rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 psegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Ltac img_chunk' NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  let nbs := eval vm_compute in (Z.of_nat (length bs)) in
  assert (H : rw_cells psegs m A cs);
  [ apply (rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 psegs m A bs);
      [ intros a Ha; apply NONE; change (Z.of_nat (length bs)) with nbs in Ha; cbn [outside]; lia | vm_compute; reflexivity | lia | change (Z.of_nat (length bs)) with nbs; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section Proof.
  (* the launch fixes argv / envp / the exec
     name / uid / gid / hwcap (the ProcInput), the mmap base and the draw; the entry's own conjuncts
     (valid_launch, entry_launch_ok_va Sv48) replace r30q2's VFIT. *)
  Variables (sp0 brk0 mbase : word) (inp : ProcInput) (draw : EntryDraw).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation execfn := (in_execfn inp).
  Notation uid := (in_uid inp).
  Notation gid := (in_gid inp).
  Notation hw := (in_hwcap inp).
  Notation la := (launch_auxv inp sp0 mbase).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis VLAUNCH : valid_launch inp.
  Hypothesis LOK : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase draw) inp.
  Notation ph := Src_zlib_example_small_fuzzer_repro.M.phdrs.
  Notation pentry := (Z_to_bv 64 (Z.of_N Src_zlib_example_small_fuzzer_repro.M.init_pc)).
  Notation usp0 := (bv_unsigned sp0).
  Notation rrn := (run_rnd_of inp sp0 mbase draw).
  Notation img := (@img_at sp0 argv envp uid rrn).

  Lemma run_geom : geom_ok (la_rseq la) sp0 (ed_top draw) argv envp execfn.
  Proof. exact (geom_of_launch Sv48 inp sp0 brk0 mbase draw LOK). Qed.

  (* the launch fact the main-side statements take as a premise
     (rmain_stmt, main_to_P1_stmt, main_usage_stmt); P/Impl discharges it with this lemma.  The donor's own
     lemma and proof (Plain/Startup.v l.161-162). *)
  Lemma run_launch_ok : launch_ok la sp0 (ed_top draw) argv envp execfn.
  Proof. split; [exact run_geom | exact (top_of_launch inp sp0 brk0 mbase draw LOK)]. Qed.

  Lemma img_len : Z.of_nat (length img) = (bv_unsigned (ed_top draw) - usp0)%Z.
  Proof. exact (img_length la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw run_geom). Qed.

  Lemma sp_facts : (stack_max_size <= usp0)%Z /\ (usp0 + Z.of_nat (length img) <= 2^64)%Z /\
                    (usp0 mod 16 = 0)%Z /\ (0x7fff80000000 <= usp0 <= 0x800000000000)%Z.
  Proof.
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    destruct VSP as (L & H & M). unfold sp_window_lo, sp_window_hi, stack_max_size in *. lia.
  Qed.

  Lemma wlo_facts : (usp0 - stack_max_size <= stack_window_lo (in_kernel inp) mbase draw
                     <= usp0 + 2244095 - stack_max_size)%Z.
  Proof.
    split; [exact (stack_window_lo_ge_sp inp sp0 brk0 mbase draw LOK)|].
    exact (stack_window_lo_valid inp sp0 brk0 mbase draw VLAUNCH LOK).
  Qed.

  Theorem startup_spec :
    impl psegs (at_node psegs) (enode NSetTid dec_set_tid) (epost (fun _ => @at_main sp0 argv envp uid rrn))
         (init_ms psegs Src_zlib_example_small_fuzzer_repro.M.init_pc Src_zlib_example_small_fuzzer_repro.M.phdrs sp0 mbase draw inp).
  Proof.
    destruct sp_facts as (SPLO & IMGHI & SP16 & SPW). destruct wlo_facts as (WLO1 & WLO2).
    pose proof img_len as IL. pose proof (top_of_launch inp sp0 brk0 mbase draw LOK) as TW.
    pose proof run_geom as GEO.
    unfold init_ms, mkR_init.
    set (m := wrap_mem inp mbase ph pentry sp0 draw).
    change (Z.of_N Src_zlib_example_small_fuzzer_repro.M.init_pc) with 0x157fc%Z.
    unfold stack_max_size in *.
    assert (NONE : forall a : word, (bv_unsigned a < 0x5b000)%Z -> m a = None).
    { intros a Ha. apply init_none; lia. }
    pose proof (init_stk psegs inp mbase ph pentry sp0 draw (usp0 - 6144513) ltac:(lia) ltac:(lia)) as ST. fold m in ST.
    assert (IMGTOP : (usp0 + Z.of_nat (length (entry_stack_image inp mbase ph pentry sp0 draw)) <= UTOP)%Z).
    { change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img).
      unfold sp_window_hi, UTOP in *. lia. }
    pose proof (init_mem_inv' psegs inp mbase ph pentry sp0 draw 0x5b000 ltac:(lia) ltac:(lia) IMGTOP
                  ltac:(change (segs_top psegs) with 0x5b000%Z; lia)) as MI.
    fold m in MI.
    pose proof (init_stack_bytes psegs inp mbase ph pentry sp0 draw
                  ltac:(change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img); lia)) as IMG.
    fold m in IMG. change (entry_stack_image inp mbase ph pentry sp0 draw) with img in IMG.
    pose proof (init_stack_wr psegs inp mbase ph pentry sp0 draw
                  ltac:(change (length (entry_stack_image inp mbase ph pentry sp0 draw)) with (length img); lia)) as WR.
    fold m in WR. change (entry_stack_image inp mbase ph pentry sp0 draw) with img in WR.
    destruct (img_pieces psegs la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw m IMG GEO)
      as (ARGC & ARGV & ENV & AUXW & RNDB & _ & _ & _).
    rewrite (pauxv_auxv_words la pentry sp0 (ed_top draw) argv envp execfn uid gid hw) in ENV. clear AUXW.
    (* the store transport proves ENV disjoint from the start-up's stores only on the unfolded address *)
    unfold envp_addr in ENV.
    destruct VARGV as (VA1 & VA2 & VA3 & VA4 & VA5).
    assert (Harg0 : exists arg0, nth_error argv 0 = Some arg0).
    { destruct (in_argv inp) as [|a ?] eqn:EA0; [try rewrite EA0 in VA1; cbn in VA1; lia | exists a; reflexivity]. }
    destruct Harg0 as [arg0 Harg0].
    destruct (img_argv_string psegs la ph pentry sp0 (ed_top draw) argv envp execfn uid gid hw draw m IMG GEO 0 arg0 Harg0)
      as (P0 & HP0 & P0LO & P0HI & STR).
    pose proof (proj1 (Forall_forall _ _) VA4 arg0 (nth_error_In _ _ Harg0)) as NONUL0. cbn beta in NONUL0.
    assert (NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) arg0).
    { apply Forall_forall. intros b Hb E0. apply NONUL0. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (envp_ptrs_nz (la_rseq la) sp0 (ed_top draw) argv envp execfn GEO) as EPS.
    assert (RND : bytes_at psegs m (rnd_addr (la_rseq la) sp0 argv envp) (le8 (rnd_lo (ed_random draw)))).
    { rewrite at_random_bytes_split, !Z_to_bv_bv_unsigned in RNDB. apply bytes_at_app in RNDB. exact (proj1 RNDB). }
    pose proof (head_len_ge (la_rseq la) argv envp) as HLG.
    pose proof (str_base_ge _ _ _ _ _ _ GEO) as SBG.
    assert (ASZ : (160 <= auxv_size (la_rseq la))%nat) by (unfold auxv_size, auxv_count; destruct (la_rseq la); lia).
    assert (RLO : (usp0 <= rnd_addr (la_rseq la) sp0 argv envp)%Z).
    { unfold rnd_addr, argc, envc in *. lia. }
    img_chunk NONE m 0x5a708%Z [C8 z64; C8 z64] G2.
    img_chunk NONE m 0x5a780%Z [C8 z64] HW.
    img_chunk NONE m 0x3a3c0%Z [C8 z64] ENVC.
    img_chunk NONE m 0x5a700%Z [C8 z64] SI.
    img_chunk NONE m 0x5a718%Z (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) LC.
    img_chunk NONE m 0x3a3c8%Z (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) TDC.
    img_chunk NONE m 0x5a498%Z [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] MT.
    img_chunk NONE m 0x2a320%Z [C4 (Z_to_bv 64 0x20000)] DS.
    img_chunk NONE m 0x5a6f8%Z [CB 8 (repeat (Z_to_bv 8 0) 8)] GU.
    img_chunk NONE m 0x290d8%Z [C8 (Z_to_bv 64 0x3a3c0); C8 (Z_to_bv 64 0x5a710); C8 (Z_to_bv 64 0x5a708)] GOT3.
    img_chunk NONE m 0x29100%Z [C8 (Z_to_bv 64 0x5a6f8)] GG.
    img_chunk NONE m 0x29080%Z [C8 z64] GD.
    img_chunk NONE m 0x29088%Z [C8 (Z_to_bv 64 0x15948); C8 (Z_to_bv 64 0x1fb40); C8 (Z_to_bv 64 0x202a8); C8 z64] GOT0.
    img_chunk NONE m 0x290f0%Z [C8 (Z_to_bv 64 0x28f10); C8 (Z_to_bv 64 0x28f08)] GIN.
    img_chunk NONE m 0x28f08%Z [C8 (Z_to_bv 64 0x15844)] INA.
    img_chunk NONE m 0x2a330%Z [C1 (Z_to_bv 8 0)] INI.
    unfold libc_cells in LC. unfold td_cells in TDC.
    assert (HC : argc argv = Z.of_nat (length argv)) by reflexivity.
    assert (HE : envc envp = Z.of_nat (length envp)) by reflexivity.
    assert (P0GE : (usp0 + 184 <= P0)%Z).
    { unfold argc, envc in *. lia. }
    pose proof (munch_refl [(usp0 - 6144513, usp0); (0x2a330, 0x2a331); (0x3a3c0, 0x5a498); (0x3a3c8, 0x5a498); (0x5a4a0, 0x5a4d0); (0x5a6f8, 0x5a700);
                            (0x5a708, 0x5a788)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    clearbody m.
    change (id (bytes_at psegs m usp0 img)) in IMG. change (id (wr_at psegs m usp0 (Z.of_nat (length img)))) in WR.
    iprefix.
    do 7 lstep.
    pose proof (bytes_at_read psegs m usp0 _ 0 4 ARGC ltac:(lia) ltac:(rewrite length_le8; lia)) as RD.
    change (firstn 4 (skipn (Z.to_nat 0) (le8 (Z_to_bv 64 (argc argv))))) with (le4 (Z_to_bv 64 (argc argv))) in RD.
    let a := cur_mem_addr in replace (wa (usp0 + 0)) with a in RD by (unfold wa; rewrite Z.add_0_r; try reflexivity; symmetry; apply Z_to_bv_bv_unsigned).
    lstep. clear RD.
    replace (Z_to_bv 64 (Z.land usp0 18446744073709551600)) with sp0.
    2:{ change 18446744073709551600%Z with (2^64 - 2^4)%Z. rewrite land_align_down by lia.
        change (2^4)%Z with 16%Z. rewrite SP16, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
    replace (sx32 (Z_to_bv 64 (argc argv))) with (Z_to_bv 64 (argc argv)).
    2:{ unfold sx32. f_equal. unfold argc. rewrite unsigned_lit by lia. symmetry. apply swrap32_small. lia. }
    steps_to 0x1fdbc%Z.
    carve_frame 32%nat ST.
    do 8 lstep.
    pose proof (rd_u64s_g psegs _ (usp0 + 8) _ 0 _ (Z_to_bv 64 (usp0 + 8)) ARGV ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length; lia); exact HP0) ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD ARGV.
    do 3 lstep.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (envp_addr sp0 argv))
      by (unfold envp_addr; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).

    clear ARGC RNDB.
    lstep. name_sp sp0 (-32)%Z.
    icallk (init_libc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (usp0 - 6144513)%Z
              (envp_addr sp0 argv) (envp_ptrs (ed_top draw) argv envp execfn) (rnd_addr (la_rseq la) sp0 argv envp)
              (rnd_lo (ed_random draw)) uid hw P0 arg0 _ _ _ _ _ la pentry gid (Z_to_bv 64 (xfn_base (ed_top draw) argv envp execfn))).
    all: lazymatch goal with
         | |- forall _, _ => ipost psegs; unname_sp
         | |- Forall _ _ => first [exact EPS | exact NONUL]
         | |- _ => unname_sp; first [ hyp_by_addr | exact ENV | reflexivity | unfold envp_addr; lia ]
         end.
    rename PC into ST.
    unfold td_cells, rtd_cells, libc_cells, envp_addr in *.
    repeat match goal with
           | H : bytes_at _ _ _ (u64s _ ++ _) |- _ => clear H
           | H : bytes_at _ _ P0 _ |- _ => clear H
           | H : bytes_at _ _ (rnd_addr _ _ _ _) _ |- _ => clear H
           end.
    clear EPS NONUL NONUL0 VA2 VA3 VA4 P0HI RLO HLG SBG ASZ.
    steps_to 0x1fe18%Z. release_frame FR ST (bv_unsigned sp0). astep.
    carve_frame 48%nat ST. steps_to 0x1fd70%Z.
    carve_frame 32%nat ST. steps_to 0x15844%Z.
    carve_frame 16%nat ST. steps_to 0x158b4%Z. release_frame FR1 ST (usp0 + -80)%Z. astep.
    steps_to 0x1fdb8%Z. release_frame FR0 ST (usp0 + -48)%Z. astep.
    steps_to 0x15948%Z.
    replace (Z_to_bv 64 (usp0 + 8 + Z.shiftl (argc argv) 3 + 8)) with (Z_to_bv 64 (usp0 + 8 * (argc argv + 2)))
      by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    unfold id in IMG, WR.
    lazymatch type of MU with munch ?W m ?mf =>
      apply (bytes_at_transport psegs W m mf usp0 img) in IMG; [| exact MU | cbn [disjoint_from]; lia];
      apply (wr_at_transport psegs m mf) in WR; [| exact WM] end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (NONE' : forall a : word, (bv_unsigned a < 0x5b000)%Z ->
                outside [(usp0 - 6144513, usp0); (0x2a330, 0x2a331); (0x3a3c0, 0x5a498); (0x3a3c8, 0x5a498); (0x5a4a0, 0x5a4d0); (0x5a6f8, 0x5a700);
                         (0x5a708, 0x5a788)]%Z (bv_unsigned a) -> mf a = None)
        by (intros a Ha Ho; rewrite (MU a Ho); apply NONE; exact Ha);
      img_chunk' NONE' mf 0x290a8%Z [C8 (Z_to_bv 64 0x201dc); C8 z64] GCX;
      img_chunk' NONE' mf 0x290b8%Z [C8 (Z_to_bv 64 0x29068)] GSE;
      img_chunk' NONE' mf 0x290c0%Z [C8 z64] GFZ;
      img_chunk' NONE' mf 0x290d0%Z [C8 (Z_to_bv 64 0x28fb8)] GDF;
      img_chunk' NONE' mf 0x29108%Z [C8 (Z_to_bv 64 0x28f18); C8 (Z_to_bv 64 0x28f10)] GFI;
      img_chunk' NONE' mf 0x28f10%Z [C8 (Z_to_bv 64 0x158b8)] FIA;
      img_chunk' NONE' mf 0x29068%Z [C8 (Z_to_bv 64 0x2a140)] SEP;
      img_chunk' NONE' mf 0x2a378%Z [C1 (Z_to_bv 8 0)] FIN;
      img_chunk' NONE' mf 0x5a6f0%Z [C4 z64] EXL;
      img_chunk' NONE' mf 0x2a318%Z [C8 (Z_to_bv 64 0x2a230)] SOU;
      img_chunk' NONE' mf 0x2a228%Z [C8 (Z_to_bv 64 0x2a140)] SEU;
      img_chunk' NONE' mf 0x5ab38%Z [C8 z64] SIN;
      img_chunk' NONE' mf 0x5ab48%Z [C8 z64] OFL;
      img_chunk' NONE' mf 0x2a230%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x22a98 0x5ab60 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) SOF;
      img_chunk' NONE' mf 0x5ab60%Z [CB 1024 (repeat (Z_to_bv 8 0) 1024)] SBUF;
      img_chunk' NONE' mf 0x2a140%Z (file_cells (Z_to_bv 64 5) 0 0 0 0x22900 0x5ab58 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) SEF
    end.
    lazymatch goal with TD : rw_cells _ _ 0x3a3c8 _ |- _ =>
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in TD; destruct TD as [TDa TD];
      apply (proj1 (rw_cells_app _ _ _ [_] _)) in TD; destruct TD as [ERR TDb] end.
    match type of ERR with rw_cells _ _ ?A _ => replace A with 0x3a3ec%Z in ERR by reflexivity end.
    match type of TDb with rw_cells _ _ ?A _ => replace A with 0x3a3f0%Z in TDb by reflexivity end.
    lazymatch goal with L : rw_cells _ _ 0x5a718 _ |- _ =>
      rewrite envp_ptrs_length in L;
      replace (usp0 + 8 * (argc argv + 2) + 8 * (Z.of_nat (length envp) + 1))%Z with (auxv_addr sp0 argv envp) in L
        by (unfold auxv_addr; lia);
      apply (proj1 (rw_cells_app _ _ _ [_;_;_;_;_] _)) in L; destruct L as [LCa LCb] end.
    match type of LCb with rw_cells _ _ ?A _ => replace A with 0x5a720%Z in LCb by reflexivity end.
    apply evt_done. unfold at_main, envp_addr. cbn [run_draw run_hw run_la run_execfn run_gid run_rnd_of].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- stdout_file _ _ =>
             exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024);
             cbn [so_active so_first so_lbf_nl so_buf stdout_init zlength length to_bytes map firstn];
             split; [exact SOF|]; split; [reflexivity|]; split; [exact SBUF|]; split; [reflexivity|];
             split; [apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity|]; intros _; reflexivity
         | |- stderr_file _ => exists (Z_to_bv 64 5), z64, 0%Z, 0%Z, (repeat (Z_to_bv 8 0) 80); exact SEF
         | |- nth_error _ _ = _ => exact HP0
         | |- wr_at _ _ _ _ => exact WR
         | |- forall _, _ => intros a Ha Hout; rewrite (MU a); [apply NONE; lia|];
                              unfold crt_written in Hout; cbn [outside] in Hout |- *; lia
         | |- _ => first [hyp_by_addr | lia]
         end.
  Qed.
End Proof.
