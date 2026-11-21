(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up per CONFIG_RSEQ value and the new auxv layout). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ITree Image.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zcp Z9p Z9n Z10m Rnd.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

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
        F (Z_to_bv 64 0x72280) fc None m (seg_rom psegs)).
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
        F (Z_to_bv 64 0x71d00) fc None m (seg_rom psegs)).
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
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0xa9ac8); (0x89840, 0x89848)]%Z m m'
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
  (lo <= bv_unsigned sp - 16)%Z -> (0xab000 <= lo)%Z -> (bv_unsigned sp <= R)%Z ->
  evt psegs (init_ssp_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo R g x0 x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x64990) fc None m (seg_rom psegs)).
Proof.
  intros until junk. intros ST RND GU GG TDC MI -> -> LO LOLO SPR.
  unfold td_cells in TDC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (RGUARD, 0xa9ac8); (0x89840, 0x89848)]%Z m) as MU.
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

(* The auxv the default kernel lays ([Run.launch_auxv] with [kb_rseq] true):
   ARCH_DLINFO's ten entries, [create_elf_tables]' sixteen, the CONFIG_RSEQ
   pair and AT_NULL.  Keys and the image's own PhdrInfo are literal; the rest
   are the launch's values. *)
Definition auxv29 (la : LaunchAuxv) (hw ent uid gid rnd efn : word) : list word :=
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
   Z_to_bv 64 23; z64; Z_to_bv 64 25; rnd; Z_to_bv 64 31; efn;
   Z_to_bv 64 27; Z_to_bv 64 28; Z_to_bv 64 28; Z_to_bv 64 32; z64; z64].

Lemma auxv29_length : forall la hw ent uid gid rnd efn, length (auxv29 la hw ent uid gid rnd efn) = 58%nat.
Proof. reflexivity. Qed.

Lemma auxv29_auxv_words : forall la entry sp top argv envp execfn uid gid hw,
  la_rseq la = true ->
  auxv_words la Plain.M.phdrs entry sp top argv envp execfn uid gid hw
  = auxv29 la hw entry uid gid (Z_to_bv 64 (rnd_addr true sp argv envp)) (Z_to_bv 64 (xfn_base top argv envp execfn)).
Proof. intros la entry sp top argv envp execfn uid gid hw Hr. unfold auxv_words, auxv_entries. rewrite Hr. reflexivity. Qed.

(* The SAME auxv for a kernel built WITHOUT CONFIG_RSEQ: [Run.auxv_entries]
   (75d69e00 theories/LinuxProcessSem/StackLayout.v:229) appends the rseq pair
   between the twenty-six common entries and AT_NULL, conditional on
   [la_rseq la], so the rseq-off table is this one with the four words
   [27; 28; 28; 32] removed and AT_NULL's [z64; z64] kept.  54 words, matching
   [Run.auxv_count false = 27] and [auxv_size false = 432]
   (StackLayout.v:276-277).

   Added 2026-11-06 for the kernel de-pin: [Run.valid_input_either] leaves
   [kb_rseq] free, so a start-up walk must cover both tables.  The two lemmas
   below are [auxv29_length] and [auxv29_auxv_words] with the other boolean --
   same statements, same proofs, [Hr : la_rseq la = false]. *)
Definition auxv27 (la : LaunchAuxv) (hw ent uid gid rnd efn : word) : list word :=
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
   Z_to_bv 64 23; z64; Z_to_bv 64 25; rnd; Z_to_bv 64 31; efn;
   z64; z64].

Lemma auxv27_length : forall la hw ent uid gid rnd efn, length (auxv27 la hw ent uid gid rnd efn) = 54%nat.
Proof. reflexivity. Qed.

Lemma auxv27_auxv_words : forall la entry sp top argv envp execfn uid gid hw,
  la_rseq la = false ->
  auxv_words la Plain.M.phdrs entry sp top argv envp execfn uid gid hw
  = auxv27 la hw entry uid gid (Z_to_bv 64 (rnd_addr false sp argv envp)) (Z_to_bv 64 (xfn_base top argv envp execfn)).
Proof. intros la entry sp top argv envp execfn uid gid hw Hr. unfold auxv_words, auxv_entries. rewrite Hr. reflexivity. Qed.

Lemma envp_count_loop : forall (ws : list word) (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A : Z) (rest : list byte),
  Forall (fun w : word => bv_unsigned w <> 0%Z) ws ->
  bytes_at psegs m A (u64s ws ++ le8 z64 ++ rest) ->
  evt psegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (A + 8 * (Z.of_nat (length ws) + 1))) z64 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x63fdc) fc None m (seg_rom psegs)) ->
  evt psegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5
                    a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x63fd0) fc None m (seg_rom psegs)).
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
