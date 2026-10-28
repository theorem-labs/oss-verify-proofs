(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr MState.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_fuzz_stmt H_prep H_parser_init H_membuffer_append H_httpmsg_destroy HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition parser_append_entry := 0x1601c%Z.
Ltac sstep := step; fix_lit_store.
Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.
Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.
Ltac name_junk FR :=
  repeat lazymatch type of FR with context [CB _ (firstn ?a ?b)] => let j := fresh "jk" in remember (firstn a b) as j in FR
                      | context [CB _ (skipn ?a ?b)] => let j := fresh "jk" in remember (skipn a b) as j in FR end;
  repeat match goal with E : _ = firstn _ _ |- _ => clear E | E : _ = skipn _ _ |- _ => clear E end.

Lemma land_1 : forall a, Z.land a 1 = (a mod 2)%Z.
Proof. intros a. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma fz_zero : forall (D : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz fuzz_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. unfold fuzz_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. try lit_branch. zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma fz_pro : forall (D n lo : Z) (b0 : byte) (rest : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 528 <= bv_unsigned sp)%Z -> (0 <= lo)%Z -> (bv_unsigned sp < 2^63)%Z -> mem_inv rsegs m ->
  bytes_at rsegs m D (b0 :: rest) -> (0 < D)%Z -> (D + 1 + Z.of_nat (length rest) <= lo \/ bv_unsigned sp <= D)%Z -> (D + 1 + Z.of_nat (length rest) < 2^63)%Z ->
  (1 <= n < 2^63)%Z ->
  evt rsegs (fun ms' => exists m' (junk : list byte) a2',
      munch [(bv_unsigned sp - 528, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp - 528)
      /\ rw_cells rsegs m' (bv_unsigned sp - 528) [CB 504 junk] /\ rw_cells rsegs m' (bv_unsigned sp - 528 + 504) [C8 s1; C8 s0; C8 ra]
      /\ ( (bv_unsigned b0 mod 2 = 0 /\
            ms' = MS (mkR (wz 0x13ff8) (wz (bv_unsigned sp - 528)) gp tp t0 t1 t2 (wz (D + 1)) (wz (n - 1)) (wz (bv_unsigned sp - 528)) (wz n) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz parser_request_init_entry) fc None m' (seg_rom rsegs))
        \/ (bv_unsigned b0 mod 2 = 1 /\
            ms' = MS (mkR (wz 0x14004) (wz (bv_unsigned sp - 528)) gp tp t0 t1 t2 (wz (D + 1)) (wz (n - 1)) (wz (bv_unsigned sp - 528)) (wz 2) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz parser_response_init_entry) fc None m' (seg_rom rsegs)) ))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz fuzz_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LOQ LO0 SPH MI BUF DPOS DSEP DHI NR. unfold fuzz_entry, parser_request_init_entry, parser_response_init_entry.
  pose proof (munch_refl [(bv_unsigned sp - 528, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (byte_range b0) as BR. pose proof (bytes_at_bound _ _ _ _ BUF) as BB. cbn [length] in BB. pose proof (word_lt64 sp) as SPB.
  zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
  ub_null. ub_align.
  carve_frame 528%nat ST.
  sstep. sstep. sstep. sstep.
  pose proof (u8ro_read rsegs _ D (b0 :: rest) 0 b0 (Z_to_bv 64 D) BUF eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. zstep. zstep. zstep. zstep.
  name_junk FR. split_chunk FR 1%nat PJ FS.
  replace (bv_unsigned sp + -528 + Z.of_nat 504)%Z with (bv_unsigned sp - 24)%Z in FS by lia.
  replace (bv_unsigned sp + -528)%Z with (bv_unsigned sp - 528)%Z in * by lia.
  replace (n + -1)%Z with (n - 1)%Z by lia.
  rewrite land_1.
  zstep. if_cases K1; zify_cond K1.
  -
    zstep. zstep. apply evt_done. eexists _, _, _. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact PJ|]. split; [exact FS|]. right. split; [| reflexivity]. Z.div_mod_to_equations. lia.
  - zstep. apply evt_done. eexists _, _, _. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact PJ|]. split; [exact FS|]. left. split; [| reflexivity]. Z.div_mod_to_equations. lia.
Qed.

Lemma fz_j : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x14004) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x13ff8) fc None m (seg_rom rsegs)).
Proof. intros until m. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. apply evt_done. reflexivity. Qed.

Lemma fz_mid : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x14014) sp gp tp t0 t1 t2 s0 s1 sp s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz parser_append_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x14004) fc None m (seg_rom rsegs)).
Proof. intros until m. unfold parser_append_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. zstep. zstep. zstep. apply evt_done. reflexivity. Qed.

Lemma fz_mid2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x1401c) sp gp tp t0 t1 t2 s0 s1 sp a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz httpmsg_destroy_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x14014) fc None m (seg_rom rsegs)).
Proof. intros until m. unfold httpmsg_destroy_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. zstep. apply evt_done. reflexivity. Qed.

Lemma fz_epi : forall (lo : Z) ra (sp : word) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x8 x9 (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp - 528 + 504) -> (lo + 528 <= bv_unsigned sp)%Z -> (0 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp - 528 + 504) [C8 s1; C8 s0; C8 ra] ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs)
                        /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp - 528)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1401c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LOQ LO0 MI FS. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. pose proof (word_lt64 sp) as SPB.
  zstep. zstep. zstep. zstep.
  replace (bv_unsigned sp - 528 + 528)%Z with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
  zstep. zstep.
  eapply stk_release in FS; [| exact ST| lia]. cbn [cells_size csize Nat.add app] in FS.
  replace (bv_unsigned sp - 528 + 504 + Z.of_nat 24)%Z with (bv_unsigned sp) in FS by lia.
  apply evt_done. split; [reflexivity| exact FS].
Qed.

Lemma pa_pro : forall (P lo : Z) ra (sp : word) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (0 <= lo)%Z -> mem_inv rsegs m -> (0 <= P /\ P + 504 < 2^64)%Z -> (0 < P)%Z -> (P mod 8 = 0)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x16040) (wz (bv_unsigned sp - 16)) gp tp t0 t1 t2 (wz P) s1 (wz (P + 400)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz membuffer_append_entry) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp - 16)
      /\ rw_cells rsegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz parser_append_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LOQ LO0 MI PR PNZ PAL. unfold parser_append_entry, membuffer_append_entry.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM. pose proof (word_lt64 sp) as SPB.
  carve_frame 16%nat ST. sstep. sstep. sstep.
  replace (bv_unsigned sp + -16)%Z with (bv_unsigned sp - 16)%Z in * by lia.
  ub_null. zstep. ub_align. zstep. zstep.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
Qed.

Lemma pa_post : forall (P r lo err hack pos entp clen csz esp : Z) (ra sp : word) gp tp t0 t1 t2 (s0 : word) s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp - 16) -> (lo + 16 <= bv_unsigned sp)%Z -> (0 <= lo)%Z -> mem_inv rsegs m -> (bv_unsigned sp <= P /\ P + 504 < 2^64)%Z ->
  rw_cells rsegs m (bv_unsigned sp - 16) [C8 s0; C8 ra] -> rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp) ->
  (r = 0 \/ r = -104)%Z ->
  evt rsegs (fun ms' => exists m',
      munch [(P + 440, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ ( (r <> 0 /\ rw_cells rsegs m' (P + 440) (p_ctl_cells 500 hack pos entp clen csz esp)
            /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 3) (wz 500) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs))
        \/ (r = 0 /\ m' = m
            /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x15bec) fc None m' (seg_rom rsegs)) ))
    (MS (mkR x1 (wz (bv_unsigned sp - 16)) gp tp t0 t1 t2 (wz P) s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x16040) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LOQ LO0 MI PR FR EC RR. unfold p_ctl_cells in *.
  pose proof (munch_refl [(P + 440, P + 444)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM. pose proof (word_lt64 sp) as SPB.
  destruct RR as [-> | ->].
  - zstep. lit_branch. zstep. zstep. zstep. zstep.
    replace (bv_unsigned sp - 16 + 16)%Z with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
    eapply stk_release in FR; [| exact ST| lia]. cbn [cells_size csize Nat.add app] in FR. replace (bv_unsigned sp - 16 + Z.of_nat 16)%Z with (bv_unsigned sp) in FR by lia.
    zstep. apply evt_done. exists m. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|]. right. split; [reflexivity|]. split; reflexivity.
  - zstep. lit_branch. zstep. zstep. sstep. zstep. zstep. zstep.
    replace (bv_unsigned sp - 16 + 16)%Z with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
    eapply stk_release in FR; [| exact ST| lia]. cbn [cells_size csize Nat.add app] in FR. replace (bv_unsigned sp - 16 + Z.of_nat 16)%Z with (bv_unsigned sp) in FR by lia.
    zstep. apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR|]. left. split; [lia|]. split; [assumption| reflexivity].
Qed.

Lemma mba_zero : forall (lo MB A len cap SRC : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z -> (0 < MB)%Z -> (MB mod 8 = 0)%Z ->
  (0 < SRC < 2^64)%Z -> (0 <= len <= cap)%Z -> (cap + 8 < 2^32)%Z -> (0 <= A < 2^64)%Z ->
  evt rsegs (fun ms' => exists m' a2' a3' a4' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz SRC) a2' a3' a4' a5 a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' MB (mbuf_cells A len cap))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz membuffer_append_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI MBC MBLO MBHI MBNZ MBAL SR HL HC HA.
  eapply evt_cut. { eapply (iseg58 MB A len cap); try eassumption; lia. }
  intros ms' ->.
  eapply evt_mono. { eapply (isegA lo MB SRC 0 A len cap); try eassumption; lia. }
  intros ms' [(_ & m' & a2' & a4' & a6' & -> & MU & WM & MI' & ST' & MBC')|(m' & j & x1 & a0' & a1' & a4' & a6' & x19 & x20 & pc & nsz & _ & _ & _ & _ & _ & _ & _ & N1 & _)]; [| lia].
  exists m', a2', (wz len), a4', a6'. split; [reflexivity|]. repeat (split; [eassumption|]). exact MBC'.
Qed.
