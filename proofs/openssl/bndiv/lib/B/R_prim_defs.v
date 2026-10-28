(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition rb (SB c : Z) : Z := SB + c * 2^32.                  (* [comment removed for export] *)
Definition fa (SB c : Z) : Z := rb SB c + 0xE0000000.           (* [comment removed for export] *)
Definition RIS_of (SB : Z) : Z := SB + 2^37.
Definition rinfo (RIS c : Z) : Z := RIS + 128 * c.
Definition zw (z : Z) : word := Z_to_bv 64 z.
Definition cp_ok (z : Z) : Prop := 0 <= z < 2^28.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inst_cells (SB : Z) (m : mem) : Prop :=
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB); C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))]
  /\ rw_cells bsegs m i_premapped [C1 (Z_to_bv 8 0)].
(* [comment removed for export] *)
Definition mm_gcells (m : mem) : Prop :=
  rw_cells bsegs m 0x5e0cb8 [C8 (Z_to_bv 64 0x7334a0)]
  /\ rw_cells bsegs m 0x5e0cc8 [C8 (Z_to_bv 64 0x735528)]
  /\ rw_cells bsegs m 0x7334a0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x7355b8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x73562c [C1 (Z_to_bv 8 0)].
(* [comment removed for export] *)
Definition ri_lock (m : mem) (R lk : Z) : Prop := rw_cells bsegs m R [C8 (Z_to_bv 64 lk)].
Definition ri_core (m : mem) (R nfree mfa auser muser : Z) : Prop :=
  rw_cells bsegs m (R + 16) [C8 (Z_to_bv 64 nfree); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 auser); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 muser); C8 (Z_to_bv 64 0)].
Definition ri_tail (m : mem) (R : Z) (rand : word) (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 : Z) : Prop :=
  rw_cells bsegs m (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed);
                             C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)].
(* [comment removed for export] *)
Definition fl_arr (m : mem) (SB c : Z) (ws : list word) : Prop := u32arr bsegs m (fa SB c) ws.

(* [comment removed for export] *)
Definition round_fa (x : Z) : Z := ((x + 0x3ffff) / 0x40000) * 0x40000.

Lemma round_fa_ge : forall x, 0 <= x -> x <= round_fa x < x + 0x40000.
Proof. intros x Hx. unfold round_fa. pose proof (Z.div_mod (x + 0x3ffff) 0x40000 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 0x3ffff) 0x40000 ltac:(lia)). lia. Qed.

Lemma round_fa_aligned : forall x, round_fa x mod 0x40000 = 0.
Proof. intros x. unfold round_fa. apply Z.mod_mul. lia. Qed.



(* [comment removed for export] *)
Definition poison_entry : Z := 0x1bf86c.

Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a n lo : Z) (m : mem) (PC : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(shad a, shad a + n / 8); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (shad a) [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (n / 8)))]
    /\ stk bsegs m' lo (bv_unsigned sp) /\ PC m'.

(* [comment removed for export] *)
Definition poison_stmt (PC : mem -> Prop) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (a n lo : Z) (shj : list byte),
  a mod 8 = 0 -> n mod 8 = 0 -> 0 < n -> kHighShadowEnd < a -> a + n <= 2^47 ->
  rw_cells bsegs m (shad a) [CB (Z.to_nat (n / 8)) shj] ->
  PC m ->
  stk bsegs m lo (bv_unsigned sp) -> kHighShadowEnd + 8 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  evt bsegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a n lo m PC)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) (Z_to_bv 64 250) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 poison_entry) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition PC_framed (PC : mem -> Prop) : Prop :=
  forall m m' W, PC m -> munch W m m' -> wmono bsegs m m' -> disjoint_from W img_hull_lo (img_hull_hi - img_hull_lo) -> PC m'.

(* [comment removed for export] *)
Lemma find_segment_above : forall segs a, 0 <= a ->
  forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? a) segs = true -> find_segment segs a 1 = None.
Proof.
  induction segs as [|seg segs IH]; intros a Ha H; cbn in *; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1.
  rewrite (proj2 (Z.leb_gt (a + 1) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))) by lia.
  rewrite Bool.andb_false_r. apply IH; assumption.
Qed.

Lemma asegs_top : forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? img_hull_hi) bsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_mono_top : forall segs a b, a <= b ->
  forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? a) segs = true ->
  forallb (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? b) segs = true.
Proof.
  induction segs as [|seg segs IH]; intros a b Hab H; cbn in *; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply andb_true_iff. split; [apply Z.leb_le; lia| eapply IH; eauto].
Qed.

Lemma ro_free_range : forall x : word, img_hull_hi <= bv_unsigned x -> ro_addr bsegs x = false.
Proof.
  intros x Hx. unfold ro_addr. rewrite find_segment_above; [reflexivity| pose proof (bv_unsigned_in_range 64 x); lia|].
  apply (forallb_mono_top bsegs img_hull_hi); [lia| exact asegs_top].
Qed.

(* [comment removed for export] *)
Lemma land_pgmask : forall x, 0 <= x < 2^64 ->
  Z.land x (Z.land (0 + - (4096)) 18446744073709551615) = (x / 4096) * 4096.
Proof.
  intros x Hx. rewrite (Z.land_comm (0 + - (4096)) 18446744073709551615), Z.land_assoc.
  change 18446744073709551615 with (Z.ones 64). rewrite (Z.land_ones x 64) by lia. rewrite Z.mod_small by lia.
  change (0 + - (4096)) with (Z.lnot (Z.ones 12)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma land_pgmask_aligned : forall x, 0 <= x < 2^64 - 4096 -> x mod 4096 = 0 ->
  Z.land x (Z.land (0 + - (4096)) 18446744073709551615) = x /\ Z.land (x + 4095) (Z.land (0 + - (4096)) 18446744073709551615) = x.
Proof.
  intros x Hx Hal. rewrite !land_pgmask by lia.
  assert (E : x = 4096 * (x / 4096)) by (apply Z.div_exact; lia).
  split.
  - rewrite E at 2. lia.
  - replace ((x + 4095) / 4096) with (x / 4096) by (apply Z.div_unique with 4095; lia). lia.
Qed.

(* [comment removed for export] *)
Ltac sp_facts :=
  repeat match goal with
  | |- context [Z_to_bv 64 (bv_unsigned ?sp + ?k)] =>
      lazymatch goal with
      | _ : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + k)) = _ |- _ => fail
      | _ => let E := fresh "Esp" in
             assert (E : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + k)) = bv_unsigned sp + k)
               by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp) as Hr; unfold bv_modulus in Hr; cbn [Z.of_N] in Hr; lia)
      end
  end.

(* [comment removed for export] *)
Definition gcts_entry : Z := 0x1c7500.

Lemma gcts_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (TCX T lo : Z),
  thread_cells TCX T m -> 0 < TCX -> TCX + 0xa0 <= 2^64 -> 0 < T -> T + 2800 < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 ->
  (TCX + 0xa0 <= lo \/ bv_unsigned sp <= TCX + 0x98) ->
  0xbfd000 <= lo ->
  mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (T + 2800)
               [(bv_unsigned sp - 32, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gcts_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros [TS TT] HT0 HT1 HT HT2 ST LO SEP ILO MI. unfold gcts_entry.
  destruct TS as (KI & K & TS & T0).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  do 3 zstep.
  sp_facts.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]. }
  all: rewrite ?Esp in *; try lia; try eassumption.
  zstep. ifF.
  do 4 zstep.
  release_frame FR POST (bv_unsigned sp).
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Lemma box : forall P : Prop, P -> boxed P. Proof. intros P H. exact H. Qed.
Lemma unbox : forall P : Prop, boxed P -> P. Proof. intros P H. exact H. Qed.

(* [comment removed for export] *)
Lemma shad_range : forall a n, 0 <= a -> 0 <= n -> a mod 8 = 0 -> n mod 8 = 0 -> a + n <= 2^47 ->
  0x7fff8000 <= shad a /\ shad a + n / 8 <= kHighShadowEnd + 1 /\ 8 * (n / 8) = n.
Proof.
  intros a n Ha Hn Hal Hnl Hend. unfold shad, SHB, kHighShadowEnd.
  assert (E1 : a = 8 * (a / 8)) by (apply Z.div_exact; lia).
  assert (E2 : n = 8 * (n / 8)) by (apply Z.div_exact; lia).
  lia.
Qed.

(* [comment removed for export] *)
Lemma land_famask : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = (x / 262144) * 262144.
Proof.
  intros x Hx. change 18446744073709289472 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 18))).
  rewrite Z.land_assoc, (Z.land_ones x 64) by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition tsep (ACEIL SB T TCX : Z) : Prop :=
  T_ok ACEIL T /\ 0 < TCX /\ TCX + 0xa0 <= ACEIL /\ (TCX + 0xa0 <= img_hull_lo \/ img_hull_hi <= TCX)
  /\ (T + 4096 <= SB \/ SB + 2^37 + 4096 <= T) /\ (TCX + 0xa0 <= SB \/ SB + 2^37 + 4096 <= TCX)
  /\ (TCX + 0xa0 <= T \/ T + 4096 <= TCX)
  /\ (T + 4096 <= 0x7fff8000 \/ kHighShadowEnd < T) /\ (TCX + 0xa0 <= 0x7fff8000 \/ kHighShadowEnd < TCX).
