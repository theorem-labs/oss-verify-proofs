(* WireCmSegs: the footprint (lib/Lib/ExecF.v evtF) runs of the straight-line pieces of check_meter
   (fuzz_wire.asan 0x80340), each from a cut point to the next cut point, stepped by lib/Lib/StepF.v. Form and
   helpers: reac-repacer/fuzz_uci lib/A/Prog/UciCvSegs.v (the segments of check_value in image A) and the released
   libreac/fuzz_decode lib/A/Prog/crtA_segs.v it is itself in the form of; cm_shadow_byte_rng is the released
   libreac/fuzz_decode lib/A/Prog/reac_frame_counter_F.v's. No lemma here mentions the allocator
   model: the journal, the two calls and the frame release are lib/A/Prog/check_meter_cgW.v.
   The pieces (offsets from the entry 0x80340; addresses of the objdump of record):
     cm_seg1_F  0x80340 -> 0x803ac  the 0x80 frame and its thirteen stores, s0 = the entry sp, the 32-byte realign
                into sp and s1, s4 := n, s3 := f, the shadow base through GOT_CELL_K -> CELL_K into s8, the
                use-after-return flag through GOT_UAR -> UAR (1, so the `beqz a2` at 0x803a4 is not taken), a0 = 64;
                it ends at the `jal __asan_stack_malloc_0`;
     cm_seg2_F  0x803b0 -> 0x80440  the fake frame in s2 and s6 (non-zero, so the alloca path 0x803c4..0x803dc is
                not taken), its three header words, s7 = the shadow address of the frame, its eight shadow bytes
                (0xf1 x4, 0xf8, 0xf3 x3) and `sd s6, 24(s1)`;
     cm_seg3_F  0x80440 -> 0x804e0  when n < 14 (lib/A/Prog/WireCmSegsEo.v);
     cm_seg4_F  0x80440 -> 0x80484  when 14 <= n, the offset eo (lib/A/Prog/WireCmSegsEo.v);
     cm_seg5_F  0x80484 -> 0x804e0  the meter test into s10 (lib/A/Prog/WireCmSegsOk.v);
     cm_seg6_F  0x804e0 -> 0x80504  s5 = the local at frame + 0x20, its shadow byte set to 2 and the untouched
                value 0xa5c3 stored into it, the three arguments, up to the `jal rp_meter_counter`;
     cm_seg7_F  0x80508 -> 0x80568  the result and the counter tests (lib/A/Prog/WireCmSegsCmp.v);
     cm_seg8_F  0x80568 -> the `ret`  the local re-poisoned, the header retired, the frame's eight shadow bytes set
                to 0xf5, the frame's flag byte cleared through the word at frame + 56, the thirteen reloads and
                `ret`.
   Each shadow check is `lb` of the shadow byte, `bnez` to a slow arm which tests (address & 7) against it and
   either returns to the fast arm or calls __asan_report_load1: the addressability premise of the byte gives the
   shadow byte k with k = 0 or (address mod 8 < k <= 7), so both arms join and no report call is reached.
   The own 0x80 frame is kept as TWO cell blocks: cm_frlo, the stack probe word and the three words the prologue
   never writes (the realigned `sd s6, 24(s1)` lands in those), and cm_frhi, the thirteen saved words, which the
   epilogue reloads. They are disjoint, so a store into one keeps the other. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import
PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

(* ------------------------------------------------------------------ *)
(* helpers                                                             *)
(* ------------------------------------------------------------------ *)

(* [entry sp - 0x80, entry sp - 0x60): the stack probe word of `sd zero, 0(sp)` and the three words the prologue
   never writes. *)
Definition cm_frlo (j : list byte) : list cell := [C8 (Z_to_bv 64 0); CB 24 j].
(* [entry sp - 0x60, entry sp): s10 .. s0 and ra, as the prologue stored them. *)
Definition cm_frhi (c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* A block of cells of a known size, read back as one block of bytes. *)
Lemma cm_forget : forall m A cs (n : nat),
  rw_cells rsegs m A cs -> cells_size cs = n -> exists j, rw_cells rsegs m A [CB n j].
Proof.
  intros m A cs n H E. destruct (rw_cells_forget rsegs m A cs H) as [j Hj]. rewrite E in Hj. exists j. exact Hj.
Qed.

(* `andi rd, rs, -32` on a 64-bit value: the value with its low five bits cleared. *)
Lemma cm_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.shiftl (Z.ones 59) 5) by (vm_compute; reflexivity).
  replace (32 * (x / 32)) with (Z.shiftl (Z.shiftr x 5) 5)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; replace (2 ^ 5) with 32 by reflexivity; lia).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  destruct (Z.ltb_spec i 5) as [Hl | Hl].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia.
    replace (i - 5 + 5) with i by lia.
    destruct (Z.ltb_spec i 64) as [Hh | Hh].
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite (Z.ones_spec_high 59 (i - 5)) by lia. rewrite andb_false_r.
      symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
      split; [lia|]. apply (Z.lt_le_trans _ (2 ^ 64)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n). *)
Lemma cm_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* cm_seg1_F : 0x80340 -> the class-0 stack malloc at 0x803ac          *)
(* ------------------------------------------------------------------ *)

Lemma cm_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    bytes_at rsegs m GOT_UAR (le8 (wa UAR)) -> bytes_at rsegs m UAR (le4 (wa 1)) ->
    UAR + 8 <= bv_unsigned sp - 128 ->
    ExecF.rng RNG (bv_unsigned sp - 128) 128 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG GOT_UAR 8 -> ExecF.rng RNG UAR 4 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 j,
         ms' = MS (mkR (Z_to_bv 64 0x803b0) (Z_to_bv 64 (32 * ((bv_unsigned sp - 128) / 32))) gp tp t0 t1 t2
                    sp (Z_to_bv 64 (32 * ((bv_unsigned sp - 128) / 32)))
                    (Z_to_bv 64 64) (Z_to_bv 64 CELL_K) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                    s2 a0 a1 s5 s6 s7 (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x3c544) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 128) (cm_frlo j) /\
         rw_cells rsegs m1 (bv_unsigned sp - 96) (cm_frhi s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80340) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO GCK CK GUA UA HLOW RFR RGC RCK RGU RUA.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold GOT_CELL_K, CELL_K, ASAN_K, GOT_UAR, UAR in *.
  carve_frame 96%nat ST.
  carve_frame 32%nat ST.
  do 14 step.
  match goal with MU' : munch _ m ?mm |- _ => rename MU' into MU1; rename mm into m0 end.
  do 2 step.
  assert (RDGU : ov_read_bytes rsegs m0 (wa 624704) 8 = Some (le8 (wa 657280))).
  { replace (wa 624704) with (wa (624704 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 624704 _ 0 8 GUA ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDGC : ov_read_bytes rsegs m0 (wa 624616) 8 = Some (le8 (wa 657272))).
  { replace (wa 624616) with (wa (624616 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 624616 _ 0 8 GCK ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDUA : ov_read_bytes rsegs m0 (wa 657280) 4 = Some (le4 (wa 1))).
  { replace (wa 657280) with (wa (657280 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 657280 _ 0 4 UA ltac:(lia)) by (rewrite length_le4; lia). reflexivity. }
  assert (RDCK : ov_read_bytes rsegs m0 (wa 657272) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 657272) with (wa (657272 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 657272 _ 0 8 CK ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  do 8 step.
  assert (ESP1 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128))) 18446744073709551584)
                 = Z_to_bv 64 (32 * ((bv_unsigned sp + -128) / 32))).
  { f_equal. rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. apply cm_land_m32. lia. }
  rewrite ESP1.
  step. step. if_false. step. step.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|].
  split; [cbn [cm_frlo]; eassumption | cbn [cm_frhi]; eassumption].
Qed.

(* ------------------------------------------------------------------ *)
(* cm_seg2_F : the fake frame, its header and its shadow                *)
(* ------------------------------------------------------------------ *)

(* The script of cm_seg2_F, run once for each side of the fake frame's position against its own shadow bytes
   (below it in high application memory, above it in low application memory). *)
Ltac cm_seg2_run UFA USP1 ESHR FAv :=
  do 4 step; if_true; do 8 step;
  rewrite ?UFA, ?USP1, ?ESHR;
  do 16 step;
  match goal with H : rw_cells rsegs ?mm FAv _ |- _ =>
    destruct (cm_forget mm FAv _ 64%nat H ltac:(reflexivity)) as [? ?] end;
  match goal with H : rw_cells rsegs ?mm (FAv / 8 + 2147450880) _ |- _ =>
    destruct (cm_forget mm (FAv / 8 + 2147450880) _ 8%nat H ltac:(reflexivity)) as [? ?] end;
  apply evtF_done; do 3 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [cbn [cm_frhi]; eassumption|];
  split; eassumption.

Lemma cm_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (SP SP1 FA f n : Z) (jg jF jsh : list byte),
    SP - 144 <= SP1 <= SP - 128 -> 0 <= SP - 144 -> SP <= 2 ^ 47 ->
    4096 <= FA -> FA + 64 <= 2 ^ 47 ->
    FA + 64 <= SP - 144 -> FA / 8 + ASAN_K + 8 <= SP - 144 ->
    FA / 8 + ASAN_K + 8 <= FA \/ FA + 64 <= FA / 8 + ASAN_K ->
    rw_cells rsegs m SP1 [CB 32 jg] ->
    rw_cells rsegs m (SP - 96) (cm_frhi c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    rw_cells rsegs m FA [CB 64 jF] ->
    rw_cells rsegs m (shadow_addr FA) [CB 8 jsh] ->
    ExecF.rng RNG (SP - 144) 144 -> ExecF.rng RNG FA 64 -> ExecF.rng RNG (shadow_addr FA) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 jF' jsh',
         ms' = MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SP1)
                    (Z_to_bv 64 14) (Z_to_bv 64 101571) (Z_to_bv 64 525120) (Z_to_bv 64 (-13)) a4 a5 a6 a7
                    (Z_to_bv 64 FA) (Z_to_bv 64 f) (Z_to_bv 64 n) s5 (Z_to_bv 64 FA)
                    (Z_to_bv 64 (shadow_addr FA)) (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x80440) fc None m1 (seg_rom rsegs) /\
         munch [(SP - 144, SP); (FA, FA + 24); (shadow_addr FA, shadow_addr FA + 8)] m m1 /\
         wmono rsegs m m1 /\
         rw_cells rsegs m1 (SP - 96) (cm_frhi c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) /\
         rw_cells rsegs m1 FA [CB 64 jF'] /\
         rw_cells rsegs m1 (shadow_addr FA) [CB 8 jsh'])
      (MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SP1)
             (Z_to_bv 64 FA) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n) s5 s6 s7
             (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x803b0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m SP SP1 FA f n jg jF jsh
    HSP1 HSP0 HSP2 HFA0 HFA1 HDF HDS HD FRG FRH FRF FRS RFR RFF RFS.
  unfold shadow_addr, ASAN_K in *.
  pose proof (munch_refl [(SP - 144, SP); (FA, FA + 24);
                          (FA / 8 + 2147450880, FA / 8 + 2147450888)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HFA8 : 0 <= FA / 8) by (apply Z.div_pos; lia).
  assert (UFA : bv_unsigned (Z_to_bv 64 FA) = FA) by (apply unsigned_lit; lia).
  assert (USP1 : bv_unsigned (Z_to_bv 64 SP1) = SP1) by (apply unsigned_lit; lia).
  assert (ESHR : Z.shiftr FA 3 = FA / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  destruct HD as [HD | HD]; cm_seg2_run UFA USP1 ESHR FA.
Qed.
