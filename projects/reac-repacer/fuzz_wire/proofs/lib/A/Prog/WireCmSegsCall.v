(* WireCmSegsCall: cm_seg6_F, the footprint (lib/Lib/ExecF.v evtF) run of check_meter (fuzz_wire.asan 0x80340)
   from the join 0x804e0 up to the `jal rp_meter_counter` at 0x80504, stepped by lib/Lib/StepF.v. Form and
   helpers: lib/A/Prog/WireCmSegs.v (cm_forget, and the fake frame against its own shadow bytes taken as one case
   split at the top), itself in the form of reac-repacer/fuzz_uci lib/A/Prog/UciCvSegs.v.
   The instructions (s6 = the fake frame, s7 = its shadow address, s3 = f, s4 = n):
     0x804e0 addi s5, s6, 32          s5 = frame + 32, the local counter inside the fake frame;
     0x804e4 li a0, 2                 a0 = 2;
     0x804e8 sb a0, 4(s7)             the shadow byte of frame + 32 (shadow + 4) := 2, the counter's two bytes
                                      addressable;
     0x804ec lui a0, 0xa              a0 = 0xa000;
     0x804f0 addi a0, a0, 1475        a0 = 0xa5c3 = 42435;
     0x804f4 sh a0, 0(s5)             the counter := 0xa5c3, the untouched value;
     0x804f8 mv a0, s3                a0 = f;
     0x804fc mv a1, s4                a1 = n;
     0x80500 mv a2, s5                a2 = frame + 32;
     0x80504 jal 0x81168              ra = 0x80508, to rp_meter_counter.
   The only stores are the shadow byte and the counter; the post keeps the frame and its shadow as one block
   each and reads the counter's two bytes back from the frame's cells. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import
PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c check_meter.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WireCmSegs.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* helper                                                              *)
(* ------------------------------------------------------------------ *)

(* The two bytes of a C2 cell that follows a CB block, read back as bytes at their address. *)
Lemma cm_c2_bytes : forall m A n1 j1 v rest,
  rw_cells rsegs m A (CB n1 j1 :: C2 v :: rest) -> bytes_at rsegs m (A + Z.of_nat n1) (le2 v).
Proof.
  intros m A n1 j1 v rest [[Hwf Hb] _].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L1 _].
  cbn [cells_bytes cbytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite L1 in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

(* One byte of a cell list that follows a block, read back at its address: the shadow byte the instruction
   `sb a0, 4(s7)` leaves, which makes the counter's two bytes addressable. *)
Lemma cm_c1_bytes : forall m A n1 j1 (b : byte) rest,
  rw_cells rsegs m A (CB n1 j1 :: C1 b :: rest) -> bytes_at rsegs m (A + Z.of_nat n1) [b].
Proof.
  intros m A n1 j1 b rest [[Hwf Hb] _].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L1 _].
  cbn [cells_bytes cbytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite L1 in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

(* ------------------------------------------------------------------ *)
(* cm_seg6_F : 0x804e0 -> the `jal rp_meter_counter` at 0x80504         *)
(* ------------------------------------------------------------------ *)

(* The script of cm_seg6_F, run once for each side of the fake frame's position against its own shadow bytes
   (below it in high application memory, above it in low application memory). *)
Ltac cm_seg6_run FAv :=
  do 10 step;
  match goal with H : rw_cells rsegs ?mm FAv _ |- _ =>
    let HB := fresh "HB2" in
    pose proof (cm_c2_bytes mm FAv _ _ _ _ H) as HB; change (Z.of_nat 32) with 32 in HB end;
  match goal with H : rw_cells rsegs ?mm (FAv / 8 + 2147450880) _ |- _ =>
    let HS := fresh "HS1" in
    pose proof (cm_c1_bytes mm (FAv / 8 + 2147450880) _ _ _ _ H) as HS;
    change (Z.of_nat 4) with 4 in HS end;
  match goal with H : rw_cells rsegs ?mm FAv _ |- _ =>
    destruct (cm_forget mm FAv _ 64%nat H ltac:(reflexivity)) as [? ?] end;
  match goal with H : rw_cells rsegs ?mm (FAv / 8 + 2147450880) _ |- _ =>
    destruct (cm_forget mm (FAv / 8 + 2147450880) _ 8%nat H ltac:(reflexivity)) as [? ?] end;
  apply evtF_done; do 3 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split;
  [ match goal with |- bytes_at _ _ ?A _ => replace A with (FAv / 8 + 2147450880 + 4) by lia end; eassumption
  | match goal with |- bytes_at _ _ ?A _ => replace A with (FAv + 32) by lia end; eassumption ].

Lemma cm_seg6_F :
  forall (RNG : ExecF.footprint)
         (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (SP SP1 FA f n eo want : Z) (jF jsh : list byte),
    SP - 144 <= SP1 <= SP - 128 -> 0 <= SP - 144 -> SP <= 2 ^ 47 ->
    4096 <= FA -> FA + 64 <= 2 ^ 47 ->
    FA + 64 <= SP - 144 -> FA / 8 + ASAN_K + 8 <= SP - 144 ->
    FA / 8 + ASAN_K + 8 <= FA \/ FA + 64 <= FA / 8 + ASAN_K ->
    rw_cells rsegs m FA [CB 64 jF] ->
    rw_cells rsegs m (shadow_addr FA) [CB 8 jsh] ->
    ExecF.rng RNG FA 64 -> ExecF.rng RNG (shadow_addr FA) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 jF' jsh',
         ms' = MS (mkR (Z_to_bv 64 0x80508) (Z_to_bv 64 SP1) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SP1)
                     (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 (FA + 32)) a3 a4 a5 a6 a7
                     (Z_to_bv 64 FA) (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 (FA + 32)) (Z_to_bv 64 FA)
                     (Z_to_bv 64 (shadow_addr FA)) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 eo) (Z_to_bv 64 want)
                     s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81168) fc None m1 (seg_rom rsegs) /\
         munch [(FA + 32, FA + 34); (shadow_addr FA, shadow_addr FA + 8)] m m1 /\
         wmono rsegs m m1 /\
         rw_cells rsegs m1 FA [CB 64 jF'] /\
         rw_cells rsegs m1 (shadow_addr FA) [CB 8 jsh'] /\
         bytes_at rsegs m1 (shadow_addr FA + 4) [Z_to_bv 8 2] /\
         bytes_at rsegs m1 (FA + 32) (le2 (Z_to_bv 64 42435)))
      (MS (mkR ra (Z_to_bv 64 SP1) gp tp t0 t1 t2 (Z_to_bv 64 SP) (Z_to_bv 64 SP1)
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 FA) (Z_to_bv 64 f) (Z_to_bv 64 n) s5 (Z_to_bv 64 FA)
             (Z_to_bv 64 (shadow_addr FA)) (Z_to_bv 64 ASAN_K) (Z_to_bv 64 eo) (Z_to_bv 64 want)
             s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x804e0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s11 t3 t4 t5 t6 F fc m SP SP1 FA f n eo want jF jsh
    HSP1 HSP0 HSP2 HFA0 HFA1 HDF HDS HD FRF FRS RFF RFS.
  unfold shadow_addr, ASAN_K in *.
  pose proof (munch_refl [(FA + 32, FA + 34); (FA / 8 + 2147450880, FA / 8 + 2147450888)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HFA8 : 0 <= FA / 8) by (apply Z.div_pos; lia).
  destruct HD as [HD | HD]; cm_seg6_run FA.
Qed.
