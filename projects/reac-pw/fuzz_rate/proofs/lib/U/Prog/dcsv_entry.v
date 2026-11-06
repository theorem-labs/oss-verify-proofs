From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import printf_facts_c snprintf_c reac_rate_drivable_csv_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import dcsv_lib dcsv_defs.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** The entry of drivable_csv (UBSan 0x14dcc .. 0x14e58): the 176-byte frame, the 13 saves, buflen and buf to
    sp + 8 / sp + 0x10, s3 = mask, len = 0, tmp[0] = 0, and the loop constants; it reaches the loop head 0x14e5c with
    the invariant of pass 0. *)

Section Entry.
Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word)
  (S0 lo n buf : Z) (m0 : word -> option byte) (canary : word) (junk : list byte) (F0 : bvmap 5 word)
  (fc0 : bv 32).
Hypothesis HK : lo + 6112 <= S0.
Hypothesis HI : 0x50cc8 <= lo.
Hypothesis H63 : S0 < 2^63.
Hypothesis Hn : 0 <= n <= 23.
Hypothesis HB0 : 0 < n -> 0 < buf /\ (buf + n <= lo \/ S0 <= buf).
Hypothesis HBR : 0 < n -> rw_cells rsegs m0 buf [CB (Z.to_nat n) junk].
Hypothesis ST0 : stk rsegs m0 lo S0.
Hypothesis MI0 : mem_inv rsegs m0.
Hypothesis FC0 : frm0 fc0.
Hypothesis GG0 : bytes_at rsegs m0 GOT_GUARD (le8 (Z_to_bv 64 GUARD)).
Hypothesis GD0 : bytes_at rsegs m0 GUARD (le8 canary).

Local Abbreviation SV := (dsv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Abbreviation OK := (dok S0 lo n buf mask SV m0 canary junk F0).
Local Abbreviation ST := (dst gp tp mask S0).

Lemma dcsv_entry : forall Q,
  (forall len r6 r9 m F fc (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     OK 0 len r6 r9 m F fc ->
     evt rsegs Q (ST 0x14e5c len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 96000) x9 x10 x11 x12 x13 x14 x15 x16 x17
                     x28 x29 x30 x31)) ->
  evt rsegs Q (MS (mkR ra (Z_to_bv 64 S0) gp tp t0 t1 t2 s0 s1 mask (Z_to_bv 64 buf) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F0 (Z_to_bv 64 0x14dcc) fc0 None m0 (seg_rom rsegs)).
Proof.
  intros Q K.
  assert (H0 : bytes_at rsegs m0 GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ bytes_at rsegs m0 GUARD (le8 canary) /\
               (0 < n -> rw_cells rsegs m0 buf [CB (Z.to_nat n) junk]))
    by exact (conj GG0 (conj GD0 HBR)).
  clear GG0 GD0 HBR.
  pose proof ST0 as ST. pose proof ST as (Hlo & _ & _).
  pose proof (munch_refl [(lo, S0)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof MI0 as MI. clear MI0.
  carve_frame 176%nat ST.
  (* addi sp, sp, -0xb0; the 13 saves; sd a2, 8(sp); sd a1, 0x10(sp); mv s3, a0; mv s2, zero *)
  do 18 step.
  (* sb zero, 0x28(sp) *)
  step. fix_zero_store.
  (* addi a7, sp, 0x28; addi s6, zero, 3; auipc / lui x 7; not s8, a7 *)
  do 10 step.
  try (rewrite (unsigned_lit (S0 + -136)) by lia); try (rewrite zb_lxor_ones by lia).
  (* addi s9; addiw s10; addi s11; addi s7; addi s4; addiw s0; addiw s5 *)
  do 7 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m end.
  lazymatch type of FR with
  | rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      change (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with ([c1; c2; c3] ++ [c4; c5; c6] ++ rest) in FR
  end.
  apply rw_cells_app in FR. destruct FR as [FA FR]. apply rw_cells_app in FR. destruct FR as [FM FS].
  cbn [cells_size csize Nat.add] in FM, FS.
  replace (S0 + -176 + Z.of_nat 24) with (S0 + -152) in FM by lia.
  replace (S0 + -176 + Z.of_nat 24 + Z.of_nat 48) with (S0 + -104) in FS by lia.
  pose proof (stk_of_rw_cells rsegs m _ _ FM) as SC. cbn [cells_size csize Nat.add] in SC.
  replace (S0 + -152 + Z.of_nat 48) with (S0 + -104) in SC by lia.
  lazymatch type of FM with
  | rw_cells _ _ _ [?d1; ?d2; ?d3] => change [d1; d2; d3] with ([d1] ++ [d2] ++ [d3]) in FM
  end.
  apply rw_cells_app in FM. destruct FM as [_ FM]. apply rw_cells_app in FM. destruct FM as [FZ _].
  cbn [cells_size csize Nat.add] in FZ. destruct FZ as [[_ BZ] _]. cbn [cells_bytes cbytes] in BZ.
  rewrite app_nil_r in BZ. replace (S0 + -152 + Z.of_nat 16) with (S0 + -136) in BZ by lia.
  destruct H0 as (GG & GD & HBR).
  eapply K. unfold dok. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; [exact FC0 | intros k Hk; reflexivity]].
  unfold dmem, dkeep. split; [|split; [exact ST|split; [exact SC|split; [exact BZ|split; [exact MI|split; [exact WM | exact MU]]]]]].
  unfold GOT_GUARD, GUARD in *.
  split; [eexists; exact FA|]. split; [exact FS|].
  split; [eapply bytes_at_tr; [exact GG | exact MU |]; intros x Hx; rewrite length_le8 in Hx; cbn [outside]; lia|].
  split; [eapply bytes_at_tr; [exact GD | exact MU |]; intros x Hx; rewrite length_le8 in Hx; cbn [outside]; lia|].
  intros Hn0. destruct (HB0 Hn0) as (Hb0 & Hbl).
  eapply rw_cells_tr; [exact (HBR Hn0) | exact MU | exact WM |]. cbn [cells_size csize].
  intros x Hx. cbn [outside]. lia.
Qed.

End Entry.
