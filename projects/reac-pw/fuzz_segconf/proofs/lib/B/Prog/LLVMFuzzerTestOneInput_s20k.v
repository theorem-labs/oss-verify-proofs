(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the call of send_message in LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, jal at 0x86714, back at 0x86718), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s30.v, with its module paths and module names changed; 674 of its 724 lines of code are new or changed and 291 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of the
   walk of segments S11 (0x85868 .. 0x85980: the probe loop, the "nosuch0" pair, checks 24 and 25, the UBSan trap
   branches 0x858c0 / 0x858c8, calloc(cap + 1, 18)) and S12 (0x85984 .. 0x85990: calloc(cap + 1, 20)) of the test
   harness's entry function LLVMFuzzerTestOneInput (0x84dc0).

   proves function LLVMFuzzerTestOneInput (reuse search, rule 24: released units, the earlier proof delivery and working
   heads; the result is recorded with the commissioning brief; none: written new, ADAPTED from the image-A twin's
   S11 / S12 walk, the image-A G1 walk owner's LLVMFuzzerTestOneInput_s20k.v / _s20.v)

   This file holds: the inner cut statements of S11 (the probe loop's head, the points after its snprintf and
   before its latch, and the "nosuch0" pair's two points), the model facts the loop needs (the probe text, the
   harness's probe checks from SegModel.segconf_agrees), the facts of the frame state carried across a call, and the
   walk form of the calloc rule. The segment lemmas are in LLVMFuzzerTestOneInput_s20.v. The form and the lemma
   names are the image-A twin's (the image-A G1 walk owner's S11 / S12 walk); registers, slots and pcs are image B's
   (the image-B map PLAN-asanubsan-main.md, sections 2.3, 4, 5, 10, 11).

   THE CODE (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 684-758, image B):
     0x85868 ld a0,176(s1); lb a0,0(a0); bnez 0x86028     check 24 of m->n (SH(m + 0x2000) from 176(s1); its
                                                           shadow byte is 0: m + 0x2000 .. + 7 lie in m's block)
     0x85874 ld a0,216(s1); lw a0,0(a0); blez a0,0x85948   n = m->n; no turn when n <= 0
     0x85880 .. 0x858ac  s2 = 256 i = 0, s4 = i = 0, s5 = 2, s6 = 32, s7 = -8, s3 = "%sx" (0x21020, A_OBJ 7),
                         s8 = ((m + 0x2000) & 7) + 3, s9 = 192(s1) = m, s10 = 120(s1) = FR + 192 (probe)
     0x858b0 (H i)  ld a0,184(s1); sb zero,24(a0); sb zero,25(a0); sb s5,26(a0)   probe in scope (00 00 02)
                    beq s4,s6,TRAP (i = 32: refuted, i < m->n <= 32); ld a0,208(s1) (= ~M);
                    bltu a0,s2,TRAP (M + 256 i wraps: refuted, m's block below 2 ^ 63)
                    a3 = s9 + s2 = m->seg[i].name, a1 = 18, a0 = s10 = probe, a2 = s3 = "%sx"; jal snprintf
     0x858e0 (A i)  a0 = probe; jal strlen; a2 = a0; a0 = s9 = m; a1 = probe; jal m_find
     0x858f8        bnez a0,0x85908; a0 = 168(s1) = c; a1 = 120(s1) = probe; jal check_absent
     0x85908 (Z i)  ld a0,184(s1); sb s7,24/25/26(a0)                 probe out of scope (0xf8)
     0x85918        ld a0,176(s1); lb a0,0(a0); bnez 0x8593c         check 25 of m->n
     0x85924        ld a0,216(s1); lw a0,0(a0); s4 += 1; s2 += 256; blt s4,a0,0x858b0; j 0x85948
     0x85948 (N)    a1 = "nosuch0" (0x21040, A_OBJ 8); a2 = 7; a0 = 192(s1) = m; jal m_find; bnez a0,0x85970
                    a1 = "nosuch0"; a0 = 168(s1) = c; jal check_absent
     0x85970 (NZ)   s3 = 56(s1) + 1 = cap + 1; a1 = 18; a0 = s3; jal calloc                -> K85984
     0x85984 (S12)  s2 = a0 = tab; a1 = 20; a0 = s3; jal calloc                          -> K85994

   The snprintf wrapper returns at a new FP state (row 4's post), so every inner statement is taken at every FP
   state (the S20A_<x> forms), as the cut statements are (LTA_<cut>).

   The kit lemmas' proofs are the image-A twin's (the image-A G1 walk owner's S11 / S12 walk
   LLVMFuzzerTestOneInput_s20k.v as built on its VM, 2026-10-30 18:1x-18:3xZ), renamed to image B: KIT-1 (the model)
   verbatim, with
   SegModel.cut_nul_id for its cut_nul helper; KIT-2 with image B's lt_frame (SH(FR) at 184(s1) its last conjunct);
   KIT-3 with image B's frame (S1 352 .. 383 bytes below SP0), slots (LT_LC, 120, 176) and lt_img carried by RELRO
   in the image (s20_img_relro, a field of image B's SegRecBase.seg_img_facts) and the stack-protector cells re-read
   from AR at the later state (SegRecCells.seg_rec_cells: the .got word gotwA is runtime-owned in the regenerated
   listing, the image-B listing owner's commit ec20d5d4e1df). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_find_c check_absent_c reac_segconf_find_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtSegCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecCells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================================== the model's part (no machine) ===================================== *)
(* the probe text of a name (fuzz_segconf.c:640, snprintf(probe, 18, "%sx", name)): the name and 'x' *)
Lemma s20_probe_text : forall s : list Z, SegModel.nulfree s -> (length s < 17)%nat ->
  SegModel.snprintf_s 18 SegModel.F_probe [SegModel.AS s] = s ++ [120].
Proof.
  intros s Hn Hl. unfold SegModel.snprintf_s.
  replace (SegModel.fmt SegModel.F_probe [SegModel.AS s]) with (SegModel.cut_nul s ++ [120]) by reflexivity.
  rewrite (SegModel.cut_nul_id s Hn). apply firstn_all2. rewrite length_app. cbn [length]. lia.
Qed.

(* the harness's probe checks hold of the run of every payload (SegModel.segconf_agrees, harness_ok's fifth and
   sixth conjuncts) *)
Lemma s20_probe_ok_all : forall pl : list byte,
  forallb (fun g => SegModel.probe_ok (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl)))
                      (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl)))
                      (SegModel.snprintf_s 18 SegModel.F_probe [SegModel.AS (SegModel.ms_name g)]))
    (SegModel.mc_seg (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl)))) = true /\
  SegModel.probe_ok (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl)))
    (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl))) SegModel.S_nosuch = true.
Proof.
  intros pl.
  assert (Hd : Forall (fun b => 0 <= b < 256) (seg_spec.seg_in pl)).
  { unfold seg_spec.seg_in, seg_spec.zs. apply Forall_map, Forall_forall. intros b _.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. }
  pose proof (SegModel.segconf_agrees (seg_spec.seg_in pl) Hd) as H.
  change (SegModel.decode (seg_spec.seg_in pl)) with (seg_spec.seg_pay pl) in H.
  unfold SegModel.harness_ok in H. revert H. unfold seg_spec.seg_rc, seg_spec.seg_mc.
  destruct (SegModel.run (seg_spec.seg_pay pl)) as [[c m] ret]. cbn [fst snd]. intros H.
  cbv beta iota zeta in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H H6].
  apply andb_true_iff in H as [_ H5]. split; assumption.
Qed.

(* check_absent's model premise where m_find missed *)
Lemma s20_absent_of : forall rc mc p, SegModel.probe_ok rc mc p = true -> SegModel.m_find mc p = None ->
  SegModel.absent rc p = true.
Proof. intros rc mc p H E. unfold SegModel.probe_ok in H. rewrite E in H. exact H. Qed.

(* m_find answers an index of the table *)
Lemma s20e_m_find_go : forall l nm k i, SegModel.m_find_go l nm k = Some i -> (k <= i < k + length l)%nat.
Proof.
  induction l as [|g l IH]; intros nm k i H; cbn [SegModel.m_find_go] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end;
    [injection H as <-; cbn [length]; lia|].
  apply IH in H. cbn [length]. lia.
Qed.
Lemma s20_m_find_lt : forall mc p j, SegModel.m_find mc p = Some j -> (j < length (SegModel.mc_seg mc))%nat.
Proof. intros mc p j H. unfold SegModel.m_find in H. apply s20e_m_find_go in H. lia. Qed.

(* m_find_ptr is 0 exactly on a miss, for a block at 4096 or above holding at most 32 entries *)
Lemma s20_m_find_ptr_cases : forall m mc l, 4096 <= m -> m + seg_spec.SEG_M_SIZE <= 2 ^ 63 ->
  (length (SegModel.mc_seg mc) <= 32)%nat ->
  (SegModel.m_find mc l = None /\ m_find_c.m_find_ptr m mc l = 0) \/
  (exists j, SegModel.m_find mc l = Some j /\ m_find_c.m_find_ptr m mc l = seg_spec.mseg_addr m j /\
     4096 <= seg_spec.mseg_addr m j < 2 ^ 63).
Proof.
  intros m mc l H4096 Hhi L32. unfold m_find_c.m_find_ptr.
  destruct (SegModel.m_find mc l) as [j|] eqn:E; [right|left; split; reflexivity].
  exists j. split; [reflexivity|]. split; [reflexivity|].
  pose proof (s20_m_find_lt mc l j E) as Hj.
  unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. unfold seg_spec.SEG_M_SIZE in Hhi. lia.
Qed.

(* ===================================== the inner cut points ===================================== *)
(* offsets from BASE = 0x84dc0 (each checked against the excerpt: dis lines 696, 714, 724, 740, 750) *)
Definition LO_H : Z := 0xaf0.   (* 0x858b0: the probe loop's head, turn i *)
Definition LO_A : Z := 0xb20.   (* 0x858e0: snprintf returned *)
Definition LO_Z : Z := 0xb48.   (* 0x85908: after m_find and check_absent, before the latch *)
Definition LO_N : Z := 0xb88.   (* 0x85948: the "nosuch0" pair *)
Definition LO_NZ : Z := 0xbb0.  (* 0x85970: after it, before calloc(cap + 1, 18) *)
(* the frame's objects with the probe in scope (its shadow 00 00 02, 0x858b4 .. 0x858bc) *)
Definition LFO_P : lfo := mkLFO false false false true false.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the probe text of turn i: m->seg[i].name and 'x' *)
Definition s20_T (cx : lcx) (i : nat) : list Z := SegModel.ms_name (x_seg cx i) ++ [120].
(* the probe buffer: the frame's object at FR + 192 *)
Definition s20_probe (cx : lcx) : Z := x_fr cx + FO_PROBE.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* what every point of S11 states beyond its registers (K85868's premises with the probe's scope as o) *)
Definition s20_ctx (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) (o : lfo) (c m : Z)
  : Prop :=
  lt_core B MT cx ly S W regs mem md k acc 6 o [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_slots cx (rdW W mem)
    (LT_LC cx c m ++ [(120, x_fr cx + FO_PROBE); (176, shadow_addr (m + seg_spec.MC_N))]) /\
  lt_cm (rdW W mem) c m (x_run cx).
(* the probe loop's callee-saved registers at turn i (image B): s2 = 256 i, s3 = "%sx", s4 = i, s5 = 2, s6 = 32,
   s7 = -8, s9 = m, s10 = the probe (s8, read only by check 25's slow path, is not stated) *)
Definition s20_lregs (cx : lcx) (regs : bvmap 5 word) (m : Z) (i : nat) : Prop :=
  getr regs 18 = w64 (seg_spec.MSEG_SIZE * Z.of_nat i) /\ getr regs 19 = w64 (VAL (A_OBJ 7)) /\
  getr regs 20 = w64 (Z.of_nat i) /\ getr regs 21 = w64 2 /\ getr regs 22 = w64 32 /\
  getr regs 23 = w64 (-8) /\ getr regs 25 = w64 m /\ getr regs 26 = w64 (s20_probe cx).

(* 0x858b0: the head of turn i < m->n, the probe out of scope *)
Definition S20_H_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s20_ctx cx ly S W regs mem md k acc LFO0 c m ->
  s20_lregs cx regs m i ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_H) regs mem md) (lt_post B MT cx).

(* 0x858e0: snprintf returned; the probe in scope, holding the turn's text and its NUL *)
Definition S20_A_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s20_ctx cx ly S W regs mem md k acc LFO_P c m ->
  s20_lregs cx regs m i ->
  sa_zs (rdW W mem) (s20_probe cx) (s20_T cx i ++ [0]) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_A) regs mem md) (lt_post B MT cx).

(* 0x85908: m_find and (on a miss) check_absent returned; the probe still in scope *)
Definition S20_Z_stmt (i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (x_mcF cx)))%nat ->
  s20_ctx cx ly S W regs mem md k acc LFO_P c m ->
  s20_lregs cx regs m i ->
  sa_zs (rdW W mem) (s20_probe cx) (s20_T cx i ++ [0]) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_Z) regs mem md) (lt_post B MT cx).

(* 0x85948: past the probe loop (or no turn); image B keeps nothing in a register here (m and c from 192(s1) /
   168(s1)) *)
Definition S20_N_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 ->
  s20_ctx cx ly S W regs mem md k acc LFO0 c m ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_N) regs mem md) (lt_post B MT cx).

(* 0x85970: past the "nosuch0" pair *)
Definition S20_NZ_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 ->
  s20_ctx cx ly S W regs mem md k acc LFO0 c m ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_NZ) regs mem md) (lt_post B MT cx).

(* ---- what a call keeps of the frame state: the interface between each call's post and the carry lemmas ----
   the harness's real-stack frame part [S1, SP0) (the s1 slots, 184(s1) SH(FR) and 200(s1) the shadow base among
   them, and the 13 saved registers), the image's unowned bytes but errno (the read-only view, the literals, the
   table, longl, the cells), the side-stack frame's header words FR + 0 .. 24 and its flag word FR + 504, its 36
   shadow bytes, and the blocks c and m *)
Definition s20_kept (cx : lcx) (c m : Z) (W : world SEGS) mem (W2 : world SEGS) mem2 : Prop :=
  (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a) /\
  (forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + LT_FLAGW <= a < x_fr cx + LT_FLAGW + 8 ->
     rdW W2 mem2 a = rdW W mem a) /\
  (forall a, x_sh cx <= a < x_sh cx + 36 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE \/ m <= a < m + seg_spec.SEG_M_SIZE -> rdW W2 mem2 a = rdW W mem a).
(* the registers lt_frame names: sp, gp, tp, s0, s1 *)
Definition s20_rkept (regs regs2 : bvmap 5 word) : Prop :=
  getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
  getr regs2 8 = getr regs 8 /\ getr regs2 9 = getr regs 9.

End e.
End f.
End d.

Section lta. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Definition S20A_H (B : asyms) (MT : ameter_ops) (i : nat) : Prop :=
  forall fx1 : YK11.FPState, S20_H_stmt (fx := fx1) B MT i.
Definition S20A_A (B : asyms) (MT : ameter_ops) (i : nat) : Prop :=
  forall fx1 : YK11.FPState, S20_A_stmt (fx := fx1) B MT i.
Definition S20A_Z (B : asyms) (MT : ameter_ops) (i : nat) : Prop :=
  forall fx1 : YK11.FPState, S20_Z_stmt (fx := fx1) B MT i.
Definition S20A_N (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, S20_N_stmt (fx := fx1) B MT.
Definition S20A_NZ (B : asyms) (MT : ameter_ops) : Prop := forall fx1 : YK11.FPState, S20_NZ_stmt (fx := fx1) B MT.
End lta.

(* ======================================= the kit's lemmas ======================================= *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
(* AR's record law over B (a theorem of image B's kit copy: lib/B/YG0q.v:809 AR_laws_ok) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the image facts: image B's record SegRecBase.seg_img_facts (lib/B/Prog/SegRecBase.v, the image-B listing owner's commit c4abdaee306f),
   taken whole; lt_img at a later reader needs RELRO in the image (cif_relro_img; RLO_A / RHI_A are SEG_RLO /
   SEG_RHI) and, through SegRecCells.seg_rec_cells, the guard's ROM bytes (cif_guard_rom, guardA = 0x5ff838) *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the record of image B's symbols (lib/B/YF0m.v), which SegRecCells.seg_rec_cells takes: the stack-protector cells
   (the runtime-owned .got word gotwA = 0xa3e98 holds guardA, guardA readable) at every AR state *)
Hypothesis HSY : YF0m.SegBSyms B.
Lemma s20_img_relro : forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a.
Proof. intros a Ha. eapply cif_relro_img; [exact IMGF | exact Ha]. Qed.

(* ---- the model's objects through the reader (KIT-1) ---- *)
(* list helpers: the byte k of a field, and the byte k of a little-endian number *)
Lemma s20e_nth_firstn : forall {A} (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n k d Hk; [destruct n; reflexivity|].
  destruct n as [|n]; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s20e_nth_skipn : forall {A} (l : list A) off k d, nth k (skipn off l) d = nth (off + k) l d.
Proof.
  intros A l off. revert l. induction off as [|off IH]; intros l k d; [reflexivity|].
  destruct l as [|x l]; [destruct k; reflexivity|]. exact (IH l k d).
Qed.
Lemma s20e_nth_fld : forall (bs : list byte) off n k d, (k < n)%nat ->
  nth k (seg_spec.fld off n bs) d = nth (off + k) bs d.
Proof. intros bs off n k d Hk. unfold seg_spec.fld. rewrite s20e_nth_firstn by exact Hk. apply s20e_nth_skipn. Qed.
Lemma s20e_le_nth : forall n z k, 0 <= z -> (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
  induction n as [|n IH]; intros z k Hz Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by (try apply Z.shiftr_nonneg; lia).
    rewrite Z.shiftr_shiftr by lia. rewrite Nat2Z.inj_succ. f_equal. f_equal. lia.
Qed.
Lemma s20e_u32_byte : forall v f k, seg_spec.u32_enc v f -> (k < 4)%nat -> bv_unsigned (nth k f ZB0) = le_byte v 4 k.
Proof.
  intros v f k [Hv ->] Hk. unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.
  assert (H64 : 2 ^ 32 < bv_modulus 64) by (vm_compute; reflexivity).
  rewrite Z_to_bv_unsigned, bv_wrap_small by lia.
  rewrite s20e_le_nth by lia. unfold le_byte.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
(* m->n: the 4 bytes at m + 0x2000 hold the number of segments, at most 32 *)
Lemma s20_mconf_n : forall rd m mc, sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_N) 4 (Z.of_nat (length (SegModel.mc_seg mc))) /\
  (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
  intros rd m mc (bs & HB & L & L32 & _ & HN & _). split; [|exact L32].
  intros k Hk.
  assert (Hj : (Z.to_nat seg_spec.MC_N + k < length bs)%nat)
    by (unfold seg_spec.SEG_M_SIZE in L; unfold seg_spec.MC_N; lia).
  pose proof (HB _ Hj) as E.
  replace (m + Z.of_nat (Z.to_nat seg_spec.MC_N + k)) with (m + seg_spec.MC_N + Z.of_nat k) in E
    by (unfold seg_spec.MC_N; lia).
  rewrite E. f_equal.
  rewrite <- (s20e_nth_fld bs (Z.to_nat seg_spec.MC_N) (Z.to_nat 4) k ZB0)
    by (change (Z.to_nat 4) with 4%nat; exact Hk).
  exact (s20e_u32_byte _ _ k HN Hk).
Qed.
(* m->seg[i].name: its bytes and NUL at &m->seg[i], no NUL among them, at most 15 bytes, and the 16-byte field
   mapped (the slack a word-at-a-time reader takes) *)
Lemma s20_mconf_name : forall rd m mc i, sa_mconf rd m mc -> (i < length (SegModel.mc_seg mc))%nat ->
  sa_zs rd (seg_spec.mseg_addr m i) (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d) ++ [0]) /\
  ~ In 0 (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) /\
  (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) < 16)%nat /\
  (forall j, 0 <= j < 16 -> rd (seg_spec.mseg_addr m i + j) <> None).
Proof.
  intros rd m mc i (bs & HB & L & L32 & HS & _) Hi.
  destruct (HS i Hi) as (Lg & (Lf & Ln & Nn & Ez) & _).
  set (f := seg_spec.fld 0 16 (seg_spec.fld (256 * i) 256 bs)) in *.
  set (s := SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) in *.
  assert (Hrd : forall j, (j < 16)%nat ->
    rd (seg_spec.mseg_addr m i + Z.of_nat j) = Some (bv_unsigned (nth j f ZB0))).
  { intros j Hj. unfold f. rewrite (s20e_nth_fld _ 0 16 j ZB0 Hj).
    rewrite (s20e_nth_fld bs (256 * i) 256 (0 + j) ZB0) by lia.
    assert (Hj' : (256 * i + (0 + j) < length bs)%nat) by (unfold seg_spec.SEG_M_SIZE in L; lia).
    rewrite <- (HB _ Hj'). f_equal. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia. }
  split; [|split; [exact Nn | split; [exact Ln |]]].
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    rewrite Hrd by lia. f_equal.
    rewrite <- Ez. rewrite s20e_nth_firstn by lia. unfold seg_spec.zs.
    rewrite <- (map_nth bv_unsigned f ZB0 j). apply nth_indep. rewrite length_map. lia.
  - intros j Hj. rewrite <- (Z2Nat.id j) by lia. rewrite Hrd by lia. discriminate.
Qed.

(* ---- the frame's shadow (KIT-2) ---- *)
(* the probe in scope (shadow 00 00 02): its 18 bytes are addressable *)
Lemma s20_probe_addr : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_frame B cx ly S W regs mem md k o -> fo_probe o = true ->
  sa_addr (rdW W mem) (s20_probe cx) 18.
Proof.
  intros cx ly S W regs mem md k o HF Hp.
  destruct HF as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
  destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
  assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
  assert (Efa : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
  { unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (Hal & Happ & _).
  rewrite Efa in Hal, Happ. change (fs_frame_bytes LT_FCLS) with 512 in Happ.
  pose proof (@ASAN_CEIL_range rc) as [HC _].
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  assert (Exsh : x_sh cx = SHADOW_OFF + x_fr cx / 8) by reflexivity.
  (* the probe's three shadow bytes 00 00 02, and the 36 frame shadow bytes mapped *)
  assert (Hnn : forall i, (i < 36)%nat -> rdW W mem (x_sh cx + Z.of_nat i) <> None).
  { intros i Hi. rewrite (Hsh i ltac:(rewrite lt_fsh_len; exact Hi)). discriminate. }
  destruct o as [o1 o2 o3 o4 o5]. cbn [fo_probe] in Hp. subst o4.
  assert (Z24 : rdW W mem (x_sh cx + 24) = Some 0).
  { pose proof (Hsh 24%nat ltac:(rewrite lt_fsh_len; lia)) as E. change (Z.of_nat 24) with 24 in E.
    destruct o1, o2, o3, o5; exact E. }
  assert (Z25 : rdW W mem (x_sh cx + 25) = Some 0).
  { pose proof (Hsh 25%nat ltac:(rewrite lt_fsh_len; lia)) as E. change (Z.of_nat 25) with 25 in E.
    destruct o1, o2, o3, o5; exact E. }
  assert (Z26 : rdW W mem (x_sh cx + 26) = Some 2).
  { pose proof (Hsh 26%nat ltac:(rewrite lt_fsh_len; lia)) as E. change (Z.of_nat 26) with 26 in E.
    destruct o1, o2, o3, o5; exact E. }
  clear Hsh.
  unfold sa_addr, s20_probe, FO_PROBE.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|]. split.
  - unfold range_addressable, shadow_of_addr, saddr_ok. intros x Hx.
    destruct (Z_lt_le_dec x (x_fr cx + 200)) as [H1|H1]; [|destruct (Z_lt_le_dec x (x_fr cx + 208)) as [H2|H2]].
    + exists 0. split; [|left; reflexivity].
      assert (Ex : SHADOW_OFF + x / 8 = x_sh cx + 24)
        by (rewrite Exsh; clear - Hal Hx H1; Z.div_mod_to_equations; lia).
      rewrite Ex. exact Z24.
    + exists 0. split; [|left; reflexivity].
      assert (Ex : SHADOW_OFF + x / 8 = x_sh cx + 25)
        by (rewrite Exsh; clear - Hal Hx H1 H2; Z.div_mod_to_equations; lia).
      rewrite Ex. exact Z25.
    + exists 2. split; [|right; split; [clear - Hal Hx H2; Z.div_mod_to_equations; lia | lia]].
      assert (Ex : SHADOW_OFF + x / 8 = x_sh cx + 26)
        by (rewrite Exsh; clear - Hal Hx H2; Z.div_mod_to_equations; lia).
      rewrite Ex. exact Z26.
  - intros _. unfold shadow_hull_vis. intros s Hs. unfold shadow_addr in Hs.
    assert (Hlo : x_sh cx + 17 <= s < x_sh cx + 35)
      by (rewrite Exsh; clear - Hal Hs; unfold SHADOW_OFF in *; Z.div_mod_to_equations; lia).
    specialize (Hnn (Z.to_nat (s - x_sh cx)) ltac:(lia)).
    rewrite Z2Nat.id in Hnn by lia. replace (x_sh cx + (s - x_sh cx)) with s in Hnn by lia. exact Hnn.
Qed.
(* the probe lies in the side-stack frame of the state *)
Lemma s20_probe_fframe : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_frame B cx ly S W regs mem md k o -> sa_fframe ly S (s20_probe cx) 18.
Proof.
  intros cx ly S W regs mem md k o (HJ & _).
  destruct HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
  exists LT_FCLS, (x_fpos cx). split; [rewrite Hfrs; apply in_or_app; left; left; reflexivity|].
  split; [unfold LT_FCLS; lia|].
  assert (Efa : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
  { unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite Efa. unfold s20_probe, FO_PROBE. change (fs_frame_bytes LT_FCLS) with 512. lia.
Qed.
(* m->n's shadow byte (checks 24 and 25): 0, the 8 bytes m + 0x2000 .. + 7 lie in m's block *)
Lemma s20_mn_shadow : forall ly S rd m, lt_hblk B ly S rd m seg_spec.SEG_M_SIZE ->
  rd (shadow_addr (m + seg_spec.MC_N)) = Some 0.
Proof.
  intros ly S rd m (_ & H4096 & H16 & (_ & _ & _ & HR & _)).
  destruct (HR (m + 8199) ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as (s & Es & Hs).
  unfold shadow_of_addr in Es. unfold saddr_ok in Hs.
  assert (Hs0 : s = 0)
    by (destruct Hs as [Hs | Hs]; [exact Hs | exfalso; clear - H16 Hs; Z.div_mod_to_equations; lia]).
  subst s. unfold shadow_addr, seg_spec.MC_N.
  assert (E : (m + 0x2000) / 8 = (m + 8199) / 8) by (clear - H16; Z.div_mod_to_equations; lia).
  rewrite E. exact Es.
Qed.

(* ---- the frame state across a call (KIT-3) ---- *)
(* the entry's numbers: SP0 16-aligned, at least 32768 above the allocator ceiling (the stack window), S1 the
   32-aligned base 352 .. 383 below SP0, the layout's top within 2 ^ 47 (image A's S11 / S12 walk's s20b_nums, with
   image B's 352-byte frame) *)
Lemma s20g_nums : forall cx, lt_base B MT cx ->
  x_sp0 cx - 384 < x_s1 cx /\ x_s1 cx + 352 <= x_sp0 cx /\ alloc_ceiling + 32768 <= x_sp0 cx /\
  x_sp0 cx <= ly_top (x_ly cx) /\ ly_top (x_ly cx) <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0.
Proof.
intros cx HBs. destruct HBs as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
unfold x_s1, x_sp0, LT_FRAME.
pose proof (Z.mod_pos_bound (spZ (x_regs cx) - 352) 32 ltac:(lia)) as M.
lia.
Qed.

(* the frame chain at a call from the harness's sp S1 with s0 = SP0: the entry's chain with the frame record
   (SP0, ra, s0) the prologue saved at SP0 - 8 / SP0 - 16 pushed (achain_push), or none when SP0 is in the top 16
   bytes of the stack (achain's first arm) *)
Lemma s20_achain : forall cx ly S (W : world SEGS) regs mem md k acc rem o O,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  exists ch1, achain ly (rdW W mem) (x_s1 cx) (x_sp0 cx) ch1.
Proof.
intros cx ly S W regs mem md k acc rem o O HBs HC.
pose proof (s20g_nums cx HBs) as (N1 & N2 & N3 & N4 & N5 & N6).
pose proof HBs as (HPRE & _).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & _ & _ & Hch & _).
destruct HC as ((HJ & _ & _ & _ & _ & _ & HSV & _) & _).
destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
destruct (Z_lt_le_dec (x_sp0 cx) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((x_sp0 cx, raZ (x_regs cx), s0Z (x_regs cx)) :: x_ch cx).
  pose proof (HSV 0%nat _ eq_refl) as E0. pose proof (HSV 1%nat _ eq_refl) as E1.
  replace (x_sp0 cx - 8 * Z.of_nat 1) with (x_sp0 cx - 8) in E0 by lia.
  replace (x_sp0 cx - 8 * Z.of_nat 2) with (x_sp0 cx - 16) in E1 by lia.
  apply (achain_push ly (rdW (x_W cx) (x_mem cx)) (rdW W mem) (x_sp0 cx) (s0Z (x_regs cx)) (raZ (x_regs cx))
    (x_ch cx) (x_s1 cx)).
  + apply (achain_ly_top (x_ly cx)); [exact Etop | exact Hch].
  + lia.
  + intros a Ha. apply F1; [lia | lia |]. intros (r & Hr & Hlo & Hhi). unfold ltoi_PG in Hr.
    destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold longlA, A_LONGL, LONGL_N in Hhi. lia.
  + exact E0.
  + exact E1.
  + exact Hra4.
  + lia.
  + lia.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.
(* the saved registers are kept when their 104 bytes are (image A's S11 / S12 walk's s20b_saved_kept; fuzz_command's
   LLVMFuzzerTestOneInput_s65.v lt_saved_kept_loc) *)
Lemma s20g_saved_kept : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' Hk HS i r Hi.
assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
change (length LT_SAVED) with 13%nat in Hi13.
rewrite (rdword_ext rd rd'); [exact (HS i r Hi)|].
intros j Hj. apply Hk. lia.
Qed.
(* a word every byte of which two readers agree on (image B's S01 / S02 walk's lk_word_kept) *)
Lemma s20g_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
(* a literal at a later reader that keeps its bytes and NUL (image B's S01 / S02 walk's lk_lit_kept) *)
Lemma s20g_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros W W' mem mem' a s HK (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
(* the image facts of a point carried to a later reader at an AR state that agrees on every image byte the runtime
   does not own (all of seg_himg's objects are such bytes, sa_img; RELRO by s20_img_relro) and on the ROM bytes; the
   stack-protector cells from AR at the later state (SegRecCells.seg_rec_cells): image B's S01 / S02 walk's
   lk_img_kept and the S04 walk's k14_img_kept, the form of image A's S00 walk's s10_lt_img_kept *)
Lemma s20g_lt_img_kept : forall cx (W W' : world SEGS) mem mem' ly' S' md',
  lt_img B cx (rdW W mem) ->
  AR SEGS B ly' S' W' mem' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof.
intros cx W W' mem mem' ly' S' md' (HRO & HIMG & HGI) HAR' HK.
assert (KI : forall q n, sa_img SEGS B q n -> forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq x Hx. destruct (Hq x Hx) as (H1 & H2 & H3). exact (HK x H1 H2 H3). }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. apply (s20g_lit_kept W W' mem mem' a s); [|exact Hl].
  destruct Hl as (_ & _ & _ & _ & Himg). exact (KI _ _ Himg). }
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & _ & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Ho He. rewrite (HK a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (s20_img_relro a Hrr)].
- split; [intros k Hk; rewrite (KI _ 8 Hm40i) by lia; exact (Hm40 k Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (KL _ _ Hl)].
    apply (s20g_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci).
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (KL _ _ Hl)].
    apply (s20g_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi). lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k Hk. rewrite (KI _ _ Hri) by lia. exact (Hrs i Hi k Hk). }
  split; [exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HSY IMGF ly' S' W' mem' md' HAR')))|].
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (KI _ _ Hli) by (unfold LONGL_W, LONGL_N; lia). exact (HGI i Hi).
Qed.
(* lt_core carried to a state that keeps s20_kept's bytes, the five frame registers, and whose journal, blocks and
   budget the call's post gives *)
Lemma s20_core_carry : forall cx ly S (W : world SEGS) regs mem md k acc rem o O c m
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 acc2 rem2 O2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  s20_rkept regs regs2 -> s20_kept B cx c m W mem W2 mem2 ->
  lt_blocks B cx ly2 S2 O2 -> lt_bud MT cx S2 k2 acc2 rem2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 o O2.
Proof.
intros cx ly S W regs mem md k acc rem o O c m ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HBs HC HJ2 HRK HK HBk2 HBd2.
destruct HC as (HF & HI & _ & _).
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & HSB & HZS & HSH).
destruct HRK as (K2 & K3 & K4 & K8 & K9).
destruct HK as (KS & KI & KF & KH & KB).
pose proof (s20g_nums cx HBs) as (N1 & N2 & N3 & N4 & N5 & N6).
split; [|split; [exact (s20g_lt_img_kept cx W W2 mem mem2 ly2 S2 md2 HI (proj1 HJ2) KI) | split; [exact HBk2 | exact HBd2]]].
split; [exact HJ2|].
split; [exact (eq_trans K2 R2)|]. split; [exact (eq_trans K3 R3)|]. split; [exact (eq_trans K4 R4)|].
split; [exact (eq_trans K8 R8)|]. split; [exact (eq_trans K9 R9)|].
split; [apply (s20g_saved_kept cx (rdW W mem) (rdW W2 mem2)); [intros a Ha; apply KS; lia | exact HSV]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact HH0 | intros j Hj; apply KF; left; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact HH8 | intros j Hj; apply KF; left; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact HH16 | intros j Hj; apply KF; left; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact HFL | intros j Hj; apply KF; right; lia]|].
split; [rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact HSB | intros j Hj; apply KS; lia]|].
split.
{ intros i Hi. rewrite KH; [exact (HZS i Hi)|]. rewrite lt_fsh_len in Hi. lia. }
rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact HSH | intros j Hj; apply KS; lia].
Qed.
Lemma s20g_req : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
(* a harness block of the state stays one: live (the call's blocks contain the old ones), and its shadow is AR's *)
Lemma s20_hblk_carry : forall ly S (W : world SEGS) mem ly2 S2 (W2 : world SEGS) mem2 md2 a n,
  AR SEGS B ly2 S2 W2 mem2 md2 -> lt_hblk B ly S (rdW W mem) a n ->
  (forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2)) ->
  lt_hblk B ly2 S2 (rdW W2 mem2) a n.
Proof.
intros ly S W mem ly2 S2 W2 mem2 md2 a n HAR2 (Hin & H4 & Hal & Ha0 & Han & Hamr & _ & _) Hsub.
pose proof (Hsub _ Hin) as Hin2. pose proof (s20g_req n) as Rn.
split; [exact Hin2|]. split; [exact H4|]. split; [exact Hal|].
split; [exact Ha0|]. split; [exact Han|]. split; [exact Hamr|]. split.
- exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 a n a n HAR2 Hin2 (Z.le_refl a) ltac:(lia)).
- intros Hn.
  exact (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 a n a n HAR2 Hin2 (Z.le_refl a) ltac:(lia) Hn).
Qed.
(* the s1 slots of s20_ctx lie at offsets 16 .. 216 *)
Lemma s20g_slot_off : forall cx c m o v,
  In (o, v) (LT_LC cx c m ++ [(120, x_fr cx + FO_PROBE); (176, shadow_addr (m + seg_spec.MC_N))]) -> 16 <= o <= 216.
Proof.
intros cx c m o v H. unfold LT_LC in H. cbn [app] in H.
repeat (destruct H as [H | H]; [injection H as <- _; lia |]). destruct H.
Qed.
(* s20_ctx across a call that allocates nothing *)
Lemma s20_ctx_carry : forall cx ly S (W : world SEGS) regs mem md k acc o c m
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 acc2,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  s20_rkept regs regs2 -> s20_kept B cx c m W mem W2 mem2 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> lt_bud MT cx S2 k2 acc2 6 ->
  s20_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 o c m.
Proof.
intros cx ly S W regs mem md k acc o c m ly2 S2 W2 regs2 mem2 md2 k2 acc2 HBs Hctx HJ2 HRK HK HP HBd2.
destruct Hctx as (HC & Hhc & Hhm & HSL & HCM).
pose proof HC as (_ & _ & HBk & _).
pose proof HJ2 as (HAR2 & _).
pose proof HK as (KS & _ & _ & _ & KB).
pose proof (s20g_nums cx HBs) as (N1 & N2 & N3 & N4 & N5 & N6).
assert (Hsub : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym HP) Hpn)).
split; [|split; [|split; [|split]]].
- apply (s20_core_carry cx ly S W regs mem md k acc 6 o _ c m ly2 S2 W2 regs2 mem2 md2 k2 acc2 6 _ HBs HC HJ2 HRK HK);
    [|exact HBd2].
  unfold lt_blocks in *. exact (Permutation_trans HP HBk).
- exact (s20_hblk_carry ly S W mem ly2 S2 W2 mem2 md2 c _ HAR2 Hhc Hsub).
- exact (s20_hblk_carry ly S W mem ly2 S2 W2 mem2 md2 m _ HAR2 Hhm Hsub).
- intros o0 v Hov. pose proof (s20g_slot_off cx c m o0 v Hov) as Ho.
  rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact (HSL o0 v Hov) | intros j Hj; apply KS; lia].
- unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp in *. destruct HCM as ((bs & Hbs & Henc) & (bs' & Hbs' & Henc')).
  split.
  + exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as (Hlen & _).
    rewrite KB; [exact (Hbs i Hi) | left; lia].
  + exists bs'. split; [|exact Henc']. intros i Hi. destruct Henc' as (Hlen & _).
    rewrite KB; [exact (Hbs' i Hi) | right; lia].
Qed.
(* the class-3 frame of the walk's journal: live, at FR in every layout of the journal, inside the application
   memory and below the allocator ceiling (image A's S11 / S12 walk's s20b_jframe) *)
Lemma s20g_jframe : forall cx ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  AR SEGS B ly S W mem md /\ In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512.
Proof.
intros cx ly S W mem md k HJ.
destruct HJ as (HAR & Hly & _ & _ & _ & Hfr & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfr; left; reflexivity).
assert (Efa : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by (unfold x_fr, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (B1 & B2 & B3).
rewrite Efa in B1, B2, B3. change (fs_frame_bytes LT_FCLS) with 512 in B2, B3.
exact (conj HAR (conj Hin (conj Efa (conj B1 (conj B2 B3))))).
Qed.
(* the frame's shadow lies above the image and below the allocator ceiling *)
Lemma s20g_sh_nums : forall cx, 4096 <= x_fr cx -> x_fr cx + 512 <= alloc_ceiling ->
  kImgEnd < x_sh cx /\ x_sh cx + 64 <= alloc_ceiling.
Proof.
intros cx H1 H2. pose proof asan_consts as (C1 & _). unfold x_sh, shadow_addr, SHADOW_OFF, kImgEnd. lia.
Qed.
(* a shadow byte of an address below the ceiling is no byte of application memory *)
Lemma s20g_app_sh : forall f p n a, 0 <= f <= 0x7fffff800000 -> in_app p n -> p <= a < p + n ->
  ~ (shadow_addr f <= a < shadow_addr f + 64).
Proof.
intros f p n a Hf Happ Ha Hs. pose proof asan_consts as (C1 & _).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ. unfold shadow_addr, SHADOW_OFF in Hs. lia.
Qed.
(* s20_kept from a call that keeps every byte outside its stack window [lo, S1) below the harness's sp and outside
   the probe (snprintf writes the probe; strlen, m_find and check_absent write nothing outside their window) *)
Lemma s20_kept_of_win : forall cx ly S (W : world SEGS) regs mem md k acc o c m (W2 : world SEGS) mem2 lo,
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m -> alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < x_s1 cx) -> ~ (s20_probe cx <= a < s20_probe cx + 18) ->
     rdW W2 mem2 a = rdW W mem a) ->
  s20_kept B cx c m W mem W2 mem2.
Proof.
intros cx ly S W regs mem md k acc o c m W2 mem2 lo HBs Hctx Hlo K.
destruct Hctx as (((HJ & _) & _ & _ & _) & (Hc & _ & _ & _) & (Hm & _ & _ & _) & _ & _).
destruct (s20g_jframe cx ly S W mem md k HJ) as (HAR & Hin & Efa & F0 & F1 & Fapp).
pose proof (s20g_nums cx HBs) as (N1 & N2 & N3 & N4 & N5 & N6).
pose proof (s20g_sh_nums cx F0 F1) as (Sh1 & Sh2). unfold kImgEnd in Sh1.
pose proof asan_consts as (C1 & _).
unfold s20_probe, FO_PROBE in K.
split; [|split; [|split; [|split]]].
- intros a Ha. apply K; lia.
- intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr.
  apply K; [lia | lia |]. intros Hp.
  apply (frm_img SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) a HAR Hin); [|exact Hi].
  rewrite Efa. change (fs_frame_bytes LT_FCLS) with 512. lia.
- intros a Ha. unfold LT_FLAGW in Ha. apply K; lia.
- intros a Ha. apply K; [lia | lia |]. intros Hp.
  apply (s20g_app_sh (x_fr cx) (x_fr cx) 512 a); [lia | exact Fapp | lia | unfold x_sh in Ha; lia].
- intros a Ha. destruct Ha as [Ha | Ha].
  + destruct (al_blocks SEGS B LAWS ly S W mem md c _ HAR Hc) as (_ & Hc4 & Hcc & _).
    pose proof (sep_block_frame SEGS B LAWS ly S W mem md c _ LT_FCLS (x_fpos cx) HAR Hc Hin) as D.
    rewrite Efa in D. change (fs_frame_bytes LT_FCLS) with 512 in D. unfold zdisjoint in D. cbn [fst snd] in D.
    assert (RC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity. rewrite RC in Hcc, D.
    unfold seg_spec.SEG_C_SIZE in Ha. apply K; lia.
  + destruct (al_blocks SEGS B LAWS ly S W mem md m _ HAR Hm) as (_ & Hm4 & Hmc & _).
    pose proof (sep_block_frame SEGS B LAWS ly S W mem md m _ LT_FCLS (x_fpos cx) HAR Hm Hin) as D.
    rewrite Efa in D. change (fs_frame_bytes LT_FCLS) with 512 in D. unfold zdisjoint in D. cbn [fst snd] in D.
    assert (RM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity. rewrite RM in Hmc, D.
    unfold seg_spec.SEG_M_SIZE in Ha. apply K; lia.
Qed.
(* s20_kept from an allocator call's acall_kept (calloc): the new block E is apart from the frame, its shadow, the
   image and the blocks c and m *)
Lemma s20_kept_of_acall : forall cx ly S (W : world SEGS) regs mem md k acc rem o O c m ly2 S2 (W2 : world SEGS)
  mem2 md2 k2 slo (E : Z -> Prop),
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S) -> In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) ->
  acall_kept SEGS B ly S W mem W2 mem2 slo (x_s1 cx) E ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  (exists p n, ablocks B ly2 S2 = ablocks B ly S ++ [(p, n)] /\ forall a, E a -> p <= a < p + req_size n) ->
  s20_kept B cx c m W mem W2 mem2.
Proof.
intros cx ly S W regs mem md k acc rem o O c m ly2 S2 W2 mem2 md2 k2 slo E HBs HC Hc Hm HAK HJ2 (p & n & Eb & HE).
destruct HC as ((HJ & _) & _ & _ & _).
destruct (s20g_jframe cx ly S W mem md k HJ) as (HAR & Hin & Efa & F0 & F1 & Fapp).
destruct (s20g_jframe cx ly2 S2 W2 mem2 md2 k2 HJ2) as (HAR2 & Hin2 & Efa2 & _).
destruct HAK as (A1 & A2 & A3 & A4 & _).
pose proof (s20g_nums cx HBs) as (N1 & N2 & N3 & N4 & N5 & N6).
pose proof (s20g_sh_nums cx F0 F1) as (Sh1 & Sh2). unfold kImgEnd in Sh1.
pose proof asan_consts as (C1 & _).
assert (Hpin : In (p, n) (ablocks B ly2 S2)) by (rewrite Eb; apply in_or_app; right; left; reflexivity).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hpin) as (_ & Hp4 & Hpc & Hpapp & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 p n LT_FCLS (x_fpos cx) HAR2 Hpin Hin2) as Dpf.
rewrite Efa2 in Dpf. change (fs_frame_bytes LT_FCLS) with 512 in Dpf. unfold zdisjoint in Dpf. cbn [fst snd] in Dpf.
split; [|split; [|split; [|split]]].
- intros a Ha. apply A1; lia.
- exact A3.
- intros a Ha. unfold LT_FLAGW in Ha. apply (A4 LT_FCLS (x_fpos cx) a Hin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes LT_FCLS) with 512. lia.
  + intros HEa. apply HE in HEa. lia.
- intros a Ha. apply (A4 LT_FCLS (x_fpos cx) a Hin).
  + right. unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes LT_FCLS / 8) with 64.
    unfold x_sh in Ha. lia.
  + intros HEa. apply HE in HEa.
    apply (s20g_app_sh (x_fr cx) p (req_size n) a); [lia | exact Hpapp | lia | unfold x_sh in Ha; lia].
- intros a Ha. destruct Ha as [Ha | Ha].
  + pose proof Hc as Hc'. apply in_split in Hc' as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (c, seg_spec.SEG_C_SIZE) (p, n) l1 l2 [] HAR2
      ltac:(rewrite Eb, El, <- app_assoc; reflexivity)) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
    assert (RC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity. rewrite RC in D.
    unfold seg_spec.SEG_C_SIZE in Ha.
    assert (Ea : a = c + (a - c)) by ring. rewrite Ea.
    apply (A2 c seg_spec.SEG_C_SIZE (a - c) Hc); [rewrite RC; lia |].
    intros HEa. apply HE in HEa. lia.
  + pose proof Hm as Hm'. apply in_split in Hm' as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (m, seg_spec.SEG_M_SIZE) (p, n) l1 l2 [] HAR2
      ltac:(rewrite Eb, El, <- app_assoc; reflexivity)) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
    assert (RM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity. rewrite RM in D.
    unfold seg_spec.SEG_M_SIZE in Ha.
    assert (Ea : a = m + (a - m)) by ring. rewrite Ea.
    apply (A2 m seg_spec.SEG_M_SIZE (a - m) Hm); [rewrite RM; lia |].
    intros HEa. apply HE in HEa. lia.
Qed.
(* the frame's 36 shadow bytes: the probe's three (24 .. 26) between the 24 before and the 9 after (image A's
   S11 / S12 walk's s20b_pre .. s20b_fsh_store) *)
Definition s20g_pre (o : lfo) : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1] ++ (if fo_v o then [0; 0; 4] else [0xf8; 0xf8; 0xf8]) ++ repeat 0xf2 5 ++
  (if fo_label o then repeat 0 5 else repeat 0xf8 5) ++ repeat 0xf2 5 ++
  (if fo_r o then [4] else [0xf8]) ++ [0xf2].
Definition s20g_post (o : lfo) : list Z := repeat 0xf2 5 ++ (if fo_n o then [4] else [0xf8]) ++ [0xf3; 0xf3; 0xf3].
Lemma s20g_fsh_split : forall o,
  lt_fsh o = s20g_pre o ++ (if fo_probe o then [0; 0; 2] else [0xf8; 0xf8; 0xf8]) ++ s20g_post o.
Proof. intros [[] [] [] [] []]; reflexivity. Qed.
Lemma s20g_pre_len : forall o, length (s20g_pre o) = 24%nat.
Proof. intros [[] [] [] [] []]; reflexivity. Qed.
Lemma s20g_plen : forall b : bool, length (if b then [0; 0; 2] else [0xf8; 0xf8; 0xf8]) = 3%nat.
Proof. intros []; reflexivity. Qed.
Lemma s20g_pre_eq : forall o o', fo_v o' = fo_v o -> fo_label o' = fo_label o -> fo_r o' = fo_r o ->
  s20g_pre o' = s20g_pre o.
Proof. intros o o' Ev El Er. unfold s20g_pre. rewrite Ev, El, Er. reflexivity. Qed.
Lemma s20g_post_eq : forall o o', fo_n o' = fo_n o -> s20g_post o' = s20g_post o.
Proof. intros o o' En. unfold s20g_post. rewrite En. reflexivity. Qed.
(* the frame's shadow with the probe's three bytes rewritten and the other 33 kept *)
Lemma s20g_fsh_store : forall (rd rd2 : reader) a o o',
  fo_v o' = fo_v o -> fo_label o' = fo_label o -> fo_r o' = fo_r o -> fo_n o' = fo_n o ->
  sa_zs rd a (lt_fsh o) ->
  (forall i, (i < 36)%nat -> (i < 24 \/ 27 <= i)%nat -> rd2 (a + Z.of_nat i) = rd (a + Z.of_nat i)) ->
  sa_zs rd2 (a + 24) (if fo_probe o' then [0; 0; 2] else [0xf8; 0xf8; 0xf8]) ->
  sa_zs rd2 a (lt_fsh o').
Proof.
intros rd rd2 a o o' Ev El Er En HZ K HP i Hi.
rewrite lt_fsh_len in Hi.
assert (HZ' : forall j, (j < 36)%nat -> rd (a + Z.of_nat j) =
  Some (nth j (s20g_pre o ++ (if fo_probe o then [0; 0; 2] else [0xf8; 0xf8; 0xf8]) ++ s20g_post o) 0)).
{ intros j Hj. rewrite <- s20g_fsh_split. apply HZ. rewrite lt_fsh_len. exact Hj. }
rewrite s20g_fsh_split, (s20g_pre_eq o o' Ev El Er), (s20g_post_eq o o' En).
destruct (Nat.lt_ge_cases i 24) as [H1 | H1].
- rewrite K by lia. rewrite (HZ' i Hi). rewrite !app_nth1 by (rewrite s20g_pre_len; lia). reflexivity.
- destruct (Nat.lt_ge_cases i 27) as [H2 | H2].
  + rewrite app_nth2 by (rewrite s20g_pre_len; lia). rewrite s20g_pre_len.
    rewrite app_nth1 by (rewrite s20g_plen; lia).
    pose proof (HP (i - 24)%nat ltac:(rewrite s20g_plen; lia)) as E.
    replace (a + 24 + Z.of_nat (i - 24)) with (a + Z.of_nat i) in E by lia. exact E.
  + rewrite K by lia. rewrite (HZ' i Hi).
    rewrite !app_nth2 by (rewrite ?s20g_pre_len, ?s20g_plen; lia).
    rewrite !s20g_pre_len, !s20g_plen. reflexivity.
Qed.
(* s20_ctx across the harness's own stores of the probe's three shadow bytes (0x858b4 .. 0x858bc: 00 00 02, in
   scope; 0x8590c .. 0x85914: f8 f8 f8, out of scope), at the same allocator state: memory unchanged elsewhere, the
   run's journal, the frame registers kept *)
Lemma s20_ctx_store : forall cx ly S (W : world SEGS) regs mem md k acc o c m regs2 mem2 md2 o',
  lt_base B MT cx -> s20_ctx B MT cx ly S W regs mem md k acc o c m ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  s20_rkept regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W mem2 a = rdW W mem a) ->
  fo_v o' = fo_v o -> fo_label o' = fo_label o -> fo_r o' = fo_r o -> fo_n o' = fo_n o ->
  sa_zs (rdW W mem2) (x_sh cx + 24) (if fo_probe o' then [0; 0; 2] else [0xf8; 0xf8; 0xf8]) ->
  s20_ctx B MT cx ly S W regs2 mem2 md2 k acc o' c m.
Proof.
intros cx ly S W regs mem md k acc o c m regs2 mem2 md2 o' HBs Hctx HJ2 HRK K Ev El Er En Hzs.
destruct Hctx as (HC & Hhc & Hhm & HSL & HCM).
destruct HC as (HF & HI & HBk & HBd).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & HSB & HZS & HSH).
destruct HRK as (K2 & K3 & K4 & K8 & K9).
destruct (s20g_jframe cx ly S W mem md k HJ) as (HAR & Hin & Efa & F0 & F1 & Fapp).
pose proof HJ2 as (HAR2 & _).
pose proof (s20g_nums cx HBs) as (N1 & N2 & N3 & N4 & N5 & N6).
pose proof (s20g_sh_nums cx F0 F1) as (Sh1 & Sh2). unfold kImgEnd in Sh1.
pose proof asan_consts as (C1 & _).
(* every byte but the probe's three shadow bytes is kept; the frame and the blocks are application memory *)
assert (KH : forall a, 0 <= a < 2 ^ 64 -> (a < x_sh cx + 24 \/ x_sh cx + 27 <= a) -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha Hb; apply K; lia).
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem2 a = rdW W mem a).
{ intros a Ha. apply K; [lia|]. intros Hs.
  apply (s20g_app_sh (x_fr cx) (x_fr cx) 512 a); [lia | exact Fapp | lia | unfold x_sh in Hs; lia]. }
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> rdW W mem2 a = rdW W mem a).
{ intros p n a Hpn Ha. destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hpn) as (_ & Hp4 & Hpc & Hpapp & _).
  apply K; [lia|]. intros Hs.
  apply (s20g_app_sh (x_fr cx) p (req_size n) a); [lia | exact Hpapp | lia | unfold x_sh in Hs; lia]. }
split; [|split; [|split; [|split]]].
- split; [|split; [|split; [exact HBk | exact HBd]]].
  + split; [exact HJ2|].
    split; [exact (eq_trans K2 R2)|]. split; [exact (eq_trans K3 R3)|]. split; [exact (eq_trans K4 R4)|].
    split; [exact (eq_trans K8 R8)|]. split; [exact (eq_trans K9 R9)|].
    split; [apply (s20g_saved_kept cx (rdW W mem) (rdW W mem2)); [intros a Ha; apply KH; lia | exact HSV]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact HH0 | intros j Hj; apply KF; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact HH8 | intros j Hj; apply KF; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact HH16 | intros j Hj; apply KF; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W mem2));
      [exact HFL | intros j Hj; apply KF; unfold LT_FLAGW; lia]|].
    split; [rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact HSB | intros j Hj; apply KH; lia]|].
    split.
    { apply (s20g_fsh_store (rdW W mem) (rdW W mem2) (x_sh cx) o o' Ev El Er En HZS); [|exact Hzs].
      intros i Hi Hi2. apply KH; lia. }
    rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact HSH | intros j Hj; apply KH; lia].
  + apply (s20g_lt_img_kept cx W W mem mem2 ly S md2 HI HAR2).
    intros a Hia _ _. pose proof (pa_img_range a Hia) as Hr. unfold kImgEnd in Hr. apply KH; lia.
- exact (s20_hblk_carry ly S W mem ly S W mem2 md2 c _ HAR2 Hhc (fun pn H => H)).
- exact (s20_hblk_carry ly S W mem ly S W mem2 md2 m _ HAR2 Hhm (fun pn H => H)).
- intros o0 v Hov. pose proof (s20g_slot_off cx c m o0 v Hov) as Ho.
  rewrite (rdword_ext (rdW W mem) (rdW W mem2)); [exact (HSL o0 v Hov) | intros j Hj; apply KH; lia].
- unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp in *. destruct HCM as ((bs & Hbs & Henc) & (bs' & Hbs' & Henc')).
  split.
  + exists bs. split; [|exact Henc]. intros i Hi. destruct Henc as (Hlen & _).
    assert (RC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity.
    rewrite (KB c seg_spec.SEG_C_SIZE); [exact (Hbs i Hi) | exact (proj1 Hhc) |].
    rewrite RC. unfold seg_spec.SEG_C_SIZE in Hlen. lia.
  + exists bs'. split; [|exact Henc']. intros i Hi. destruct Henc' as (Hlen & _).
    assert (RM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity.
    rewrite (KB m seg_spec.SEG_M_SIZE); [exact (Hbs' i Hi) | exact (proj1 Hhm) |].
    rewrite RM. unfold seg_spec.SEG_M_SIZE in Hlen. lia.
Qed.
End k.
