(* diginet_frame_build_seg_a: twelve control-flow pieces of the image-A walk of diginet_frame_build
   (fuzz_transport.asan 0x8bcf8), each the Lemma of a statement of lib/A/Prog/diginet_frame_build_iface.v, as a
   footprint run (lib/Lib/ExecF.v evtF) stepped by lib/Lib/StepF.v step:
     fb_seg1_F    the prologue (twelve frame stores), the null, mode and length tests, the shadow base through
                  GOT_CELL_K -> CELL_K into s10, and the call of diginet_body_check (body = 0 only with body_len = 0);
     fb_seg1L_F   the same prologue with body_len > 1484: s8 := -4 and the jump to the epilogue;
     fb_seg1M_F   the same prologue with mode not 0 or 1: `bltu 1,mode` taken to the epilogue with s8 = -1;
     fb_seg2R_F   the return of diginet_body_check with a0 <> 0: s8 := -10;
     fb_seg2S_F   a0 = 0, s9 := 30 + body_len, s8 := max 60 s9, cap < s8: s8 := -5;
     fb_seg2C_F   a0 = 0 and s8 <= cap: the first __asan_memcpy (out, dst, 6);
     fb_seg3_F    the second __asan_memcpy (out + 6, src, 6);
     fb_seg4Z_F   body_len = 0: the body copy is skipped;
     fb_seg4_F    the third __asan_memcpy (out + 30, body, body_len);
     fb_seg5Z_F   30 + body_len >= len: the padding is skipped;
     fb_seg5_F    the __asan_memset (out + 30 + body_len, 0, len - 30 - body_len);
     fb_epi_F     a0 := sext.w s8, ra and s0 .. s10 reloaded from the frame, sp += 96, `ret`.
   None of these pieces makes an instrumented access or a store into out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof diginet_frame_build_iface.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(** * Helpers *)

(* Eight bytes are the little-endian encoding of the word they spell. *)
Lemma fb_le8_word : forall bs : list byte, length bs = 8%nat ->
  le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

(* n eight-byte words read from a byte list. *)
Fixpoint fb_words (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S k => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: fb_words k (skipn 8 bs)
  end.

Lemma fb_words_ok : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (fb_words n bs) /\ cells_bytes (fb_words n bs) = bs /\ cells_size (fb_words n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - apply length_zero_iff_nil in L. subst bs. cbn. auto.
  - assert (L1 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (L2 : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ L2) as (W & B & S).
    cbn [fb_words cells_wf cells_bytes cells_size cell_wf cbytes csize].
    rewrite fb_le8_word by exact L1. rewrite B, S.
    split; [split; [exact I | exact W]|]. split; [apply firstn_skipn | lia].
Qed.

(* The 96 carved bytes, seen as twelve words. *)
Lemma fb_frame_c8 : forall m A junk, rw_cells rsegs m A [CB 96 junk] ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : word,
    rw_cells rsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11].
Proof.
  intros m A junk [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (fb_words_ok 12 junk L) as (W & B & S).
  assert (H : rw_cells rsegs m A (fb_words 12 junk)).
  { split; [split|].
    - exact W.
    - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
    - rewrite S. exact Hw. }
  cbn [fb_words] in H. do 12 eexists. exact H.
Qed.

(* A word cell, as the read a load makes of it. *)
Lemma fb_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a _ 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  rewrite firstn_all2; [reflexivity|]. rewrite ?length_skipn, length_le8. lia.
Qed.

(* `seqz` of a nonzero word. *)
Lemma fb_seqz_nz : forall x, 0 < x < 2 ^ 64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  destruct (Z.ltb_spec x 1); [lia | reflexivity].
Qed.

(* `snez` of the zero word. *)
Lemma fb_snez_z : forall x, v_sltu x (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof.
  intros x. unfold v_sltu, c_ltu. destruct (bv_ltu x (Z_to_bv 64 0)) eqn:E; [|reflexivity].
  exfalso. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
  unfold bv_ltu in E. rewrite ?U0 in E.
  first [apply Z.ltb_lt in E; lia | apply bool_decide_eq_true in E; lia].
Qed.

(* `bltu 1,a7` with a7 the int mode sign-extended: taken when mode is neither 0 nor 1. *)
Lemma fb_mode_u : forall mode, - 2 ^ 31 <= mode < 2 ^ 31 -> mode <> 0 -> mode <> 1 ->
  1 < bv_unsigned (Z_to_bv 64 mode).
Proof.
  intros mode H H0 H1. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

(* `sext.w` (addiw rd, rs, 0) of a word that holds a 32-bit signed value leaves that word. *)
Lemma fb_sext_w : forall v, - 2 ^ 31 <= v < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0)) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite Z.add_0_r, unsigned_lit_wrap. apply Z_to_bv_eqm. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 `div` 2) with (2 ^ 31).
  Z.div_mod_to_equations. lia.
Qed.

(* Every pc of these pieces is a closed iface name; compute each to its value, since step reads a literal pc. *)
Ltac fb_lit X := let v := eval vm_compute in X in change X with v.
Ltac fb_lits :=
  repeat match goal with
  | |- context [FB_RET_BC] => fb_lit FB_RET_BC
  | |- context [FB_RET_C1] => fb_lit FB_RET_C1
  | |- context [FB_RET_C2] => fb_lit FB_RET_C2
  | |- context [FB_RET_C3] => fb_lit FB_RET_C3
  | |- context [FB_TAIL] => fb_lit FB_TAIL
  | |- context [FB_EPI] => fb_lit FB_EPI
  | |- context [FB_BC] => fb_lit FB_BC
  | |- context [FB_CPY] => fb_lit FB_CPY
  | |- context [FB_SET] => fb_lit FB_SET
  | |- context [FB_AT ?o] => fb_lit (FB_AT o)
  | |- context [FB_ENTRY] => fb_lit FB_ENTRY
  end.

(* bv_unsigned of a literal word whose value is in range. *)
Ltac fb_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

(* A branch decided by the numeric premises. *)
Ltac fb_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; rewrite ?w0_lit; fb_usub; solve_cond_rec.
Ltac fb_br b :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; fb_cond]
  end.

(* The final register file, register by register. *)
Ltac fb_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac fb_w := fb_usub; first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia ].
Ltac fb_fin := apply evtF_done; f_equal; fb_regs; fb_w.
Ltac fb_mem k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(** * fb_seg1: FB_ENTRY -> the call of diginet_body_check *)

Lemma fb_seg1_F : fb_seg1_stmt.
Proof.
  unfold fb_seg1_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out cap dst src hp body blen mode lo ST LO GCK CK HLOW HOUT HDST HSRC HHP HBODY HBZ HCAP HBLEN HMODE RFR RGC RCK.
  fb_lits.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW. unfold ASAN_K in CK.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (UO : bv_unsigned (Z_to_bv 64 out) = out) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
  assert (UH : bv_unsigned (Z_to_bv 64 hp) = hp) by (apply unsigned_lit; lia).
  assert (UB : bv_unsigned (Z_to_bv 64 body) = body) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 blen) = blen) by (apply unsigned_lit; lia).
  assert (UM : bv_unsigned (Z_to_bv 64 mode) = mode) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  destruct (fb_frame_c8 _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & FR').
  clear FR. rename FR' into FR.
  (* 0x8267c addi sp; 0x82680 .. 0x826ac the twelve frame stores; 0x826b0 li s8,-1; 0x826b4 beqz a0 (out) *)
  do 15 step.
  fb_br false.
  (* 0x826b8 mv s6,a2; beqz a2 (dst); mv s5,a3; beqz a3 (src); mv s3,a4; beqz a4 (hp) *)
  step. step. fb_br false.
  step. step. fb_br false.
  step. step. fb_br false.
  (* 0x826d0 .. 0x826dc mv s1,a6; mv s2,a5; mv s7,a1; mv s0,a0; 0x826e0 snez a0,a6; 0x826e4 seqz a1,a5 *)
  do 6 step.
  (* 0x826e8 and a0,a1,a0; 0x826ec bnez a0: seqz body is 0 when body <> 0, snez body_len is 0 when body_len = 0 *)
  destruct HBZ as [HBZ | ->]; [rewrite (fb_seqz_nz body) by lia | rewrite fb_snez_z].
  all: step; rewrite ?Z.land_0_l, ?Z.land_0_r; step; fb_br false.
  (* 0x826f0 mv s4,a7; li a0,1; bltu a0,a7 (1 < mode) *)
  all: step; step; step; fb_br false.
  (* 0x826fc li a0,1484; 0x82700 bgeu a0,s1 (blen <= 1484) *)
  all: step; step; fb_br true.
  (* the frame stores kept the two cells; 0x8270c auipc; ld a0 (GOT_CELL_K); ld s10 (CELL_K); mv a0,s2; mv a1,s1;
     0x82720 jal diginet_body_check *)
  all: pose proof (fb_rd8 _ _ _ GCK) as RDG.
  all: pose proof (fb_rd8 _ _ _ CK) as RDS.
  all: do 6 step.
  all: fb_mem ltac:(fun mm => apply evtF_done; exists mm).
  all: try replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia.
  all: split; [|split; [exact MU|split; [exact WM|exact FR]]].
  all: f_equal; fb_regs; fb_w.
Qed.

(** * fb_seg1L: FB_ENTRY -> FB_EPI with s8 = -4 *)

Lemma fb_seg1L_F : fb_seg1L_stmt.
Proof.
  unfold fb_seg1L_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out cap dst src hp body blen mode lo ST LO HOUT HDST HSRC HHP HBODY HCAP HBLEN HMODE RFR.
  fb_lits.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (UO : bv_unsigned (Z_to_bv 64 out) = out) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
  assert (UH : bv_unsigned (Z_to_bv 64 hp) = hp) by (apply unsigned_lit; lia).
  assert (UB : bv_unsigned (Z_to_bv 64 body) = body) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 blen) = blen) by (apply unsigned_lit; lia).
  assert (UM : bv_unsigned (Z_to_bv 64 mode) = mode) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  destruct (fb_frame_c8 _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & FR').
  clear FR. rename FR' into FR.
  do 15 step.
  fb_br false.
  step. step. fb_br false.
  step. step. fb_br false.
  step. step. fb_br false.
  do 6 step.
  rewrite (fb_seqz_nz body) by lia.
  step. rewrite ?Z.land_0_l. step. fb_br false.
  step. step. step. fb_br false.
  (* 0x82700 bgeu a0,s1 not taken (1484 < blen); 0x82704 li s8,-4; 0x82708 j FB_EPI *)
  step. step. fb_br false.
  step. step.
  fb_mem ltac:(fun mm => apply evtF_done; exists mm).
  try replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; fb_regs; fb_w.
Qed.

(** * fb_seg1M: FB_ENTRY -> FB_EPI with s8 = -1 (mode not 0 or 1) *)

Lemma fb_seg1M_F : fb_seg1M_stmt.
Proof.
  unfold fb_seg1M_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out cap dst src hp body blen mode lo ST LO HOUT HDST HSRC HHP HBODY HBZ HCAP HBLEN HMODE HM0 HM1 RFR.
  fb_lits.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (UO : bv_unsigned (Z_to_bv 64 out) = out) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
  assert (UH : bv_unsigned (Z_to_bv 64 hp) = hp) by (apply unsigned_lit; lia).
  assert (UB : bv_unsigned (Z_to_bv 64 body) = body) by (apply unsigned_lit; lia).
  assert (UL : bv_unsigned (Z_to_bv 64 blen) = blen) by (apply unsigned_lit; lia).
  pose proof (fb_mode_u mode HMODE HM0 HM1) as UM.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  destruct (fb_frame_c8 _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & v48 & v56 & v64 & v72 & v80 & v88 & FR').
  clear FR. rename FR' into FR.
  do 15 step.
  fb_br false.
  step. step. fb_br false.
  step. step. fb_br false.
  step. step. fb_br false.
  do 6 step.
  destruct HBZ as [HBZ | ->]; [rewrite (fb_seqz_nz body) by lia | rewrite fb_snez_z].
  all: step; rewrite ?Z.land_0_l, ?Z.land_0_r; step; fb_br false.
  (* 0x826f0 mv s4,a7; li a0,1; bltu a0,a7 taken (mode is not 0 or 1, as an unsigned word above 1): FB_EPI, s8 = -1 *)
  all: step; step; step.
  all: lazymatch goal with
       | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
           replace c with true;
           [cbv iota | symmetry; unfold bv_ltu, c_ltu; rewrite ?(unsigned_lit 1) by lia;
                       first [apply Z.ltb_lt | apply bool_decide_eq_true]; rewrite ?(unsigned_lit 1) by lia; lia]
       end.
  all: fb_mem ltac:(fun mm => apply evtF_done; eexists; exists mm).
  all: try replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia.
  all: split; [|split; [exact MU|split; [exact WM|exact FR]]].
  all: f_equal; fb_regs; fb_w.
Qed.

(** * fb_seg2R: FB_RET_BC with a0 <> 0 -> FB_EPI with s8 = -10 *)

Lemma fb_seg2R_F : fb_seg2R_stmt.
Proof.
  unfold fb_seg2R_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HA0.
  fb_lits.
  step. fb_br false.
  step. step.
  fb_fin.
Qed.

(** * fb_seg2S: FB_RET_BC with a0 = 0 and cap < fb_len -> FB_EPI with s8 = -5 *)

Lemma fb_seg2S_F : fb_seg2S_stmt.
Proof.
  unfold fb_seg2S_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    blen cap HA0 HBLEN HCAP HLT.
  fb_lits. unfold fb_len in *.
  assert (UL : bv_unsigned (Z_to_bv 64 blen) = blen) by (apply unsigned_lit; lia).
  (* 0x82724 beqz a0 taken; 0x82730 addi s9,s1,30; li a0,30; mv s8,s9; 0x8273c bgeu s1,a0 *)
  step. fb_br true.
  step. step. step. rewrite ?Z.add_0_r. step.
  destruct (Z.le_gt_cases 30 blen) as [HB|HB].
  - fb_br true.
    (* 0x82744 bgeu s7,s8 not taken (cap < 30 + blen); li s8,-5; j FB_EPI *)
    step. fb_br false.
    step. step.
    fb_fin.
  - fb_br false.
    (* 0x82740 li s8,60; 0x82744 bgeu s7,s8 not taken (cap < 60); li s8,-5; j FB_EPI *)
    step. step. fb_br false.
    step. step.
    fb_fin.
Qed.

(** * fb_seg2C: FB_RET_BC with a0 = 0 and fb_len <= cap -> the first __asan_memcpy *)

Lemma fb_seg2C_F : fb_seg2C_stmt.
Proof.
  unfold fb_seg2C_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst blen cap HA0 HBLEN HCAP HLE HOUT HDST.
  fb_lits. unfold fb_len in *.
  assert (UL : bv_unsigned (Z_to_bv 64 blen) = blen) by (apply unsigned_lit; lia).
  step. fb_br true.
  step. step. step. rewrite ?Z.add_0_r. step.
  destruct (Z.le_gt_cases 30 blen) as [HB|HB].
  - fb_br true.
    (* 0x82744 bgeu s7,s8 taken; 0x82750 li a2,6; mv a0,s0; mv a1,s6; jal __asan_memcpy *)
    step. fb_br true.
    do 4 step.
    fb_fin.
  - fb_br false.
    step. step. fb_br true.
    do 4 step.
    fb_fin.
Qed.

(** * fb_seg3: FB_RET_C1 -> the second __asan_memcpy *)

Lemma fb_seg3_F : fb_seg3_stmt.
Proof.
  unfold fb_seg3_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out src HOUT HOUT6 HSRC.
  fb_lits.
  (* 0x82760 addi a0,s0,6; li a2,6; mv a1,s5; 0x8276c jal __asan_memcpy *)
  do 4 step.
  fb_fin.
Qed.

(** * fb_seg4Z: FB_TAIL with s1 = 0 -> FB_RET_C3 *)

Lemma fb_seg4Z_F : fb_seg4Z_stmt.
Proof.
  unfold fb_seg4Z_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  fb_lits.
  step. fb_br true.
  fb_fin.
Qed.

(** * fb_seg4: FB_TAIL with s1 = body_len <> 0 -> the third __asan_memcpy *)

Lemma fb_seg4_F : fb_seg4_stmt.
Proof.
  unfold fb_seg4_stmt.
  intros RNG ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out body blen HOUT HOUT30 HBODY HBLEN.
  fb_lits.
  (* 0x82a24 beqz s1 not taken; 0x82a28 addi a0,s0,30; mv a1,s2; mv a2,s1; 0x82a34 jal __asan_memcpy *)
  step. fb_br false.
  do 4 step.
  fb_fin.
Qed.

(** * fb_seg5Z: FB_RET_C3 with 30 + body_len >= len -> FB_EPI *)

Lemma fb_seg5Z_F : fb_seg5Z_stmt.
Proof.
  unfold fb_seg5Z_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m
    blen HBLEN.
  fb_lits. unfold fb_len in *.
  step. fb_br true.
  fb_fin.
Qed.

(** * fb_seg5: FB_RET_C3 with 30 + body_len < len -> the __asan_memset *)

Lemma fb_seg5_F : fb_seg5_stmt.
Proof.
  unfold fb_seg5_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m
    out blen HOUT HOUT60 HBLEN.
  fb_lits.
  (* 0x82a38 bgeu s9,s8 not taken (30 + blen < 60); add a0,s0,s9; sub a2,s8,s9; li a1,0; 0x82a48 jal __asan_memset *)
  step. fb_br false.
  do 4 step.
  fb_fin.
Qed.

(** * fb_epi: FB_EPI -> the return *)

Lemma fb_epi_F : fb_epi_stmt.
Proof.
  unfold fb_epi_stmt.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m
    v c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra FR HSP RFR HV.
  fb_lits.
  unfold fb_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  (* 0x82a4c sext.w a0,s8 *)
  step. rewrite (fb_sext_w v HV).
  (* 0x82a50 .. 0x82a7c the twelve reloads; 0x82a80 addi sp,sp,96; 0x82a84 ret *)
  do 14 step.
  apply evtF_done. f_equal.
Qed.
