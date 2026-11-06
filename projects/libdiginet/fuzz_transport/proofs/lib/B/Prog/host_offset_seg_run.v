(* host_offset_seg_run: the straight-line footprint runs (lib/Lib/ExecF.v evtF) of host_offset in image B
   (fuzz_transport.asan-ubsan, entry 0x85040 = transportb_sigma TB_host_offset, 48 words), for the caller-journal
   walk of lib/B/Prog/host_offset_cg.v (lib/B/Prog/host_offset_cgW.v):
     ho_head_F  0x8508c .. the call of the bcmp wrapper at 0x850ac: one round's two UBSan branches to the trap word
                0x850fc (both refuted: p + i is not 0 mod 2^64, and p + i does not wrap below p) and the three
                argument registers (p + i, HOST, 6);
     ho_pro_F   the entry 0x85040 .. that call for i = 0: the 80-byte frame (ra and s0 .. s7 at sp + 72 .. sp + 8,
                sp + 0 unwritten), the loop's registers (s1 = p, s0 = i, s4 = -p, s5 = the rounds left, s6 = p <> 0,
                s2 = HOST, s3 = s7 = p + i), then ho_head_F;
     ho_tail_F  the call's return 0x850b0: a0 = 0 gives a0 = i and the epilogue; else round i + 1 (through
                ho_head_F) when i < 9, and a0 = -1 and the epilogue when i = 9.
   Each run takes its continuation Q as an argument, so the three compose without restating a state. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The addresses: the listing's entry and trampoline (lib/B/Prog/DgnTransportBAddr.v) and the two offsets inside
   the function (lib/B/Prog/DgnTransportBList.v, the 48 slots of TB_host_offset). *)
Definition HO_ENTRY : Z := transportb_sigma TB_host_offset.
Definition HO_BCMP : Z := transportb_sigma TB___interceptor_trampoline_bcmp.
Definition HO_HEAD : Z := HO_ENTRY + 0x4c.   (* 0x8508c, the loop head *)
Definition HO_RET1 : Z := HO_ENTRY + 0x70.   (* 0x850b0, after the jal at 0x850ac *)
(* HOST (fuzz_transport.c:109), the read-only global at 0x20fe0 = DgnTransportBCg.v TRANS_HOST. *)
Definition HO_HOST : Z := 0x20fe0.
Definition HO_FRAME : Z := 80.

(* The frame: sp + 0 is not written; sp + 8 .. sp + 72 hold s7 .. s0 and ra. *)
Definition ho_fr (junk : list byte) (c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [CB 8 junk; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* The state at the bcmp trampoline for round i, with the pointer q = p + i. *)
Definition ho_call_st (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p i q : Z) : machine_state :=
  MS (mkR (Z_to_bv 64 HO_RET1) sp gp tp t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 p)
           (Z_to_bv 64 q) (Z_to_bv 64 HO_HOST) (Z_to_bv 64 6) a3 a4 a5 a6 a7
           (Z_to_bv 64 HO_HOST) (Z_to_bv 64 q) (Z_to_bv 64 (0 - p)) (Z_to_bv 64 (10 - i))
           (Z_to_bv 64 1) (Z_to_bv 64 q) s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 HO_BCMP) fc None m (seg_rom rsegs).

(* The state at the return, with the result r in a0: ra and s0 .. s7 reloaded from the frame, sp back up. *)
Definition ho_ret_st (spw gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z) : machine_state :=
  MS (mkR cra (Z_to_bv 64 (bv_unsigned spw + 80)) gp tp t0 t1 t2 c0 c1
           (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
           c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (ret_pc cra) fc None m (seg_rom rsegs).

(* ---- the small facts the branches and the registers need ---- *)

Lemma ho_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ho_eqb_w0 : forall v : word, bv_eqb v (Z_to_bv 64 0) = (bv_unsigned v =? 0).
Proof. intros v. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. reflexivity. Qed.

Lemma ho_w0 : forall v : word, bv_unsigned v = 0 -> v = Z_to_bv 64 0.
Proof. intros v H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma ho_nw0 : forall v : word, bv_unsigned v <> 0 -> v <> Z_to_bv 64 0.
Proof. intros v H E. apply H. rewrite E. reflexivity. Qed.

Lemma ho_ltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. rewrite bv_ltu_Z, !unsigned_lit by lia. reflexivity. Qed.

(* `sltu rd,x0,a0` with a0 = p <> 0 gives 1. *)
Lemma ho_sltu_pos : forall (x : word) (y : Z), bv_unsigned x = 0 -> 0 < y < 2 ^ 64 ->
  v_sltu x (Z_to_bv 64 y) = Z_to_bv 64 1.
Proof.
  intros x y Hx Hy. unfold v_sltu, c_ltu. rewrite bv_ltu_Z, Hx, unsigned_lit by lia.
  destruct (Z.ltb_spec 0 y) as [H|H]; [reflexivity | lia].
Qed.

(* `sltiu rd,rs,1` of a value that is not 0 mod 2^64 gives 0: the UBSan test of p + i = 0. *)
Lemma ho_sltiu_nz : forall (z c : Z), bv_wrap 64 c = 1 -> z mod 2 ^ 64 <> 0 ->
  v_sltiu (Z_to_bv 64 z) c = Z_to_bv 64 0.
Proof.
  intros z c Hc Hz. unfold v_sltiu. rewrite Hc, unsigned_lit_wrap.
  pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)) as Hb.
  destruct (Z.ltb_spec (z mod 2 ^ 64) 1) as [H|H]; [lia | reflexivity].
Qed.

(* `addiw rd,rs,1` on a small index. *)
Lemma ho_swrap32 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31). Z.div_mod_to_equations. lia.
Qed.

(* ---- tactics ---- *)

(* The start pc of a run is a name; StepF's step reads a literal. *)
Ltac ho_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let v := eval vm_compute in pc in change pc with v
  end.

(* A branch whose condition is a closed boolean. *)
Ltac ho_bclosed b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (first [ reflexivity | vm_compute; reflexivity ])
  end; cbv iota.

(* The UBSan test `sltiu a0,a0,1` of the round's p + i. *)
Ltac ho_sltiu_zero := lazymatch goal with
  | |- context [v_sltiu (Z_to_bv 64 ?z) ?c] =>
      rewrite (ho_sltiu_nz z c ltac:(reflexivity) ltac:(Z.div_mod_to_equations; lia))
  end.

(* The UBSan test `bltu s7,s1` of the round's p + i against p. *)
Ltac ho_bltu_false := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
      replace (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with false
        by (symmetry; rewrite (ho_ltu_lit x y) by lia; apply Z.ltb_ge; lia)
  end; cbv iota.

(* ---- one round's head: 0x8508c .. the call at 0x850ac ---- *)

Lemma ho_head_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) (p i q f : Z)
    (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 < p -> 0 <= i -> q = p + i -> f = 10 - i -> q < 2 ^ 64 ->
  Q (ho_call_st sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p i q) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 HO_HOST) (Z_to_bv 64 q) (Z_to_bv 64 (0 - p)) (Z_to_bv 64 f)
             (Z_to_bv 64 1) (Z_to_bv 64 q) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 HO_HEAD) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q p i q f ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hp Hi Hq Hf Hq64 HQ.
  subst q f.
  ho_pc.
  (* 0x8508c add a0,s4,s5 ; 0x85090 addi a0,a0,-10 ; 0x85094 sltiu a0,a0,1 *)
  step. step. step.
  ho_sltiu_zero.
  (* 0x85098 beq s6,a0 : s6 = 1 and a0 = 0, so the trap word 0x850fc is not reached *)
  step. ho_bclosed false.
  (* 0x8509c bltu s7,s1 : p + i does not wrap below p *)
  step. ho_bltu_false.
  (* 0x850a0 a2 = 6 ; 0x850a4 a0 = p + i ; 0x850a8 a1 = HOST ; 0x850ac jal *)
  step. step. step. step.
  apply evtF_done. exact HQ.
Qed.

(* ---- the entry: 0x85040 .. the first call ---- *)

Lemma ho_pro_F : forall (RNG : ExecF.footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z),
  0 < p -> p < 2 ^ 64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
  ExecF.rng RNG (bv_unsigned sp - 80) 80 ->
  ExecF.evtF rsegs RNG
    (fun ms' => exists (m1 : word -> option byte) (junk : list byte),
       ms' = ho_call_st (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 a3 a4 a5 a6 a7
               s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p 0 p /\
       munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
       stk rsegs m1 lo (bv_unsigned sp + -80) /\
       rw_cells rsegs m1 (bv_unsigned sp + -80) (ho_fr junk s7 s6 s5 s4 s3 s2 s1 s0 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 HO_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p Hp Hp64 ST HLO RFR.
  ho_pc.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- ExecF.evtF _ _ ?Q _ => set (QQ := Q) end.
  carve_frame 80%nat ST.
  (* 0x85040 addi sp,sp,-80 and the nine saves 0x85044 .. 0x85064 *)
  do 10 step.
  (* 0x85068 s1 = p ; 0x8506c s0 = 0 ; 0x85070 s4 = -p *)
  step. step. step.
  rewrite (unsigned_lit p ltac:(lia)).
  (* 0x85074 s5 = 10 ; 0x85078 s6 = (p <> 0) *)
  step. step.
  lazymatch goal with
  | |- context [v_sltu ?x (Z_to_bv 64 ?y)] => rewrite (ho_sltu_pos x y ltac:(reflexivity) ltac:(lia))
  end.
  (* 0x8507c auipc ; 0x85080 s2 = HOST ; 0x85084 s3 = p ; 0x85088 s7 = p *)
  step. step. step. step.
  apply ho_head_F; [lia | lia | lia | lia | lia |].
  unfold QQ.
  lazymatch goal with H : rw_cells rsegs ?mm _ (CB 8 ?j :: _) |- _ => exists mm, j end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact FR].
Qed.

(* ---- the call's return: 0x850b0 .. the next call, or the ret ---- *)

Lemma ho_tail_F : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop) (p i q f : Z)
    (x1 spw gp tp t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (junk : list byte) (c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 < p -> 0 <= i <= 9 -> q = p + i -> f = 10 - i -> q + 1 < 2 ^ 64 ->
  80 <= bv_unsigned spw -> bv_unsigned spw + 80 <= 2 ^ 63 ->
  rw_cells rsegs m (bv_unsigned spw) (ho_fr junk c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  ExecF.rng RNG (bv_unsigned spw) 80 ->
  (a0v = Z_to_bv 64 0 ->
     Q (ho_ret_st spw gp tp t0 t1 t2 a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
          c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m i)) ->
  (a0v <> Z_to_bv 64 0 -> i < 9 ->
     Q (ho_call_st spw gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p (i + 1) (q + 1))) ->
  (a0v <> Z_to_bv 64 0 -> i = 9 ->
     Q (ho_ret_st spw gp tp t0 t1 t2 a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
          c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m (-1))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR x1 spw gp tp t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 p) a0v a1v a2v a3 a4 a5 a6 a7
             (Z_to_bv 64 HO_HOST) (Z_to_bv 64 q) (Z_to_bv 64 (0 - p)) (Z_to_bv 64 f)
             (Z_to_bv 64 1) (Z_to_bv 64 q) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 HO_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q p i q f x1 spw gp tp t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
    junk c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m Hp Hi Hq Hf Hq64 HS1 HS2 FR RFR HQhit HQnext HQmiss.
  subst q f.
  ho_pc.
  pose proof (u64_range spw) as Rsp.
  unfold ho_fr in FR.
  (* 0x850b0 beqz a0 *)
  step. rewrite ho_eqb_w0.
  destruct (Z.eqb_spec (bv_unsigned a0v) 0) as [V0|V0]; cbv iota.
  - (* bcmp answered 0: 0x850cc a0 = s0 = i, then the epilogue *)
    do 12 step.
    apply evtF_done. apply HQhit. apply ho_w0. exact V0.
  - (* bcmp did not answer 0: 0x850b4 .. 0x850c0 the four increments *)
    step. rewrite (unsigned_lit i ltac:(lia)), (ho_swrap32 (i + 1) ltac:(lia)).
    step. step. step.
    replace (10 - i + -1) with (10 - (i + 1)) by lia.
    (* 0x850c4 bnez s5 *)
    destruct (Z.eq_dec i 9) as [E9|E9].
    + (* the tenth round missed: 0x850c8 a0 = -1, then the epilogue *)
      subst i. step. ho_bclosed false.
      do 13 step.
      apply evtF_done. apply HQmiss; [apply ho_nw0; exact V0 | reflexivity].
    + (* round i + 1 *)
      step.
      lazymatch goal with
      | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with true
            by (symmetry; apply Bool.negb_true_iff; rewrite (ho_eqb_lit (10 - (i + 1)) 0) by lia;
                apply Z.eqb_neq; lia)
      end; cbv iota.
      apply ho_head_F; [lia | lia | lia | lia | lia |].
      apply HQnext; [apply ho_nw0; exact V0 | lia].
Qed.

(* The same, with the three ends as one post, so that a walk's run takes it without an evar. *)
Definition ho_tail_post (spw gp tp t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (c7 c6 c5 c4 c3 c2 c1 c0 cra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (p i q : Z) (ms' : machine_state) : Prop :=
  (a0v = Z_to_bv 64 0 /\
   ms' = ho_ret_st spw gp tp t0 t1 t2 a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
           c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m i) \/
  (a0v <> Z_to_bv 64 0 /\ i < 9 /\
   ms' = ho_call_st spw gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p (i + 1) (q + 1)) \/
  (a0v <> Z_to_bv 64 0 /\ i = 9 /\
   ms' = ho_ret_st spw gp tp t0 t1 t2 a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
           c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m (-1)).

Lemma ho_tail_run_F : forall (RNG : ExecF.footprint) (p i q f : Z)
    (x1 spw gp tp t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (junk : list byte) (c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  0 < p -> 0 <= i <= 9 -> q = p + i -> f = 10 - i -> q + 1 < 2 ^ 64 ->
  80 <= bv_unsigned spw -> bv_unsigned spw + 80 <= 2 ^ 63 ->
  rw_cells rsegs m (bv_unsigned spw) (ho_fr junk c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
  ExecF.rng RNG (bv_unsigned spw) 80 ->
  ExecF.evtF rsegs RNG
    (ho_tail_post spw gp tp t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
       c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m p i q)
    (MS (mkR x1 spw gp tp t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 p) a0v a1v a2v a3 a4 a5 a6 a7
             (Z_to_bv 64 HO_HOST) (Z_to_bv 64 q) (Z_to_bv 64 (0 - p)) (Z_to_bv 64 f)
             (Z_to_bv 64 1) (Z_to_bv 64 q) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 HO_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG p i q f x1 spw gp tp t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
    junk c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m Hp Hi Hq Hf Hq64 HS1 HS2 FR RFR.
  apply ho_tail_F with (p := p) (i := i) (q := q) (f := f) (junk := junk)
    (c7 := c7) (c6 := c6) (c5 := c5) (c4 := c4) (c3 := c3) (c2 := c2) (c1 := c1) (c0 := c0) (cra := cra);
    [ exact Hp | exact Hi | exact Hq | exact Hf | exact Hq64 | exact HS1 | exact HS2 | exact FR | exact RFR
    | intros E; left; split; [exact E | reflexivity]
    | intros E Hlt; right; left; split; [exact E | split; [exact Hlt | reflexivity]]
    | intros E E9; right; right; split; [exact E | split; [exact E9 | reflexivity]] ].
Qed.
