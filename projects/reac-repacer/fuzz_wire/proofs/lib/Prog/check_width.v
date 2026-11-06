(* check_width walk, fuzz_wire plain c8763dfc4e81 0x13168..0x131d8 (fuzz_wire.c:146-168); new. rp_frame_channels is the
   named Section hypothesis HFC (its contract, rp_frame_channels_c.v), called twice: at 0x13178 on (long)n and
   at 0x131b8 on -1 - (long)n. Between them the inlined w_width((long)n) (fuzz.h:55-63) runs as the loop 0x13194..0x131ac
   (a5 = 126 + 72 k - n, a1 = 2 k, a2 = nch = 2 + 2 k). The first abort() (0x131b0 `bne a0, a2` -> 0x131d4) is
   unreachable because the loop's result is w_width_model n and w_width_frame_law proves it equal to
   rp_frame_channels_model n for every n of 0..1600 (a closed check over the 1601 lengths, by vm_compute); the second
   (0x131c0) because -1 - n is negative as a long for such n, so rp_frame_channels_model gives -1. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import reac_frame_clean_len_c rp_frame_channels_c
  check_width_c.
Import ListNotations.
Open Scope Z_scope.

(* fuzz.h:52-63, the frame law as the harness states it:
     static inline int w_width(long len)
     {
             for (int nch = 2; nch <= W_MAX_CH; nch += 2) {
                     long clean = W_OVERHEAD + (long)nch * W_PER_CH;
                     if (len == clean || len == clean + W_RESIDUE)
                             return nch;
             }
             return -1;
     }
   with W_OVERHEAD = 52, W_PER_CH = 36, W_MAX_CH = 40, W_RESIDUE = 2 (fuzz.h:26-30). w_width_from f nch len is the loop
   from the width nch on, with f passes left (20 passes: nch = 2, 4, .., 40). *)
Fixpoint w_width_from (fuel : nat) (nch len : Z) : Z :=
  match fuel with
  | O => -1
  | S f => if (len =? 52 + nch * 36) || (len =? 52 + nch * 36 + 2) then nch else w_width_from f (nch + 2) len
  end.

Definition w_width_model (len : Z) : Z := w_width_from 20 2 len.

Lemma w_width_frame_law_b :
  forallb (fun k => Z.eqb (w_width_model (Z.of_nat k)) (rp_frame_channels_model (Z.of_nat k))) (seq 0 1601) = true.
Proof. vm_compute. reflexivity. Qed.

(* The harness's frame law and the reader's arithmetic agree on every length LLVMFuzzerTestOneInput passes on. *)
Lemma w_width_frame_law : forall n, 0 <= n <= 1600 -> w_width_model n = rp_frame_channels_model n.
Proof.
  intros n Hn. pose proof (proj1 (forallb_forall _ _) w_width_frame_law_b (Z.to_nat n)) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia. apply Z.eqb_eq, H. apply in_seq. lia.
Qed.

Lemma sw32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma fc_model_neg : forall v : word, 2^63 <= bv_unsigned v -> rp_frame_channels_model (bv_signed v) = -1.
Proof.
  intros v Hv. pose proof (u64_range v). rewrite zb_signed. rewrite (proj2 (Z.ltb_ge _ _) Hv).
  unfold rp_frame_channels_model. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Section Loop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (Q : machine_state -> Prop).
Hypothesis Hn : 0 <= n <= 1600.

Local Notation ST pc a1 a2 a5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 2) (Z_to_bv 64 38) a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* The loop's exit at 0x131b0 with a2 = w_width(n). *)
Hypothesis K : forall a1' a2' a5' : word, bv_unsigned a2' = w_width_model n mod 2^64 -> evt rsegs Q (ST 78256 a1' a2' a5').

(* 0x13194 with k passes done (k < 20) and none of them matched. *)
Lemma width_loop : forall f k (a1 a2 a5 : word),
  (S f + k = 20)%nat ->
  w_width_from (S f) (2 + 2 * Z.of_nat k) n = w_width_model n ->
  bv_unsigned a1 = 2 * Z.of_nat k -> bv_unsigned a2 = 2 + 2 * Z.of_nat k ->
  bv_unsigned a5 = (126 + 72 * Z.of_nat k - n) mod 2^64 ->
  evt rsegs Q (ST 78228 a1 a2 a5).
Proof.
  induction f as [|f IH]; intros k a1 a2 a5 Hk Hw H1 H2 H5; cbn [w_width_from] in Hw.
  all: step; if_cases HE;
    [ zify_cond HE; rewrite H5 in HE;
      assert (En : n = 52 + (2 + 2 * Z.of_nat k) * 36) by (Z.div_mod_to_equations; lia);
      rewrite (proj2 (Z.eqb_eq _ _) En) in Hw; cbn [orb] in Hw;
      apply K; rewrite <- Hw, H2; rewrite Z.mod_small by lia; reflexivity
    | step; if_cases HZ ].
  all: zify_cond HE; rewrite H5 in HE.
  1, 3: zify_cond HZ; rewrite H5 in HZ;
    assert (En : n = 52 + (2 + 2 * Z.of_nat k) * 36 + 2) by (Z.div_mod_to_equations; lia);
    rewrite (proj2 (Z.eqb_neq n (52 + (2 + 2 * Z.of_nat k) * 36))) in Hw by lia;
    rewrite (proj2 (Z.eqb_eq _ _) En) in Hw; cbn [orb] in Hw;
    apply K; rewrite <- Hw, H2; rewrite Z.mod_small by lia; reflexivity.
  all: zify_cond HZ; rewrite H5 in HZ.
  all: assert (N1 : n <> 52 + (2 + 2 * Z.of_nat k) * 36)
         by (intro E; apply HE; replace (126 + 72 * Z.of_nat k - n) with 2 by lia; reflexivity).
  all: assert (N2 : n <> 52 + (2 + 2 * Z.of_nat k) * 36 + 2)
         by (intro E; apply HZ; replace (126 + 72 * Z.of_nat k - n) with 0 by lia; reflexivity).
  all: rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in Hw; cbn [orb] in Hw.
  all: do 3 step; step; if_cases HC.
  - (* last pass, back-branch taken: impossible, a1 = 40 > 38 *)
    exfalso. zify_cond HC. rewrite ?unsigned_lit_wrap, ?H1 in HC. Z.div_mod_to_equations. lia.
  - (* last pass, the loop ends: w_width = -1 *)
    step. apply K. rewrite <- Hw. reflexivity.
  - apply (IH (S k)).
    + lia.
    + rewrite Nat2Z.inj_succ. replace (2 + 2 * Z.succ (Z.of_nat k)) with (2 + 2 * Z.of_nat k + 2) by lia. exact Hw.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H1. rewrite Z.mod_small by lia. lia.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H2, sw32_id by lia. rewrite Z.mod_small by lia. lia.
    + rewrite Nat2Z.inj_succ, ?unsigned_lit_wrap, H5, Zplus_mod_idemp_l. f_equal. lia.
  - (* the loop ends before the last pass: impossible, a1 <= 38 *)
    exfalso. zify_cond HC. rewrite ?unsigned_lit_wrap, ?H1 in HC. Z.div_mod_to_equations. lia.
Qed.

End Loop.

(* `jal rp_frame_channels` (one step done) to its return at RA: the callee's frame below this one, the frame, the
   footprint, wmono, mem_inv and stk carried over its post. *)
Ltac fc_call HFC RA :=
  lazymatch goal with MI : mem_inv _ ?mm, ST : stk _ ?mm ?lo _ |- _ =>
    eapply evt_cut;
    [ eapply HFC; [ exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia ] | ]
  end;
  let ms := fresh "ms" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
  let MIc := fresh "MIc" in let STc := fresh "STc" in
  intros ms (? & ? & ? & ? & -> & MUc & WMc & MIc & STc);
  replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
  rewrite unsigned_lit in MUc, STc by lia;
  lazymatch type of MUc with munch _ ?mo ?mn =>
    lazymatch goal with MI : mem_inv _ mo |- _ => clear MI end;
    transport_after_call rsegs mo mn MUc WMc; clear MUc WMc
  end;
  rename MIc into MI; rename STc into ST.

Section C.
Hypothesis HFC : rp_frame_channels_contract.

Theorem check_width_holds : check_width_contract.
Proof.
  unfold check_width_contract, CHECK_WIDTH, CHECK_WIDTH_STACK, CHECK_WIDTH_FRAME. change (16 + 16) with 32.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    HN MI ST HLO.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (BSn : bv_signed a0 = bv_unsigned a0)
    by (rewrite zb_signed; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 3 step.
  do 2 step.
  fc_call HFC 78204.
  rewrite BSn, <- (w_width_frame_law (bv_unsigned a0)) by lia.
  do 6 step.
  eapply (width_loop) with (f := 19%nat) (k := 0%nat) (n := bv_unsigned a0).
  all: lazymatch goal with
       | |- forall _ : word, _ => idtac
       | _ => first [ lia | reflexivity | (rewrite unsigned_lit_wrap; f_equal; lia) ]
       end.
  intros a1' a2' a5' H2'.
  replace a2' with (Z_to_bv 64 (w_width_model (bv_unsigned a0)))
    by (apply bv_eq; rewrite unsigned_lit_wrap; symmetry; exact H2').
  step. first [if_true | if_false].
  do 2 step.
  fc_call HFC 78268.
  rewrite fc_model_neg by (rewrite ?unsigned_lit_wrap, ?zb_lxor_ones by lia; rewrite ?Z.mod_small by lia; lia).
  step. step. first [if_true | if_false].
  do 4 step.
  apply evt_done. do 16 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|].
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

End C.
