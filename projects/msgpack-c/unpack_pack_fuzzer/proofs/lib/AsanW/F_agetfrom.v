(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame ARefill_iface RT_stubs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aensure F_apopulate.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_agetfrom.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

Ltac lrsc_stepA AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; rewrite ?Z.eqb_refl; exec_cbv; amo_align AMO; rewrite ?Z.eqb_refl;
        simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma sx32_small : forall w : word, bv_unsigned w < 2^31 -> sx32 w = w.
Proof.
  intros w Hw. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  rewrite <- (Z_to_bv_bv_unsigned w). rewrite sx32_lit by lia. reflexivity.
Qed.

Lemma aclass_eta0 : forall r, mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) (c_count r) = r.
Proof. intros []; reflexivity. Qed.

Lemma fvals_small : forall au S k, 0 <= au -> 0 <= S -> au + Z.of_nat k * S <= 2^32 ->
  Forall (fun w : word => bv_unsigned w < 2^31) (fvals au S k).
Proof.
  intros au S k AU SZ B. unfold fvals. apply Forall_rev. apply Forall_map. apply Forall_forall. intros j Hj.
  apply in_seq in Hj. rewrite Z.shiftr_div_pow2 by lia.
  assert (J : 0 <= Z.of_nat j * S <= Z.of_nat k * S) by nia.
  rewrite unsigned_lit; [| change (2^4) with 16; Z.div_mod_to_equations; lia]. change (2^4) with 16. Z.div_mod_to_equations; lia.
Qed.

Lemma u32arr_app : forall m A ws1 ws2,
  u32arr asegs m A ws1 -> u32arr asegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> u32arr asegs m A (ws1 ++ ws2).
Proof.
  intros m A ws1 ws2 [[B0 [B1 B]] [W0 [W1 W]]] [[C0 [C1 C]] [V0 [V1 V]]].
  rewrite u32s_length in B1. rewrite u32s_length in C1.
  split.
  - split; [exact B0|]. split; [rewrite u32s_app, length_app, !u32s_length; lia|].
    intros i Hi. rewrite u32s_app in Hi |- *. rewrite length_app, !u32s_length in Hi.
    destruct (Nat.lt_ge_cases i (4 * length ws1)) as [LT|GE].
    + rewrite nth_error_app1 by (rewrite u32s_length; exact LT). apply B. rewrite u32s_length. exact LT.
    + rewrite nth_error_app2 by (rewrite u32s_length; exact GE). rewrite u32s_length.
      specialize (C (i - 4 * length ws1)%nat ltac:(rewrite u32s_length; lia)).
      replace (A + 4 * Z.of_nat (length ws1) + Z.of_nat (i - 4 * length ws1)) with (A + Z.of_nat i) in C by lia. exact C.
  - split; [exact W0|]. split; [rewrite length_app; lia|].
    intros i Hi. rewrite length_app in Hi.
    destruct (Z_lt_le_dec i (4 * Z.of_nat (length ws1))) as [LT|GE].
    + apply W. lia.
    + specialize (V (i - 4 * Z.of_nat (length ws1)) ltac:(lia)).
      replace (A + 4 * Z.of_nat (length ws1) + (i - 4 * Z.of_nat (length ws1))) with (A + i) in V by lia. exact V.
Qed.

Lemma u32arr_skipn : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
  u32arr asegs m (A + 4 * Z.of_nat k) (skipn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_skipn; lia|].
    intros i Hi. rewrite u32s_length, length_skipn in Hi.
    specialize (B (4 * k + i)%nat ltac:(rewrite u32s_length; lia)).
    replace (A + Z.of_nat (4 * k + i)) with (A + 4 * Z.of_nat k + Z.of_nat i) in B by lia. rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app2 by (rewrite u32s_length, length_firstn; lia).
    rewrite u32s_length, length_firstn. f_equal. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|].
    intros i Hi. rewrite length_skipn in Hi. specialize (W (4 * Z.of_nat k + i) ltac:(lia)).
    replace (A + (4 * Z.of_nat k + i)) with (A + 4 * Z.of_nat k + i) in W by lia. exact W.
Qed.

Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition getfrom_entry := 0x41c70.
End CANSEC1.
Notation GETFROM_STACK := 640 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u32arr asegs m SRC src -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  u32arr asegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv asegs m ->
  0 <= SRC -> SRC + 4 * n < 2^47 -> 0 <= DST -> DST + 4 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 4 * n <= DST \/ DST + 4 * Z.of_nat (length ws0) <= SRC) ->
  (forall k, 0 <= k < n -> rng RNG (SRC + 4 * k) 4) -> rng RNG DST (4 * n) ->
  evtF asegs RNG (fun ms' => exists a2' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2' (Z_to_bv 64 (DST + 4 * n)) a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 (SRC + 4 * n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x41df8) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2 (Z_to_bv 64 (DST + 4 * i)) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (SRC + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x41de4) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1.
  step. clear RD RS1.
  rewrite (sx32_small w W31).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write asegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 4 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  clear DSTA. store_done. try clear SOK.
  zstep. zstep.
  setreg 13 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.
  -
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a2' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a2', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  -
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

Definition gftail_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (F : bvmap 5 word) (fc : bv 32)
    (RI FA CHK n base lo : Z) (fl2 chunks0 : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (stn' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (RI + 72) [C8 stn']
    /\ u32arr asegs m' FA fl2
    /\ u32arr asegs m' CHK (skipn (Z.to_nat base) fl2 ++ skipn (Z.to_nat n) chunks0).

Lemma gf_tail_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word)
    (rax t0 t1 t2 s1x a0x a1x a2x a6 a7 s2x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (RI FA CHK n base lo : Z) (fl2 chunks0 : list word) (stn : word) (fr0 : list byte),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 24 fr0; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 1152921504606846976)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u32arr asegs m FA fl2 -> length fl2 = Z.to_nat (base + n) -> Forall (fun w : word => bv_unsigned w < 2^31) fl2 ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  amo_aligned AD (Z_to_bv 64 RI) = true ->
  0 <= base -> 1 <= n <= 16 ->
  0x10007fff8000 <= FA -> FA + 4 * (base + n) <= ATOP -> 4096 <= CHK -> CHK + 64 <= ATOP -> (FA + 4 * (base + n) <= CHK \/ CHK + 64 <= FA) ->
  0x10007fff8000 <= RI -> RI + 128 <= ATOP -> (RI + 128 <= CHK \/ CHK + 64 <= RI) -> (RI + 128 <= FA \/ FA + 4 * (base + n) <= RI) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> (forall k, 0 <= k < base + n -> rng RNG (FA + 4 * k) 4) -> rng RNG CHK 64 ->
  evtF asegs RNG (gftail_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc RI FA CHK n base lo fl2 chunks0 m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x a0x a1x a2x (Z_to_bv 64 CHK) (Z_to_bv 64 n) (Z_to_bv 64 base) a6 a7
             s2x (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 FA) s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x41dd4) fc None m (seg_rom asegs)).
Proof.
  intros until fr0. intros ST CEIL LO MI FR MTX STN FL LFL FL31 CH LCH AMO B0 N FA0 FA1 CH0 CH1 DJ RI0 RI1 DJ2 DJ3 RIMG RSTK RRI RFA RCH.
  unfold AIMG_HI in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.
  setreg 11 (Z_to_bv 64 (CHK + 4 * n)) ltac:(rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (FA + 4 * Z.of_nat (Z.to_nat base) + 4 * 0)) ltac:(rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -B0; lia).
  setreg 13 (Z_to_bv 64 (CHK + 4 * 0)) ltac:(f_equal; clear; lia).
  pose proof (u32arr_skipn m FA fl2 (Z.to_nat base) FL ltac:(rewrite LFL; clear -B0 N; lia)) as SRCA.
  eapply evtF_cut.
  { eapply (copy_loop_spec RNG _ 0 n (FA + 4 * Z.of_nat (Z.to_nat base)) CHK (skipn (Z.to_nat base) fl2) chunks0); try reflexivity.
    - clear -N; lia.
    - rewrite length_skipn, LFL. clear -B0 N; lia.
    - rewrite LCH. clear -N; lia.
    - exact SRCA.
    - apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) FL31 w). rewrite <- (firstn_skipn (Z.to_nat base) fl2). apply in_or_app. right. exact Hw.
    - cbn [Z.to_nat firstn skipn app]. exact CH.
    - exact MI.
    - clear -FA0 B0; lia.
    - clear -FA1 B0 N; lia.
    - clear -CH0; lia.
    - rewrite LCH; clear -CH1; lia.
    - rewrite LCH. clear -DJ B0 N; lia.
    - intros kk Hkk. replace (FA + 4 * Z.of_nat (Z.to_nat base) + 4 * kk) with (FA + 4 * (base + kk)) by (clear -B0; lia). apply RFA. clear -B0 Hkk; lia.
    - eapply rng_sub'; [exact RCH|]. clear -N; lia. }
  cbv beta. intros ms' (a2' & m2 & -> & MU2 & WM2 & MI2 & SR2 & CH2).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO CH0 CH1 N; lia).
  xport MTX MU2 WM2 ltac:(clear -DJ2 N; lia).
  xport STN MU2 WM2 ltac:(clear -DJ2 N; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; clear -DJ N B0; lia).
  pose proof (stk_transport_disjoint asegs _ m m2 _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; clear -SPR CEIL LO CH0 CH1 N; lia)) as ST2.
  clear ST MI SRCA.
  assert (MUF : munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU MU2.

  step. zstep.
  snapshot [(RI, RI + 8); (RI + 72, RI + 80)]%Z MUb WMb.
  box CH2. box FL. clear SR2.
  step.
  step.

  step.
  do 7 zstep. step. do 5 zstep.
  step.
  zstep. zstep. step. if_lit.
  zstep. step. if_lit.
  do 7 zstep. step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  step. if_lit.
  step. if_lit.
  step.
  do 15 step.
  carry CH2 MUb WMb ltac:(rewrite length_app, !length_skipn, LFL, LCH; clear -DJ2 N B0; lia).
  carry FL MUb WMb ltac:(rewrite LFL; clear -DJ3 N B0; lia).
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. unfold gftail_post.
  do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MUF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact STN|]. split; [exact FL|].
  exact CH2.
Qed.

Definition gfa_take {R} (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) (st2 : astate) : AM R :=
  if c_num_freed (get_cls st2 c) <? n then aundef_ (UCheck 229) (k st2 false) else KK st2.

Definition gfa_tree {R} (st1 : astate) (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) : AM R :=
  if n <=? c_num_freed (get_cls st1 c) then gfa_take c n k KK st1
  else populate_free_array st1 c (n - c_num_freed (get_cls st1 c)) (fun st2 ok => if ok then gfa_take c n k KK st2 else k st2 false).

Lemma cache_refill_tree_gfa : forall {R} st c (k : astate -> bool -> AM R),
  cache_refill_tree st c k =
  (let st1 := init_cache st in let n := max_count st1 c / 2 in
   gfa_tree st1 c n k (fun st2 => k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true)).
Proof. intros. reflexivity. Qed.

Definition getfrom_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n CHK lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in

     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'

  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)

  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)

  /\ munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)

  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m' (RI + 72) [C8 stn']
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2792) [C8 stm']
  /\ u32arr asegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma getfrom_spec : forall RNG {R} (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n CHK lo : Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GETFROM_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 CHK -> a4 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (gfa_tree st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom asegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC N MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, getfrom_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite RBE in AZU. rewrite FAE in FL, FJ, AZF, RFA.
  iprefix.
  carve_frame 128%nat ST.

  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry EXH MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry STM MUp WMp ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry FL MUp WMp ltac:(rewrite LFL; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry FJ MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  step. step. step.
  step. step.
  do 9 zstep.
  do 4 zstep.
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.
  do 5 zstep.
  zstep. step. if_lit.
  zstep. zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).

  lrsc_stepA AMO.
  step. if_lit.
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS. box STM.
  lrsc_stepA AMO.
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM MUl WMl ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.

  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZU1 : azero m1 (shad (al_space_beg L + c * 4294967296 + mu)) (shlen (3758096384 - mu)));
    [ eapply azero_frame; [exact AZU | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE; Z.div_mod_to_equations; lia |];
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |];
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  clear AZU AZF.
  box MU01.
  step.
  step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by (clear -NF NFA MU MUX N; lia).
  all: cycle 1.
  {
    zstep.
    snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
    box CT. box CH. box STATS. box STM.
    step.
    carry CT MUr WMr ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
    carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
    carry STATS MUr WMr ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    carry STM MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }
    unbox MU01.
    eapply evtF_cut.
    { eapply (gf_tail_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf - n) (fl2 := fl) (chunks0 := chunks0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL
       | |- Forall _ _ => exact FL31
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL; clear -KP N; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => intros kk Hkk; eapply rng_sub'; [exact RFA|]; clear -KP N NF MFA Hkk; lia
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KP N NF MFA RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KP N NF MFA RIE; lia
       end;
      atop_facts; clear -SPR CEIL LO KP N NF MFA SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & stn' & m3 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
    lazymatch type of MUr with munch _ ?m1 ?m2 =>
    assert (MU13 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                          (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z m1 m3)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
    end.
    pose proof (wmono_trans _ _ _ _ WMr WM3) as WM13. clear MUr WMr.
    xport REG MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport EXH MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STATS MU3 WM3 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STM MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport FJ MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N NF MFA Y TIC TB; lia).
    apply evtF_done. unfold gfa_tree, gfa_take. fold nf.
    replace (n <=? nf) with true by (symmetry; apply Z.leb_le; exact KP).
    replace (nf <? n) with false by (symmetry; apply Z.ltb_ge; exact KP).
    eapply KONT.
    unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
    split; [apply fp_le_refl|].
    exists mu, mfa, 0, sj, stm, stn'.
    replace (nf + 0) with nf by (clear; lia). replace (au + 0 * S) with au by (clear; lia).
    split; [left; reflexivity|]. split; [clear -MU MUX; lia|]. split; [exact MUM|].
    split; [left; split; [exact KP| reflexivity]|]. split; [clear; lia|]. split; [clear -MU; lia|].
    split; [left; reflexivity|]. split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|]. split; [exact KP|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; exact FL3|].
    split; [exists fj; exact FJ|].
    split; [symmetry; apply aclass_eta0|| (destruct (get_cls st c); reflexivity)|].
    split; [left; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MU13]]; unfold sub_fp; cbn [outside]; clear -N MFA NF; intros x Hx; lia. }
    split; [eapply wmono_trans; [exact WM01| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact MTX3|]. split; [exact REG|]. split; [exact EXH|]. split; [exact STN3|]. split; [exact STATS|]. split; [exact LSJ|]. split; [exact STM|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; replace (nf - n) with (nf - n) by reflexivity; exact CH3|].
    split. { eapply azero_frame; [exact AZU1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    split. { eapply azero_frame; [exact AZF1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    eapply m3_cells_frame; [exact MC1 | exact MU13 | exact WM13 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }

  step. step. step. zstep. step. step.
  step.
  apply evtF_done. unfold gfa_tree. fold nf.
  replace (n <=? nf) with false by (symmetry; apply Z.leb_gt; exact KP).
  unbox MU01. name_sp sp (-128).
  eapply populate_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (aregion _ _ + _)) _ => rewrite RBE; exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; eapply rng_sub'; [exact RFA|]; clear -NF MFA; lia
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N KP HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PR.
  unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in PR. cbv zeta in PR. fold S mu au nf mfa in PR. rewrite FAE, RBE in PR.
  destruct PR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & UD & MUB & MUM' & NCE & NC0 & FD & NEWB & NEWM & NEWMOD & AR & JR & ST2E
                  & MU2 & WM2 & MI2 & ST2 & REG2 & EXH2 & STATS2 & LSJ2 & STM2 & AZU2 & AZF2 & MC2).
  box UD. box FD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (GC2 : get_cls st2 c = mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count (get_cls st c))) by (rewrite ST2E; apply get_cls_put_cls_eq).
  assert (NCS : au + ncnt * S <= mu' /\ 0 <= ncnt * S).
  { split; [| clear -NC0 SZ; nia]. pose proof NCE as E. clear -E MUB MU NC0 SZ. subst ncnt. Z.div_mod_to_equations. nia. }
  destruct NCS as [NCS1 NCS2].
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + mu) + shlen (mu' - mu) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 TIC TB SHF3 SHF4; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 CHK0 CHK1 Y TIC TB SHF3 SHF4; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  clear ST MI REG EXH STATS STM FJ MC1 AZU1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC.
  pose proof (u32arr_app _ _ _ _ FL ltac:(rewrite LFL, Z2Nat.id by (clear -NF; lia); exact AR)) as FL2.
  assert (LFL2 : length (fl ++ fvals au S (Z.to_nat ncnt)) = Z.to_nat (nf + ncnt)) by (rewrite length_app, fvals_length, LFL; clear -NF NC0; lia).
  assert (FL231 : Forall (fun w : word => bv_unsigned w < 2^31) (fl ++ fvals au S (Z.to_nat ncnt))).
  { apply Forall_app. split; [exact FL31|]. apply fvals_small; [clear -MU; lia | clear -SZ; lia |]. rewrite Z2Nat.id by (clear -NC0; lia). clear -NCS1 MUB; lia. }
  replace (ret_pc (Z_to_bv 64 270124)) with (Z_to_bv 64 270124 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  step. step.
  step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear -NF NC0 N MFA NEWB; lia).
  {
    apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
    replace (nf + ncnt <? n) with true by (symmetry; apply Z.ltb_lt; exact KQ).
    rewrite aembed_aundef_. apply implF_ret_unr. }
  step. zstep.
  snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
  box CH. box STATS2. box STM2. box FL2. clear FL AR.
  step.
  carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS2 MUr WMr ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM2 MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry FL2 MUr WMr ltac:(rewrite LFL2; clear -SP1 SP2 HC RIE NF NC0 MFA NEWB; lia).
  step. step.
  eapply evtF_cut.
  { eapply (gf_tail_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf + ncnt - n) (fl2 := fl ++ fvals au S (Z.to_nat ncnt)) (chunks0 := chunks0);
    try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL2; clear -KQ N; f_equal; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => (
             intros kk Hkk; assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia); destruct M4 as [q Hq];
             with_box FD ltac:(destruct DX as [Enew|(LT & Enew & _ & GR1 & _)];
               [ eapply rng_sub'; [exact RFA|]; clear -Hkk Enew MFA NF NC0 NEWB; lia
               | destruct (Z_lt_le_dec (4 * kk + 3) mfa) as [LO4|HI4];
                 [ eapply rng_sub'; [exact RFA|]; clear -Hkk LO4 MFA NF NC0; lia
                 | eapply rng_sub'; [exact GR1|]; clear -Hkk HI4 MFA NF NC0 NEWB Hq; lia ] ]))
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE; lia
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- @eq word _ _ => f_equal; clear; lia
       end;
    try (atop_facts; clear -SPR CEIL LO KQ N NF NC0 MFA NEWB SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia). }
  cbv beta. intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & stn' & m4 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
  lazymatch type of MUr with munch _ ?ma ?mb =>
  assert (MU24 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                        (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z ma m4)
    by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  pose proof (wmono_trans _ _ _ _ WMr WM3) as WM24. clear MUr WMr.
  xport REG2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport EXH2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STM2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
  replace (nf + ncnt <? n) with false by (symmetry; apply Z.ltb_ge; exact KQ).
  eapply KONT.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
  split; [exact FPLE|].
  exists mu', mfa', ncnt, sj', stm', stn'.
  assert (SHU : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu) /\ shad (al_space_beg L + c * 4294967296 + mu') + shlen (3758096384 - mu') <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHU as (SHU1 & SHU2 & SHU3 & SHU4).
  split. { with_box UD ltac:(destruct DX as [(LE & Emu)|(LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact KP|]; split; [exact LT|]; split; [exact Emu|];
             split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MU24 | exact WM24 |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from] ];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MU MUB SHU1 SHF2 Y TIC TB SHF3 SHF4; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|].
  split; [right; split; [exact KP| exact NCE]|]. split; [exact NC0|]. split; [exact NCS1|].
  split. { with_box FD ltac:(destruct DX as [(LE & Emfa)|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NEWB NEWM SHF1 SHU4 Y TIC TB; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact KQ|].
  split; [exact FL3|].
  split. { eapply junk_frame; [exact JR | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NC0 NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|].
  split; [right; rewrite GC2; exact ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
           unfold sub_fp; cbn [outside]; clear -N MFA NF NC0 NEWB NEWM MUB KP KQ; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
  split; [exact MTX3|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN3|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [exact CH3|].
  split. { eapply azero_frame; [exact AZU2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUB RIE T0 T1 CHK0 CHK1 N SHU1 SHU2 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM RIE T0 T1 CHK0 CHK1 N SHU3 SHU4 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MU24 | exact WM24 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
  do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil.
Qed.
End CANSEC2.
End F_agetfrom.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMalloc_iface AEmbRep AFrameD AEmbFrame F_apopulate_x.
Module F_agetfrom_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame. Import F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate_x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

Ltac lrsc_stepA AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; rewrite ?Z.eqb_refl; exec_cbv; amo_align AMO; rewrite ?Z.eqb_refl;
        simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Notation GETFROM_STACK_X := 1472 (only parsing).

Section CANSECX. Context {rc : runConstT} {ov : annOV}.

Definition gfunlock_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v b : word) (F : bvmap 5 word) (fc : bv 32)
    (RI lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v b a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)].

Lemma gf_unlock_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v b : word)
    (rax t0 t1 t2 a0x a1x a2x a3x a4x a5x a6 a7 s2x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (RI lo : Z) (fr0 : list byte),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 24 fr0; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 1152921504606846976)] ->
  amo_aligned AD (Z_to_bv 64 RI) = true ->
  0x10007fff8000 <= RI -> RI + 128 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 ->
  evtF asegs RNG (gfunlock_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v b F fc RI lo m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 RI) b a0x a1x a2x a3x a4x a5x a6 a7
             s2x (Z_to_bv 64 2305843009213693952) s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x41e08) fc None m (seg_rom asegs)).
Proof.
  intros until fr0. intros ST CEIL LO MI FR MTX AMO RI0 RI1 RIMG RSTK RRI.
  unfold AIMG_HI in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.

  step.
  do 7 zstep. step. do 5 zstep.
  step.
  zstep. zstep. step. if_lit.
  zstep. step. if_lit.
  do 7 zstep. step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  step. if_lit.
  step. if_lit.
  step.
  do 15 step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. unfold gfunlock_post.
  do 15 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  exact MTX.
Qed.

Definition gfa_tree_x {R} (RESV : list (Z * Z)) (st1 : astate) (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) : AM R :=
  if n <=? c_num_freed (get_cls st1 c) then gfa_take c n k KK st1
  else populate_free_array_g (exh_report ATOP RESV c) (exh_clear c) st1 c (n - c_num_freed (get_cls st1 c))
         (fun st2 ok => if ok then gfa_take c n k KK st2 else k st2 false).

Definition xfalse_ret (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (XS : Z) (st : astate) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ ((exh_mem c st = true /\ st2 = st) \/ (exh_mem c st = false /\ exists e2, st2 = set_emb e2 (exh_set c st)))
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m'
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 1)]
  /\ (exists d1 cap1,
        munch [(bv_unsigned sp - XS, bv_unsigned sp); (RI, RI + 8); (RI + 68, RI + 69); (AEMB, AEMB + 56);
               (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z m m'
        /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2 /\ (cap1 = 0 \/ d1 + cap1 <= ATOP))
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Definition getfrom_ret_x (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n CHK lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in

     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'

  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)

  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st \/ st2 = exh_clear c (put_cls c (get_cls st2 c) st))

  /\ munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)

  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st2 then 1 else 0))]
  /\ rw_cells asegs m' (RI + 72) [C8 stn']
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2792) [C8 stm']
  /\ u32arr asegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma getfrom_spec_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n CHK lo : Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GETFROM_STACK_X ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 CHK -> a4 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->

  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      xfalse_ret L RESV RNG sp GETFROM_STACK_X st c lo m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret_x L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (gfa_tree_x RESV st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom asegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC N MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG KF KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, getfrom_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite RBE in AZU. rewrite FAE in FL, FJ, AZF, RFA.
  iprefix.
  carve_frame 128%nat ST.

  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry EXH MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry STM MUp WMp ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry FL MUp WMp ltac:(rewrite LFL; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry FJ MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  step. step. step.
  step. step.
  do 9 zstep.
  do 4 zstep.
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.
  do 5 zstep.
  zstep. step. if_lit.
  zstep. zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).

  lrsc_stepA AMO.
  step. if_lit.
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS. box STM.
  lrsc_stepA AMO.
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM MUl WMl ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.

  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZU1 : azero m1 (shad (al_space_beg L + c * 4294967296 + mu)) (shlen (3758096384 - mu)));
    [ eapply azero_frame; [exact AZU | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE; Z.div_mod_to_equations; lia |];
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |];
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  clear AZU AZF.
  box MU01.
  step.
  step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by (clear -NF NFA MU MUX N; lia).
  all: cycle 1.
  {
    zstep.
    snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
    box CT. box CH. box STATS. box STM.
    step.
    carry CT MUr WMr ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
    carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
    carry STATS MUr WMr ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    carry STM MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }
    unbox MU01.
    eapply evtF_cut.
    { eapply (gf_tail_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf - n) (fl2 := fl) (chunks0 := chunks0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL
       | |- Forall _ _ => exact FL31
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL; clear -KP N; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => intros kk Hkk; eapply rng_sub'; [exact RFA|]; clear -KP N NF MFA Hkk; lia
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KP N NF MFA RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KP N NF MFA RIE; lia
       end;
      atop_facts; clear -SPR CEIL LO KP N NF MFA SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & stn' & m3 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
    lazymatch type of MUr with munch _ ?m1 ?m2 =>
    assert (MU13 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                          (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z m1 m3)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
    end.
    pose proof (wmono_trans _ _ _ _ WMr WM3) as WM13. clear MUr WMr.
    xport REG MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport EXH MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STATS MU3 WM3 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STM MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport FJ MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N NF MFA Y TIC TB; lia).
    apply evtF_done. unfold gfa_tree_x, gfa_take. fold nf.
    replace (n <=? nf) with true by (symmetry; apply Z.leb_le; exact KP).
    replace (nf <? n) with false by (symmetry; apply Z.ltb_ge; exact KP).
    eapply KONT.
    unfold getfrom_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
    split; [apply fp_le_refl|].
    exists mu, mfa, 0, sj, stm, stn'.
    replace (nf + 0) with nf by (clear; lia). replace (au + 0 * S) with au by (clear; lia).
    split; [left; reflexivity|]. split; [clear -MU MUX; lia|]. split; [exact MUM|].
    split; [left; split; [exact KP| reflexivity]|]. split; [clear; lia|]. split; [clear -MU; lia|].
    split; [left; reflexivity|]. split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|]. split; [exact KP|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; exact FL3|].
    split; [exists fj; exact FJ|].
    split; [symmetry; apply aclass_eta0|| (destruct (get_cls st c); reflexivity)|].
    split; [left; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MU13]]; unfold sub_fp; cbn [outside]; clear -N MFA NF; intros x Hx; lia. }
    split; [eapply wmono_trans; [exact WM01| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact MTX3|]. split; [exact REG|]. split; [exact EXH|]. split; [exact STN3|]. split; [exact STATS|]. split; [exact LSJ|]. split; [exact STM|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; replace (nf - n) with (nf - n) by reflexivity; exact CH3|].
    split. { eapply azero_frame; [exact AZU1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    split. { eapply azero_frame; [exact AZF1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    eapply m3_cells_frame; [exact MC1 | exact MU13 | exact WM13 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }

  step. step. step. zstep. step. step.
  step.
  apply evtF_done. unfold gfa_tree_x. fold nf.
  replace (n <=? nf) with false by (symmetry; apply Z.leb_gt; exact KP).
  unbox MU01.

  assert (RIB : 6483968 <= aregion_info L c /\ aregion_info L c + 128 <= ATOP) by (rewrite RIE; clear -SP1 SP2 HC; lia).
  destruct RIB as [RILO RIHI]. pose proof atop_range as ATR.
  lazymatch type of MU01 with munch ?WW _ ?mp =>
    assert (WHI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) WW)
      by (apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst]; unfold AIMG_HI; clear -LO CEIL ATR RILO; lia);
    assert (RELROp : arelro mp) by (exact (arelro_frameD m mp _ RELRO MU01 WHI));
    assert (XCp : exh_cells mp) by (exact (exh_cells_frameD m mp _ XC MU01 WHI));
    assert (ECp : emb_cells st mp)
      by (apply (emb_cells_frameD st m mp _ EC MU01);
          [ cbn [disjoint_from]; unfold AEMB; clear -LO CEIL ATR RILO; lia
          | pose proof RIOLD as RIO; destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE0; rewrite ?EE0 in RIO; cbv beta iota in RIO;
            destruct (emb_cells_top st m d0 cap0 sz0 EC EE0) as [Z0|(CP0 & _ & TB0)]; [left; exact Z0| right];
            cbn [disjoint_from]; clear -LO CEIL TB0 CP0 RIO; lia ])
  end.
  name_sp sp (-128).
  eapply populate_spec_x with (lo := lo) (L := L) (RESV := RESV);
  try lazymatch goal with
       | |- exh_first_stmt => exact EXHW | |- aresv_ok _ _ => exact ROK | |- arelro _ => exact RELROp
       | |- exh_cells _ => exact XCp | |- emb_cells _ _ => exact ECp | |- pcov _ _ _ => exact RIRES | |- emb_rng _ _ => exact ERNG
       | |- bv_unsigned _ < 2 ^ 63 => rewrite Hsp; clear -SP63 SPR CEIL LO ATR; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (aregion _ _ + _)) _ => rewrite RBE; exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; eapply rng_sub'; [exact RFA|]; clear -NF MFA; lia
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N KP HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).

  1: {
    intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PRF.
    unfold populate_ret_false in PRF. cbv zeta in PRF.
    destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
    destruct PRF as (FPLE & STREL & EC2 & ERNG2 & XC2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TP1) & MI2 & ST2).
    unname_sp.
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RRI.
    cbv beta iota in RIOLD.
    lazymatch type of MU01 with munch _ _ ?mp =>
      assert (B0 : cap0 = 0 \/ (0 < cap0 /\ d0 + cap0 <= ATOP)) by (destruct (emb_cells_top st mp d0 cap0 sz0 ECp EE) as [Z0|(CP0 & _ & TB0)]; [left| right; split]; assumption) end.
    assert (B2 : cap2 = 0 \/ (0 < cap2 /\ d2 + cap2 <= ATOP)) by (destruct (emb_cells_top st2 m2 d2 cap2 sz2 EC2 EE2) as [Z2|(CP2 & _ & TB2)]; [left| right; split]; assumption).
    assert (CL : forall d cap, emb_prov RESV st d0 cap0 d cap -> cap <= 0 \/ aregion_info L c + 128 <= d \/ d + cap <= aregion_info L c).
    { intros d cap [(-> & ->)|AV]; [clear -RIOLD; lia|].
      destruct (Z_le_gt_dec cap 0) as [LE0|GT0]; [left; exact LE0| right].
      unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
      pose proof (pcov_clear _ _ _ _ _ RIRES AV ltac:(clear; lia) ltac:(clear -GT0; lia)) as C. clear -C. lia. }
    pose proof (CL d1 cap1 PV1) as CL1. pose proof (CL d2 cap2 PV2) as CL2.
    rewrite Hsp in MU2, ST2 || idtac.
    assert (FR2 : True) by exact I.
    eapply (cells_frame_focus _ _ m2) in FR; [| exact MU2 |
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; intros x Hx; cbn [outside]; unfold AEMB;
      repeat split; try exact I; clear -Hx SPR LO CEIL RIHI ATR B0 B2 TP1; lia].
    eapply (cells_frame_focus _ _ m2) in MTX; [| exact MU2 |
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros x Hx; cbn [outside]; unfold AEMB;
      repeat split; try exact I; clear -Hx SPR LO CEIL RILO RIHI ATR RIOLD CL1 CL2; lia].
    replace (ret_pc (Z_to_bv 64 270124)) with (Z_to_bv 64 270124 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    iprefix.
    step. if_lit.
    step. step. step.
    eapply evtF_cut.
    { eapply (gf_unlock_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0)) with (lo := lo) (RI := aregion_info L c);
      try lazymatch goal with
         | |- stk _ _ _ _ => exact ST2
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
         | |- amo_aligned _ _ = true => exact AMO
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (aregion_info _ _) _ => exact RRI
         end;
      try (atop_facts; clear -SPR CEIL LO SP1 SP2 HC RIE RILO RIHI; lia). }
    cbv beta. intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m4 & -> & MU3 & WM3 & MI3 & ST3 & MTX3).
    apply evtF_done. cbv beta iota. eapply KF.
    unfold xfalse_ret. cbv zeta. rewrite EE, EE2.
    assert (WHI3 : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z)
      by (apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst]; unfold AIMG_HI; clear -LO CEIL ATR RILO; lia).
    split; [exact FPLE|]. split; [exact STREL|].
    split. { apply (emb_cells_frameD st2 m2 m4 _ EC2 MU3); [cbn [disjoint_from]; unfold AEMB; clear -LO CEIL ATR RILO; lia|].
             rewrite EE2. destruct B2 as [Z2|[CP2 TB2]]; [left; exact Z2| right]. cbn [disjoint_from]. clear -LO CEIL TB2 CP2 CL2. lia. }
    split; [exact ERNG2|]. split; [exact (exh_cells_frameD m2 m4 _ XC2 MU3 WHI3)|].
    split; [exact MTX3|].
    split. { eapply AFrameD.cells_frameD; [exact FLG2| exact MU3|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. clear -LO CEIL RIHI. lia. }
    split. { exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TP1]]].
             eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
               unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
    split; [exact MI3| exact ST3]. }

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PR.
  unfold populate_ret_g, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in PR. cbv zeta in PR. fold S mu au nf mfa in PR. rewrite FAE, RBE in PR.
  destruct PR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & UD & MUB & MUM' & NCE & NC0 & FD & NEWB & NEWM & NEWMOD & AR & JR & ST2E
                  & MU2 & WM2 & MI2 & ST2 & REG2 & EXH2 & STATS2 & LSJ2 & STM2 & AZU2 & AZF2 & MC2).
  box UD. box FD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (GC2 : get_cls st2 c = mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count (get_cls st c))) by (rewrite ST2E, get_cls_exh_clear; apply get_cls_put_cls_eq).
  assert (NCS : au + ncnt * S <= mu' /\ 0 <= ncnt * S).
  { split; [| clear -NC0 SZ; nia]. pose proof NCE as E. clear -E MUB MU NC0 SZ. subst ncnt. Z.div_mod_to_equations. nia. }
  destruct NCS as [NCS1 NCS2].
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + mu) + shlen (mu' - mu) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 TIC TB SHF3 SHF4; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 CHK0 CHK1 Y TIC TB SHF3 SHF4; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  clear ST MI REG EXH STATS STM FJ MC1 AZU1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC.
  pose proof (u32arr_app _ _ _ _ FL ltac:(rewrite LFL, Z2Nat.id by (clear -NF; lia); exact AR)) as FL2.
  assert (LFL2 : length (fl ++ fvals au S (Z.to_nat ncnt)) = Z.to_nat (nf + ncnt)) by (rewrite length_app, fvals_length, LFL; clear -NF NC0; lia).
  assert (FL231 : Forall (fun w : word => bv_unsigned w < 2^31) (fl ++ fvals au S (Z.to_nat ncnt))).
  { apply Forall_app. split; [exact FL31|]. apply fvals_small; [clear -MU; lia | clear -SZ; lia |]. rewrite Z2Nat.id by (clear -NC0; lia). clear -NCS1 MUB; lia. }
  replace (ret_pc (Z_to_bv 64 270124)) with (Z_to_bv 64 270124 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  step. step.
  step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear -NF NC0 N MFA NEWB; lia).
  {
    apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
    replace (nf + ncnt <? n) with true by (symmetry; apply Z.ltb_lt; exact KQ).
    rewrite aembed_aundef_. apply implF_ret_unr. }
  step. zstep.
  snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
  box CH. box STATS2. box STM2. box FL2. clear FL AR.
  step.
  carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS2 MUr WMr ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM2 MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry FL2 MUr WMr ltac:(rewrite LFL2; clear -SP1 SP2 HC RIE NF NC0 MFA NEWB; lia).
  step. step.
  eapply evtF_cut.
  { eapply (gf_tail_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf + ncnt - n) (fl2 := fl ++ fvals au S (Z.to_nat ncnt)) (chunks0 := chunks0);
    try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL2; clear -KQ N; f_equal; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => (
             intros kk Hkk; assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia); destruct M4 as [q Hq];
             with_box FD ltac:(destruct DX as [Enew|(LT & Enew & _ & GR1 & _)];
               [ eapply rng_sub'; [exact RFA|]; clear -Hkk Enew MFA NF NC0 NEWB; lia
               | destruct (Z_lt_le_dec (4 * kk + 3) mfa) as [LO4|HI4];
                 [ eapply rng_sub'; [exact RFA|]; clear -Hkk LO4 MFA NF NC0; lia
                 | eapply rng_sub'; [exact GR1|]; clear -Hkk HI4 MFA NF NC0 NEWB Hq; lia ] ]))
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE; lia
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- @eq word _ _ => f_equal; clear; lia
       end;
    try (atop_facts; clear -SPR CEIL LO KQ N NF NC0 MFA NEWB SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia). }
  cbv beta. intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & stn' & m4 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
  lazymatch type of MUr with munch _ ?ma ?mb =>
  assert (MU24 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                        (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z ma m4)
    by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  pose proof (wmono_trans _ _ _ _ WMr WM3) as WM24. clear MUr WMr.
  xport REG2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport EXH2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STM2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
  replace (nf + ncnt <? n) with false by (symmetry; apply Z.ltb_ge; exact KQ).
  eapply KONT.
  unfold getfrom_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
  split; [exact FPLE|].
  exists mu', mfa', ncnt, sj', stm', stn'.
  assert (SHU : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu) /\ shad (al_space_beg L + c * 4294967296 + mu') + shlen (3758096384 - mu') <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHU as (SHU1 & SHU2 & SHU3 & SHU4).
  split. { with_box UD ltac:(destruct DX as [(LE & Emu)|(LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact KP|]; split; [exact LT|]; split; [exact Emu|];
             split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MU24 | exact WM24 |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from] ];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MU MUB SHU1 SHF2 Y TIC TB SHF3 SHF4; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|].
  split; [right; split; [exact KP| exact NCE]|]. split; [exact NC0|]. split; [exact NCS1|].
  split. { with_box FD ltac:(destruct DX as [(LE & Emfa)|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NEWB NEWM SHF1 SHU4 Y TIC TB; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact KQ|].
  split; [exact FL3|].
  split. { eapply junk_frame; [exact JR | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NC0 NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|].
  split; [right; rewrite GC2; exact ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
           unfold sub_fp; cbn [outside]; clear -N MFA NF NC0 NEWB NEWM MUB KP KQ; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
  split; [exact MTX3|]. split; [exact REG2|]. split; [replace (exh_mem c st2) with false by (rewrite ST2E; symmetry; apply exh_mem_clear_same); exact EXH2|]. split; [exact STN3|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [exact CH3|].
  split. { eapply azero_frame; [exact AZU2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUB RIE T0 T1 CHK0 CHK1 N SHU1 SHU2 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM RIE T0 T1 CHK0 CHK1 N SHU3 SHU4 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MU24 | exact WM24 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
  do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil.
Qed.
End CANSECX.
End F_agetfrom_x.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKitR.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_amaybe.
Module F_areturn.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition rta_entry : Z := 0x3f914.
End CANSEC1.
Notation RTA_STACK := 576 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma rta_copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u32arr asegs m SRC src -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  u32arr asegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv asegs m ->
  0 <= SRC -> SRC + 4 * n < 2^47 -> 0 <= DST -> DST + 4 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 4 * n <= DST \/ DST + 4 * Z.of_nat (length ws0) <= SRC) ->
  (forall k, 0 <= k < n -> rng RNG (SRC + 4 * k) 4) -> (forall k, 0 <= k < n -> rng RNG (DST + 4 * k) 4) ->
  evtF asegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1' a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * n)) s7 s8 (Z_to_bv 64 (DST + 4 * n)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3faa4) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * i)) s7 s8 (Z_to_bv 64 (DST + 4 * i)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3fa90) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1. pose proof (RDS i ltac:(lia)) as RD1.
  step. clear RD RS1.
  rewrite (sx32_small w W31).
  zstep.
  setreg 22 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write asegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 4 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  clear DSTA. store_done. try clear SOK. clear RD1.
  zstep.
  setreg 25 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.
  -
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a1' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a1', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  -
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

Lemma junk_of_cells' : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

Lemma set_mfa_eq : forall v r,
  cls_set_mapped_free_array v r = mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) v (c_count r).
Proof. intros v []; reflexivity. Qed.

Definition rta_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n SRC lo : Z) (src : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let nf2 := nf + n in
  fp_le RNG RNG' /\
  exists mfa' sj',
     (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ get_cls st2 c = mkAClass (c_mapped_user r) (c_allocated_user r) nf mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)
  /\ munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp);
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf2); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ u32arr asegs m' (FA + 4 * nf) src
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma rta_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n SRC lo : Z) (sj src : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RTA_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c -> a4 = Z_to_bv 64 SRC -> a5 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  u32arr asegs m SRC src -> length src = Z.to_nat n -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Proof.
  intros until src. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CH LCH CH31 FJ AZF SBE HC N NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, rta_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - RTA_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite FAE in FJ, AZF, RFA.

  destruct (junk_split m (aregion_info L c + 72) 8 48 J72 ltac:(lia) ltac:(lia)) as [J72a J80].
  destruct (junk_split m (aregion_info L c + 72 + 8) 8 40 J80 ltac:(lia) ltac:(lia)) as [J80a J88].
  destruct (junk_split m (aregion_info L c + 72 + 8 + 8) 8 32 J88 ltac:(lia) ltac:(lia)) as [J88a J96].
  replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) in J80a by lia.
  replace (aregion_info L c + 72 + 8 + 8) with (aregion_info L c + 88) in J88a by lia.
  replace (aregion_info L c + 72 + 8 + 8 + 8) with (aregion_info L c + 96) in J96 by lia.
  destruct (c8_of_junk m _ J72a) as [stn STN]. destruct (c8_of_junk m _ J80a) as [w80 W80]. destruct (c8_of_junk m _ J88a) as [w88 W88].
  destruct J96 as [j96 J96].
  clear J72 J72a J80 J80a J88 J88a.
  iprefix.
  carve_frame 128%nat ST.
  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box STN. box W80. box W88. box J96. box STATS. box CH. box FJ. box AZF.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  do 7 step.
  step. step.
  do 9 zstep.
  zstep. zstep. zstep. zstep.
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 25 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 12 (Z_to_bv 64 (aregion L c)) ltac:(rewrite RBE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.
  zstep.
  step.
  do 4 zstep.
  zstep. step. if_lit.
  zstep. zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).

  lrsc_stepA AMO.
  step. if_lit.
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS.
  lrsc_stepA AMO.
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.

  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  unbox FJ. eapply junk_frame in FJ; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; clear -SPR CEIL LO SP1 SP2 HC RIE NF MFA; lia].
  unbox AZF.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |]
  end.
  clear AZF.
  box MU01.
  step.
  zstep.
  step. step. step.
  step.
  apply evtF_done.
  name_sp sp (-128).
  eapply ensure_spec with (lo := lo) (L := L) (sj := sj);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold mu au nf mfa; first [assumption | clear -NF MFA MFAM NFN N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TIC TB CXI; lia]).

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
  unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold nf mfa in ER. rewrite FAE in ER.
  destruct ER as (FPLE & new & sj' & UD & NEWB & NEWGE & NEWM & MU2 & WM2 & MI2 & ST2 & REG2 & STATS2 & LSJ2 & AZF2 & MC2).
  box UD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  assert (SHFL : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
  { rewrite !shad_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF. Z.div_mod_to_equations. lia. }
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF TIC TB SHFL; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W80 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W88 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport J96 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF CHK0 CHK1 N Y TIC TB SHFL; lia).
  eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; cbn [disjoint_from]; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia].
  clear ST MI REG STATS MC1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC MC.

  assert (JD : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (new - 4 * nf)).
  { ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & ZCB & _)].
    - rewrite E. exact FJ.
    - replace (new - 4 * nf) with ((mfa - 4 * nf) + (new - mfa)) by (clear; lia).
      apply junk_merge; [exact FJ | | clear -MFA; lia | clear -NEWGE; lia].
      replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + (mfa - 4 * nf)) with (al_space_beg L + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
      eapply junk_of_cb. exact ZCB. }
  clear FJ.
  destruct (junk_split m2 _ (4 * n) (new - 4 * nf - 4 * n) ltac:(eapply junk_at_eq; [exact JD| reflexivity | clear; lia]) ltac:(clear -N; lia) ltac:(clear -NEWB; lia)) as [JD4 JR].
  destruct (u32arr_of_junk m2 _ n JD4 ltac:(clear -N; lia)) as (ws0 & U0 & L0). clear JD JD4.
  set (DST := al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) in *.
  replace (ret_pc (Z_to_bv 64 260728)) with (Z_to_bv 64 260728 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }
  zstep. zstep. zstep. zstep.
  setreg 25 (Z_to_bv 64 (DST + 4 * 0)) ltac:(subst DST; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 10 (Z_to_bv 64 (SRC + 4 * n)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 22 (Z_to_bv 64 (SRC + 4 * 0)) ltac:(f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (rta_copy_loop_spec RNG' _ 0 n SRC DST src ws0); try reflexivity.
    - clear -N; lia.
    - exact LCH.
    - rewrite L0. clear -N; lia.
    - exact CH.
    - exact CH31.
    - cbn [Z.to_nat firstn skipn app]. exact U0.
    - exact MI2.
    - clear -CHK0 T0 TIC TB; lia.
    - clear -CHK1 T1 N TIC TB; lia.
    - subst DST. clear -SP1 HC NF; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). clear -SP2 HC NF N NEWB MFA; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). ub TSP. clear -Y CHK0 CHK1 T0 T1 SP1 SP2 HC NF N NEWB MFA TIC TB. destruct Y as [Y|Y]; [left; lia| right; lia].
    - intros kk Hkk. eapply rng_sub'; [exact RT|]. clear -CHK0 CHK1 Hkk N; lia.
    - intros kk Hkk. subst DST. destruct (Z_lt_le_dec (4 * nf + 4 * kk) mfa) as [LT|GE].
      + eapply rng_sub'; [exact RFA|]. assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia).
        destruct M4 as [q Hq]. clear -LT Hkk NF Hq. lia.
      + ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & _ & _ & R1 & _)].
        * exfalso. clear -E GE Hkk NEWB. lia.
        * eapply rng_sub'; [exact R1|]. clear -GE Hkk NEWB. lia. }
  cbv beta. intros ms' (a1x & m3 & -> & MU3 & WM3 & MI3 & SR3 & DS3).
  xport FR MU3 WM3 ltac:(subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  xport MTX MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STN MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W80 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W88 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport J96 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport REG2 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; subst DST; ub TSP; clear -SP1 SP2 HC T0 T1 NF N NEWB Y TIC TB; lia).
  eapply junk_frame in JR; [| exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; subst DST; clear -NF N; lia].
  pose proof (stk_transport_disjoint asegs _ m2 m3 _ _ ST2 MU3 WM3 ltac:(cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia)) as ST3.
  assert (AZF3 : azero m3 (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new))).
  { eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 |]. intros _; cbn [disjoint_from].
    rewrite shad_div, shlen_div; unfold ASHOFF; subst DST; clear -SP1 SP2 HC NF N NEWB; Z.div_mod_to_equations; lia. }
  assert (MC3 : m3_cells L m3).
  { eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. ub SCX; unfold AIMG_HI, AIMG_LO.
    apply Forall_cons; [cbn [fst snd]; subst DST; clear -CX0 CX1 SP1 SP2 HC NF N NEWB Y CXI; lia |]. apply Forall_nil. }
  clear ST2 MI2 AZF2 MC2 U0. box MU3. box MU2.

  step.
  snapshot [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88)]%Z MUs WMs.
  box SR3. box DS3. box STATS2. clear CH.
  step.
  zstep.
  step.
  carry SR3 MUs WMs ltac:(rewrite LCH; ub TSP; clear -SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUs WMs ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUs WMs ltac:(rewrite LSJ2; ub TSP; clear -SP1 SP2 HC RIE T0 T1 Y TIC TB; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MC4 : m3_cells L mm) ; [eapply m3_cells_frame; [exact MC3 | exact MUs | exact WMs |]; ub SCX; unfold AIMG_HI, AIMG_LO;
    do 2 (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |] end.
  eapply junk_frame in JR; [| exact MUs | exact WMs | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia].
  clear MC3. box MUs.

  step. step. step. step.
  step.
  box SR3. box DS3. box STATS2. box MTX. box STN. box W88. box J96. box REG2. box W80.
  snapshot [(bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z MUm WMm.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of REG2 with boxed (rw_cells _ _ _ [C8 _; C8 _; C8 (Z_to_bv 64 ?auv); C8 _; C8 (Z_to_bv 64 ?muv); C8 _]) =>
    lazymatch type of W80 with boxed (rw_cells _ _ _ [C8 ?w80v]) =>
      call_sp (maybe_release_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm L c lo (nf + n) new auv muv w80v w88);
      [ exact ST3 | atop_facts; exact CEIL | clear -LO; lia | assumption | reflexivity | reflexivity | reflexivity
      | exact MC4 | unboxed REG2 | unboxed W80 | unboxed W88 | unfold K_NUM_CLASSES; exact HC | exact SP1 | unfold K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; exact SP2
      | ]
    end end end.
  rename POST into ST5.
  carry SR3 MUm WMm ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry DS3 MUm WMm ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  carry STATS2 MUm WMm ltac:(rewrite LSJ2; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry MTX MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG2 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  eapply junk_frame in JR; [| exact MUm | exact WMm | intros _; cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MC5 : m3_cells L mm); [eapply m3_cells_frame; [exact MC4 | exact MUm | exact WMm |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI; lia |]; apply Forall_nil |];
    assert (MU35 : munch [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                          (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z m3 mm);
    [ eapply munch_trans; [eapply munch_weaken; [| unboxed MUs] | eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |];
    pose proof WMs as WM35;
    assert (AZF5 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF3 | exact MU35 | exact WM35 |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |]
  end.
  clear MC4 AZF3.

  step.
  do 7 zstep. step. do 5 zstep.
  step.
  zstep. zstep. step. if_lit.
  zstep. step. if_lit.
  do 7 zstep. step. if_lit.
  box SR3. box DS3. box STATS2. box MUm. box MU35.
  snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUu WMu.
  lrsc_stepA AMO.
  step. if_lit.
  lrsc_stepA AMO.
  carry SR3 MUu WMu ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUu WMu ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUu WMu ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.
  step. if_lit.
  do 15 step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MUx4 : munch [(aregion_info L c, aregion_info L c + 8)]%Z x14 mm) by (eapply munch_weaken; [| exact MUu]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia);
    eapply junk_frame in JR; [| exact MUx4 | exact WMu | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia];
    assert (AZF6 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF5 | exact MUx4 | exact WMu |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |];
    assert (MC6 : m3_cells L mm); [eapply m3_cells_frame; [exact MC5 | exact MUx4 | exact WMu |]; unfold AIMG_HI, AIMG_LO; ub SCX;
      apply Forall_cons; [cbn [fst snd]; clear -SP1 SP2 HC RIE CX0 CX1 Y CXI; lia |]; apply Forall_nil |]
  end.
  clear MC5 AZF5 MUu.
  apply evtF_done. eapply KONT.
  unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mu au nf mfa. rewrite FAE.
  split; [exact FPLE|].
  exists new, sj'.

  lazymatch goal with |- context [munch ?W m ?mm] =>
    assert (MUT : munch W m mm);
    [ ub MU01; ub MU3; ub MU35; ub MU2; subst DST;
      eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y2] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y1] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |]
  end.
  assert (WMT : wmono asegs m _) by (eapply wmono_trans; [exact WM01 | eapply wmono_trans; [exact WM2 | exact WM3]]).
  split.
  { ub UD. destruct Y as [(_ & E & _ & _)|(LT & E & _ & _ & FILL & R1 & R2 & BW)]; [left; exact E| right].
    split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
    ub MU3; ub MU35; subst DST.
    eapply (fill_frame [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * n);
                        (aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                        (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128); (aregion_info L c, aregion_info L c + 8)]%Z);
      [exact FILL | | exact WM3 |].
    - eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia.
    - intros _. cbn [disjoint_from]. rewrite shad_div, shlen_div; unfold ASHOFF. clear -SPR CEIL LO SP1 SP2 HC NF N NEWB NEWGE MFA RIE. Z.div_mod_to_equations; lia. }
  split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
  assert (GC2 : get_cls st2 c = mkAClass mu au nf new (c_count (get_cls st c))).
  { ub UD. destruct Y as [(_ & E & -> & _)|(_ & _ & -> & _)].
    - rewrite E. subst mu au nf mfa. symmetry. apply aclass_eta0.
    - rewrite get_cls_put_cls_eq. subst mu au nf mfa. apply set_mfa_eq. }
  split; [exact GC2|].
  split. { ub UD. destruct Y as [(_ & _ & -> & _)|(_ & _ & E & _)]; [left; reflexivity| right]. rewrite GC2. rewrite E at 1. f_equal; subst mu au nf mfa; apply set_mfa_eq. }
  split; [exact MUT|]. split; [exact WMT|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact REG2|].
  split. { replace 56 with (8 + (8 + (8 + 32))) by reflexivity.
           apply junk_merge; [eapply junk_of_cells'; [exact STN| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W80| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 80 + 8) with (aregion_info L c + 88) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W88| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 88 + 8) with (aregion_info L c + 96) by (clear; lia). exists j96. exact J96. }
  split; [exact STATS2|]. split; [exact LSJ2|].
  split; [exact (proj1 (u32arr_app_inv _ _ _ _ DS3))|].
  split; [eapply junk_at_eq; [exact JR | subst DST; clear; lia | clear; lia]|].
  split; [exact AZF6| exact MC6].
Qed.
End CANSEC2.
End F_areturn.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module F_agetfrom.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

Ltac lrsc_stepA AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; rewrite ?Z.eqb_refl; exec_cbv; amo_align AMO; rewrite ?Z.eqb_refl;
        simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma sx32_small : forall w : word, bv_unsigned w < 2^31 -> sx32 w = w.
Proof.
  intros w Hw. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  rewrite <- (Z_to_bv_bv_unsigned w). rewrite sx32_lit by lia. reflexivity.
Qed.

Lemma aclass_eta0 : forall r, mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) (c_count r) = r.
Proof. intros []; reflexivity. Qed.

Lemma fvals_small : forall au S k, 0 <= au -> 0 <= S -> au + Z.of_nat k * S <= 2^32 ->
  Forall (fun w : word => bv_unsigned w < 2^31) (fvals au S k).
Proof.
  intros au S k AU SZ B. unfold fvals. apply Forall_rev. apply Forall_map. apply Forall_forall. intros j Hj.
  apply in_seq in Hj. rewrite Z.shiftr_div_pow2 by lia.
  assert (J : 0 <= Z.of_nat j * S <= Z.of_nat k * S) by nia.
  rewrite unsigned_lit; [| change (2^4) with 16; Z.div_mod_to_equations; lia]. change (2^4) with 16. Z.div_mod_to_equations; lia.
Qed.

Lemma u32arr_app : forall m A ws1 ws2,
  u32arr bsegs m A ws1 -> u32arr bsegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> u32arr bsegs m A (ws1 ++ ws2).
Proof.
  intros m A ws1 ws2 [[B0 [B1 B]] [W0 [W1 W]]] [[C0 [C1 C]] [V0 [V1 V]]].
  rewrite u32s_length in B1. rewrite u32s_length in C1.
  split.
  - split; [exact B0|]. split; [rewrite u32s_app, length_app, !u32s_length; lia|].
    intros i Hi. rewrite u32s_app in Hi |- *. rewrite length_app, !u32s_length in Hi.
    destruct (Nat.lt_ge_cases i (4 * length ws1)) as [LT|GE].
    + rewrite nth_error_app1 by (rewrite u32s_length; exact LT). apply B. rewrite u32s_length. exact LT.
    + rewrite nth_error_app2 by (rewrite u32s_length; exact GE). rewrite u32s_length.
      specialize (C (i - 4 * length ws1)%nat ltac:(rewrite u32s_length; lia)).
      replace (A + 4 * Z.of_nat (length ws1) + Z.of_nat (i - 4 * length ws1)) with (A + Z.of_nat i) in C by lia. exact C.
  - split; [exact W0|]. split; [rewrite length_app; lia|].
    intros i Hi. rewrite length_app in Hi.
    destruct (Z_lt_le_dec i (4 * Z.of_nat (length ws1))) as [LT|GE].
    + apply W. lia.
    + specialize (V (i - 4 * Z.of_nat (length ws1)) ltac:(lia)).
      replace (A + 4 * Z.of_nat (length ws1) + (i - 4 * Z.of_nat (length ws1))) with (A + i) in V by lia. exact V.
Qed.

Lemma u32arr_skipn : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat ->
  u32arr bsegs m (A + 4 * Z.of_nat k) (skipn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1.
  split.
  - split; [lia|]. split; [rewrite u32s_length, length_skipn; lia|].
    intros i Hi. rewrite u32s_length, length_skipn in Hi.
    specialize (B (4 * k + i)%nat ltac:(rewrite u32s_length; lia)).
    replace (A + Z.of_nat (4 * k + i)) with (A + 4 * Z.of_nat k + Z.of_nat i) in B by lia. rewrite B.
    rewrite <- (firstn_skipn k ws) at 1. rewrite u32s_app, nth_error_app2 by (rewrite u32s_length, length_firstn; lia).
    rewrite u32s_length, length_firstn. f_equal. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|].
    intros i Hi. rewrite length_skipn in Hi. specialize (W (4 * Z.of_nat k + i) ltac:(lia)).
    replace (A + (4 * Z.of_nat k + i)) with (A + 4 * Z.of_nat k + i) in W by lia. exact W.
Qed.

Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition getfrom_entry := 0x42600.
End CANSEC1.
Notation GETFROM_STACK := 640 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u32arr bsegs m SRC src -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  u32arr bsegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv bsegs m ->
  0 <= SRC -> SRC + 4 * n < 2^47 -> 0 <= DST -> DST + 4 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 4 * n <= DST \/ DST + 4 * Z.of_nat (length ws0) <= SRC) ->
  (forall k, 0 <= k < n -> rng RNG (SRC + 4 * k) 4) -> rng RNG DST (4 * n) ->
  evtF bsegs RNG (fun ms' => exists a2' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2' (Z_to_bv 64 (DST + 4 * n)) a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 (SRC + 4 * n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x42788) fc None m' (seg_rom bsegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ u32arr bsegs m' SRC src /\ u32arr bsegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2 (Z_to_bv 64 (DST + 4 * i)) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (SRC + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x42774) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read bsegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1.
  step. clear RD RS1.
  rewrite (sx32_small w W31).
  pose proof (u32arr_store_ok bsegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write bsegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 4 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  clear DSTA. store_done. try clear SOK.
  zstep. zstep.
  setreg 13 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.
  -
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a2' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a2', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  -
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

Definition gftail_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (F : bvmap 5 word) (fc : bv 32)
    (RI FA CHK n base lo : Z) (fl2 chunks0 : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (stn' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (RI + 72) [C8 stn']
    /\ u32arr bsegs m' FA fl2
    /\ u32arr bsegs m' CHK (skipn (Z.to_nat base) fl2 ++ skipn (Z.to_nat n) chunks0).

Lemma gf_tail_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word)
    (rax t0 t1 t2 s1x a0x a1x a2x a6 a7 s2x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (RI FA CHK n base lo : Z) (fl2 chunks0 : list word) (stn : word) (fr0 : list byte),
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 24 fr0; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 1152921504606846976)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u32arr bsegs m FA fl2 -> length fl2 = Z.to_nat (base + n) -> Forall (fun w : word => bv_unsigned w < 2^31) fl2 ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  amo_aligned AD (Z_to_bv 64 RI) = true ->
  0 <= base -> 1 <= n <= 16 ->
  0x10007fff8000 <= FA -> FA + 4 * (base + n) <= ATOP -> 4096 <= CHK -> CHK + 64 <= ATOP -> (FA + 4 * (base + n) <= CHK \/ CHK + 64 <= FA) ->
  0x10007fff8000 <= RI -> RI + 128 <= ATOP -> (RI + 128 <= CHK \/ CHK + 64 <= RI) -> (RI + 128 <= FA \/ FA + 4 * (base + n) <= RI) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> (forall k, 0 <= k < base + n -> rng RNG (FA + 4 * k) 4) -> rng RNG CHK 64 ->
  evtF bsegs RNG (gftail_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc RI FA CHK n base lo fl2 chunks0 m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x a0x a1x a2x (Z_to_bv 64 CHK) (Z_to_bv 64 n) (Z_to_bv 64 base) a6 a7
             s2x (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 FA) s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x42764) fc None m (seg_rom bsegs)).
Proof.
  intros until fr0. intros ST CEIL LO MI FR MTX STN FL LFL FL31 CH LCH AMO B0 N FA0 FA1 CH0 CH1 DJ RI0 RI1 DJ2 DJ3 RIMG RSTK RRI RFA RCH.
  unfold AIMG_HI in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. zstep. zstep.
  setreg 11 (Z_to_bv 64 (CHK + 4 * n)) ltac:(rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (FA + 4 * Z.of_nat (Z.to_nat base) + 4 * 0)) ltac:(rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -B0; lia).
  setreg 13 (Z_to_bv 64 (CHK + 4 * 0)) ltac:(f_equal; clear; lia).
  pose proof (u32arr_skipn m FA fl2 (Z.to_nat base) FL ltac:(rewrite LFL; clear -B0 N; lia)) as SRCA.
  eapply evtF_cut.
  { eapply (copy_loop_spec RNG _ 0 n (FA + 4 * Z.of_nat (Z.to_nat base)) CHK (skipn (Z.to_nat base) fl2) chunks0); try reflexivity.
    - clear -N; lia.
    - rewrite length_skipn, LFL. clear -B0 N; lia.
    - rewrite LCH. clear -N; lia.
    - exact SRCA.
    - apply Forall_forall. intros w Hw. apply (proj1 (Forall_forall _ _) FL31 w). rewrite <- (firstn_skipn (Z.to_nat base) fl2). apply in_or_app. right. exact Hw.
    - cbn [Z.to_nat firstn skipn app]. exact CH.
    - exact MI.
    - clear -FA0 B0; lia.
    - clear -FA1 B0 N; lia.
    - clear -CH0; lia.
    - rewrite LCH; clear -CH1; lia.
    - rewrite LCH. clear -DJ B0 N; lia.
    - intros kk Hkk. replace (FA + 4 * Z.of_nat (Z.to_nat base) + 4 * kk) with (FA + 4 * (base + kk)) by (clear -B0; lia). apply RFA. clear -B0 Hkk; lia.
    - eapply rng_sub'; [exact RCH|]. clear -N; lia. }
  cbv beta. intros ms' (a2' & m2 & -> & MU2 & WM2 & MI2 & SR2 & CH2).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO CH0 CH1 N; lia).
  xport MTX MU2 WM2 ltac:(clear -DJ2 N; lia).
  xport STN MU2 WM2 ltac:(clear -DJ2 N; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; clear -DJ N B0; lia).
  pose proof (stk_transport_disjoint bsegs _ m m2 _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; clear -SPR CEIL LO CH0 CH1 N; lia)) as ST2.
  clear ST MI SRCA.
  assert (MUF : munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU MU2.

  step. zstep.
  snapshot [(RI, RI + 8); (RI + 72, RI + 80)]%Z MUb WMb.
  box CH2. box FL. clear SR2.
  step.
  step.

  step.
  do 7 zstep. step. do 5 zstep.
  step.
  zstep. zstep. step. if_lit.
  zstep. step. if_lit.
  do 7 zstep. step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  step. if_lit.
  step. if_lit.
  step.
  do 15 step.
  carry CH2 MUb WMb ltac:(rewrite length_app, !length_skipn, LFL, LCH; clear -DJ2 N B0; lia).
  carry FL MUb WMb ltac:(rewrite LFL; clear -DJ3 N B0; lia).
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -128) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. unfold gftail_post.
  do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MUF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact STN|]. split; [exact FL|].
  exact CH2.
Qed.

Definition gfa_take {R} (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) (st2 : astate) : AM R :=
  if c_num_freed (get_cls st2 c) <? n then aundef_ (UCheck 229) (k st2 false) else KK st2.

Definition gfa_tree {R} (st1 : astate) (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) : AM R :=
  if n <=? c_num_freed (get_cls st1 c) then gfa_take c n k KK st1
  else populate_free_array st1 c (n - c_num_freed (get_cls st1 c)) (fun st2 ok => if ok then gfa_take c n k KK st2 else k st2 false).

Lemma cache_refill_tree_gfa : forall {R} st c (k : astate -> bool -> AM R),
  cache_refill_tree st c k =
  (let st1 := init_cache st in let n := max_count st1 c / 2 in
   gfa_tree st1 c n k (fun st2 => k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true)).
Proof. intros. reflexivity. Qed.

Definition getfrom_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n CHK lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in

     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells bsegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'

  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr bsegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)

  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)

  /\ munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)

  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m' (RI + 72) [C8 stn']
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2792) [C8 stm']
  /\ u32arr bsegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma getfrom_spec : forall RNG {R} (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n CHK lo : Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GETFROM_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 CHK -> a4 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (gfa_tree st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC N MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, getfrom_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl bsegs m) as WM.
  rewrite RBE in AZU. rewrite FAE in FL, FJ, AZF, RFA.
  iprefix.
  carve_frame 128%nat ST.

  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry EXH MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry STM MUp WMp ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry FL MUp WMp ltac:(rewrite LFL; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry FJ MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  step. step. step.
  step. step.
  do 9 zstep.
  do 4 zstep.
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.
  do 5 zstep.
  zstep. step. if_lit.
  zstep. zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).

  lrsc_stepA AMO.
  step. if_lit.
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS. box STM.
  lrsc_stepA AMO.
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM MUl WMl ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.

  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZU1 : azero m1 (shad (al_space_beg L + c * 4294967296 + mu)) (shlen (3758096384 - mu)));
    [ eapply azero_frame; [exact AZU | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE; Z.div_mod_to_equations; lia |];
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |];
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  clear AZU AZF.
  box MU01.
  step.
  step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by (clear -NF NFA MU MUX N; lia).
  all: cycle 1.
  {
    zstep.
    snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
    box CT. box CH. box STATS. box STM.
    step.
    carry CT MUr WMr ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
    carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
    carry STATS MUr WMr ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    carry STM MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }
    unbox MU01.
    eapply evtF_cut.
    { eapply (gf_tail_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf - n) (fl2 := fl) (chunks0 := chunks0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL
       | |- Forall _ _ => exact FL31
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL; clear -KP N; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => intros kk Hkk; eapply rng_sub'; [exact RFA|]; clear -KP N NF MFA Hkk; lia
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KP N NF MFA RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KP N NF MFA RIE; lia
       end;
      atop_facts; clear -SPR CEIL LO KP N NF MFA SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & stn' & m3 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
    lazymatch type of MUr with munch _ ?m1 ?m2 =>
    assert (MU13 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                          (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z m1 m3)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
    end.
    pose proof (wmono_trans _ _ _ _ WMr WM3) as WM13. clear MUr WMr.
    xport REG MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport EXH MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STATS MU3 WM3 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STM MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport FJ MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N NF MFA Y TIC TB; lia).
    apply evtF_done. unfold gfa_tree, gfa_take. fold nf.
    replace (n <=? nf) with true by (symmetry; apply Z.leb_le; exact KP).
    replace (nf <? n) with false by (symmetry; apply Z.ltb_ge; exact KP).
    eapply KONT.
    unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
    split; [apply fp_le_refl|].
    exists mu, mfa, 0, sj, stm, stn'.
    replace (nf + 0) with nf by (clear; lia). replace (au + 0 * S) with au by (clear; lia).
    split; [left; reflexivity|]. split; [clear -MU MUX; lia|]. split; [exact MUM|].
    split; [left; split; [exact KP| reflexivity]|]. split; [clear; lia|]. split; [clear -MU; lia|].
    split; [left; reflexivity|]. split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|]. split; [exact KP|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; exact FL3|].
    split; [exists fj; exact FJ|].
    split; [symmetry; apply aclass_eta0|| (destruct (get_cls st c); reflexivity)|].
    split; [left; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MU13]]; unfold sub_fp; cbn [outside]; clear -N MFA NF; intros x Hx; lia. }
    split; [eapply wmono_trans; [exact WM01| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact MTX3|]. split; [exact REG|]. split; [exact EXH|]. split; [exact STN3|]. split; [exact STATS|]. split; [exact LSJ|]. split; [exact STM|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; replace (nf - n) with (nf - n) by reflexivity; exact CH3|].
    split. { eapply azero_frame; [exact AZU1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    split. { eapply azero_frame; [exact AZF1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    eapply m3_cells_frame; [exact MC1 | exact MU13 | exact WM13 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }

  step. step. step. zstep. step. step.
  step.
  apply evtF_done. unfold gfa_tree. fold nf.
  replace (n <=? nf) with false by (symmetry; apply Z.leb_gt; exact KP).
  unbox MU01. name_sp sp (-128).
  eapply populate_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (aregion _ _ + _)) _ => rewrite RBE; exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; eapply rng_sub'; [exact RFA|]; clear -NF MFA; lia
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N KP HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PR.
  unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in PR. cbv zeta in PR. fold S mu au nf mfa in PR. rewrite FAE, RBE in PR.
  destruct PR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & UD & MUB & MUM' & NCE & NC0 & FD & NEWB & NEWM & NEWMOD & AR & JR & ST2E
                  & MU2 & WM2 & MI2 & ST2 & REG2 & EXH2 & STATS2 & LSJ2 & STM2 & AZU2 & AZF2 & MC2).
  box UD. box FD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (GC2 : get_cls st2 c = mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count (get_cls st c))) by (rewrite ST2E; apply get_cls_put_cls_eq).
  assert (NCS : au + ncnt * S <= mu' /\ 0 <= ncnt * S).
  { split; [| clear -NC0 SZ; nia]. pose proof NCE as E. clear -E MUB MU NC0 SZ. subst ncnt. Z.div_mod_to_equations. nia. }
  destruct NCS as [NCS1 NCS2].
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + mu) + shlen (mu' - mu) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 TIC TB SHF3 SHF4; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 CHK0 CHK1 Y TIC TB SHF3 SHF4; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  clear ST MI REG EXH STATS STM FJ MC1 AZU1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC.
  pose proof (u32arr_app _ _ _ _ FL ltac:(rewrite LFL, Z2Nat.id by (clear -NF; lia); exact AR)) as FL2.
  assert (LFL2 : length (fl ++ fvals au S (Z.to_nat ncnt)) = Z.to_nat (nf + ncnt)) by (rewrite length_app, fvals_length, LFL; clear -NF NC0; lia).
  assert (FL231 : Forall (fun w : word => bv_unsigned w < 2^31) (fl ++ fvals au S (Z.to_nat ncnt))).
  { apply Forall_app. split; [exact FL31|]. apply fvals_small; [clear -MU; lia | clear -SZ; lia |]. rewrite Z2Nat.id by (clear -NC0; lia). clear -NCS1 MUB; lia. }
  replace (ret_pc (Z_to_bv 64 272572)) with (Z_to_bv 64 272572 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  step. step.
  step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear -NF NC0 N MFA NEWB; lia).
  {
    apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
    replace (nf + ncnt <? n) with true by (symmetry; apply Z.ltb_lt; exact KQ).
    rewrite aembed_aundef_. apply implF_ret_unr. }
  step. zstep.
  snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
  box CH. box STATS2. box STM2. box FL2. clear FL AR.
  step.
  carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS2 MUr WMr ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM2 MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry FL2 MUr WMr ltac:(rewrite LFL2; clear -SP1 SP2 HC RIE NF NC0 MFA NEWB; lia).
  step. step.
  eapply evtF_cut.
  { eapply (gf_tail_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf + ncnt - n) (fl2 := fl ++ fvals au S (Z.to_nat ncnt)) (chunks0 := chunks0);
    try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL2; clear -KQ N; f_equal; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => (
             intros kk Hkk; assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia); destruct M4 as [q Hq];
             with_box FD ltac:(destruct DX as [Enew|(LT & Enew & _ & GR1 & _)];
               [ eapply rng_sub'; [exact RFA|]; clear -Hkk Enew MFA NF NC0 NEWB; lia
               | destruct (Z_lt_le_dec (4 * kk + 3) mfa) as [LO4|HI4];
                 [ eapply rng_sub'; [exact RFA|]; clear -Hkk LO4 MFA NF NC0; lia
                 | eapply rng_sub'; [exact GR1|]; clear -Hkk HI4 MFA NF NC0 NEWB Hq; lia ] ]))
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE; lia
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- @eq word _ _ => f_equal; clear; lia
       end;
    try (atop_facts; clear -SPR CEIL LO KQ N NF NC0 MFA NEWB SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia). }
  cbv beta. intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & stn' & m4 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
  lazymatch type of MUr with munch _ ?ma ?mb =>
  assert (MU24 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                        (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z ma m4)
    by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  pose proof (wmono_trans _ _ _ _ WMr WM3) as WM24. clear MUr WMr.
  xport REG2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport EXH2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STM2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
  replace (nf + ncnt <? n) with false by (symmetry; apply Z.ltb_ge; exact KQ).
  eapply KONT.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
  split; [exact FPLE|].
  exists mu', mfa', ncnt, sj', stm', stn'.
  assert (SHU : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu) /\ shad (al_space_beg L + c * 4294967296 + mu') + shlen (3758096384 - mu') <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHU as (SHU1 & SHU2 & SHU3 & SHU4).
  split. { with_box UD ltac:(destruct DX as [(LE & Emu)|(LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact KP|]; split; [exact LT|]; split; [exact Emu|];
             split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MU24 | exact WM24 |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from] ];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MU MUB SHU1 SHF2 Y TIC TB SHF3 SHF4; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|].
  split; [right; split; [exact KP| exact NCE]|]. split; [exact NC0|]. split; [exact NCS1|].
  split. { with_box FD ltac:(destruct DX as [(LE & Emfa)|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NEWB NEWM SHF1 SHU4 Y TIC TB; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact KQ|].
  split; [exact FL3|].
  split. { eapply junk_frame; [exact JR | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NC0 NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|].
  split; [right; rewrite GC2; exact ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
           unfold sub_fp; cbn [outside]; clear -N MFA NF NC0 NEWB NEWM MUB KP KQ; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
  split; [exact MTX3|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN3|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [exact CH3|].
  split. { eapply azero_frame; [exact AZU2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUB RIE T0 T1 CHK0 CHK1 N SHU1 SHU2 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM RIE T0 T1 CHK0 CHK1 N SHU3 SHU4 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MU24 | exact WM24 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
  do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil.
Qed.
End CANSEC2.
End F_agetfrom.

Module F_agetfrom_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.TwinB. Import F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate_x.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

Ltac lrsc_stepA AMO :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply (evtF_step_acc segs RNG);
      [ reflexivity
      | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; amo_align AMO; rewrite ?Z.eqb_refl; exec_cbv; amo_align AMO; rewrite ?Z.eqb_refl;
        simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | solve_accs
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Notation GETFROM_STACK_X := 1472 (only parsing).

Section CANSECX. Context {rc : runConstT} {ov : annOV}.

Definition gfunlock_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v b : word) (F : bvmap 5 word) (fc : bv 32)
    (RI lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v b a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)].

Lemma gf_unlock_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v b : word)
    (rax t0 t1 t2 a0x a1x a2x a3x a4x a5x a6 a7 s2x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (RI lo : Z) (fr0 : list byte),
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 24 fr0; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 1152921504606846976)] ->
  amo_aligned AD (Z_to_bv 64 RI) = true ->
  0x10007fff8000 <= RI -> RI + 128 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 ->
  evtF bsegs RNG (gfunlock_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v b F fc RI lo m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 RI) b a0x a1x a2x a3x a4x a5x a6 a7
             s2x (Z_to_bv 64 2305843009213693952) s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x42798) fc None m (seg_rom bsegs)).
Proof.
  intros until fr0. intros ST CEIL LO MI FR MTX AMO RI0 RI1 RIMG RSTK RRI.
  unfold AIMG_HI in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  step.
  do 7 zstep. step. do 5 zstep.
  step.
  zstep. zstep. step. if_lit.
  zstep. step. if_lit.
  do 7 zstep. step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  lrsc_stepA AMO.
  step. if_lit.
  step. if_lit.
  step. if_lit.
  step.
  do 15 step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -128) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. unfold gfunlock_post.
  do 15 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  exact MTX.
Qed.

Definition gfa_tree_x {R} (RESV : list (Z * Z)) (st1 : astate) (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) : AM R :=
  if n <=? c_num_freed (get_cls st1 c) then gfa_take c n k KK st1
  else populate_free_array_g (exh_report ATOP RESV c) (exh_clear c) st1 c (n - c_num_freed (get_cls st1 c))
         (fun st2 ok => if ok then gfa_take c n k KK st2 else k st2 false).

Definition xfalse_ret (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (XS : Z) (st : astate) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ ((exh_mem c st = true /\ st2 = st) \/ (exh_mem c st = false /\ exists e2, st2 = set_emb e2 (exh_set c st)))
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m'
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 1)]
  /\ (exists d1 cap1,
        munch [(bv_unsigned sp - XS, bv_unsigned sp); (RI, RI + 8); (RI + 68, RI + 69); (AEMB, AEMB + 56);
               (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z m m'
        /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2 /\ (cap1 = 0 \/ d1 + cap1 <= ATOP))
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Definition getfrom_ret_x (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n CHK lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in

     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells bsegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'

  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr bsegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)

  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st \/ st2 = exh_clear c (put_cls c (get_cls st2 c) st))

  /\ munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)

  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st2 then 1 else 0))]
  /\ rw_cells bsegs m' (RI + 72) [C8 stn']
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2792) [C8 stm']
  /\ u32arr bsegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma getfrom_spec_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n CHK lo : Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GETFROM_STACK_X ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 CHK -> a4 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->

  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      xfalse_ret L RESV RNG sp GETFROM_STACK_X st c lo m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret_x L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (gfa_tree_x RESV st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC N MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG KF KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, getfrom_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl bsegs m) as WM.
  rewrite RBE in AZU. rewrite FAE in FL, FJ, AZF, RFA.
  iprefix.
  carve_frame 128%nat ST.

  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry EXH MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry STM MUp WMp ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry FL MUp WMp ltac:(rewrite LFL; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry FJ MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  step. step. step.
  step. step.
  do 9 zstep.
  do 4 zstep.
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.
  do 5 zstep.
  zstep. step. if_lit.
  zstep. zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).

  lrsc_stepA AMO.
  step. if_lit.
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS. box STM.
  lrsc_stepA AMO.
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM MUl WMl ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.

  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZU1 : azero m1 (shad (al_space_beg L + c * 4294967296 + mu)) (shlen (3758096384 - mu)));
    [ eapply azero_frame; [exact AZU | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE; Z.div_mod_to_equations; lia |];
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |];
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  clear AZU AZF.
  box MU01.
  step.
  step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by (clear -NF NFA MU MUX N; lia).
  all: cycle 1.
  {
    zstep.
    snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
    box CT. box CH. box STATS. box STM.
    step.
    carry CT MUr WMr ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
    carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
    carry STATS MUr WMr ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    carry STM MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }
    unbox MU01.
    eapply evtF_cut.
    { eapply (gf_tail_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf - n) (fl2 := fl) (chunks0 := chunks0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL
       | |- Forall _ _ => exact FL31
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL; clear -KP N; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => intros kk Hkk; eapply rng_sub'; [exact RFA|]; clear -KP N NF MFA Hkk; lia
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KP N NF MFA RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KP N NF MFA RIE; lia
       end;
      atop_facts; clear -SPR CEIL LO KP N NF MFA SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & stn' & m3 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
    lazymatch type of MUr with munch _ ?m1 ?m2 =>
    assert (MU13 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                          (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z m1 m3)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
    end.
    pose proof (wmono_trans _ _ _ _ WMr WM3) as WM13. clear MUr WMr.
    xport REG MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport EXH MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STATS MU3 WM3 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport STM MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
    xport FJ MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N NF MFA Y TIC TB; lia).
    apply evtF_done. unfold gfa_tree_x, gfa_take. fold nf.
    replace (n <=? nf) with true by (symmetry; apply Z.leb_le; exact KP).
    replace (nf <? n) with false by (symmetry; apply Z.ltb_ge; exact KP).
    eapply KONT.
    unfold getfrom_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
    split; [apply fp_le_refl|].
    exists mu, mfa, 0, sj, stm, stn'.
    replace (nf + 0) with nf by (clear; lia). replace (au + 0 * S) with au by (clear; lia).
    split; [left; reflexivity|]. split; [clear -MU MUX; lia|]. split; [exact MUM|].
    split; [left; split; [exact KP| reflexivity]|]. split; [clear; lia|]. split; [clear -MU; lia|].
    split; [left; reflexivity|]. split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|]. split; [exact KP|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; exact FL3|].
    split; [exists fj; exact FJ|].
    split; [symmetry; apply aclass_eta0|| (destruct (get_cls st c); reflexivity)|].
    split; [left; reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MU13]]; unfold sub_fp; cbn [outside]; clear -N MFA NF; intros x Hx; lia. }
    split; [eapply wmono_trans; [exact WM01| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact MTX3|]. split; [exact REG|]. split; [exact EXH|]. split; [exact STN3|]. split; [exact STATS|]. split; [exact LSJ|]. split; [exact STM|].
    split; [cbn [Z.to_nat fvals seq map rev]; rewrite app_nil_r; replace (nf - n) with (nf - n) by reflexivity; exact CH3|].
    split. { eapply azero_frame; [exact AZU1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUX RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    split. { eapply azero_frame; [exact AZF1 | exact MU13 | exact WM13 |]. intros _; cbn [disjoint_from].
             rewrite shad_div, shlen_div; unfold ASHOFF; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE T0 T1 CHK0 CHK1 N Y TIC TB; Z.div_mod_to_equations; lia. }
    eapply m3_cells_frame; [exact MC1 | exact MU13 | exact WM13 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }

  step. step. step. zstep. step. step.
  step.
  apply evtF_done. unfold gfa_tree_x. fold nf.
  replace (n <=? nf) with false by (symmetry; apply Z.leb_gt; exact KP).
  unbox MU01.

  assert (RIB : 6492160 <= aregion_info L c /\ aregion_info L c + 128 <= ATOP) by (rewrite RIE; clear -SP1 SP2 HC; lia).
  destruct RIB as [RILO RIHI]. pose proof atop_range as ATR.
  lazymatch type of MU01 with munch ?WW _ ?mp =>
    assert (WHI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) WW)
      by (apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst]; unfold AIMG_HI; clear -LO CEIL ATR RILO; lia);
    assert (RELROp : arelro mp) by (exact (arelro_frameD m mp _ RELRO MU01 WHI));
    assert (XCp : exh_cells mp) by (exact (exh_cells_frameD m mp _ XC MU01 WHI));
    assert (ECp : emb_cells st mp)
      by (apply (emb_cells_frameD st m mp _ EC MU01);
          [ cbn [disjoint_from]; unfold AEMB; clear -LO CEIL ATR RILO; lia
          | pose proof RIOLD as RIO; destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE0; rewrite ?EE0 in RIO; cbv beta iota in RIO;
            destruct (emb_cells_top st m d0 cap0 sz0 EC EE0) as [Z0|(CP0 & _ & TB0)]; [left; exact Z0| right];
            cbn [disjoint_from]; clear -LO CEIL TB0 CP0 RIO; lia ])
  end.
  name_sp sp (-128).
  eapply populate_spec_x with (lo := lo) (L := L) (RESV := RESV);
  try lazymatch goal with
       | |- exh_first_stmt => exact EXHW | |- aresv_ok _ _ => exact ROK | |- arelro _ => exact RELROp
       | |- exh_cells _ => exact XCp | |- emb_cells _ _ => exact ECp | |- pcov _ _ _ => exact RIRES | |- emb_rng _ _ => exact ERNG
       | |- bv_unsigned _ < 2 ^ 63 => rewrite Hsp; clear -SP63 SPR CEIL LO ATR; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (aregion _ _ + _)) _ => rewrite RBE; exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; eapply rng_sub'; [exact RFA|]; clear -NF MFA; lia
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N KP HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).

  1: {
    intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PRF.
    unfold populate_ret_false in PRF. cbv zeta in PRF.
    destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
    destruct PRF as (FPLE & STREL & EC2 & ERNG2 & XC2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TP1) & MI2 & ST2).
    unname_sp.
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RRI.
    cbv beta iota in RIOLD.
    lazymatch type of MU01 with munch _ _ ?mp =>
      assert (B0 : cap0 = 0 \/ (0 < cap0 /\ d0 + cap0 <= ATOP)) by (destruct (emb_cells_top st mp d0 cap0 sz0 ECp EE) as [Z0|(CP0 & _ & TB0)]; [left| right; split]; assumption) end.
    assert (B2 : cap2 = 0 \/ (0 < cap2 /\ d2 + cap2 <= ATOP)) by (destruct (emb_cells_top st2 m2 d2 cap2 sz2 EC2 EE2) as [Z2|(CP2 & _ & TB2)]; [left| right; split]; assumption).
    assert (CL : forall d cap, emb_prov RESV st d0 cap0 d cap -> cap <= 0 \/ aregion_info L c + 128 <= d \/ d + cap <= aregion_info L c).
    { intros d cap [(-> & ->)|AV]; [clear -RIOLD; lia|].
      destruct (Z_le_gt_dec cap 0) as [LE0|GT0]; [left; exact LE0| right].
      unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
      pose proof (pcov_clear _ _ _ _ _ RIRES AV ltac:(clear; lia) ltac:(clear -GT0; lia)) as C. clear -C. lia. }
    pose proof (CL d1 cap1 PV1) as CL1. pose proof (CL d2 cap2 PV2) as CL2.
    rewrite Hsp in MU2, ST2 || idtac.
    assert (FR2 : True) by exact I.
    eapply (cells_frame_focus _ _ m2) in FR; [| exact MU2 |
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; intros x Hx; cbn [outside]; unfold AEMB;
      repeat split; try exact I; clear -Hx SPR LO CEIL RIHI ATR B0 B2 TP1; lia].
    eapply (cells_frame_focus _ _ m2) in MTX; [| exact MU2 |
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros x Hx; cbn [outside]; unfold AEMB;
      repeat split; try exact I; clear -Hx SPR LO CEIL RILO RIHI ATR RIOLD CL1 CL2; lia].
    replace (ret_pc (Z_to_bv 64 272572)) with (Z_to_bv 64 272572 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    iprefix.
    step. if_lit.
    step. step. step.
    eapply evtF_cut.
    { eapply (gf_unlock_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0)) with (lo := lo) (RI := aregion_info L c);
      try lazymatch goal with
         | |- stk _ _ _ _ => exact ST2
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
         | |- amo_aligned _ _ = true => exact AMO
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (aregion_info _ _) _ => exact RRI
         end;
      try (atop_facts; clear -SPR CEIL LO SP1 SP2 HC RIE RILO RIHI; lia). }
    cbv beta. intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m4 & -> & MU3 & WM3 & MI3 & ST3 & MTX3).
    apply evtF_done. cbv beta iota. eapply KF.
    unfold xfalse_ret. cbv zeta. rewrite EE, EE2.
    assert (WHI3 : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z)
      by (apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst]; unfold AIMG_HI; clear -LO CEIL ATR RILO; lia).
    split; [exact FPLE|]. split; [exact STREL|].
    split. { apply (emb_cells_frameD st2 m2 m4 _ EC2 MU3); [cbn [disjoint_from]; unfold AEMB; clear -LO CEIL ATR RILO; lia|].
             rewrite EE2. destruct B2 as [Z2|[CP2 TB2]]; [left; exact Z2| right]. cbn [disjoint_from]. clear -LO CEIL TB2 CP2 CL2. lia. }
    split; [exact ERNG2|]. split; [exact (exh_cells_frameD m2 m4 _ XC2 MU3 WHI3)|].
    split; [exact MTX3|].
    split. { eapply AFrameD.TwinB.cells_frameD; [exact FLG2| exact MU3|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. clear -LO CEIL RIHI. lia. }
    split. { exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TP1]]].
             eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
               unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
    split; [exact MI3| exact ST3]. }

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PR.
  unfold populate_ret_g, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in PR. cbv zeta in PR. fold S mu au nf mfa in PR. rewrite FAE, RBE in PR.
  destruct PR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & UD & MUB & MUM' & NCE & NC0 & FD & NEWB & NEWM & NEWMOD & AR & JR & ST2E
                  & MU2 & WM2 & MI2 & ST2 & REG2 & EXH2 & STATS2 & LSJ2 & STM2 & AZU2 & AZF2 & MC2).
  box UD. box FD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (GC2 : get_cls st2 c = mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count (get_cls st c))) by (rewrite ST2E, get_cls_exh_clear; apply get_cls_put_cls_eq).
  assert (NCS : au + ncnt * S <= mu' /\ 0 <= ncnt * S).
  { split; [| clear -NC0 SZ; nia]. pose proof NCE as E. clear -E MUB MU NC0 SZ. subst ncnt. Z.div_mod_to_equations. nia. }
  destruct NCS as [NCS1 NCS2].
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + mu) + shlen (mu' - mu) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 TIC TB SHF3 SHF4; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 CHK0 CHK1 Y TIC TB SHF3 SHF4; lia).
  xport FL MU2 WM2 ltac:(rewrite LFL; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 Y TIC TB SHF3 SHF4; lia).
  clear ST MI REG EXH STATS STM FJ MC1 AZU1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC.
  pose proof (u32arr_app _ _ _ _ FL ltac:(rewrite LFL, Z2Nat.id by (clear -NF; lia); exact AR)) as FL2.
  assert (LFL2 : length (fl ++ fvals au S (Z.to_nat ncnt)) = Z.to_nat (nf + ncnt)) by (rewrite length_app, fvals_length, LFL; clear -NF NC0; lia).
  assert (FL231 : Forall (fun w : word => bv_unsigned w < 2^31) (fl ++ fvals au S (Z.to_nat ncnt))).
  { apply Forall_app. split; [exact FL31|]. apply fvals_small; [clear -MU; lia | clear -SZ; lia |]. rewrite Z2Nat.id by (clear -NC0; lia). clear -NCS1 MUB; lia. }
  replace (ret_pc (Z_to_bv 64 272572)) with (Z_to_bv 64 272572 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  step. step.
  step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear -NF NC0 N MFA NEWB; lia).
  {
    apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
    replace (nf + ncnt <? n) with true by (symmetry; apply Z.ltb_lt; exact KQ).
    rewrite aembed_aundef_. apply implF_ret_unr. }
  step. zstep.
  snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
  box CH. box STATS2. box STM2. box FL2. clear FL AR.
  step.
  carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS2 MUr WMr ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM2 MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry FL2 MUr WMr ltac:(rewrite LFL2; clear -SP1 SP2 HC RIE NF NC0 MFA NEWB; lia).
  step. step.
  eapply evtF_cut.
  { eapply (gf_tail_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (base := nf + ncnt - n) (fl2 := fl ++ fvals au S (Z.to_nat ncnt)) (chunks0 := chunks0);
    try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- u32arr _ _ CHK _ => exact CH
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- amo_aligned _ _ = true => exact AMO
       | |- length _ = _ => first [exact LCH | rewrite LFL2; clear -KQ N; f_equal; lia]
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ CHK _ => eapply rng_sub'; [exact RT|]; clear -CHK0 CHK1 N; lia
       | |- forall _, _ => (
             intros kk Hkk; assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia); destruct M4 as [q Hq];
             with_box FD ltac:(destruct DX as [Enew|(LT & Enew & _ & GR1 & _)];
               [ eapply rng_sub'; [exact RFA|]; clear -Hkk Enew MFA NF NC0 NEWB; lia
               | destruct (Z_lt_le_dec (4 * kk + 3) mfa) as [LO4|HI4];
                 [ eapply rng_sub'; [exact RFA|]; clear -Hkk LO4 MFA NF NC0; lia
                 | eapply rng_sub'; [exact GR1|]; clear -Hkk HI4 MFA NF NC0 NEWB Hq; lia ] ]))
       | |- _ <= CHK \/ _ => ub TSP; clear -Y T0 T1 SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE CHK0 CHK1 TIC TB; destruct Y as [Y|Y]; [right; lia| left; lia]
       | |- _ \/ _ => right; clear -SP1 SP2 HC KQ N NF NC0 MFA NEWB RIE; lia
       | |- u32arr _ _ _ _ => exact FL2
       | |- Forall _ _ => exact FL231
       | |- @eq word _ _ => f_equal; clear; lia
       end;
    try (atop_facts; clear -SPR CEIL LO KQ N NF NC0 MFA NEWB SP1 SP2 HC RIE T0 T1 CHK0 CHK1 TIC TB; lia). }
  cbv beta. intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & stn' & m4 & -> & MU3 & WM3 & MI3 & ST3 & MTX3 & STN3 & FL3 & CH3).
  lazymatch type of MUr with munch _ ?ma ?mb =>
  assert (MU24 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8); (aregion_info L c + 16, aregion_info L c + 56);
                        (aregion_info L c + 72, aregion_info L c + 80); (CHK, CHK + 4 * n)]%Z ma m4)
    by (eapply munch_trans; [eapply munch_weaken; [| exact MUr] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  pose proof (wmono_trans _ _ _ _ WMr WM3) as WM24. clear MUr WMr.
  xport REG2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport EXH2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  xport STM2 MU3 WM3 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
  replace (nf + ncnt <? n) with false by (symmetry; apply Z.ltb_ge; exact KQ).
  eapply KONT.
  unfold getfrom_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RBE.
  split; [exact FPLE|].
  exists mu', mfa', ncnt, sj', stm', stn'.
  assert (SHU : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu) /\ shad (al_space_beg L + c * 4294967296 + mu') + shlen (3758096384 - mu') <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHU as (SHU1 & SHU2 & SHU3 & SHU4).
  split. { with_box UD ltac:(destruct DX as [(LE & Emu)|(LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact KP|]; split; [exact LT|]; split; [exact Emu|];
             split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MU24 | exact WM24 |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from] ];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MU MUB SHU1 SHF2 Y TIC TB SHF3 SHF4; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|].
  split; [right; split; [exact KP| exact NCE]|]. split; [exact NC0|]. split; [exact NCS1|].
  split. { with_box FD ltac:(destruct DX as [(LE & Emfa)|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MU24 | exact WM24 |]; intros _; cbn [disjoint_from];
             ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NEWB NEWM SHF1 SHU4 Y TIC TB; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact KQ|].
  split; [exact FL3|].
  split. { eapply junk_frame; [exact JR | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N MFA NF NC0 NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|].
  split; [right; rewrite GC2; exact ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
           unfold sub_fp; cbn [outside]; clear -N MFA NF NC0 NEWB NEWM MUB KP KQ; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2 | exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
  split; [exact MTX3|]. split; [exact REG2|]. split; [replace (exh_mem c st2) with false by (rewrite ST2E; symmetry; apply exh_mem_clear_same); exact EXH2|]. split; [exact STN3|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [exact CH3|].
  split. { eapply azero_frame; [exact AZU2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MU MUB RIE T0 T1 CHK0 CHK1 N SHU1 SHU2 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
           ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM RIE T0 T1 CHK0 CHK1 N SHU3 SHU4 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MU24 | exact WM24 |]. ub SCX; ub TCX; unfold AIMG_HI, AIMG_LO.
  do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil.
Qed.
End CANSECX.
End F_agetfrom_x.

Module F_areturn.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition rta_entry : Z := 0x402a4.
End CANSEC1.
Notation RTA_STACK := 576 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma rta_copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u32arr bsegs m SRC src -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  u32arr bsegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv bsegs m ->
  0 <= SRC -> SRC + 4 * n < 2^47 -> 0 <= DST -> DST + 4 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 4 * n <= DST \/ DST + 4 * Z.of_nat (length ws0) <= SRC) ->
  (forall k, 0 <= k < n -> rng RNG (SRC + 4 * k) 4) -> (forall k, 0 <= k < n -> rng RNG (DST + 4 * k) 4) ->
  evtF bsegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1' a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * n)) s7 s8 (Z_to_bv 64 (DST + 4 * n)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40434) fc None m' (seg_rom bsegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ u32arr bsegs m' SRC src /\ u32arr bsegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * i)) s7 s8 (Z_to_bv 64 (DST + 4 * i)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40420) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read bsegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1. pose proof (RDS i ltac:(lia)) as RD1.
  step. clear RD RS1.
  rewrite (sx32_small w W31).
  zstep.
  setreg 22 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u32arr_store_ok bsegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write bsegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 4 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  clear DSTA. store_done. try clear SOK. clear RD1.
  zstep.
  setreg 25 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.
  -
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a1' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a1', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  -
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

Lemma junk_of_cells' : forall m A cs n, rw_cells bsegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

Lemma set_mfa_eq : forall v r,
  cls_set_mapped_free_array v r = mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) v (c_count r).
Proof. intros v []; reflexivity. Qed.

Definition rta_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n SRC lo : Z) (src : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let nf2 := nf + n in
  fp_le RNG RNG' /\
  exists mfa' sj',
     (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ get_cls st2 c = mkAClass (c_mapped_user r) (c_allocated_user r) nf mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)
  /\ munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp);
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf2); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ u32arr bsegs m' (FA + 4 * nf) src
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma rta_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n SRC lo : Z) (sj src : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RTA_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c -> a4 = Z_to_bv 64 SRC -> a5 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  u32arr bsegs m SRC src -> length src = Z.to_nat n -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until src. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CH LCH CH31 FJ AZF SBE HC N NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, rta_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - RTA_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl bsegs m) as WM.
  rewrite FAE in FJ, AZF, RFA.

  destruct (junk_split m (aregion_info L c + 72) 8 48 J72 ltac:(lia) ltac:(lia)) as [J72a J80].
  destruct (junk_split m (aregion_info L c + 72 + 8) 8 40 J80 ltac:(lia) ltac:(lia)) as [J80a J88].
  destruct (junk_split m (aregion_info L c + 72 + 8 + 8) 8 32 J88 ltac:(lia) ltac:(lia)) as [J88a J96].
  replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) in J80a by lia.
  replace (aregion_info L c + 72 + 8 + 8) with (aregion_info L c + 88) in J88a by lia.
  replace (aregion_info L c + 72 + 8 + 8 + 8) with (aregion_info L c + 96) in J96 by lia.
  destruct (c8_of_junk m _ J72a) as [stn STN]. destruct (c8_of_junk m _ J80a) as [w80 W80]. destruct (c8_of_junk m _ J88a) as [w88 W88].
  destruct J96 as [j96 J96].
  clear J72 J72a J80 J80a J88 J88a.
  iprefix.
  carve_frame 128%nat ST.
  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box STN. box W80. box W88. box J96. box STATS. box CH. box FJ. box AZF.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  do 7 step.
  step. step.
  do 9 zstep.
  zstep. zstep. zstep. zstep.
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 25 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 12 (Z_to_bv 64 (aregion L c)) ltac:(rewrite RBE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.
  zstep.
  step.
  do 4 zstep.
  zstep. step. if_lit.
  zstep. zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).

  lrsc_stepA AMO.
  step. if_lit.
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS.
  lrsc_stepA AMO.
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.

  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  unbox FJ. eapply junk_frame in FJ; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; clear -SPR CEIL LO SP1 SP2 HC RIE NF MFA; lia].
  unbox AZF.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |]
  end.
  clear AZF.
  box MU01.
  step.
  zstep.
  step. step. step.
  step.
  apply evtF_done.
  name_sp sp (-128).
  eapply ensure_spec with (lo := lo) (L := L) (sj := sj);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold mu au nf mfa; first [assumption | clear -NF MFA MFAM NFN N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TIC TB CXI; lia]).

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
  unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold nf mfa in ER. rewrite FAE in ER.
  destruct ER as (FPLE & new & sj' & UD & NEWB & NEWGE & NEWM & MU2 & WM2 & MI2 & ST2 & REG2 & STATS2 & LSJ2 & AZF2 & MC2).
  box UD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  assert (SHFL : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).
  { rewrite !shad_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF. Z.div_mod_to_equations. lia. }
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF TIC TB SHFL; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W80 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W88 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport J96 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF CHK0 CHK1 N Y TIC TB SHFL; lia).
  eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; cbn [disjoint_from]; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia].
  clear ST MI REG STATS MC1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC MC.

  assert (JD : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (new - 4 * nf)).
  { ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & ZCB & _)].
    - rewrite E. exact FJ.
    - replace (new - 4 * nf) with ((mfa - 4 * nf) + (new - mfa)) by (clear; lia).
      apply junk_merge; [exact FJ | | clear -MFA; lia | clear -NEWGE; lia].
      replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + (mfa - 4 * nf)) with (al_space_beg L + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
      eapply junk_of_cb. exact ZCB. }
  clear FJ.
  destruct (junk_split m2 _ (4 * n) (new - 4 * nf - 4 * n) ltac:(eapply junk_at_eq; [exact JD| reflexivity | clear; lia]) ltac:(clear -N; lia) ltac:(clear -NEWB; lia)) as [JD4 JR].
  destruct (u32arr_of_junk m2 _ n JD4 ltac:(clear -N; lia)) as (ws0 & U0 & L0). clear JD JD4.
  set (DST := al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) in *.
  replace (ret_pc (Z_to_bv 64 263176)) with (Z_to_bv 64 263176 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }
  zstep. zstep. zstep. zstep.
  setreg 25 (Z_to_bv 64 (DST + 4 * 0)) ltac:(subst DST; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 10 (Z_to_bv 64 (SRC + 4 * n)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 22 (Z_to_bv 64 (SRC + 4 * 0)) ltac:(f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (rta_copy_loop_spec RNG' _ 0 n SRC DST src ws0); try reflexivity.
    - clear -N; lia.
    - exact LCH.
    - rewrite L0. clear -N; lia.
    - exact CH.
    - exact CH31.
    - cbn [Z.to_nat firstn skipn app]. exact U0.
    - exact MI2.
    - clear -CHK0 T0 TIC TB; lia.
    - clear -CHK1 T1 N TIC TB; lia.
    - subst DST. clear -SP1 HC NF; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). clear -SP2 HC NF N NEWB MFA; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). ub TSP. clear -Y CHK0 CHK1 T0 T1 SP1 SP2 HC NF N NEWB MFA TIC TB. destruct Y as [Y|Y]; [left; lia| right; lia].
    - intros kk Hkk. eapply rng_sub'; [exact RT|]. clear -CHK0 CHK1 Hkk N; lia.
    - intros kk Hkk. subst DST. destruct (Z_lt_le_dec (4 * nf + 4 * kk) mfa) as [LT|GE].
      + eapply rng_sub'; [exact RFA|]. assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia).
        destruct M4 as [q Hq]. clear -LT Hkk NF Hq. lia.
      + ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & _ & _ & R1 & _)].
        * exfalso. clear -E GE Hkk NEWB. lia.
        * eapply rng_sub'; [exact R1|]. clear -GE Hkk NEWB. lia. }
  cbv beta. intros ms' (a1x & m3 & -> & MU3 & WM3 & MI3 & SR3 & DS3).
  xport FR MU3 WM3 ltac:(subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  xport MTX MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STN MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W80 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W88 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport J96 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport REG2 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; subst DST; ub TSP; clear -SP1 SP2 HC T0 T1 NF N NEWB Y TIC TB; lia).
  eapply junk_frame in JR; [| exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; subst DST; clear -NF N; lia].
  pose proof (stk_transport_disjoint bsegs _ m2 m3 _ _ ST2 MU3 WM3 ltac:(cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia)) as ST3.
  assert (AZF3 : azero m3 (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new))).
  { eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 |]. intros _; cbn [disjoint_from].
    rewrite shad_div, shlen_div; unfold ASHOFF; subst DST; clear -SP1 SP2 HC NF N NEWB; Z.div_mod_to_equations; lia. }
  assert (MC3 : m3_cells L m3).
  { eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. ub SCX; unfold AIMG_HI, AIMG_LO.
    apply Forall_cons; [cbn [fst snd]; subst DST; clear -CX0 CX1 SP1 SP2 HC NF N NEWB Y CXI; lia |]. apply Forall_nil. }
  clear ST2 MI2 AZF2 MC2 U0. box MU3. box MU2.

  step.
  snapshot [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88)]%Z MUs WMs.
  box SR3. box DS3. box STATS2. clear CH.
  step.
  zstep.
  step.
  carry SR3 MUs WMs ltac:(rewrite LCH; ub TSP; clear -SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUs WMs ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUs WMs ltac:(rewrite LSJ2; ub TSP; clear -SP1 SP2 HC RIE T0 T1 Y TIC TB; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MC4 : m3_cells L mm) ; [eapply m3_cells_frame; [exact MC3 | exact MUs | exact WMs |]; ub SCX; unfold AIMG_HI, AIMG_LO;
    do 2 (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |] end.
  eapply junk_frame in JR; [| exact MUs | exact WMs | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia].
  clear MC3. box MUs.

  step. step. step. step.
  step.
  box SR3. box DS3. box STATS2. box MTX. box STN. box W88. box J96. box REG2. box W80.
  snapshot [(bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z MUm WMm.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of REG2 with boxed (rw_cells _ _ _ [C8 _; C8 _; C8 (Z_to_bv 64 ?auv); C8 _; C8 (Z_to_bv 64 ?muv); C8 _]) =>
    lazymatch type of W80 with boxed (rw_cells _ _ _ [C8 ?w80v]) =>
      call_sp (maybe_release_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm L c lo (nf + n) new auv muv w80v w88);
      [ exact ST3 | atop_facts; exact CEIL | clear -LO; lia | assumption | reflexivity | reflexivity | reflexivity
      | exact MC4 | unboxed REG2 | unboxed W80 | unboxed W88 | unfold K_NUM_CLASSES; exact HC | exact SP1 | unfold K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; exact SP2
      | ]
    end end end.
  rename POST into ST5.
  carry SR3 MUm WMm ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry DS3 MUm WMm ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  carry STATS2 MUm WMm ltac:(rewrite LSJ2; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry MTX MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG2 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  eapply junk_frame in JR; [| exact MUm | exact WMm | intros _; cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MC5 : m3_cells L mm); [eapply m3_cells_frame; [exact MC4 | exact MUm | exact WMm |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI; lia |]; apply Forall_nil |];
    assert (MU35 : munch [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                          (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z m3 mm);
    [ eapply munch_trans; [eapply munch_weaken; [| unboxed MUs] | eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |];
    pose proof WMs as WM35;
    assert (AZF5 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF3 | exact MU35 | exact WM35 |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |]
  end.
  clear MC4 AZF3.

  step.
  do 7 zstep. step. do 5 zstep.
  step.
  zstep. zstep. step. if_lit.
  zstep. step. if_lit.
  do 7 zstep. step. if_lit.
  box SR3. box DS3. box STATS2. box MUm. box MU35.
  snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUu WMu.
  lrsc_stepA AMO.
  step. if_lit.
  lrsc_stepA AMO.
  carry SR3 MUu WMu ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUu WMu ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUu WMu ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.
  step. if_lit.
  step. if_lit.
  do 15 step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -128) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MUx4 : munch [(aregion_info L c, aregion_info L c + 8)]%Z x14 mm) by (eapply munch_weaken; [| exact MUu]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia);
    eapply junk_frame in JR; [| exact MUx4 | exact WMu | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia];
    assert (AZF6 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF5 | exact MUx4 | exact WMu |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |];
    assert (MC6 : m3_cells L mm); [eapply m3_cells_frame; [exact MC5 | exact MUx4 | exact WMu |]; unfold AIMG_HI, AIMG_LO; ub SCX;
      apply Forall_cons; [cbn [fst snd]; clear -SP1 SP2 HC RIE CX0 CX1 Y CXI; lia |]; apply Forall_nil |]
  end.
  clear MC5 AZF5 MUu.
  apply evtF_done. eapply KONT.
  unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mu au nf mfa. rewrite FAE.
  split; [exact FPLE|].
  exists new, sj'.

  lazymatch goal with |- context [munch ?W m ?mm] =>
    assert (MUT : munch W m mm);
    [ ub MU01; ub MU3; ub MU35; ub MU2; subst DST;
      eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y2] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y1] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |]
  end.
  assert (WMT : wmono bsegs m _) by (eapply wmono_trans; [exact WM01 | eapply wmono_trans; [exact WM2 | exact WM3]]).
  split.
  { ub UD. destruct Y as [(_ & E & _ & _)|(LT & E & _ & _ & FILL & R1 & R2 & BW)]; [left; exact E| right].
    split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
    ub MU3; ub MU35; subst DST.
    eapply (fill_frame [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * n);
                        (aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                        (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128); (aregion_info L c, aregion_info L c + 8)]%Z);
      [exact FILL | | exact WM3 |].
    - eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia.
    - intros _. cbn [disjoint_from]. rewrite shad_div, shlen_div; unfold ASHOFF. clear -SPR CEIL LO SP1 SP2 HC NF N NEWB NEWGE MFA RIE. Z.div_mod_to_equations; lia. }
  split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
  assert (GC2 : get_cls st2 c = mkAClass mu au nf new (c_count (get_cls st c))).
  { ub UD. destruct Y as [(_ & E & -> & _)|(_ & _ & -> & _)].
    - rewrite E. subst mu au nf mfa. symmetry. apply aclass_eta0.
    - rewrite get_cls_put_cls_eq. subst mu au nf mfa. apply set_mfa_eq. }
  split; [exact GC2|].
  split. { ub UD. destruct Y as [(_ & _ & -> & _)|(_ & _ & E & _)]; [left; reflexivity| right]. rewrite GC2. rewrite E at 1. f_equal; subst mu au nf mfa; apply set_mfa_eq. }
  split; [exact MUT|]. split; [exact WMT|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact REG2|].
  split. { replace 56 with (8 + (8 + (8 + 32))) by reflexivity.
           apply junk_merge; [eapply junk_of_cells'; [exact STN| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W80| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 80 + 8) with (aregion_info L c + 88) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W88| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 88 + 8) with (aregion_info L c + 96) by (clear; lia). exists j96. exact J96. }
  split; [exact STATS2|]. split; [exact LSJ2|].
  split; [exact (proj1 (u32arr_app_inv _ _ _ _ DS3))|].
  split; [eapply junk_at_eq; [exact JR | subst DST; clear; lia | clear; lia]|].
  split; [exact AZF6| exact MC6].
Qed.
End CANSEC2.
End F_areturn.
End TwinB.
