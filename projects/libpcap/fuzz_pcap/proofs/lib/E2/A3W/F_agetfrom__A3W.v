(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_agetfrom.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac split_for_access_post H ::= split_junk_name H.
(* [comment removed for export] *)
Local Ltac slm_footprint_with segs m m' Heq a bs n Hn Ha Hl ::= slm_footprint_with_d0 segs m m' Heq a bs n Hn Ha Hl.
Local Ltac footprint_after_store_with segs m a bs n Hn Ha Hl ::= footprint_after_store_with_d0 segs m a bs n Hn Ha Hl.

Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma sx32_small : forall w : word, bv_unsigned w < 2^31 -> sx32 w = w.
Proof.
  intros w Hw. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  rewrite <- (Z_to_bv_bv_unsigned w). rewrite sx32_lit by lia. reflexivity.
Qed.

#[using="Type"] Lemma aclass_eta0 : forall r, mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) (c_count r) = r.
Proof. intros []; reflexivity. Qed.

#[using="Type"] Lemma fvals_small : forall au S k, 0 <= au -> 0 <= S -> au + Z.of_nat k * S <= 2^32 ->
  Forall (fun w : word => bv_unsigned w < 2^31) (fvals au S k).
Proof.
  intros au S k AU SZ B. unfold fvals. apply Forall_rev. apply Forall_map. apply Forall_forall. intros j Hj.
  apply in_seq in Hj. rewrite Z.shiftr_div_pow2 by lia.
  assert (J : 0 <= Z.of_nat j * S <= Z.of_nat k * S) by nia.
  rewrite unsigned_lit; [| change (2^4) with 16; Z.div_mod_to_equations; lia]. change (2^4) with 16. Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma u32arr_app : forall m A ws1 ws2,
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

#[using="Type"] Lemma u32arr_skipn : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
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

#[using="Type"] Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition getfrom_entry := 0x38bd8.
End CANSEC1.
Notation GETFROM_STACK := 640 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
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
                    s2 s3 (Z_to_bv 64 (SRC + 4 * n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x38d60) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2 (Z_to_bv 64 (DST + 4 * i)) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (SRC + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x38d4c) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1.
  step. clear RD RS1.                                    (* [comment removed for export] *)
  rewrite (sx32_small w W31).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
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
  zstep. zstep.                                          (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a2' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a2', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Definition gf_tail_spec__stmt : Prop := forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word)
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
  0x10007fff8000 <= FA -> FA + 4 * (base + n) <= ATOP -> 4096 <= CHK -> CHK + 64 <= ATOP -> (FA + 4 * (base + n) <= CHK \/ CHK + 64 <= FA) ->      (* [comment removed for export] *)
  0x10007fff8000 <= RI -> RI + 128 <= ATOP -> (RI + 128 <= CHK \/ CHK + 64 <= RI) -> (RI + 128 <= FA \/ FA + 4 * (base + n) <= RI) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> (forall k, 0 <= k < base + n -> rng RNG (FA + 4 * k) 4) -> rng RNG CHK 64 ->
  evtF asegs RNG (gftail_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc RI FA CHK n base lo fl2 chunks0 m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x a0x a1x a2x (Z_to_bv 64 CHK) (Z_to_bv 64 n) (Z_to_bv 64 base) a6 a7
             s2x (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 FA) s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x38d3c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 0).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 4).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 5).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 6).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 7).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 8).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 9).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 10).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 11).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 12).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 13).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 14).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 15).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 16).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 17).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 18).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 19).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 20).
Variable s1x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 21).
Variable a0x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 22).
Variable a1x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 23).
Variable a2x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 24).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 25).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 26).
Variable s2x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 27).
Variable s5x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 28).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 29).
Variable s7x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 30).
Variable s8x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 31).
Variable s9x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 32).
Variable s10x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 33).
Variable s11x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 34).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 35).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 36).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 37).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 38).
Variable F : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 39).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 40).
Variable m : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 41).
Variable RI : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 42).
Variable FA : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 43).
Variable CHK : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 44).
Variable n : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 45).
Variable base : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 46).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 47).
Variable fl2 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 48).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 49).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 50).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 51).
#[using="Type"] Lemma gf_tail_spec__body : ltac:(let T := type of (fun (h : gf_tail_spec__stmt) => h RNG rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v rax t0 t1 t2 s1x a0x a1x a2x a6 a7 s2x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 F fc m RI FA CHK n base lo fl2 chunks0 stn fr0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (rav, (sp, (gp, (tp, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, (s11v, (rax, (t0, (t1, (t2, (s1x, (a0x, (a1x, (a2x, (a6, (a7, (s2x, (s5x, (s6x, (s7x, (s8x, (s9x, (s10x, (s11x, (t3, (t4, (t5, (t6, (F, (fc, (m, (RI, (FA, (CHK, (n, (base, (lo, (fl2, (chunks0, (stn, fr0)))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI FR MTX STN FL LFL FL31 CH LCH AMO B0 N FA0 FA1 CH0 CH1 DJ RI0 RI1 DJ2 DJ3 RIMG RTLS RSTK RRI RFA RCH.
  unfold AIMG_HI in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  snapshot [(RI, RI + 8); (RI + 72, RI + 80)]%Z MUb WMb.
  box CH2. box FL. clear SR2.
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 7 zstep. step. do 5 zstep.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  do 7 zstep. step. if_lit.                                    (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 15 step.                                                  (* [comment removed for export] *)
  carry CH2 MUb WMb ltac:(rewrite length_app, !length_skipn, LFL, LCH; clear -DJ2 N B0; lia).
  carry FL MUb WMb ltac:(rewrite LFL; clear -DJ3 N B0; lia).
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. unfold gftail_post.
  do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MUF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact STN|]. split; [exact FL|].
  exact CH2.
Qed.
End Zd1.
#[using="Type"] Lemma gf_tail_spec : ltac:(let t := eval cbv delta [gf_tail_spec__stmt] in gf_tail_spec__stmt in exact t).
Proof. exact gf_tail_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_take {R} (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) (st2 : astate) : AM R :=
  if c_num_freed (get_cls st2 c) <? n then aundef_ (UCheck 229) (k st2 false) else KK st2.

Definition gfa_tree {R} (st1 : astate) (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) : AM R :=
  if n <=? c_num_freed (get_cls st1 c) then gfa_take c n k KK st1
  else populate_free_array st1 c (n - c_num_freed (get_cls st1 c)) (fun st2 ok => if ok then gfa_take c n k KK st2 else k st2 false).

#[using="Type"] Lemma cache_refill_tree_gfa : forall {R} st c (k : astate -> bool -> AM R),
  cache_refill_tree st c k =
  (let st1 := init_cache st in let n := max_count st1 c / 2 in
   gfa_tree st1 c n k (fun st2 => k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true)).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition getfrom_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n CHK lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (* [comment removed for export] *)
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
     (* [comment removed for export] *)
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
     (* [comment removed for export] *)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)
     (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
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

Definition getfrom_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (gfa_tree st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 2).
Variable KK : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 38).
Variable L : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 39).
Variable st : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 40).
Variable c : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 41).
Variable n : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 42).
Variable CHK : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 44).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 45).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 46).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 47).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 48).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 49).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 50).
Let S := size_of_class c.
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
#[using="S mu au nf mfa"] Lemma getfrom_spec__body : ltac:(let T := type of (fun (h : getfrom_spec__stmt) => h RNG R k KK Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c n CHK lo sj fl chunks0 stm stn fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (KK, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (n, (CHK, (lo, (sj, (fl, (chunks0, (stm, (stn, fj))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC N MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP CHK0 CHK1 RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros PC RC TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, getfrom_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  chg (size_of_class c) S.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite RBE in AZU. rewrite FAE in FL, FJ, AZF, RFA.
  iprefix.
  carve_frame 128%nat ST.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.                                                  (* [comment removed for export] *)
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
  step. step. step.                                            (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 9 zstep.                                                  (* [comment removed for export] *)
  do 4 zstep.                                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.                                                        (* [comment removed for export] *)
  do 5 zstep.                                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS. box STM.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM MUl WMl ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  step.                                                        (* [comment removed for export] *)
  step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by (clear -NF NFA MU MUX N; lia).   (* [comment removed for export] *)
  all: cycle 1.
  { (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
    box CT. box CH. box STATS. box STM.
    step.                                                      (* [comment removed for export] *)
    carry CT MUr WMr ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
    carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
    carry STATS MUr WMr ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    carry STM MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }   (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
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
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. zstep. step. step.                         (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done. unfold gfa_tree. fold nf.
  replace (n <=? nf) with false by (symmetry; apply Z.leb_gt; exact KP).
  unbox MU01. name_sp sp (-128).
  eapply populate_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; eapply rng_sub'; [exact RFA|]; clear -NF MFA; lia
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N KP HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PR.
  unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in PR. cbv zeta in PR. fold S mu au nf mfa in PR. rewrite FAE, RBE in PR.
  (nd_pre PR 30%nat; intros FPLE mu' mfa' ncnt sj' stm' UD MUB MUM' NCE NC0 FD NEWB NEWM NEWMOD AR JR ST2E MU2 WM2 MI2 ST2 REG2 EXH2 STATS2 LSJ2 STM2 AZU2 AZF2 MC2; nd_post).
  box UD. box FD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (GC2 : get_cls st2 c = mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count (get_cls st c))) by (rewrite ST2E; apply get_cls_put_cls_eq).
  assert (NCS : au + ncnt * S <= mu' /\ 0 <= ncnt * S).
  { split; [| clear -NC0 SZ; nia]. pose proof NCE as E. clear -E MUB MU NC0 SZ. subst ncnt. Z.div_mod_to_equations. nia. }
  destruct NCS as [NCS1 NCS2].
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + mu) + shlen (mu' - mu) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)).   (* [comment removed for export] *)
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 4%nat; intros SHF1 SHF2 SHF3 SHF4; nd_post).
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
  replace (ret_pc (Z_to_bv 64 233108)) with (Z_to_bv 64 233108 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear -NF NC0 N MFA NEWB; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
    replace (nf + ncnt <? n) with true by (symmetry; apply Z.ltb_lt; exact KQ).
    rewrite aembed_aundef_. apply implF_ret_unr. }
  step. zstep.                                                 (* [comment removed for export] *)
  snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
  box CH. box STATS2. box STM2. box FL2. clear FL AR.
  step.                                                        (* [comment removed for export] *)
  carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS2 MUr WMr ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM2 MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry FL2 MUr WMr ltac:(rewrite LFL2; clear -SP1 SP2 HC RIE NF NC0 MFA NEWB; lia).
  step. step.                                                  (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
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
  (nd_pre SHU 4%nat; intros SHU1 SHU2 SHU3 SHU4; nd_post).
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
  do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil.   (* [comment removed for export] *)
Qed.
End Zd2.
#[using="Type"] Lemma getfrom_spec : forall RNG {R} (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (gfa_tree st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom asegs)).
Proof. exact getfrom_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac split_for_access_post H ::= split_junk_name H.
(* [comment removed for export] *)
Local Ltac slm_footprint_with segs m m' Heq a bs n Hn Ha Hl ::= slm_footprint_with_d0 segs m m' Heq a bs n Hn Ha Hl.
Local Ltac footprint_after_store_with segs m a bs n Hn Ha Hl ::= footprint_after_store_with_d0 segs m a bs n Hn Ha Hl.

Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma sx32_small : forall w : word, bv_unsigned w < 2^31 -> sx32 w = w.
Proof.
  intros w Hw. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  rewrite <- (Z_to_bv_bv_unsigned w). rewrite sx32_lit by lia. reflexivity.
Qed.

#[using="Type"] Lemma aclass_eta0 : forall r, mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) (c_count r) = r.
Proof. intros []; reflexivity. Qed.

#[using="Type"] Lemma fvals_small : forall au S k, 0 <= au -> 0 <= S -> au + Z.of_nat k * S <= 2^32 ->
  Forall (fun w : word => bv_unsigned w < 2^31) (fvals au S k).
Proof.
  intros au S k AU SZ B. unfold fvals. apply Forall_rev. apply Forall_map. apply Forall_forall. intros j Hj.
  apply in_seq in Hj. rewrite Z.shiftr_div_pow2 by lia.
  assert (J : 0 <= Z.of_nat j * S <= Z.of_nat k * S) by nia.
  rewrite unsigned_lit; [| change (2^4) with 16; Z.div_mod_to_equations; lia]. change (2^4) with 16. Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma u32arr_app : forall m A ws1 ws2,
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

#[using="Type"] Lemma u32arr_skipn : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat ->
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

#[using="Type"] Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition getfrom_entry := 0x38c40.
End CANSEC1.
Notation GETFROM_STACK := 640 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
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
                    s2 s3 (Z_to_bv 64 (SRC + 4 * n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x38dc8) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (DST + 4 * n)) a2 (Z_to_bv 64 (DST + 4 * i)) a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 (SRC + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x38db4) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1.
  step. clear RD RS1.                                    (* [comment removed for export] *)
  rewrite (sx32_small w W31).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
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
  zstep. zstep.                                          (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  setreg 20 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a2' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a2', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Definition gf_tail_spec__stmt : Prop := forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word)
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
  0x10007fff8000 <= FA -> FA + 4 * (base + n) <= ATOP -> 4096 <= CHK -> CHK + 64 <= ATOP -> (FA + 4 * (base + n) <= CHK \/ CHK + 64 <= FA) ->      (* [comment removed for export] *)
  0x10007fff8000 <= RI -> RI + 128 <= ATOP -> (RI + 128 <= CHK \/ CHK + 64 <= RI) -> (RI + 128 <= FA \/ FA + 4 * (base + n) <= RI) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> (forall k, 0 <= k < base + n -> rng RNG (FA + 4 * k) 4) -> rng RNG CHK 64 ->
  evtF asegs RNG (gftail_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v F fc RI FA CHK n base lo fl2 chunks0 m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x a0x a1x a2x (Z_to_bv 64 CHK) (Z_to_bv 64 n) (Z_to_bv 64 base) a6 a7
             s2x (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 FA) s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 0x38da4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 0).
Variable rav : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 4).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 5).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 6).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 7).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 8).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 9).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 10).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 11).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 12).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 13).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 14).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 15).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 16).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 17).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 18).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 19).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 20).
Variable s1x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 21).
Variable a0x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 22).
Variable a1x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 23).
Variable a2x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 24).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 25).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 26).
Variable s2x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 27).
Variable s5x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 28).
Variable s6x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 29).
Variable s7x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 30).
Variable s8x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 31).
Variable s9x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 32).
Variable s10x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 33).
Variable s11x : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 34).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 35).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 36).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 37).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 38).
Variable F : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 39).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 40).
Variable m : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 41).
Variable RI : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 42).
Variable FA : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 43).
Variable CHK : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 44).
Variable n : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 45).
Variable base : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 46).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 47).
Variable fl2 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 48).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 49).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 50).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'gf_tail_spec__stmt 51).
#[using="Type"] Lemma gf_tail_spec__body : ltac:(let T := type of (fun (h : gf_tail_spec__stmt) => h RNG rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v rax t0 t1 t2 s1x a0x a1x a2x a6 a7 s2x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 F fc m RI FA CHK n base lo fl2 chunks0 stn fr0) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (rav, (sp, (gp, (tp, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, (s11v, (rax, (t0, (t1, (t2, (s1x, (a0x, (a1x, (a2x, (a6, (a7, (s2x, (s5x, (s6x, (s7x, (s8x, (s9x, (s10x, (s11x, (t3, (t4, (t5, (t6, (F, (fc, (m, (RI, (FA, (CHK, (n, (base, (lo, (fl2, (chunks0, (stn, fr0)))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI FR MTX STN FL LFL FL31 CH LCH AMO B0 N FA0 FA1 CH0 CH1 DJ RI0 RI1 DJ2 DJ3 RIMG RTLS RSTK RRI RFA RCH.
  unfold AIMG_HI in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (RI, RI + 8); (RI + 72, RI + 80); (CHK, CHK + 4 * n)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  snapshot [(RI, RI + 8); (RI + 72, RI + 80)]%Z MUb WMb.
  box CH2. box FL. clear SR2.
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 7 zstep. step. do 5 zstep.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  do 7 zstep. step. if_lit.                                    (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 15 step.                                                  (* [comment removed for export] *)
  carry CH2 MUb WMb ltac:(rewrite length_app, !length_skipn, LFL, LCH; clear -DJ2 N B0; lia).
  carry FL MUb WMb ltac:(rewrite LFL; clear -DJ3 N B0; lia).
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. unfold gftail_post.
  do 16 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MUF|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact STN|]. split; [exact FL|].
  exact CH2.
Qed.
End Zd1.
#[using="Type"] Lemma gf_tail_spec : ltac:(let t := eval cbv delta [gf_tail_spec__stmt] in gf_tail_spec__stmt in exact t).
Proof. exact gf_tail_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_take {R} (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) (st2 : astate) : AM R :=
  if c_num_freed (get_cls st2 c) <? n then aundef_ (UCheck 229) (k st2 false) else KK st2.

Definition gfa_tree {R} (st1 : astate) (c n : Z) (k : astate -> bool -> AM R) (KK : astate -> AM R) : AM R :=
  if n <=? c_num_freed (get_cls st1 c) then gfa_take c n k KK st1
  else populate_free_array st1 c (n - c_num_freed (get_cls st1 c)) (fun st2 ok => if ok then gfa_take c n k KK st2 else k st2 false).

#[using="Type"] Lemma cache_refill_tree_gfa : forall {R} st c (k : astate -> bool -> AM R),
  cache_refill_tree st c k =
  (let st1 := init_cache st in let n := max_count st1 c / 2 in
   gfa_tree st1 c n k (fun st2 => k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true)).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition getfrom_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n CHK lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (* [comment removed for export] *)
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
     (* [comment removed for export] *)
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
     (* [comment removed for export] *)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)
     (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
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

Definition getfrom_spec__stmt : Prop := forall RNG {R} (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (gfa_tree st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 2).
Variable KK : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 38).
Variable L : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 39).
Variable st : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 40).
Variable c : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 41).
Variable n : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 42).
Variable CHK : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 44).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 45).
Variable fl : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 46).
Variable chunks0 : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 47).
Variable stm : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 48).
Variable stn : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 49).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'getfrom_spec__stmt 50).
Let S := size_of_class c.
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
#[using="S mu au nf mfa"] Lemma getfrom_spec__body : ltac:(let T := type of (fun (h : getfrom_spec__stmt) => h RNG R k KK Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c n CHK lo sj fl chunks0 stm stn fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (KK, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (n, (CHK, (lo, (sj, (fl, (chunks0, (stm, (stn, fj))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC N MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP CHK0 CHK1 RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros PC RC TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, getfrom_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  chg (size_of_class c) S.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - GETFROM_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite RBE in AZU. rewrite FAE in FL, FJ, AZF, RFA.
  iprefix.
  carve_frame 128%nat ST.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.                                                  (* [comment removed for export] *)
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
  step. step. step.                                            (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 9 zstep.                                                  (* [comment removed for export] *)
  do 4 zstep.                                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.                                                        (* [comment removed for export] *)
  do 5 zstep.                                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS. box STM.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM MUl WMl ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  step.                                                        (* [comment removed for export] *)
  step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by (clear -NF NFA MU MUX N; lia).   (* [comment removed for export] *)
  all: cycle 1.
  { (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
    box CT. box CH. box STATS. box STM.
    step.                                                      (* [comment removed for export] *)
    carry CT MUr WMr ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
    carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
    carry STATS MUr WMr ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    carry STM MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
    step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }   (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
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
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step. zstep. step. step.                         (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done. unfold gfa_tree. fold nf.
  replace (n <=? nf) with false by (symmetry; apply Z.leb_gt; exact KP).
  unbox MU01. name_sp sp (-128).
  eapply populate_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; eapply rng_sub'; [exact RFA|]; clear -NF MFA; lia
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N KP HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PR.
  unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in PR. cbv zeta in PR. fold S mu au nf mfa in PR. rewrite FAE, RBE in PR.
  (nd_pre PR 30%nat; intros FPLE mu' mfa' ncnt sj' stm' UD MUB MUM' NCE NC0 FD NEWB NEWM NEWMOD AR JR ST2E MU2 WM2 MI2 ST2 REG2 EXH2 STATS2 LSJ2 STM2 AZU2 AZF2 MC2; nd_post).
  box UD. box FD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (GC2 : get_cls st2 c = mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count (get_cls st c))) by (rewrite ST2E; apply get_cls_put_cls_eq).
  assert (NCS : au + ncnt * S <= mu' /\ 0 <= ncnt * S).
  { split; [| clear -NC0 SZ; nia]. pose proof NCE as E. clear -E MUB MU NC0 SZ. subst ncnt. Z.div_mod_to_equations. nia. }
  destruct NCS as [NCS1 NCS2].
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + mu) + shlen (mu' - mu) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)).   (* [comment removed for export] *)
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  (nd_pre SHF 4%nat; intros SHF1 SHF2 SHF3 SHF4; nd_post).
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
  replace (ret_pc (Z_to_bv 64 233212)) with (Z_to_bv 64 233212 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by (clear -NF NC0 N MFA NEWB; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    apply evtF_done. unfold gfa_take. rewrite GC2. cbn [c_num_freed].
    replace (nf + ncnt <? n) with true by (symmetry; apply Z.ltb_lt; exact KQ).
    rewrite aembed_aundef_. apply implF_ret_unr. }
  step. zstep.                                                 (* [comment removed for export] *)
  snapshot [(aregion_info L c + 16, aregion_info L c + 56)]%Z MUr WMr.
  box CH. box STATS2. box STM2. box FL2. clear FL AR.
  step.                                                        (* [comment removed for export] *)
  carry CH MUr WMr ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 Y TIC TB; lia).
  carry STATS2 MUr WMr ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry STM2 MUr WMr ltac:(ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  carry FL2 MUr WMr ltac:(rewrite LFL2; clear -SP1 SP2 HC RIE NF NC0 MFA NEWB; lia).
  step. step.                                                  (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
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
  (nd_pre SHU 4%nat; intros SHU1 SHU2 SHU3 SHU4; nd_post).
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
  do 5 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE T0 T1 TIC CHK0 CHK1 N Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil.   (* [comment removed for export] *)
Qed.
End Zd2.
#[using="Type"] Lemma getfrom_spec : forall RNG {R} (k : astate -> bool -> AM R) (KK : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= CHK -> CHK + 64 <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      getfrom_ret L RNG sp st c n CHK lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KK st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (gfa_tree st c n k KK)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 getfrom_entry) fc None m (seg_rom asegs)).
Proof. exact getfrom_spec__body. Qed.
End CANSEC2.
End TwB.
End F_agetfrom.

(* [comment removed for export] *)
Module F_areturn.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition rta_entry : Z := 0x3687c.
End CANSEC1.
Notation RTA_STACK := 576 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma rta_copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
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
                    s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * n)) s7 s8 (Z_to_bv 64 (DST + 4 * n)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36a0c) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * i)) s7 s8 (Z_to_bv 64 (DST + 4 * i)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x369f8) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1. pose proof (RDS i ltac:(lia)) as RD1.
  step. clear RD RS1.                                    (* [comment removed for export] *)
  rewrite (sx32_small w W31).
  zstep.                                                 (* [comment removed for export] *)
  setreg 22 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
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
  zstep.                                                 (* [comment removed for export] *)
  setreg 25 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a1' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a1', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

#[using="Type"] Lemma junk_of_cells' : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

#[using="Type"] Lemma set_mfa_eq : forall v r,
  cls_set_mapped_free_array v r = mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) v (c_count r).
Proof. intros v []; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Definition rta_spec__stmt : Prop := forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 1).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 41).
Variable SRC : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 43).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 44).
Variable src : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 45).
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
Let DST := al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf.
#[using="mu au nf mfa DST"] Lemma rta_spec__body : ltac:(let T := type of (fun (h : rta_spec__stmt) => h RNG R kb Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c n SRC lo sj src) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (kb, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (n, (SRC, (lo, (sj, src)))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CH LCH CH31 FJ AZF SBE HC N NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP CHK0 CHK1 RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros PC RC TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, rta_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - RTA_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite FAE in FJ, AZF, RFA.
  (* [comment removed for export] *)
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
  do 14 step.                                                  (* [comment removed for export] *)
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
  do 7 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 9 zstep.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 25 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 12 (Z_to_bv 64 (aregion L c)) ltac:(rewrite RBE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 4 zstep.                                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done.
  name_sp sp (-128).
  eapply ensure_spec with (lo := lo) (L := L) (sj := sj);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold mu au nf mfa; first [assumption | clear -NF MFA MFAM NFN N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
  unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold nf mfa in ER. rewrite FAE in ER.
  (nd_pre ER 16%nat; intros FPLE new sj' UD NEWB NEWGE NEWM MU2 WM2 MI2 ST2 REG2 STATS2 LSJ2 AZF2 MC2; nd_post).
  box UD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  assert (SHFL : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (JD : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (new - 4 * nf)).
  { ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & ZCB & _)].
    - rewrite E. exact FJ.
    - replace (new - 4 * nf) with ((mfa - 4 * nf) + (new - mfa)) by (clear; lia).
      apply junk_merge; [exact FJ | | clear -MFA; lia | clear -NEWGE; lia].
      replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + (mfa - 4 * nf)) with (al_space_beg L + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
      eapply junk_of_cb. exact ZCB. }
  clear FJ.
  destruct (junk_split m2 _ (4 * n) (new - 4 * nf - 4 * n) ltac:(eapply junk_at_eq; [exact JD| reflexivity | clear; lia]) ltac:(clear -N; lia) ltac:(clear -NEWB; lia)) as [JD4 JR].
  (nd_pre (u32arr_of_junk m2 _ n JD4 ltac:(clear -N; lia)) 3%nat; intros ws0 U0 L0; nd_post). clear JD JD4.
  chg (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) DST.
  replace (ret_pc (Z_to_bv 64 223712)) with (Z_to_bv 64 223712 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  snapshot [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88)]%Z MUs WMs.
  box SR3. box DS3. box STATS2. clear CH.
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carry SR3 MUs WMs ltac:(rewrite LCH; ub TSP; clear -SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUs WMs ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUs WMs ltac:(rewrite LSJ2; ub TSP; clear -SP1 SP2 HC RIE T0 T1 Y TIC TB; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MC4 : m3_cells L mm) ; [eapply m3_cells_frame; [exact MC3 | exact MUs | exact WMs |]; ub SCX; unfold AIMG_HI, AIMG_LO;
    do 2 (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |] end.
  eapply junk_frame in JR; [| exact MUs | exact WMs | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia].
  clear MC3. box MUs.
  (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 7 zstep. step. do 5 zstep.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  do 7 zstep. step. if_lit.                                    (* [comment removed for export] *)
  box SR3. box DS3. box STATS2. box MUm. box MU35.
  snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUu WMu.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry SR3 MUu WMu ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUu WMu ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUu WMu ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  do 15 step.                                                  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
End Zd1.
#[using="Type"] Lemma rta_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Proof. exact rta_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition rta_entry : Z := 0x368e4.
End CANSEC1.
Notation RTA_STACK := 576 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma rta_copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
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
                    s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * n)) s7 s8 (Z_to_bv 64 (DST + 4 * n)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36a74) fc None m' (seg_rom asegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u32arr asegs m' SRC src /\ u32arr asegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * i)) s7 s8 (Z_to_bv 64 (DST + 4 * i)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36a60) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read asegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1. pose proof (RDS i ltac:(lia)) as RD1.
  step. clear RD RS1.                                    (* [comment removed for export] *)
  rewrite (sx32_small w W31).
  zstep.                                                 (* [comment removed for export] *)
  setreg 22 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u32arr_store_ok asegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
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
  zstep.                                                 (* [comment removed for export] *)
  setreg 25 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a1' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a1', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

#[using="Type"] Lemma junk_of_cells' : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

#[using="Type"] Lemma set_mfa_eq : forall v r,
  cls_set_mapped_free_array v r = mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) v (c_count r).
Proof. intros v []; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Definition rta_spec__stmt : Prop := forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 1).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 41).
Variable SRC : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 42).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 43).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 44).
Variable src : ltac2:(SecDietF.SzSecF.ty 'rta_spec__stmt 45).
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
Let DST := al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf.
#[using="mu au nf mfa DST"] Lemma rta_spec__body : ltac:(let T := type of (fun (h : rta_spec__stmt) => h RNG R kb Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c n SRC lo sj src) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (kb, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (n, (SRC, (lo, (sj, src)))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CH LCH CH31 FJ AZF SBE HC N NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP CHK0 CHK1 RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. (nd_pre MC0 11%nat; intros PC RC TI TK T88 TSD CT ISB IREL ISE IPRE; nd_post).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, rta_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - RTA_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  rewrite FAE in FJ, AZF, RFA.
  (* [comment removed for export] *)
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
  do 14 step.                                                  (* [comment removed for export] *)
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
  do 7 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 9 zstep.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 25 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 12 (Z_to_bv 64 (aregion L c)) ltac:(rewrite RBE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 4 zstep.                                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done.
  name_sp sp (-128).
  eapply ensure_spec with (lo := lo) (L := L) (sj := sj);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
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
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold mu au nf mfa; first [assumption | clear -NF MFA MFAM NFN N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
  unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold nf mfa in ER. rewrite FAE in ER.
  (nd_pre ER 16%nat; intros FPLE new sj' UD NEWB NEWGE NEWM MU2 WM2 MI2 ST2 REG2 STATS2 LSJ2 AZF2 MC2; nd_post).
  box UD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  assert (SHFL : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (JD : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (new - 4 * nf)).
  { ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & ZCB & _)].
    - rewrite E. exact FJ.
    - replace (new - 4 * nf) with ((mfa - 4 * nf) + (new - mfa)) by (clear; lia).
      apply junk_merge; [exact FJ | | clear -MFA; lia | clear -NEWGE; lia].
      replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + (mfa - 4 * nf)) with (al_space_beg L + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
      eapply junk_of_cb. exact ZCB. }
  clear FJ.
  destruct (junk_split m2 _ (4 * n) (new - 4 * nf - 4 * n) ltac:(eapply junk_at_eq; [exact JD| reflexivity | clear; lia]) ltac:(clear -N; lia) ltac:(clear -NEWB; lia)) as [JD4 JR].
  (nd_pre (u32arr_of_junk m2 _ n JD4 ltac:(clear -N; lia)) 3%nat; intros ws0 U0 L0; nd_post). clear JD JD4.
  chg (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) DST.
  replace (ret_pc (Z_to_bv 64 223816)) with (Z_to_bv 64 223816 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  snapshot [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88)]%Z MUs WMs.
  box SR3. box DS3. box STATS2. clear CH.
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carry SR3 MUs WMs ltac:(rewrite LCH; ub TSP; clear -SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUs WMs ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUs WMs ltac:(rewrite LSJ2; ub TSP; clear -SP1 SP2 HC RIE T0 T1 Y TIC TB; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MC4 : m3_cells L mm) ; [eapply m3_cells_frame; [exact MC3 | exact MUs | exact WMs |]; ub SCX; unfold AIMG_HI, AIMG_LO;
    do 2 (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |] end.
  eapply junk_frame in JR; [| exact MUs | exact WMs | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia].
  clear MC3. box MUs.
  (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 7 zstep. step. do 5 zstep.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  do 7 zstep. step. if_lit.                                    (* [comment removed for export] *)
  box SR3. box DS3. box STATS2. box MUm. box MU35.
  snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUu WMu.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry SR3 MUu WMu ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUu WMu ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUu WMu ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  do 15 step.                                                  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
End Zd1.
#[using="Type"] Lemma rta_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
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
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom asegs)).
Proof. exact rta_spec__body. Qed.
End CANSEC2.
End TwB.
End F_areturn.

(* [comment removed for export] *)
Module F_acdrain.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cdrain_entry : Z := 0x366d8.
End CANSEC1.
Notation CDRAIN_STACK := 640 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma disjoint_from_stack : forall W A k, Forall (fun iv => ATOP <= fst iv) W -> A + k <= ATOP -> disjoint_from W A k.
Proof.
  induction W as [|[lo hi] W IH]; intros A k HW LE; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [left; lia| apply IH; assumption].
Qed.

#[using="Type"] Lemma rta_ret_frame : forall L RNG sp st c n SRC lo src m st2 RNG' m2 m4,
  rta_ret L RNG sp st c n SRC lo src m st2 RNG' m2 ->
  munch [(bv_unsigned sp - 576, bv_unsigned sp)]%Z m2 m4 -> wmono asegs m2 m4 -> ATOP <= lo -> lo <= bv_unsigned sp - 576 ->
  mem_inv asegs m4 -> stk asegs m4 lo (bv_unsigned sp) ->
  1 <= c < K_NUM_CLASSES -> 0 <= n -> length src = Z.to_nat n -> 0 <= c_num_freed (get_cls st c) -> 4 * (c_num_freed (get_cls st c) + n) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP ->
  rta_ret L RNG sp st c n SRC lo src m st2 RNG' m4.
Proof.
  intros L RNG sp st c n SRC lo src m st2 RNG' m2 m4 RR MU WM CEIL LO MI4 ST4 HC N0 LS NF0 NFN SP1 SP2 T1 CX0 CX1. band_lin.   (* [comment removed for export] *)
  unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in *. cbv zeta in *.
  (nd_pre RR 22%nat; intros FPLE mfa' sj' UD NEWB NEWGE NEWM GC2 ST2E MU2 WM2 _ _ MTX REG J72 STATS LSJ SRC3 JR AZF MC; nd_post).
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  unfold K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  assert (D : forall A k, A + k <= ATOP -> disjoint_from [(bv_unsigned sp - 576, bv_unsigned sp)]%Z A k) by (intros A k LE; cbn; split; [left; clear -LE CEIL LO; lia| exact I]).
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st c)) + shlen (mfa' - c_mapped_free_array (get_cls st c)) <= 0x10007fff8000
                /\ shad (afreearr L c + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC NEWB NEWGE NF0 N0. Z.div_mod_to_equations. lia. }
  destruct SHF as [SHF1 SHF2].
  split; [exact FPLE|]. exists mfa', sj'.
  split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
           split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
           eapply fill_frame; [exact FILL | exact MU | exact WM | intros _; apply D; clear -SHF1; lia]. }
  split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|]. split; [exact GC2|]. split; [exact ST2E|].
  split. { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia. }
  split; [eapply wmono_trans; [exact WM2| exact WM]|]. split; [exact MI4|]. split; [exact ST4|].
  split; [eapply cells_frame; [exact MTX | exact MU | exact WM | cbn; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply cells_frame; [exact REG | exact MU | exact WM | cbn; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply junk_frame; [exact J72 | exact MU | exact WM | intros _; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | apply D; rewrite LSJ; clear -T1; lia]|].
  split; [exact LSJ|].
  split; [eapply u32arr_frame; [exact SRC3 | exact MU | exact WM | apply D; rewrite FAE, LS; clear -SP2 HC NEWB NF0 N0 NFN; lia]|].
  split; [eapply junk_frame; [exact JR | exact MU | exact WM | intros _; apply D; rewrite FAE; clear -SP2 HC NEWB NF0 N0; lia]|].
  split; [eapply azero_frame; [exact AZF | exact MU | exact WM | intros _; apply D; clear -SHF2; lia]|].
  eapply m3_cells_frame; [exact MC | exact MU | exact WM |]. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1; pose proof atop_range; lia |]. apply Forall_nil.   (* [comment removed for export] *)
Qed.


(* [comment removed for export] *)
Definition cdrain_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c cnt mc csz lo : Z) (chunks : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let half := mc / 2 in let CA := acache_addr L c in
  exists m1,
       munch [(bv_unsigned sp - 64, bv_unsigned sp); (CA, CA + 4)]%Z m m1 /\ wmono asegs m m1
    /\ rta_ret L RNG (Z_to_bv 64 (bv_unsigned sp + -64)) st c half (CA + 16 + 4 * (cnt - half)) lo
               (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)) m1 st2 RNG' m'
    /\ rw_cells asegs m' CA [C4 (Z_to_bv 64 (cnt - half)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr asegs m' (CA + 16) chunks
    /\ stk asegs m' lo (bv_unsigned sp).

Definition cdrain_spec__stmt : Prop := forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c cnt mc csz lo : Z) (sj chunks : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let half := mc / 2 in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDRAIN_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 CA -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m CA [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 2 <= mc <= 16 -> half <= cnt <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + half) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdrain_ret L RNG sp st c cnt mc csz lo chunks m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + half) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdrain_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 1).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 40).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 41).
Variable mc : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 42).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 44).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 45).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 46).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
#[using="nf mfa"] Lemma cdrain_spec__body : ltac:(let T := type of (fun (h : cdrain_spec__stmt) => h RNG R kb Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c cnt mc csz lo sj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (kb, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (cnt, (mc, (csz, (lo, (sj, chunks))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CR CH LCH CH31 FJ AZF SBE HC MC16 CNT NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdrain_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (HALF : 1 <= mc / 2 <= 8) by (clear -MC16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  box TCX. box SCX. box TSP.
  iprefix.
  carve_frame 64%nat ST.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  rewrite (sx32_lit cnt) by (clear -CNT HALF; lia). rewrite (zx32_lit mc) by (clear -MC16; lia).
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  rewrite ?(unsigned_lit mc) by (clear -MC16; lia). rewrite ?(unsigned_lit cnt) by (clear -CNT HALF; lia).
  rewrite ?Z.shiftr_div_pow2 by (clear; lia). change (2^1) with 2.
  rewrite ?(Z.mod_small cnt 4294967296) by (clear -CNT HALF; lia).
  step. if_cases KC; zify_cond KC. { exfalso. rewrite ?unsigned_lit in KC by (clear -CNT HALF MC16; lia). clear -KC CNT HALF. lia. }   (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  box MUN. snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box CH. box STATS. box MTX. box REG. box J72. box FJ. box AZF. box MC.
  step.                                                        (* [comment removed for export] *)
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STATS MUc WMc ltac:(rewrite LSJ, CAE; clear -HC; lia).
  carry MTX MUc WMc ltac:(rewrite CAE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; ub TSP; clear -HC Y; lia).
  carry REG MUc WMc ltac:(rewrite CAE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; ub TSP; clear -HC Y; lia).
  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MU01 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4)]%Z m mm)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia)
  end.
  rename WM into WM01. clear MUN MUc WMc.
  unbox J72. eapply junk_frame in J72; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; rewrite CAE, RIE; ub TSP; clear -HC Y SPR CEIL LO SP1 SP2; lia].
  unbox FJ. eapply junk_frame in FJ; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; rewrite CAE, FAE; ub TSP; clear -HC Y NF MFA SPR CEIL LO SP1 SP2; lia].
  unbox AZF.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF1 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, CAE, FAE; unfold ASHOFF; clear -SP1 SP2 HC T0 T1 SPR CEIL LO MFA NF; pose proof atop_range as AR; unfold sclr, KLS in T0; Z.div_mod_to_equations; lia |];   (* [comment removed for export] *)
    unbox MC; assert (MC1 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; unfold AIMG_HI, AIMG_LO; ub TCX;
      do 2 (apply Forall_cons; [cbn [fst snd]; rewrite ?CAE; clear -T0 TIC CXI CX0 CX1 HC Y SPR CEIL LO T1; pose proof atop_range; lia |]); apply Forall_nil |]   (* [comment removed for export] *)
  end.
  clear AZF MC.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done.
  pose proof (u32arr_firstn _ _ _ (Z.to_nat (mc / 2)) (u32arr_skipn' _ _ chunks (Z.to_nat (cnt - mc / 2)) CH ltac:(rewrite LCH; clear -CNT HALF; lia))
                ltac:(rewrite length_skipn, LCH; clear -CNT HALF; lia)) as SRCA.
  rewrite Z2Nat.id in SRCA by (clear -CNT HALF; lia).
  name_sp sp (-64).
  eapply rta_spec with (lo := lo) (L := L) (sj := sj) (SRC := acache_addr L c + 16 + 4 * (cnt - mc / 2))
                       (src := firstn (Z.to_nat (mc / 2)) (skipn (Z.to_nat (cnt - mc / 2)) chunks));
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => eapply u32arr_addr_eq; [exact SRCA| clear; lia]
       | |- length _ = _ => first [exact LSJ | rewrite length_firstn, length_skipn, LCH; clear -CNT HALF; lia]
       | |- Forall _ _ => eapply Forall_firstn_skipn; [exact CH31| clear -CNT HALF; lia]
       | |- azero _ _ _ => exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold nf mfa; first [assumption | rewrite ?CAE; clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNT HALF MC16; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
  (nd_pre RR0 14%nat; intros FPLE new sj' _ NEWB NEWGE NEWM _ _ MU2 WM2 MI2 ST2 _; nd_post).
  rewrite Hsp in MU2, ST2. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  rewrite RIE, FAE in MU2.
  assert (SHB2 : 2148238848 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) by (rewrite shad_div; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof T0 as T0u. unfold sclr, KLS in T0u.   (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  xport CR MU2 WM2 ltac:(rewrite CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  clear ST MI MTX REG J72 STATS FJ AZF1 MC1 SRCA.
  replace (ret_pc (Z_to_bv 64 223036)) with (Z_to_bv 64 223036 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  snapshot [(bv_unsigned sp + -64 - 576, bv_unsigned sp + -64)]%Z MUk WMk.
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 48%nat ST2.
  do 5 step.                                                   (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  do 6 step.                                                   (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -112) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -64) end.
  step. step. step.                                            (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -64) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. eapply KONT.
  unfold cdrain_ret. cbv zeta.
  exists m1.
  split; [exact MU01|]. split; [exact WM01|].
  split.
  { lazymatch goal with H : mem_inv asegs ?mm, STK : stk asegs ?mm lo _ |- rta_ret _ _ _ _ _ _ _ _ _ _ _ _ ?mm =>
      eapply rta_ret_frame;
      [ exact RR
      | eapply munch_weaken; [| exact MUk]; unfold sub_fp; cbn [outside]; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear; intros xq Hxq; lia
      | exact WMk | atop_facts; exact CEIL | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); clear -LO; lia | exact H
      | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact (proj1 (stk_split asegs _ lo (bv_unsigned sp + -64) (bv_unsigned sp) STK ltac:(clear -SPR CEIL LO; lia)))
      | unfold K_NUM_CLASSES; exact HC | clear -HALF; lia | rewrite length_firstn, length_skipn, LCH; clear -CNT HALF; lia
      | exact NF | unfold K_FREEARR_MAX; exact NFN | exact SP1 | unfold K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; exact SP2
      | atop_facts; exact T1 | exact CX0 | atop_facts; exact CX1 ]
    end. }
  split; [exact CR|]. split; [exact CH|]. assumption.
Qed.
End Zd1.
#[using="Type"] Lemma cdrain_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c cnt mc csz lo : Z) (sj chunks : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let half := mc / 2 in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDRAIN_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 CA -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m CA [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 2 <= mc <= 16 -> half <= cnt <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + half) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdrain_ret L RNG sp st c cnt mc csz lo chunks m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + half) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdrain_entry) fc None m (seg_rom asegs)).
Proof. exact cdrain_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cdrain_entry : Z := 0x36740.
End CANSEC1.
Notation CDRAIN_STACK := 640 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma disjoint_from_stack : forall W A k, Forall (fun iv => ATOP <= fst iv) W -> A + k <= ATOP -> disjoint_from W A k.
Proof.
  induction W as [|[lo hi] W IH]; intros A k HW LE; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [left; lia| apply IH; assumption].
Qed.

#[using="Type"] Lemma rta_ret_frame : forall L RNG sp st c n SRC lo src m st2 RNG' m2 m4,
  rta_ret L RNG sp st c n SRC lo src m st2 RNG' m2 ->
  munch [(bv_unsigned sp - 576, bv_unsigned sp)]%Z m2 m4 -> wmono asegs m2 m4 -> ATOP <= lo -> lo <= bv_unsigned sp - 576 ->
  mem_inv asegs m4 -> stk asegs m4 lo (bv_unsigned sp) ->
  1 <= c < K_NUM_CLASSES -> 0 <= n -> length src = Z.to_nat n -> 0 <= c_num_freed (get_cls st c) -> 4 * (c_num_freed (get_cls st c) + n) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) -> sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP ->
  rta_ret L RNG sp st c n SRC lo src m st2 RNG' m4.
Proof.
  intros L RNG sp st c n SRC lo src m st2 RNG' m2 m4 RR MU WM CEIL LO MI4 ST4 HC N0 LS NF0 NFN SP1 SP2 T1 CX0 CX1. band_lin.   (* [comment removed for export] *)
  unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in *. cbv zeta in *.
  (nd_pre RR 22%nat; intros FPLE mfa' sj' UD NEWB NEWGE NEWM GC2 ST2E MU2 WM2 _ _ MTX REG J72 STATS LSJ SRC3 JR AZF MC; nd_post).
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  unfold K_NUM_CLASSES, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  assert (D : forall A k, A + k <= ATOP -> disjoint_from [(bv_unsigned sp - 576, bv_unsigned sp)]%Z A k) by (intros A k LE; cbn; split; [left; clear -LE CEIL LO; lia| exact I]).
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st c)) + shlen (mfa' - c_mapped_free_array (get_cls st c)) <= 0x10007fff8000
                /\ shad (afreearr L c + mfa') + shlen (536870912 - mfa') <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC NEWB NEWGE NF0 N0. Z.div_mod_to_equations. lia. }
  destruct SHF as [SHF1 SHF2].
  split; [exact FPLE|]. exists mfa', sj'.
  split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
           split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
           eapply fill_frame; [exact FILL | exact MU | exact WM | intros _; apply D; clear -SHF1; lia]. }
  split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|]. split; [exact GC2|]. split; [exact ST2E|].
  split. { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia. }
  split; [eapply wmono_trans; [exact WM2| exact WM]|]. split; [exact MI4|]. split; [exact ST4|].
  split; [eapply cells_frame; [exact MTX | exact MU | exact WM | cbn; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply cells_frame; [exact REG | exact MU | exact WM | cbn; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply junk_frame; [exact J72 | exact MU | exact WM | intros _; apply D; rewrite RIE; clear -SP2 HC; lia]|].
  split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | apply D; rewrite LSJ; clear -T1; lia]|].
  split; [exact LSJ|].
  split; [eapply u32arr_frame; [exact SRC3 | exact MU | exact WM | apply D; rewrite FAE, LS; clear -SP2 HC NEWB NF0 N0 NFN; lia]|].
  split; [eapply junk_frame; [exact JR | exact MU | exact WM | intros _; apply D; rewrite FAE; clear -SP2 HC NEWB NF0 N0; lia]|].
  split; [eapply azero_frame; [exact AZF | exact MU | exact WM | intros _; apply D; clear -SHF2; lia]|].
  eapply m3_cells_frame; [exact MC | exact MU | exact WM |]. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1; pose proof atop_range; lia |]. apply Forall_nil.   (* [comment removed for export] *)
Qed.


(* [comment removed for export] *)
Definition cdrain_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c cnt mc csz lo : Z) (chunks : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let half := mc / 2 in let CA := acache_addr L c in
  exists m1,
       munch [(bv_unsigned sp - 64, bv_unsigned sp); (CA, CA + 4)]%Z m m1 /\ wmono asegs m m1
    /\ rta_ret L RNG (Z_to_bv 64 (bv_unsigned sp + -64)) st c half (CA + 16 + 4 * (cnt - half)) lo
               (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)) m1 st2 RNG' m'
    /\ rw_cells asegs m' CA [C4 (Z_to_bv 64 (cnt - half)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr asegs m' (CA + 16) chunks
    /\ stk asegs m' lo (bv_unsigned sp).

Definition cdrain_spec__stmt : Prop := forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c cnt mc csz lo : Z) (sj chunks : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let half := mc / 2 in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDRAIN_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 CA -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m CA [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 2 <= mc <= 16 -> half <= cnt <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + half) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdrain_ret L RNG sp st c cnt mc csz lo chunks m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + half) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdrain_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 1).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 3).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 10).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 11).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 12).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 13).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 14).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 15).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 16).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 17).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 18).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 19).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 20).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 21).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 22).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 23).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 24).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 25).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 26).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 27).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 28).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 29).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 30).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 31).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 32).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 33).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 34).
Variable F : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 35).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 36).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 37).
Variable L : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 39).
Variable c : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 40).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 41).
Variable mc : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 42).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 44).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 45).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'cdrain_spec__stmt 46).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
#[using="nf mfa"] Lemma cdrain_spec__body : ltac:(let T := type of (fun (h : cdrain_spec__stmt) => h RNG R kb Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c cnt mc csz lo sj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (kb, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (L, (st, (c, (cnt, (mc, (csz, (lo, (sj, chunks))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CR CH LCH CH31 FJ AZF SBE HC MC16 CNT NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RTLS RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdrain_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (HALF : 1 <= mc / 2 <= 8) by (clear -MC16; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4)]%Z m) as MUN.
  pose proof (wmono_refl asegs m) as WM.
  box TCX. box SCX. box TSP.
  iprefix.
  carve_frame 64%nat ST.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  rewrite (sx32_lit cnt) by (clear -CNT HALF; lia). rewrite (zx32_lit mc) by (clear -MC16; lia).
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  rewrite ?(unsigned_lit mc) by (clear -MC16; lia). rewrite ?(unsigned_lit cnt) by (clear -CNT HALF; lia).
  rewrite ?Z.shiftr_div_pow2 by (clear; lia). change (2^1) with 2.
  rewrite ?(Z.mod_small cnt 4294967296) by (clear -CNT HALF; lia).
  step. if_cases KC; zify_cond KC. { exfalso. rewrite ?unsigned_lit in KC by (clear -CNT HALF MC16; lia). clear -KC CNT HALF. lia. }   (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  box MUN. snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box CH. box STATS. box MTX. box REG. box J72. box FJ. box AZF. box MC.
  step.                                                        (* [comment removed for export] *)
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STATS MUc WMc ltac:(rewrite LSJ, CAE; clear -HC; lia).
  carry MTX MUc WMc ltac:(rewrite CAE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; ub TSP; clear -HC Y; lia).
  carry REG MUc WMc ltac:(rewrite CAE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; ub TSP; clear -HC Y; lia).
  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MU01 : munch [(bv_unsigned sp - 64, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4)]%Z m mm)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia)
  end.
  rename WM into WM01. clear MUN MUc WMc.
  unbox J72. eapply junk_frame in J72; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; rewrite CAE, RIE; ub TSP; clear -HC Y SPR CEIL LO SP1 SP2; lia].
  unbox FJ. eapply junk_frame in FJ; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; rewrite CAE, FAE; ub TSP; clear -HC Y NF MFA SPR CEIL LO SP1 SP2; lia].
  unbox AZF.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF1 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, CAE, FAE; unfold ASHOFF; clear -SP1 SP2 HC T0 T1 SPR CEIL LO MFA NF; pose proof atop_range as AR; unfold sclr, KLS in T0; Z.div_mod_to_equations; lia |];   (* [comment removed for export] *)
    unbox MC; assert (MC1 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; unfold AIMG_HI, AIMG_LO; ub TCX;
      do 2 (apply Forall_cons; [cbn [fst snd]; rewrite ?CAE; clear -T0 TIC CXI CX0 CX1 HC Y SPR CEIL LO T1; pose proof atop_range; lia |]); apply Forall_nil |]   (* [comment removed for export] *)
  end.
  clear AZF MC.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done.
  pose proof (u32arr_firstn _ _ _ (Z.to_nat (mc / 2)) (u32arr_skipn' _ _ chunks (Z.to_nat (cnt - mc / 2)) CH ltac:(rewrite LCH; clear -CNT HALF; lia))
                ltac:(rewrite length_skipn, LCH; clear -CNT HALF; lia)) as SRCA.
  rewrite Z2Nat.id in SRCA by (clear -CNT HALF; lia).
  name_sp sp (-64).
  eapply rta_spec with (lo := lo) (L := L) (sj := sj) (SRC := acache_addr L c + 16 + 4 * (cnt - mc / 2))
                       (src := firstn (Z.to_nat (mc / 2)) (skipn (Z.to_nat (cnt - mc / 2)) chunks));
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => eapply u32arr_addr_eq; [exact SRCA| clear; lia]
       | |- length _ = _ => first [exact LSJ | rewrite length_firstn, length_skipn, LCH; clear -CNT HALF; lia]
       | |- Forall _ _ => eapply Forall_firstn_skipn; [exact CH31| clear -CNT HALF; lia]
       | |- azero _ _ _ => exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold nf mfa; first [assumption | rewrite ?CAE; clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNT HALF MC16; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
  (nd_pre RR0 14%nat; intros FPLE new sj' _ NEWB NEWGE NEWM _ _ MU2 WM2 MI2 ST2 _; nd_post).
  rewrite Hsp in MU2, ST2. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RTLS. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  rewrite RIE, FAE in MU2.
  assert (SHB2 : 2148239360 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) by (rewrite shad_div; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  pose proof T0 as T0u. unfold sclr, KLS in T0u.   (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  xport CR MU2 WM2 ltac:(rewrite CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0u SHB2 T1 NF MFA NEWB NEWGE SHF Y; lia).
  clear ST MI MTX REG J72 STATS FJ AZF1 MC1 SRCA.
  replace (ret_pc (Z_to_bv 64 223140)) with (Z_to_bv 64 223140 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  snapshot [(bv_unsigned sp + -64 - 576, bv_unsigned sp + -64)]%Z MUk WMk.
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 48%nat ST2.
  do 5 step.                                                   (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  do 6 step.                                                   (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -112) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -64) end.
  step. step. step.                                            (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -64) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. eapply KONT.
  unfold cdrain_ret. cbv zeta.
  exists m1.
  split; [exact MU01|]. split; [exact WM01|].
  split.
  { lazymatch goal with H : mem_inv asegs ?mm, STK : stk asegs ?mm lo _ |- rta_ret _ _ _ _ _ _ _ _ _ _ _ _ ?mm =>
      eapply rta_ret_frame;
      [ exact RR
      | eapply munch_weaken; [| exact MUk]; unfold sub_fp; cbn [outside]; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear; intros xq Hxq; lia
      | exact WMk | atop_facts; exact CEIL | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); clear -LO; lia | exact H
      | rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact (proj1 (stk_split asegs _ lo (bv_unsigned sp + -64) (bv_unsigned sp) STK ltac:(clear -SPR CEIL LO; lia)))
      | unfold K_NUM_CLASSES; exact HC | clear -HALF; lia | rewrite length_firstn, length_skipn, LCH; clear -CNT HALF; lia
      | exact NF | unfold K_FREEARR_MAX; exact NFN | exact SP1 | unfold K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; exact SP2
      | atop_facts; exact T1 | exact CX0 | atop_facts; exact CX1 ]
    end. }
  split; [exact CR|]. split; [exact CH|]. assumption.
Qed.
End Zd1.
#[using="Type"] Lemma cdrain_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c cnt mc csz lo : Z) (sj chunks : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let half := mc / 2 in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDRAIN_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 CA -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m CA [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 2 <= mc <= 16 -> half <= cnt <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + half) <= K_FREEARR_MAX ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true) -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdrain_ret L RNG sp st c cnt mc csz lo chunks m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ensure_free_array st c (nf + half) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdrain_entry) fc None m (seg_rom asegs)).
Proof. exact cdrain_spec__body. Qed.
End CANSEC2.
End TwB.
End F_acdrain.
