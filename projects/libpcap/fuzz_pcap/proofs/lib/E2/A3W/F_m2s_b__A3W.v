(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ShadowTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_m2s_b.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition m2sb_entry := 0x3f748%Z.

End CANSEC1.
Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_lits :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a <? b)%Z) in change (Z.b2z (a <? b)%Z) with v
  | |- context [Z.b2z (?a =? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a =? b)%Z) in change (Z.b2z (a =? b)%Z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  end.

Section CANSEC2. Context {rc : runConstT}.
Definition m2sb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t1 t2 t3 t4 t5 t6 : word) (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (shad (bv_unsigned a0))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

#[using="Type"] Lemma m2sb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  rt_got m -> rt_shbase m -> rt_layout m ->
  ((bv_unsigned a0 + 1 <= KLOW) \/ (KHIGH <= bv_unsigned a0 /\ bv_unsigned a0 + 1 <= KEND))%Z ->
  rng_aimg RNG ->
  evtF asegs RNG (m2sb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t1 t2 t3 t4 t5 t6 a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f748) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI GOT SHB LAY APP RI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold KLOW, KHIGH, KEND in APP.
  do 5 zstep. fold_lits. zsimp. do 3 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep. finish.
  - do 7 zstep. fold_lits. zsimp. zstep.
    if_cases K2; zify_cond K2. 2: { exfalso; lia. }
    do 6 zstep.
    if_cases K3; zify_cond K3. { exfalso; lia. }
    zstep.
    if_cases K4; zify_cond K4. { exfalso; lia. }
    do 3 zstep.
    finish.
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition m2sb_entry := 0x3f7b0%Z.

End CANSEC1.
Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_lits :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a <? b)%Z) in change (Z.b2z (a <? b)%Z) with v
  | |- context [Z.b2z (?a =? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a =? b)%Z) in change (Z.b2z (a =? b)%Z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  end.

Section CANSEC2. Context {rc : runConstT}.
Definition m2sb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t1 t2 t3 t4 t5 t6 : word) (a0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (shad (bv_unsigned a0))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

#[using="Type"] Lemma m2sb_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv asegs m ->
  rt_got m -> rt_shbase m -> rt_layout m ->
  ((bv_unsigned a0 + 1 <= KLOW) \/ (KHIGH <= bv_unsigned a0 /\ bv_unsigned a0 + 1 <= KEND))%Z ->
  rng_aimg RNG ->
  evtF asegs RNG (m2sb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t1 t2 t3 t4 t5 t6 a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f7b0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI GOT SHB LAY APP RI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold KLOW, KHIGH, KEND in APP.
  do 5 zstep. fold_lits. zsimp. do 3 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep. finish.
  - do 7 zstep. fold_lits. zsimp. zstep.
    if_cases K2; zify_cond K2. 2: { exfalso; lia. }
    do 6 zstep.
    if_cases K3; zify_cond K3. { exfalso; lia. }
    zstep.
    if_cases K4; zify_cond K4. { exfalso; lia. }
    do 3 zstep.
    finish.
Qed.
End CANSEC2.
End TwB.
End F_m2s_b.

(* [comment removed for export] *)
Module F_irt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ShadowTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
(* [comment removed for export] *) From Ltac2 Require Ltac2.
#[local] Ltac2 Set StepFast.sf_fold_goal := Ltac2.Init.false.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition istrlen_entry := 0x67bec%Z.
Definition istrchr_entry := 0x67b4c%Z.
Definition imemset_entry := 0x67a98%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition istrlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Section Strlen.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str : list byte) (rest : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis RR : rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation POST := (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 str m).

  #[using="rest MI STR NOZ RR"] Lemma istrlen_loop : forall (k : nat) (i : Z) x12,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 i) x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67bf0) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    induction k as [|k IH]; intros i x12 Hk Hi.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m A _ len (Z_to_bv 8 0) _ STR ltac:(rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity) ltac:(lia) eq_refl) as RD.
      do 2 zstep. cbv beta. zsimp. fold_lits. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear - K. cbv in K. lia. }
      zstep. zstep. unfold istrlen_post. finish.
    - destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
      assert (Hb : bv_unsigned b <> 0%Z). { rewrite Forall_forall in NOZ. apply NOZ. eapply nth_error_In; eauto. }
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
      pose proof (u8ro_read asegs m A _ i b _ STR ltac:(rewrite nth_error_app1 by lia; exact E) ltac:(lia) eq_refl) as RD.
      do 2 zstep. cbv beta. zsimp. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
      apply IH; lia.
  Qed.

  #[using="rest MI STR NOZ RR"] Lemma istrlen_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67bec) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    zstep. apply (istrlen_loop (Z.to_nat len) 0); lia.
  Qed.
End Strlen.

#[using="Type"] Lemma istrlen_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str rest : list byte),
  mem_inv asegs m ->
  bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest) ->
  Forall (fun b : byte => bv_unsigned b <> 0%Z) str ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
  evtF asegs RNG (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 str m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67bec) fc None m (seg_rom asegs)).
Proof. intros. eapply istrlen_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint find_byte (c : Z) (l : list byte) : option nat :=
  match l with
  | [] => None
  | b :: l' => if (bv_unsigned b =? c)%Z then Some 0%nat else option_map S (find_byte c l')
  end.

Definition istrchr_res (A : Z) (str : list byte) (c : Z) : Z :=
  match find_byte c str with Some i => (A + Z.of_nat i)%Z | None => 0%Z end.

#[using="Type"] Lemma find_byte_Some : forall c l i, find_byte c l = Some i ->
  (i < length l)%nat /\ (exists b, nth_error l i = Some b /\ bv_unsigned b = c) /\
  forall j b, (j < i)%nat -> nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l. induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec (bv_unsigned b) c).
  - injection H as <-. cbn. split; [lia|]. split; [eauto|]. intros; lia.
  - destruct (find_byte c l) as [i0|] eqn:E; cbn in H; [|discriminate]. injection H as <-.
    (nd_pre (IH i0 eq_refl) 3%nat; intros L (b0 & Hn & Hc) NO; nd_post). cbn. split; [lia|]. split; [eauto|].
    intros [|j] b' Hj Hn'; cbn in Hn'. { injection Hn' as <-. exact n. } eapply NO; [|exact Hn']. lia.
Qed.

#[using="Type"] Lemma find_byte_None : forall c l, find_byte c l = None -> forall j b, nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l. induction l as [|b l IH]; intros H j b' Hn; [destruct j; discriminate|].
  cbn in H. destruct (Z.eqb_spec (bv_unsigned b) c); [discriminate|].
  destruct (find_byte c l) eqn:E; [discriminate|].
  destruct j as [|j]; cbn in Hn. { injection Hn as <-. exact n. } eapply IH; eauto.
Qed.

Definition istrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : Z) (str : list byte) (c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (istrchr_res A str c)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Section Strchr.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str : list byte) (rest : list byte) (c : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis C : a1 = Z_to_bv 64 c.
  Hypothesis CR : (0 < c < 256)%Z.
  Hypothesis RR : rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ (Z_to_bv 8 0) :: rest).
  Notation POST := (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) str c m).

  #[using="NOZ"] Lemma full_nth : forall i, (0 <= i <= len)%Z -> exists b, nth_error full (Z.to_nat i) = Some b /\
     (i < len -> nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0)%Z /\ (i = len -> b = Z_to_bv 8 0).
  Proof.
    intros i Hi. destruct (Z.eq_dec i len) as [->|].
    - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. cbn. split; [reflexivity|]. split; [lia| auto].
    - destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
      exists b. rewrite nth_error_app1 by lia. split; [exact E|]. split; [|lia]. intros _. split; [reflexivity|].
      rewrite Forall_forall in NOZ. apply NOZ. eapply nth_error_In; eauto.
  Qed.

  (* [comment removed for export] *)
  #[using="MI STR NOZ CR RR"] Lemma istrchr_loop : forall (k : nat) (i : Z) (b : byte) x10 x11,
    x10 = Z_to_bv 64 (A + i) ->
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z ->
    nth_error full (Z.to_nat i) = Some b -> bv_unsigned b <> c ->
    (forall j b', (j <= Z.to_nat i)%nat -> nth_error str j = Some b' -> bv_unsigned b' <> c) ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 c) (Z_to_bv 64 (bv_unsigned b)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67b5c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    induction k as [|k IH]; intros i b x10 x11 -> Hk Hi Hn Hc NO.
    - assert (Ei : i = len) by lia. subst i.
      rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag in Hn by lia. cbn in Hn. injection Hn as <-.
      zstep. if_cases K; zify_cond K. 2:{ exfalso. clear - K. cbv in K. lia. }
      zstep. zstep. unfold istrchr_post, istrchr_res.
      destruct (find_byte c str) as [i0|] eqn:FB.
      { exfalso. (nd_pre (find_byte_Some _ _ _ FB) 3%nat; intros L (b0 & Hb0 & Hc0) _; nd_post). eapply NO; [|exact Hb0| exact Hc0]. lia. }
      finish.
    - (nd_pre (full_nth i ltac:(lia)) 4%nat; intros b0 Hn0 Hlt _; nd_post). rewrite Hn in Hn0. injection Hn0 as <-.
      destruct (Hlt ltac:(lia)) as [Hstr Hb0].
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
      zstep. if_cases K; zify_cond K. { exfalso. lia. }
      (nd_pre (full_nth (i + 1) ltac:(lia)) 4%nat; intros b1 Hn1 Hlt1 Heq1; nd_post).
      pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb1.
      pose proof (u8ro_read asegs m A _ (i + 1) b1 _ STR Hn1 ltac:(lia) eq_refl) as RD.
      zstep. cbv beta. zsimp. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        apply (IH (i + 1)%Z b1); [f_equal; lia | lia | lia | assumption | lia |].
        intros j b' Hj Hn'. destruct (Nat.eq_dec j (Z.to_nat (i + 1))).
        * subst j. destruct (Z.eq_dec (i + 1) len) as [E|].
          { exfalso. apply nth_error_some_bound in Hn'. lia. } 
          destruct (Hlt1 ltac:(lia)) as [Hs1 _]. rewrite Hs1 in Hn'. injection Hn' as <-. lia.
        * eapply NO; [|exact Hn']. lia.
      + (* [comment removed for export] *)
        zstep. zstep. unfold istrchr_post, istrchr_res.
        assert (FB : find_byte c str = Some (Z.to_nat (i + 1))).
        { destruct (find_byte c str) as [i0|] eqn:FB.
          - (nd_pre (find_byte_Some _ _ _ FB) 3%nat; intros L (bb & Hbb & Hcc) NOi; nd_post).
            destruct (Nat.lt_trichotomy i0 (Z.to_nat (i + 1))) as [Hl|[He|Hg]].
            + exfalso. eapply NO; [|exact Hbb|exact Hcc]. lia.
            + rewrite He. reflexivity.
            + exfalso. destruct (Z.eq_dec (i + 1) len) as [E|].
              { lia. }
              destruct (Hlt1 ltac:(lia)) as [Hs1 _]. eapply NOi; [exact Hg| exact Hs1| lia].
          - exfalso. destruct (Z.eq_dec (i + 1) len) as [E|].
            { rewrite (Heq1 E) in K2. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in K2. lia. }
            destruct (Hlt1 ltac:(lia)) as [Hs1 _]. eapply (find_byte_None _ _ FB); [exact Hs1| lia]. }
        rewrite FB. replace (A + Z.of_nat (Z.to_nat (i + 1)))%Z with (A + i + 1)%Z by lia. finish.
  Qed.

  #[using="rest MI STR NOZ C CR RR"] Lemma istrchr_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67b4c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. subst a1.
    (nd_pre (full_nth 0 ltac:(lia)) 4%nat; intros b0 Hn0 Hlt0 Heq0; nd_post).
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb0.
    pose proof (u8ro_read asegs m A _ 0 b0 _ STR Hn0 ltac:(lia) eq_refl) as RD.
    replace (wa (A + 0)) with a0 in RD by (unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
    zstep. cbv beta. zsimp. zstep.
    replace (Z.land c 255) with c by (change 255%Z with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    zstep. if_cases K; zify_cond K.
    - eapply (istrchr_loop (Z.to_nat len) 0 b0); [rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | exact Hn0 | lia |].
      intros j b' Hj Hn'. assert (j = 0%nat) by lia. subst j.
      destruct (Z.eq_dec 0 len) as [E|]. { exfalso. apply nth_error_some_bound in Hn'. lia. }
      destruct (Hlt0 ltac:(lia)) as [Hs _]. change (Z.to_nat 0) with 0%nat in Hs. rewrite Hs in Hn'. injection Hn' as <-. lia.
    - zstep. unfold istrchr_post, istrchr_res.
      assert (FB : find_byte c str = Some 0%nat).
      { destruct (Z.eq_dec 0 len) as [E|]. { rewrite (Heq0 E) in K. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in K. lia. }
        destruct (Hlt0 ltac:(lia)) as [Hs _]. destruct str as [|bb l]; [discriminate|]. cbn in Hs. injection Hs as ->.
        cbn. rewrite (proj2 (Z.eqb_eq _ _) K). reflexivity. }
      rewrite FB. cbn [Z.of_nat]. rewrite Z.add_0_r.
      replace (Z_to_bv 64 A) with a0 by (symmetry; apply Z_to_bv_bv_unsigned). finish.
  Qed.
End Strchr.

#[using="Type"] Lemma istrchr_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str rest : list byte) (c : Z),
  mem_inv asegs m ->
  bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest) ->
  Forall (fun b : byte => bv_unsigned b <> 0%Z) str ->
  a1 = Z_to_bv 64 c -> (0 < c < 256)%Z ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
  evtF asegs RNG (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) str c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67b4c) fc None m (seg_rom asegs)).
Proof. intros. eapply istrchr_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma list_all_repeat : forall {X} (l : list X) (x : X) k,
  length l = k -> (forall j, (j < k)%nat -> nth_error l j = Some x) -> l = repeat x k.
Proof.
  intros X l x k Hl H. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j k).
  - rewrite H, nth_error_repeat by lia. reflexivity.
  - rewrite (proj2 (nth_error_None l j)) by lia. rewrite (proj2 (nth_error_None _ j)) by (rewrite repeat_length; lia). reflexivity.
Qed.

#[using="Type"] Lemma lor_land15_ne : forall n x, (0 <= n)%Z -> (0 <= x)%Z -> Z.land n 15 <> 0%Z -> Z.land (Z.lor n x) 15 <> 0%Z.
Proof.
  intros n x Hn Hx H. rewrite Z.land_lor_distr_l. intros E. apply Z.lor_eq_0_iff in E. lia.
Qed.

Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' (bv_unsigned a0) (repeat (Z_to_bv 8 (bv_unsigned a1)) (Z.to_nat n)).

Section Memset.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (junk : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis DST : u8arr asegs m (bv_unsigned a0) junk.
  Hypothesis LEN : length junk = Z.to_nat n.
  Hypothesis N : a2 = Z_to_bv 64 n.
  Hypothesis NR : (1 <= n)%Z.
  Hypothesis NB : (bv_unsigned a0 + n < 2^64)%Z.
  Hypothesis BYTEPATH : Z.land n 15 <> 0%Z.
  Hypothesis RR : rng RNG (bv_unsigned a0) n.
  Notation D := (bv_unsigned a0).
  Notation cb := (Z_to_bv 8 (bv_unsigned a1)).
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 m n).

  (* [comment removed for export] *)
  #[using="junk DST LEN NR NB RR"] Lemma imemset_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
    u8arr asegs mc D bs -> length bs = Z.to_nat n -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = Some cb) ->
    munch [(D, D + n)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67ab0) fc None mc (seg_rom asegs)).
  Proof.
    pose proof (u8arr_bound _ _ _ _ DST) as AB. rewrite LEN in AB.
    induction k as [|k IH]; intros i mc bs Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
    pose proof (u8arr_store_ok asegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write asegs mc D bs i cb ARR ltac:(rewrite LBS; lia)) as ARR'.
    change (le1 a1) with [cb].
    store_done.
    zstep. zstep. if_cases K; zify_cond K.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite upd_length; exact LBS | | assumption | assumption | assumption].
      intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
      + subst j. rewrite nth_error_upd_same by (rewrite LBS; lia). reflexivity.
      + rewrite nth_error_upd_other by lia. apply DONE. lia.
    - zstep. zstep. unfold imemset_post.
      assert (E : upd bs (Z.to_nat i) cb = repeat cb (Z.to_nat n)).
      { apply list_all_repeat. { rewrite upd_length; exact LBS. }
        intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        + subst j. rewrite nth_error_upd_same by (rewrite LBS; lia). reflexivity.
        + rewrite nth_error_upd_other by lia. apply DONE. lia. }
      rewrite E in ARR'. finish.
  Qed.

  #[using="junk MI DST LEN N NR NB BYTEPATH RR"] Lemma imemset_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67a98) fc None m (seg_rom asegs)).
  Proof.
    pose proof (u8arr_bound _ _ _ _ DST) as AB. rewrite LEN in AB.
    pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. subst a2.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    { exfalso. apply (lor_land15_ne n D); try lia; first [exact K | rewrite Z.lor_comm; exact K]. }
    zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. zstep.
    replace a0 with (Z_to_bv 64 (D + 0)) at 2 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
    eapply (imemset_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
  Qed.
End Memset.


#[using="Type"] Lemma imemset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : Z) (junk : list byte),
  mem_inv asegs m ->
  u8arr asegs m (bv_unsigned a0) junk -> length junk = Z.to_nat n ->
  a2 = Z_to_bv 64 n -> (1 <= n)%Z -> (bv_unsigned a0 + n < 2^64)%Z -> Z.land n 15 <> 0%Z ->
  rng RNG (bv_unsigned a0) n ->
  evtF asegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 m n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a98) fc None m (seg_rom asegs)).
Proof. intros. eapply imemset_body; eassumption. Qed.

(* [comment removed for export] *)
Definition imemset_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (D n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' D (repeat (Z_to_bv 8 (bv_unsigned a1)) (Z.to_nat n)).

#[using="Type"] Lemma imemset_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D n : Z) (junk : list byte),
  mem_inv asegs m ->
  u8arr asegs m D junk -> length junk = Z.to_nat n ->
  (1 <= n)%Z -> (0 <= D)%Z -> (D + n < 2^64)%Z -> Z.land n 15 <> 0%Z ->
  rng RNG D n ->
  evtF asegs RNG (imemset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 m D n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67a98) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI DST LEN NR D0 NB BP RR.
  assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  { eapply (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n junk);
      rewrite ?U; try eassumption; try reflexivity; lia. }
  intros ms' P. unfold imemset_post in P. rewrite !U in P. exact P.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition istrlen_entry := 0x67c54%Z.
Definition istrchr_entry := 0x67bb4%Z.
Definition imemset_entry := 0x67b00%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition istrlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Section Strlen.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str : list byte) (rest : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis RR : rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation POST := (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 str m).

  #[using="rest MI STR NOZ RR"] Lemma istrlen_loop : forall (k : nat) (i : Z) x12,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 i) x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67c58) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    induction k as [|k IH]; intros i x12 Hk Hi.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m A _ len (Z_to_bv 8 0) _ STR ltac:(rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity) ltac:(lia) eq_refl) as RD.
      do 2 zstep. cbv beta. zsimp. fold_lits. zstep. zstep. if_cases K; zify_cond K. { exfalso. clear - K. cbv in K. lia. }
      zstep. zstep. unfold istrlen_post. finish.
    - destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
      assert (Hb : bv_unsigned b <> 0%Z). { rewrite Forall_forall in NOZ. apply NOZ. eapply nth_error_In; eauto. }
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
      pose proof (u8ro_read asegs m A _ i b _ STR ltac:(rewrite nth_error_app1 by lia; exact E) ltac:(lia) eq_refl) as RD.
      do 2 zstep. cbv beta. zsimp. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
      apply IH; lia.
  Qed.

  #[using="rest MI STR NOZ RR"] Lemma istrlen_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67c54) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    zstep. apply (istrlen_loop (Z.to_nat len) 0); lia.
  Qed.
End Strlen.

#[using="Type"] Lemma istrlen_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str rest : list byte),
  mem_inv asegs m ->
  bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest) ->
  Forall (fun b : byte => bv_unsigned b <> 0%Z) str ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
  evtF asegs RNG (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 str m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67c54) fc None m (seg_rom asegs)).
Proof. intros. eapply istrlen_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint find_byte (c : Z) (l : list byte) : option nat :=
  match l with
  | [] => None
  | b :: l' => if (bv_unsigned b =? c)%Z then Some 0%nat else option_map S (find_byte c l')
  end.

Definition istrchr_res (A : Z) (str : list byte) (c : Z) : Z :=
  match find_byte c str with Some i => (A + Z.of_nat i)%Z | None => 0%Z end.

#[using="Type"] Lemma find_byte_Some : forall c l i, find_byte c l = Some i ->
  (i < length l)%nat /\ (exists b, nth_error l i = Some b /\ bv_unsigned b = c) /\
  forall j b, (j < i)%nat -> nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l. induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec (bv_unsigned b) c).
  - injection H as <-. cbn. split; [lia|]. split; [eauto|]. intros; lia.
  - destruct (find_byte c l) as [i0|] eqn:E; cbn in H; [|discriminate]. injection H as <-.
    (nd_pre (IH i0 eq_refl) 3%nat; intros L (b0 & Hn & Hc) NO; nd_post). cbn. split; [lia|]. split; [eauto|].
    intros [|j] b' Hj Hn'; cbn in Hn'. { injection Hn' as <-. exact n. } eapply NO; [|exact Hn']. lia.
Qed.

#[using="Type"] Lemma find_byte_None : forall c l, find_byte c l = None -> forall j b, nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
  intros c l. induction l as [|b l IH]; intros H j b' Hn; [destruct j; discriminate|].
  cbn in H. destruct (Z.eqb_spec (bv_unsigned b) c); [discriminate|].
  destruct (find_byte c l) eqn:E; [discriminate|].
  destruct j as [|j]; cbn in Hn. { injection Hn as <-. exact n. } eapply IH; eauto.
Qed.

Definition istrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : Z) (str : list byte) (c : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (istrchr_res A str c)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Section Strchr.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str : list byte) (rest : list byte) (c : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) str.
  Hypothesis C : a1 = Z_to_bv 64 c.
  Hypothesis CR : (0 < c < 256)%Z.
  Hypothesis RR : rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ (Z_to_bv 8 0) :: rest).
  Notation POST := (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) str c m).

  #[using="NOZ"] Lemma full_nth : forall i, (0 <= i <= len)%Z -> exists b, nth_error full (Z.to_nat i) = Some b /\
     (i < len -> nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0)%Z /\ (i = len -> b = Z_to_bv 8 0).
  Proof.
    intros i Hi. destruct (Z.eq_dec i len) as [->|].
    - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. cbn. split; [reflexivity|]. split; [lia| auto].
    - destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E. 2:{ apply nth_error_None in E. lia. }
      exists b. rewrite nth_error_app1 by lia. split; [exact E|]. split; [|lia]. intros _. split; [reflexivity|].
      rewrite Forall_forall in NOZ. apply NOZ. eapply nth_error_In; eauto.
  Qed.

  (* [comment removed for export] *)
  #[using="MI STR NOZ CR RR"] Lemma istrchr_loop : forall (k : nat) (i : Z) (b : byte) x10 x11,
    x10 = Z_to_bv 64 (A + i) ->
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z ->
    nth_error full (Z.to_nat i) = Some b -> bv_unsigned b <> c ->
    (forall j b', (j <= Z.to_nat i)%nat -> nth_error str j = Some b' -> bv_unsigned b' <> c) ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 c) (Z_to_bv 64 (bv_unsigned b)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67bc4) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    induction k as [|k IH]; intros i b x10 x11 -> Hk Hi Hn Hc NO.
    - assert (Ei : i = len) by lia. subst i.
      rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag in Hn by lia. cbn in Hn. injection Hn as <-.
      zstep. if_cases K; zify_cond K. 2:{ exfalso. clear - K. cbv in K. lia. }
      zstep. zstep. unfold istrchr_post, istrchr_res.
      destruct (find_byte c str) as [i0|] eqn:FB.
      { exfalso. (nd_pre (find_byte_Some _ _ _ FB) 3%nat; intros L (b0 & Hb0 & Hc0) _; nd_post). eapply NO; [|exact Hb0| exact Hc0]. lia. }
      finish.
    - (nd_pre (full_nth i ltac:(lia)) 4%nat; intros b0 Hn0 Hlt _; nd_post). rewrite Hn in Hn0. injection Hn0 as <-.
      destruct (Hlt ltac:(lia)) as [Hstr Hb0].
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb.
      zstep. if_cases K; zify_cond K. { exfalso. lia. }
      (nd_pre (full_nth (i + 1) ltac:(lia)) 4%nat; intros b1 Hn1 Hlt1 Heq1; nd_post).
      pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb1.
      pose proof (u8ro_read asegs m A _ (i + 1) b1 _ STR Hn1 ltac:(lia) eq_refl) as RD.
      zstep. cbv beta. zsimp. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        apply (IH (i + 1)%Z b1); [f_equal; lia | lia | lia | assumption | lia |].
        intros j b' Hj Hn'. destruct (Nat.eq_dec j (Z.to_nat (i + 1))).
        * subst j. destruct (Z.eq_dec (i + 1) len) as [E|].
          { exfalso. apply nth_error_some_bound in Hn'. lia. } 
          destruct (Hlt1 ltac:(lia)) as [Hs1 _]. rewrite Hs1 in Hn'. injection Hn' as <-. lia.
        * eapply NO; [|exact Hn']. lia.
      + (* [comment removed for export] *)
        zstep. zstep. unfold istrchr_post, istrchr_res.
        assert (FB : find_byte c str = Some (Z.to_nat (i + 1))).
        { destruct (find_byte c str) as [i0|] eqn:FB.
          - (nd_pre (find_byte_Some _ _ _ FB) 3%nat; intros L (bb & Hbb & Hcc) NOi; nd_post).
            destruct (Nat.lt_trichotomy i0 (Z.to_nat (i + 1))) as [Hl|[He|Hg]].
            + exfalso. eapply NO; [|exact Hbb|exact Hcc]. lia.
            + rewrite He. reflexivity.
            + exfalso. destruct (Z.eq_dec (i + 1) len) as [E|].
              { lia. }
              destruct (Hlt1 ltac:(lia)) as [Hs1 _]. eapply NOi; [exact Hg| exact Hs1| lia].
          - exfalso. destruct (Z.eq_dec (i + 1) len) as [E|].
            { rewrite (Heq1 E) in K2. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in K2. lia. }
            destruct (Hlt1 ltac:(lia)) as [Hs1 _]. eapply (find_byte_None _ _ FB); [exact Hs1| lia]. }
        rewrite FB. replace (A + Z.of_nat (Z.to_nat (i + 1)))%Z with (A + i + 1)%Z by lia. finish.
  Qed.

  #[using="rest MI STR NOZ C CR RR"] Lemma istrchr_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67bb4) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM. subst a1.
    (nd_pre (full_nth 0 ltac:(lia)) 4%nat; intros b0 Hn0 Hlt0 Heq0; nd_post).
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0. change (2 ^ Z.of_N 8)%Z with 256%Z in Rb0.
    pose proof (u8ro_read asegs m A _ 0 b0 _ STR Hn0 ltac:(lia) eq_refl) as RD.
    replace (wa (A + 0)) with a0 in RD by (unfold wa; rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned).
    zstep. cbv beta. zsimp. zstep.
    replace (Z.land c 255) with c by (change 255%Z with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    zstep. if_cases K; zify_cond K.
    - eapply (istrchr_loop (Z.to_nat len) 0 b0); [rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | exact Hn0 | lia |].
      intros j b' Hj Hn'. assert (j = 0%nat) by lia. subst j.
      destruct (Z.eq_dec 0 len) as [E|]. { exfalso. apply nth_error_some_bound in Hn'. lia. }
      destruct (Hlt0 ltac:(lia)) as [Hs _]. change (Z.to_nat 0) with 0%nat in Hs. rewrite Hs in Hn'. injection Hn' as <-. lia.
    - zstep. unfold istrchr_post, istrchr_res.
      assert (FB : find_byte c str = Some 0%nat).
      { destruct (Z.eq_dec 0 len) as [E|]. { rewrite (Heq0 E) in K. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in K. lia. }
        destruct (Hlt0 ltac:(lia)) as [Hs _]. destruct str as [|bb l]; [discriminate|]. cbn in Hs. injection Hs as ->.
        cbn. rewrite (proj2 (Z.eqb_eq _ _) K). reflexivity. }
      rewrite FB. cbn [Z.of_nat]. rewrite Z.add_0_r.
      replace (Z_to_bv 64 A) with a0 by (symmetry; apply Z_to_bv_bv_unsigned). finish.
  Qed.
End Strchr.

#[using="Type"] Lemma istrchr_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str rest : list byte) (c : Z),
  mem_inv asegs m ->
  bytes_at asegs m (bv_unsigned a0) (str ++ (Z_to_bv 8 0) :: rest) ->
  Forall (fun b : byte => bv_unsigned b <> 0%Z) str ->
  a1 = Z_to_bv 64 c -> (0 < c < 256)%Z ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
  evtF asegs RNG (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned a0) str c m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67bb4) fc None m (seg_rom asegs)).
Proof. intros. eapply istrchr_body; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma list_all_repeat : forall {X} (l : list X) (x : X) k,
  length l = k -> (forall j, (j < k)%nat -> nth_error l j = Some x) -> l = repeat x k.
Proof.
  intros X l x k Hl H. apply nth_error_ext. intros j.
  destruct (Nat.lt_ge_cases j k).
  - rewrite H, nth_error_repeat by lia. reflexivity.
  - rewrite (proj2 (nth_error_None l j)) by lia. rewrite (proj2 (nth_error_None _ j)) by (rewrite repeat_length; lia). reflexivity.
Qed.

#[using="Type"] Lemma lor_land15_ne : forall n x, (0 <= n)%Z -> (0 <= x)%Z -> Z.land n 15 <> 0%Z -> Z.land (Z.lor n x) 15 <> 0%Z.
Proof.
  intros n x Hn Hx H. rewrite Z.land_lor_distr_l. intros E. apply Z.lor_eq_0_iff in E. lia.
Qed.

Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' (bv_unsigned a0) (repeat (Z_to_bv 8 (bv_unsigned a1)) (Z.to_nat n)).

Section Memset.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (junk : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis DST : u8arr asegs m (bv_unsigned a0) junk.
  Hypothesis LEN : length junk = Z.to_nat n.
  Hypothesis N : a2 = Z_to_bv 64 n.
  Hypothesis NR : (1 <= n)%Z.
  Hypothesis NB : (bv_unsigned a0 + n < 2^64)%Z.
  Hypothesis BYTEPATH : Z.land n 15 <> 0%Z.
  Hypothesis RR : rng RNG (bv_unsigned a0) n.
  Notation D := (bv_unsigned a0).
  Notation cb := (Z_to_bv 8 (bv_unsigned a1)).
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 m n).

  (* [comment removed for export] *)
  #[using="junk DST LEN NR NB RR"] Lemma imemset_loop : forall (k : nat) (i : Z) (mc : word -> option byte) (bs : list byte),
    Z.to_nat (n - i) = k -> (0 <= i < n)%Z ->
    u8arr asegs mc D bs -> length bs = Z.to_nat n -> (forall j, (j < Z.to_nat i)%nat -> nth_error bs j = Some cb) ->
    munch [(D, D + n)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (D + i)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67b18) fc None mc (seg_rom asegs)).
  Proof.
    pose proof (u8arr_bound _ _ _ _ DST) as AB. rewrite LEN in AB.
    induction k as [|k IH]; intros i mc bs Hk Hi ARR LBS DONE MU WM MI1; [exfalso; lia|].
    pose proof (u8arr_store_ok asegs mc D bs i (wa (D + i)) ARR ltac:(rewrite LBS; lia) eq_refl) as SOK.
    zstep.
    pose proof (u8arr_write asegs mc D bs i cb ARR ltac:(rewrite LBS; lia)) as ARR'.
    change (le1 a1) with [cb].
    store_done.
    zstep. zstep. if_cases K; zify_cond K.
    - replace (D + i + 1)%Z with (D + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [lia | lia | exact ARR' | rewrite upd_length; exact LBS | | assumption | assumption | assumption].
      intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
      + subst j. rewrite nth_error_upd_same by (rewrite LBS; lia). reflexivity.
      + rewrite nth_error_upd_other by lia. apply DONE. lia.
    - zstep. zstep. unfold imemset_post.
      assert (E : upd bs (Z.to_nat i) cb = repeat cb (Z.to_nat n)).
      { apply list_all_repeat. { rewrite upd_length; exact LBS. }
        intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)).
        + subst j. rewrite nth_error_upd_same by (rewrite LBS; lia). reflexivity.
        + rewrite nth_error_upd_other by lia. apply DONE. lia. }
      rewrite E in ARR'. finish.
  Qed.

  #[using="junk MI DST LEN N NR NB BYTEPATH RR"] Lemma imemset_body :
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x67b00) fc None m (seg_rom asegs)).
  Proof.
    pose proof (u8arr_bound _ _ _ _ DST) as AB. rewrite LEN in AB.
    pose proof (munch_refl [(D, D + n)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. subst a2.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    { exfalso. apply (lor_land15_ne n D); try lia; first [exact K | rewrite Z.lor_comm; exact K]. }
    zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. zstep.
    replace a0 with (Z_to_bv 64 (D + 0)) at 2 by (rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
    eapply (imemset_loop (Z.to_nat n) 0 m junk); try assumption; try lia.
  Qed.
End Memset.


#[using="Type"] Lemma imemset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : Z) (junk : list byte),
  mem_inv asegs m ->
  u8arr asegs m (bv_unsigned a0) junk -> length junk = Z.to_nat n ->
  a2 = Z_to_bv 64 n -> (1 <= n)%Z -> (bv_unsigned a0 + n < 2^64)%Z -> Z.land n 15 <> 0%Z ->
  rng RNG (bv_unsigned a0) n ->
  evtF asegs RNG (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a0 a1 a4 a5 a6 a7 t3 t4 t5 t6 m n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67b00) fc None m (seg_rom asegs)).
Proof. intros. eapply imemset_body; eassumption. Qed.

(* [comment removed for export] *)
Definition imemset_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (D n : Z) : machine_state -> Prop :=
  fun ms' => exists a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' D (repeat (Z_to_bv 8 (bv_unsigned a1)) (Z.to_nat n)).

#[using="Type"] Lemma imemset_specZ : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D n : Z) (junk : list byte),
  mem_inv asegs m ->
  u8arr asegs m D junk -> length junk = Z.to_nat n ->
  (1 <= n)%Z -> (0 <= D)%Z -> (D + n < 2^64)%Z -> Z.land n 15 <> 0%Z ->
  rng RNG D n ->
  evtF asegs RNG (imemset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a1 a4 a5 a6 a7 t3 t4 t5 t6 m D n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x67b00) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI DST LEN NR D0 NB BP RR.
  assert (U : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evtF_mono.
  { eapply (imemset_body RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n junk);
      rewrite ?U; try eassumption; try reflexivity; lia. }
  intros ms' P. unfold imemset_post in P. rewrite !U in P. exact P.
Qed.
End CANSEC1.
End TwB.
End F_irt.

(* [comment removed for export] *)
Module F_tryinit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg RtCells ShadowTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition tryinit_entry := 0x5d608%Z.

Definition tryinit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rt_inited m'.

#[using="Type"] Lemma tryinit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (KHIGH <= lo)%Z ->
  rt_inited m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (tryinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d608) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO INI RI RSTK.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
  carve_frame 16%nat ST.
  do 5 zstep. fold_lits. zstep. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep.
  zstep. if_cases K; zify_cond K. { exfalso. clear - K. cbv in K. lia. }
  do 4 zstep. release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Section CANSEC1. Context {rc : runConstT}.
Definition tryinit_entry := 0x5d670%Z.

Definition tryinit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rt_inited m'.

#[using="Type"] Lemma tryinit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (KHIGH <= lo)%Z ->
  rt_inited m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (tryinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5d670) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ST LO KLO INI RI RSTK.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
  carve_frame 16%nat ST.
  do 5 zstep. fold_lits. zstep. rewrite sxb_sval. change (sval (Z_to_bv 8 1)) with 1%Z. zstep. zstep.
  zstep. if_cases K; zify_cond K. { exfalso. clear - K. cbv in K. lia. }
  do 4 zstep. release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.
End TwB.
End F_tryinit.

(* [comment removed for export] *)
Module I_asan_memset.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac easm2 := first [ lazymatch goal with |- rw_cells ?s _ ?A _ => match goal with H : rw_cells s _ A _ |- _ => exact H end end
                          | eassumption ].
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
(* [comment removed for export] *)
Local Ltac solve_acc_shadow H ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        first [ solve [ zify_prune; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]
      end
  end.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

(* [comment removed for export] *)
Local Lemma rw_cells_app_fr : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1))%Z cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    (nd_pre WR 3%nat; intros HA HN HW; nd_post).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition asan_memset_entry := 0x54e00%Z.

Definition asan_memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (junk : list byte) (RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2128)
                  [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2128)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
    /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.

  #[using="m ST LO KLO APPD NSZ R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LED AD R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].   (* [comment removed for export] *)
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
  #[using="m ST LO KLO APPD NSZ R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    (nd_pre H 13%nat; intros (jk & FR) ST1 MU1 WM1 MI1 GOT1 RIC1 SHB1 INI1 LAY1 REAL1 UD1 WR21; nd_post).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  #[using="ST LO KLO APPD UDST NSZ R2 WR2"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2128) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x54e90) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    zstep. zstep. zstep.
    unfold sf_hide in SEPD.
    apply (munch_weaken _ [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR21.
    call memset_spec; [exact DST1 | exact MI1 |].
    do 10 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x21 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x54fbc) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; easm2.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x21 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
               (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x54fa0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    (nd_pre (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) 3%nat; intros b2 RD2 CK2; nd_post).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; easm2.
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma LB : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x54e38) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      do 5 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv_of; easm2.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; easm2.
      + eapply LX; exact IV0.
  Qed.

  #[using="junk RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma asan_memset_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x54e00) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    change (?P) with (sf_hide P) in DST.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    carve_frame 2128%nat ST0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk0] =>
      apply (rw_cells_split_CB asegs m _ [] 2128 jk0 [] [2072%nat; 56%nat]) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR;
      set (jk1 := firstn 2072 jk0) in FR; set (jk2 := firstn 56 (skipn 2072 jk0)) in FR; clearbody jk1 jk2; clear jk0 end.
    change [CB 2072 jk1; CB 56 jk2] with ([CB 2072 jk1] ++ [CB 56 jk2]) in FR.
    apply rw_cells_app_fr in FR. destruct FR as [FR FR2].
    change (Z.of_nat (cells_size [CB 2072 jk1])) with 2072%Z in FR2.
    replace (bv_unsigned sp + -2128 + 2072)%Z with (bv_unsigned sp + -56)%Z in FR2 by lia.
    do 10 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -2128) [CB 2072 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -56) ?cs |- _ =>
      assert (FRJ : rw_cells asegs mm (bv_unsigned sp + -2128) ([CB 2072 j] ++ cs))
        by (apply rw_cells_app_fr; split; [exact H1 | change (Z.of_nat (cells_size [CB 2072 j])) with 2072%Z;
                                                     replace (bv_unsigned sp + -2128 + 2072)%Z with (bv_unsigned sp + -56)%Z by lia; exact H2]);
      cbn [app] in FRJ; clear H1 H2; rename FRJ into FR end.
    eapply LB. eapply inv_of; easm2.
  Qed.
End Proofs.

#[using="Type"] Lemma asan_memset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54e00) fc None m (seg_rom asegs)).
Proof. intros. eapply asan_memset_body; eassumption. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac easm2 := first [ lazymatch goal with |- rw_cells ?s _ ?A _ => match goal with H : rw_cells s _ A _ |- _ => exact H end end
                          | eassumption ].
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
(* [comment removed for export] *)
Local Ltac solve_acc_shadow H ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        first [ solve [ zify_prune; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]
      end
  end.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

(* [comment removed for export] *)
Local Lemma rw_cells_app_fr : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1))%Z cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    (nd_pre WR 3%nat; intros HA HN HW; nd_post).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition asan_memset_entry := 0x54e68%Z.

Definition asan_memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (junk : list byte) (RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2208)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2128)
                  [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2128)
    /\ munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
    /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.

  #[using="m ST LO KLO APPD NSZ R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LED AD R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].   (* [comment removed for export] *)
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2208 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
  #[using="m ST LO KLO APPD NSZ R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    (nd_pre H 13%nat; intros (jk & FR) ST1 MU1 WM1 MI1 GOT1 RIC1 SHB1 INI1 LAY1 REAL1 UD1 WR21; nd_post).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  #[using="ST LO KLO APPD UDST NSZ R2 WR2"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2128) [CB 2072 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2128) ->
    munch [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x54ef8) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    zstep. zstep. zstep.
    unfold sf_hide in SEPD.
    apply (munch_weaken _ [(bv_unsigned sp + -2208, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR21.
    call memset_spec; [exact DST1 | exact MI1 |].
    do 10 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x21 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55024) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; easm2.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x21 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
               (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55008) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    (nd_pre (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) 3%nat; intros b2 RD2 CK2; nd_post).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; easm2.
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma LB : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x54ea0) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      do 5 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv_of; easm2.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; easm2.
      + eapply LX; exact IV0.
  Qed.

  #[using="junk RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma asan_memset_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x54e68) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2208, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2208) 2208) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2128)%Z) by lia.
    change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    change (?P) with (sf_hide P) in DST.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    carve_frame 2128%nat ST0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk0] =>
      apply (rw_cells_split_CB asegs m _ [] 2128 jk0 [] [2072%nat; 56%nat]) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR;
      set (jk1 := firstn 2072 jk0) in FR; set (jk2 := firstn 56 (skipn 2072 jk0)) in FR; clearbody jk1 jk2; clear jk0 end.
    change [CB 2072 jk1; CB 56 jk2] with ([CB 2072 jk1] ++ [CB 56 jk2]) in FR.
    apply rw_cells_app_fr in FR. destruct FR as [FR FR2].
    change (Z.of_nat (cells_size [CB 2072 jk1])) with 2072%Z in FR2.
    replace (bv_unsigned sp + -2128 + 2072)%Z with (bv_unsigned sp + -56)%Z in FR2 by lia.
    do 10 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -2128) [CB 2072 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -56) ?cs |- _ =>
      assert (FRJ : rw_cells asegs mm (bv_unsigned sp + -2128) ([CB 2072 j] ++ cs))
        by (apply rw_cells_app_fr; split; [exact H1 | change (Z.of_nat (cells_size [CB 2072 j])) with 2072%Z;
                                                     replace (bv_unsigned sp + -2128 + 2072)%Z with (bv_unsigned sp + -56)%Z by lia; exact H2]);
      cbn [app] in FRJ; clear H1 H2; rename FRJ into FR end.
    eapply LB. eapply inv_of; easm2.
  Qed.
End Proofs.

#[using="Type"] Lemma asan_memset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2208)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54e68) fc None m (seg_rom asegs)).
Proof. intros. eapply asan_memset_body; eassumption. Qed.
End CANSEC1.
End TwB.
End I_asan_memset.

(* [comment removed for export] *)
Module I_memset.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells ShadowTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_rip. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac easm2 := first [ lazymatch goal with |- rw_cells ?s _ ?A _ => match goal with H : rw_cells s _ A _ |- _ => exact H end end
                          | eassumption ].
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
(* [comment removed for export] *)
Local Ltac solve_acc_shadow H ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        first [ solve [ zify_prune; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]
      end
  end.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

(* [comment removed for export] *)
Local Lemma rw_cells_app_fr : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1))%Z cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    (nd_pre WR 3%nat; intros HA HN HW; nd_post).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition memset_i_entry := 0x55040%Z.

Definition memset_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (junk : list byte) (RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
                  [CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
    /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.

  #[using="m ST LO KLO APPD NSZ R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LED AD R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].   (* [comment removed for export] *)
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
  #[using="m ST LO KLO APPD NSZ R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    (nd_pre H 13%nat; intros (jk & FR) ST1 MU1 WM1 MI1 GOT1 RIC1 SHB1 INI1 LAY1 REAL1 UD1 WR21; nd_post).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  #[using="ST LO KLO APPD UDST NSZ R2 WR2"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x550d4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    zstep. zstep. zstep.
    unfold sf_hide in SEPD.
    apply (munch_weaken _ [(bv_unsigned sp + -2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR21.
    call memset_spec; [exact DST1 | exact MI1 |].
    do 11 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55208) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; easm2.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
               (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x551ec) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    (nd_pre (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) 3%nat; intros b2 RD2 CK2; nd_post).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; easm2.
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma LB : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5507c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      do 5 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv_of; easm2.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; easm2.
      + eapply LX; exact IV0.
  Qed.

  #[using="junk RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma memset_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55040) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    change (?P) with (sf_hide P) in DST.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    carve_frame 2144%nat ST0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk0] =>
      apply (rw_cells_split_CB asegs m _ [] 2144 jk0 [] [2080%nat; 64%nat]) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR;
      set (jk1 := firstn 2080 jk0) in FR; set (jk2 := firstn 64 (skipn 2080 jk0)) in FR; clearbody jk1 jk2; clear jk0 end.
    change [CB 2080 jk1; CB 64 jk2] with ([CB 2080 jk1] ++ [CB 64 jk2]) in FR.
    apply rw_cells_app_fr in FR. destruct FR as [FR FR2].
    change (Z.of_nat (cells_size [CB 2080 jk1])) with 2080%Z in FR2.
    replace (bv_unsigned sp + -2144 + 2080)%Z with (bv_unsigned sp + -64)%Z in FR2 by lia.
    do 11 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -2144) [CB 2080 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -64) ?cs |- _ =>
      assert (FRJ : rw_cells asegs mm (bv_unsigned sp + -2144) ([CB 2080 j] ++ cs))
        by (apply rw_cells_app_fr; split; [exact H1 | change (Z.of_nat (cells_size [CB 2080 j])) with 2080%Z;
                                                     replace (bv_unsigned sp + -2144 + 2080)%Z with (bv_unsigned sp + -64)%Z by lia; exact H2]);
      cbn [app] in FRJ; clear H1 H2; rename FRJ into FR end.
    eapply LB. eapply inv_of; easm2.
  Qed.
End Proofs.

#[using="Type"] Lemma memset_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55040) fc None m (seg_rom asegs)).
Proof. intros. eapply memset_i_body; eassumption. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ShadowTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_rip.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac easm2 := first [ lazymatch goal with |- rw_cells ?s _ ?A _ => match goal with H : rw_cells s _ A _ |- _ => exact H end end
                          | eassumption ].
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
(* [comment removed for export] *)
Local Ltac solve_acc_shadow H ::=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with rng _ ?lo ?len =>
        apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
        let B := fresh "B" in acc_facts B;
        rewrite ?shad_div in B |- *; unfold ASHOFF in B |- *;
        rewrite ?Z.shiftr_div_pow2 in B |- * by lia; change (2 ^ 3)%Z with 8%Z in B |- *;
        first [ solve [ zify_prune; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]
      end
  end.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

(* [comment removed for export] *)
Local Lemma rw_cells_app_fr : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1))%Z cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    (nd_pre WR 3%nat; intros HA HN HW; nd_post).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Definition memset_i_entry := 0x550a8%Z.

Definition memset_i_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (junk : list byte) (RLO2 RHI2 : Z).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2224)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis RIC : rt_got_ric m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis LAY : rt_layout m.
  Hypothesis REAL : rt_real_mem m.
  Hypothesis DST : rw_cells asegs m D [CB (Z.to_nat n) junk].
  Hypothesis SEPD : (D + n <= lo \/ bv_unsigned sp <= D)%Z.
  Hypothesis APPD : app_blk D (D + n).
  Hypothesis UDST : unpoisoned m D (D + n).
  Hypothesis NSZ : (n <= 2^40)%Z.
  Hypothesis R2 : (RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z.
  Hypothesis WR2 : wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RD : rng RNG D n.
  Hypothesis RSH2 : rng RNG (shad RLO2) (shad RHI2 - shad RLO2).

  Notation POST := (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).

  Definition INV (mc : word -> option byte) : Prop :=
    (exists jk, rw_cells asegs mc (bv_unsigned sp + -2144)
                  [CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs mc lo (bv_unsigned sp + -2144)
    /\ munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc
    /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rt_got mc /\ rt_got_ric mc /\ rt_shbase mc /\ rt_inited mc /\ rt_layout mc /\ rt_real_mem mc
    /\ unpoisoned mc D (D + n)
    /\ wr_at asegs mc (shad RLO2) (shad RHI2 - shad RLO2).

  Definition BND : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ KHIGH <= lo /\ 0 <= n < 2^64 /\ n <= 2^40
     /\ 0 <= D /\ D + n + 8 <= KEND
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= KHIGH
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ shad RLO2 mod 8 = 0 /\ shad RHI2 mod 8 = 0
     /\ RLO2 <= D /\ D + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0)%Z.

  #[using="m ST LO KLO APPD NSZ R2"] Lemma BND_ok : BND.
  Proof.
    unfold BND. pose proof (bv_unsigned_in_range 64 a2) as Rn. unfold bv_modulus in Rn.
    destruct ST as (L0 & _). destruct APPD as [LED AD]. unfold KLOW, KHIGH, KEND in *.
    pose proof R2 as R2'. unfold sf_hide in R2'.
    rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rn.
    first [clear -Rn L0 LO KLO NSZ LED AD R2'; Z.div_mod_to_equations; nia | Z.div_mod_to_equations; nia].   (* [comment removed for export] *)
  Qed.

  Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2224 /\ 17594333495296 <= lo /\ 0 <= n < 2^64 /\ 0 <= D /\ D + n + 8 <= 2^47
     /\ 0 <= Z.shiftr D 3 < 2^44 /\ -1 <= Z.shiftr (D + n + -1) 3 < 2^44
     /\ 2147450880 <= shad RLO2 /\ shad RLO2 <= shad D /\ shad (D + n - 1) + 1 <= shad RHI2 /\ shad RHI2 <= 17594333495296)%Z.
  #[using="m ST LO KLO APPD NSZ R2"] Lemma BL_ok : BL. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BL. lia. Qed.

  Ltac inv_open H :=
    let jk := fresh "jk" in
    (nd_pre H 13%nat; intros (jk & FR) ST1 MU1 WM1 MI1 GOT1 RIC1 SHB1 INI1 LAY1 REAL1 UD1 WR21; nd_post).

  Ltac prep IV :=
    pose proof IV as IV0; inv_open IV;
    let B := fresh "BL" in pose proof BL_ok as B; unfold BL in B;
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]);
    change (?P) with (sf_hide P) in DST; change (?P) with (sf_hide P) in SEPD; change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.

  #[using="ST LO KLO APPD UDST NSZ R2 WR2"] Lemma inv_of : forall mc jk,
    rw_cells asegs mc (bv_unsigned sp + -2144) [CB 2080 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -2144) ->
    munch [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m mc -> wmono asegs m mc -> mem_inv asegs mc ->
    rt_got mc -> rt_got_ric mc -> rt_shbase mc -> rt_inited mc -> rt_layout mc -> rt_real_mem mc ->
    INV mc.
  Proof.
    intros mc jk FR ST1 MU1 WM1 MI1 G1 G2 G3 G4 G5 G6. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
    split; [exists jk; exact FR|]. repeat (split; [assumption|]).
    assert (SS : forall lo' hi', (0 <= lo' -> hi' + 8 <= 2^47 -> shad (hi' - 1) + 1 <= 17594333495296)%Z).
    { intros lo' hi' H1 H2. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
    split. { eapply unpoisoned_munch; [exact UDST | exact MU1 |]. cbn [disjoint_from]. pose proof (SS D (D + n)%Z). lia. }
    eapply wr_at_transport; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD"] Lemma LX : forall mc x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x5513c) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    assert (DST1 : rw_cells asegs mc D [CB (Z.to_nat n) junk]).
    { unfold sf_hide in *. eapply rw_cells_transport; [exact DST | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    zstep. zstep. zstep.
    unfold sf_hide in SEPD.
    apply (munch_weaken _ [(bv_unsigned sp + -2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z) in MU1.
    2:{ unfold sub_fp; cbn [outside]; intros; lia. }
    clear GOT1 RIC1 SHB1 INI1 LAY1 REAL1 WR21.
    call memset_spec; [exact DST1 | exact MI1 |].
    do 11 zstep.
    release_frame FR ST1 (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWL : forall mc (k : nat) (c : Z) x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    Z.to_nat (shad (D + n - 1) - c) = k -> (shad D <= c < shad (D + n - 1))%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3)) (Z_to_bv 64 0) x16 x17
               x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55270) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1 Hk Hc. prep IV.
    revert c x16 Hk Hc. induction k as [|k IH]; intros c x16 Hk Hc; [exfalso; lia|].
    assert (SL : (shad (D + n - 1) = 2147450880 + Z.shiftr (D + n + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
    pose proof (unpoisoned_full_rd asegs mc D (D + n) c UD1 ltac:(lia)
                  ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K; zify_cond K.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LX; easm2.
  Qed.

  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD NSZ R2 RI RSTK RD RSH2"] Lemma LWS : forall mc x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    INV mc -> (1 <= n <= 64)%Z ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2
               (Z_to_bv 64 (2147450880 + Z.shiftr D 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (D + n + -1) 3))
               (Z_to_bv 64 (D + n + -1)) x16 x17
               x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x55254) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV N1. prep IV.
    (nd_pre (unpoisoned_check_rd asegs mc D (D + n) (D + n + -1) 1 UD1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) 3%nat; intros b2 RD2 CK2; nd_post).
    unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
    zstep. rewrite sxb_sval. do 5 zstep.
    rewrite land7_mod. rewrite (aip_zero ((D + n + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LX; easm2.
    - eapply LWL; [exact IV0 | assumption | reflexivity |].
      unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
      Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="junk ST LO KLO DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma LB : forall mc x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    INV mc ->
    evtF asegs RNG POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9 a0 a1 a2 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x550e4) fc None mc (seg_rom asegs)).
  Proof.
    intros until x31. intros IV. prep IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      zstep. if_cases K3; zify_cond K3.
      2:{ zstep. eapply LX; exact IV0. }
      do 5 zstep.
      call_sp rip_spec;
        [ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1 | exact APPD | exact UD1
        | pose proof BND_ok as B; unfold BND in B; lia
        | eapply rng_sub'; [exact RSTK | lia] | ].
      do 5 zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LX; eapply inv_of; easm2.
    - (* [comment removed for export] *)
      assert (N1 : (1 <= n <= 64)%Z) by (clear - K2 BL0; Z.div_mod_to_equations; lia).
      do 11 zstep.
      change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
      unfold sf_hide in R2.
      destruct (shadow_probe8 asegs mc RLO2 RHI2 D WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w1 P1].
      destruct (shadow_probe8 asegs mc RLO2 RHI2 (D + n + -1) WR21 ltac:(apply no_image_asan; pose proof BND_ok as B; unfold BND in B; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R2; lia)) as [w2 P2].
      unfold ASHOFF in P1, P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LWS; easm2.
      + eapply LX; exact IV0.
  Qed.

  #[using="junk RLO2 RHI2 MI ST LO KLO GOT RIC SHB INI LAY REAL DST SEPD APPD UDST NSZ R2 WR2 RI RSTK RD RSH2"] Lemma memset_i_body :
    evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x550a8) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as BL0. unfold BL in BL0.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (LO' : (lo <= bv_unsigned sp - 2144)%Z) by lia.
    change (?P) with (sf_hide P) in R2;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO; change (?P) with (sf_hide P) in NSZ.
    change (?P) with (sf_hide P) in DST.
    pose proof ST as ST0. change (?P) with (sf_hide P) in ST. change (?P) with (sf_hide P) in WR2.
    carve_frame 2144%nat ST0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?jk0] =>
      apply (rw_cells_split_CB asegs m _ [] 2144 jk0 [] [2080%nat; 64%nat]) in FR; [| reflexivity];
      cbn [mk_CB_cells app] in FR;
      set (jk1 := firstn 2080 jk0) in FR; set (jk2 := firstn 64 (skipn 2080 jk0)) in FR; clearbody jk1 jk2; clear jk0 end.
    change [CB 2080 jk1; CB 64 jk2] with ([CB 2080 jk1] ++ [CB 64 jk2]) in FR.
    apply rw_cells_app_fr in FR. destruct FR as [FR FR2].
    change (Z.of_nat (cells_size [CB 2080 jk1])) with 2080%Z in FR2.
    replace (bv_unsigned sp + -2144 + 2080)%Z with (bv_unsigned sp + -64)%Z in FR2 by lia.
    do 11 zstep.
    do 3 zstep. cbv beta. zsimp. zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0. cbv in K0. lia. }
    lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -2144) [CB 2080 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -64) ?cs |- _ =>
      assert (FRJ : rw_cells asegs mm (bv_unsigned sp + -2144) ([CB 2080 j] ++ cs))
        by (apply rw_cells_app_fr; split; [exact H1 | change (Z.of_nat (cells_size [CB 2080 j])) with 2080%Z;
                                                     replace (bv_unsigned sp + -2144 + 2080)%Z with (bv_unsigned sp + -64)%Z by lia; exact H2]);
      cbn [app] in FRJ; clear H1 H2; rename FRJ into FR end.
    eapply LB. eapply inv_of; easm2.
  Qed.
End Proofs.

#[using="Type"] Lemma memset_i_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk : list byte) (RLO2 RHI2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2224)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  app_blk (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  unpoisoned m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
  (bv_unsigned a2 <= 2^40)%Z ->
  (RLO2 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND)%Z ->
  wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  evtF asegs RNG (memset_i_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x550a8) fc None m (seg_rom asegs)).
Proof. intros. eapply memset_i_body; eassumption. Qed.
End CANSEC1.
End TwB.
End I_memset.
