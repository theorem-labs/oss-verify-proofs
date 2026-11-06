(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From Ltac2 Require Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrlProps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_agbb.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition gbb_entry := 0x361c4.
End CANSEC1.
Abbreviation GBB_STACK := 32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition nb_step (p acc ch : Z) : Z :=
  if p <? ch then acc else if p - ch <? p - acc then ch else acc.
Definition nb_fold (p acc : Z) (l : list Z) : Z := fold_left (nb_step p) l acc.

#[using="Type"] Lemma nb_fold_cons : forall p acc ch l, nb_fold p acc (ch :: l) = nb_fold p (nb_step p acc ch) l.
Proof. reflexivity. Qed.

#[using="Type"] Lemma nb_step_range : forall p acc ch, 0 <= acc <= p -> 0 <= ch -> 0 <= nb_step p acc ch <= p.
Proof. intros p acc ch H Hc. unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - acc)); lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nb_fold_finds : forall p mb l acc,
  0 <= acc <= mb -> mb <= p -> Forall (fun ch => 0 <= ch /\ (ch <= p -> ch <= mb)) l ->
  (In mb l \/ acc = mb) -> nb_fold p acc l = mb.
Proof.
  intros p mb l. induction l as [|ch l IH]; intros acc HA HM HL HIN.
  - cbn. destruct HIN as [[]| ->]; reflexivity.
  - rewrite nb_fold_cons. apply Forall_cons_iff in HL. destruct HL as [[C0 C1] HL].
    apply IH; [| exact HM | exact HL |].
    + unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - acc)); [| lia]. split; [lia|]. apply C1. lia.
    + destruct HIN as [[E | HIN] | ->].
      * right. subst ch. unfold nb_step. destruct (Z.ltb_spec p mb); [lia|]. destruct (Z.ltb_spec (p - mb) (p - acc)); lia.
      * left; exact HIN.
      * right. unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - mb)); [| lia].
        specialize (C1 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma gbb_loop_spec : forall RNG (d : nat) (i n PA p acc : Z) (bases : list Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> Z.of_nat (length bases) = n ->
  u64arr asegs m PA (map (Z_to_bv 64) bases) ->
  Forall (fun ch => 0 <= ch < 2^64) bases -> 0 <= acc <= p -> p < 2^64 ->
  0 <= PA -> PA + 8 * n < 2^47 ->
  rng RNG PA (8 * n) ->
  evtF asegs RNG (fun ms' => exists a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PA + 8 * n))
                    (Z_to_bv 64 (nb_fold p acc (skipn (Z.to_nat i) bases))) (Z_to_bv 64 (PA + 8 * n)) a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3625c) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PA + 8 * i)) (Z_to_bv 64 acc) (Z_to_bv 64 (PA + 8 * n)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36230) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LEN ARR BR ACC P64 PA0 PA1 RPA; [lia|].
  destruct (nth_error bases (Z.to_nat i)) as [ch|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) BR ch (nth_error_In _ _ NTH)) as CHR. cbv beta in CHR.
  assert (NTHm : nth_error (map (Z_to_bv 64) bases) (Z.to_nat i) = Some (Z_to_bv 64 ch)) by (rewrite nth_error_map, NTH; reflexivity).
  pose proof (u64arr_read asegs _ _ _ i (Z_to_bv 64 ch) (wa (PA + 8 * i)) ARR NTHm ltac:(lia) eq_refl) as RD.
  pose proof (rng_sub _ _ _ (PA + 8 * i) 8 RPA ltac:(lia) ltac:(lia)) as RDi.
  (* [comment removed for export] *)
  assert (SK : skipn (Z.to_nat i) bases = ch :: skipn (Z.to_nat (i + 1)) bases).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. clear -NTH.
    revert NTH. generalize (Z.to_nat i) as k. clear. intros k. revert bases.
    induction k as [|k IHk]; intros [|b bs] H; cbn in *; try discriminate; [injection H as ->; reflexivity| apply IHk; exact H]. }
  rewrite SK, nb_fold_cons.
  step. clear RD RDi.                                          (* [comment removed for export] *)
  zstep. zstep. step.                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  step; if_cases K; zify_cond K;
    [ step; if_cases K'; zify_cond K'; [ | step; step ]
    | step; step; if_cases K'; zify_cond K'; [ | step; step; step ] ].
  all: setreg 13 (Z_to_bv 64 (nb_step p acc ch))
         ltac:(unfold nb_step; rewrite ?Z.mod_small in K by lia;
               destruct (Z.ltb_spec p ch); destruct (Z.ltb_spec (p - ch) (p - acc)); first [reflexivity | exfalso; lia]).
  all: zstep; setreg 12 (Z_to_bv 64 (PA + 8 * (i + 1))) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  all: pose proof (nb_step_range p acc ch ACC ltac:(lia)) as ACC'.
  all: step; if_cases KE; zify_cond KE.                        (* [comment removed for export] *)
  all: try (rewrite ?unsigned_lit in KE by lia).
  1,3,5,7: (* [comment removed for export] *)
       assert (EI : i + 1 = n) by lia;
       apply evtF_done; do 4 eexists;
       rewrite skipn_all2 by (rewrite <- EI in *; lia); cbn [nb_fold fold_left]; rewrite EI; reflexivity.
  all: eapply evtF_mono; [eapply (IH (i + 1) n PA p (nb_step p acc ch) bases); try eassumption; try lia |].
  all: cbv beta; intros ms' (a5' & a6' & a7' & t0' & ->); do 4 eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma gbb_mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab240 [C4 (Z_to_bv 64 b)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.
#[using="Type"] Lemma gbb_mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab240 [C4 (Z_to_bv 64 b)] ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 2 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.

Definition gbb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mb + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - GBB_STACK, bv_unsigned sp); (0xab240, 0xab244)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Definition sec_gbb_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p PA nres nsec mb ms lo : Z) (bases : list Z) (h2 h3 : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GBB_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xaafd8 -> a1 = Z_to_bv 64 p ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xaafe0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec -> 1 <= nsec ->
  ablk PA (PA + 8 * nsec) -> PA + 8 * nsec <= ATOP ->       (* [comment removed for export] *)
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= p -> ch <= mb)) bases -> In mb bases ->
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 h2; C8 h3] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> mb <= p < mb + ms -> 32 <= ms -> mb + ms <= ATOP ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG PA (8 * nsec) -> rng RNG mb 32 ->
  evtF asegs RNG (gbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gbb_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 34).
Variable p : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 35).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 36).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 37).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 41).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 42).
Variable h2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 43).
Variable h3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 44).
#[using="Type"] Lemma sec_gbb_spec__body : ltac:(let T := type of (fun (h : sec_gbb_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p PA nres nsec mb ms lo bases h2 h3) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (PA, (nres, (nsec, (mb, (ms, (lo, (bases, (h2, h3))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> I64 I72 NSC MTX ARR LEN N1 PA0b PA1 BR IN HDR MAL MPOSb PIN MS32 MCE RA RIMG RTLS RSTK RPA RMB.
  pose proof (ablk_lin _ _ PA0b) as PA0. pose proof (ablk_lin _ _ MPOSb) as MPOS. unfold AIMG_HI in PA0, MPOS.   (* [comment removed for export] *)
  unfold gbb_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - GBB_STACK, bv_unsigned sp); (0xab240, 0xab244)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  box ARR. box HDR.
  carve_frame 32%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. zstep. step.                                           (* [comment removed for export] *)
  apply (gbb_mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 700992) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0. { exfalso. clear -K0 N1 LEN PA1 PA0. rewrite ?unsigned_lit in K0 by lia. lia. }   (* [comment removed for export] *)
  step. step. zstep. zstep.                                    (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -N1 PA0 PA1; lia).
  step.                                                        (* [comment removed for export] *)
  carry ARR MU WM ltac:(rewrite length_map; clear -SPR CEIL LO PA0 PA1 LEN; lia).
  replace (Z_to_bv 64 PA : word) with (Z_to_bv 64 (PA + 8 * 0) : word) by (f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (gbb_loop_spec RNG (Z.to_nat (nsec - 0)) 0 nsec PA p 0 bases); try eassumption; try (clear -N1 LEN PA0 PA1 PIN MPOS MCE; lia).
    eapply Forall_impl; [| exact BR]. cbn. intros ch [H _]. exact H. }
  cbv beta. intros ms' (a5' & a6' & a7' & t0' & ->). change (skipn (Z.to_nat 0) bases) with bases.
  rewrite (nb_fold_finds p mb bases 0); [| clear -MPOS; lia | clear -PIN; lia | | left; exact IN].
  2: { eapply Forall_impl; [| exact BR]. cbn. intros ch [H1 H2]. split; [clear -H1; lia| exact H2]. }
  (* [comment removed for export] *)
  carry HDR MU WM ltac:(clear -SPR CEIL LO MPOS MCE PIN MS32; lia).
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 MPOS MCE PIN. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2 MPOS MCE PIN. rewrite ?unsigned_lit in K2 by lia. lia. }   (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 MPOS MCE PIN. rewrite ?unsigned_lit in K3 by lia. lia. }   (* [comment removed for export] *)
  step. if_cases K4; zify_cond K4. { exfalso. clear -K4 MPOS MCE PIN. rewrite ?unsigned_lit in K4 by lia. lia. }   (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. clear -K5 MPOS MCE PIN. rewrite ?unsigned_lit in K5 by lia. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by (clear; lia); change (2^12) with 4096; clear -MAL; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (mb + 4096)) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply (gbb_mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  step.                                                        (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  apply evtF_done. unfold gbb_post. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. exact MTX.
Qed.
End Zd1.
#[using="Type"] Lemma sec_gbb_spec : ltac:(let t := eval cbv delta [sec_gbb_spec__stmt] in sec_gbb_spec__stmt in exact t).
Proof. exact sec_gbb_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition gbb_entry := 0x3622c.
End CANSEC1.
Abbreviation GBB_STACK := 32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition nb_step (p acc ch : Z) : Z :=
  if p <? ch then acc else if p - ch <? p - acc then ch else acc.
Definition nb_fold (p acc : Z) (l : list Z) : Z := fold_left (nb_step p) l acc.

#[using="Type"] Lemma nb_fold_cons : forall p acc ch l, nb_fold p acc (ch :: l) = nb_fold p (nb_step p acc ch) l.
Proof. reflexivity. Qed.

#[using="Type"] Lemma nb_step_range : forall p acc ch, 0 <= acc <= p -> 0 <= ch -> 0 <= nb_step p acc ch <= p.
Proof. intros p acc ch H Hc. unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - acc)); lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nb_fold_finds : forall p mb l acc,
  0 <= acc <= mb -> mb <= p -> Forall (fun ch => 0 <= ch /\ (ch <= p -> ch <= mb)) l ->
  (In mb l \/ acc = mb) -> nb_fold p acc l = mb.
Proof.
  intros p mb l. induction l as [|ch l IH]; intros acc HA HM HL HIN.
  - cbn. destruct HIN as [[]| ->]; reflexivity.
  - rewrite nb_fold_cons. apply Forall_cons_iff in HL. destruct HL as [[C0 C1] HL].
    apply IH; [| exact HM | exact HL |].
    + unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - acc)); [| lia]. split; [lia|]. apply C1. lia.
    + destruct HIN as [[E | HIN] | ->].
      * right. subst ch. unfold nb_step. destruct (Z.ltb_spec p mb); [lia|]. destruct (Z.ltb_spec (p - mb) (p - acc)); lia.
      * left; exact HIN.
      * right. unfold nb_step. destruct (Z.ltb_spec p ch); [lia|]. destruct (Z.ltb_spec (p - ch) (p - mb)); [| lia].
        specialize (C1 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma gbb_loop_spec : forall RNG (d : nat) (i n PA p acc : Z) (bases : list Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> Z.of_nat (length bases) = n ->
  u64arr asegs m PA (map (Z_to_bv 64) bases) ->
  Forall (fun ch => 0 <= ch < 2^64) bases -> 0 <= acc <= p -> p < 2^64 ->
  0 <= PA -> PA + 8 * n < 2^47 ->
  rng RNG PA (8 * n) ->
  evtF asegs RNG (fun ms' => exists a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PA + 8 * n))
                    (Z_to_bv 64 (nb_fold p acc (skipn (Z.to_nat i) bases))) (Z_to_bv 64 (PA + 8 * n)) a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x362c4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PA + 8 * i)) (Z_to_bv 64 acc) (Z_to_bv 64 (PA + 8 * n)) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36298) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LEN ARR BR ACC P64 PA0 PA1 RPA; [lia|].
  destruct (nth_error bases (Z.to_nat i)) as [ch|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) BR ch (nth_error_In _ _ NTH)) as CHR. cbv beta in CHR.
  assert (NTHm : nth_error (map (Z_to_bv 64) bases) (Z.to_nat i) = Some (Z_to_bv 64 ch)) by (rewrite nth_error_map, NTH; reflexivity).
  pose proof (u64arr_read asegs _ _ _ i (Z_to_bv 64 ch) (wa (PA + 8 * i)) ARR NTHm ltac:(lia) eq_refl) as RD.
  pose proof (rng_sub _ _ _ (PA + 8 * i) 8 RPA ltac:(lia) ltac:(lia)) as RDi.
  (* [comment removed for export] *)
  assert (SK : skipn (Z.to_nat i) bases = ch :: skipn (Z.to_nat (i + 1)) bases).
  { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. clear -NTH.
    revert NTH. generalize (Z.to_nat i) as k. clear. intros k. revert bases.
    induction k as [|k IHk]; intros [|b bs] H; cbn in *; try discriminate; [injection H as ->; reflexivity| apply IHk; exact H]. }
  rewrite SK, nb_fold_cons.
  step. clear RD RDi.                                          (* [comment removed for export] *)
  zstep. zstep. step.                                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  step; if_cases K; zify_cond K;
    [ step; if_cases K'; zify_cond K'; [ | step; step ]
    | step; step; if_cases K'; zify_cond K'; [ | step; step; step ] ].
  all: setreg 13 (Z_to_bv 64 (nb_step p acc ch))
         ltac:(unfold nb_step; rewrite ?Z.mod_small in K by lia;
               destruct (Z.ltb_spec p ch); destruct (Z.ltb_spec (p - ch) (p - acc)); first [reflexivity | exfalso; lia]).
  all: zstep; setreg 12 (Z_to_bv 64 (PA + 8 * (i + 1))) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  all: pose proof (nb_step_range p acc ch ACC ltac:(lia)) as ACC'.
  all: step; if_cases KE; zify_cond KE.                        (* [comment removed for export] *)
  all: try (rewrite ?unsigned_lit in KE by lia).
  1,3,5,7: (* [comment removed for export] *)
       assert (EI : i + 1 = n) by lia;
       apply evtF_done; do 4 eexists;
       rewrite skipn_all2 by (rewrite <- EI in *; lia); cbn [nb_fold fold_left]; rewrite EI; reflexivity.
  all: eapply evtF_mono; [eapply (IH (i + 1) n PA p (nb_step p acc ch) bases); try eassumption; try lia |].
  all: cbv beta; intros ms' (a5' & a6' & a7' & t0' & ->); do 4 eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma gbb_mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xab640 [C4 (Z_to_bv 64 b)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.
#[using="Type"] Lemma gbb_mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0xab640 [C4 (Z_to_bv 64 b)] ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. replace b with (b + 256 * 0) at 2 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed.

Definition gbb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mb + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - GBB_STACK, bv_unsigned sp); (0xab640, 0xab644)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Definition sec_gbb_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p PA nres nsec mb ms lo : Z) (bases : list Z) (h2 h3 : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - GBB_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 0xab3d8 -> a1 = Z_to_bv 64 p ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xab3e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec -> 1 <= nsec ->
  ablk PA (PA + 8 * nsec) -> PA + 8 * nsec <= ATOP ->       (* [comment removed for export] *)
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= p -> ch <= mb)) bases -> In mb bases ->
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 h2; C8 h3] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> mb <= p < mb + ms -> 32 <= ms -> mb + ms <= ATOP ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG PA (8 * nsec) -> rng RNG mb 32 ->
  evtF asegs RNG (gbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gbb_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 34).
Variable p : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 35).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 36).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 37).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 41).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 42).
Variable h2 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 43).
Variable h3 : ltac2:(SecDietF.SzSecF.ty 'sec_gbb_spec__stmt 44).
#[using="Type"] Lemma sec_gbb_spec__body : ltac:(let T := type of (fun (h : sec_gbb_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p PA nres nsec mb ms lo bases h2 h3) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (p, (PA, (nres, (nsec, (mb, (ms, (lo, (bases, (h2, h3))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI -> -> I64 I72 NSC MTX ARR LEN N1 PA0b PA1 BR IN HDR MAL MPOSb PIN MS32 MCE RA RIMG RTLS RSTK RPA RMB.
  pose proof (ablk_lin _ _ PA0b) as PA0. pose proof (ablk_lin _ _ MPOSb) as MPOS. unfold AIMG_HI in PA0, MPOS.   (* [comment removed for export] *)
  unfold gbb_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - GBB_STACK, bv_unsigned sp); (0xab640, 0xab644)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  box ARR. box HDR.
  carve_frame 32%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. zstep. step.                                           (* [comment removed for export] *)
  apply (gbb_mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 702016) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0. { exfalso. clear -K0 N1 LEN PA1 PA0. rewrite ?unsigned_lit in K0 by lia. lia. }   (* [comment removed for export] *)
  step. step. zstep. zstep.                                    (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -N1 PA0 PA1; lia).
  step.                                                        (* [comment removed for export] *)
  carry ARR MU WM ltac:(rewrite length_map; clear -SPR CEIL LO PA0 PA1 LEN; lia).
  replace (Z_to_bv 64 PA : word) with (Z_to_bv 64 (PA + 8 * 0) : word) by (f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (gbb_loop_spec RNG (Z.to_nat (nsec - 0)) 0 nsec PA p 0 bases); try eassumption; try (clear -N1 LEN PA0 PA1 PIN MPOS MCE; lia).
    eapply Forall_impl; [| exact BR]. cbn. intros ch [H _]. exact H. }
  cbv beta. intros ms' (a5' & a6' & a7' & t0' & ->). change (skipn (Z.to_nat 0) bases) with bases.
  rewrite (nb_fold_finds p mb bases 0); [| clear -MPOS; lia | clear -PIN; lia | | left; exact IN].
  2: { eapply Forall_impl; [| exact BR]. cbn. intros ch [H1 H2]. split; [clear -H1; lia| exact H2]. }
  (* [comment removed for export] *)
  carry HDR MU WM ltac:(clear -SPR CEIL LO MPOS MCE PIN MS32; lia).
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 MPOS MCE PIN. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2 MPOS MCE PIN. rewrite ?unsigned_lit in K2 by lia. lia. }   (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 MPOS MCE PIN. rewrite ?unsigned_lit in K3 by lia. lia. }   (* [comment removed for export] *)
  step. if_cases K4; zify_cond K4. { exfalso. clear -K4 MPOS MCE PIN. rewrite ?unsigned_lit in K4 by lia. lia. }   (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. clear -K5 MPOS MCE PIN. rewrite ?unsigned_lit in K5 by lia. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by (clear; lia); change (2^12) with 4096; clear -MAL; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (mb + 4096)) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply (gbb_mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  step.                                                        (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  apply evtF_done. unfold gbb_post. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. exact MTX.
Qed.
End Zd1.
#[using="Type"] Lemma sec_gbb_spec : ltac:(let t := eval cbv delta [sec_gbb_spec__stmt] in sec_gbb_spec__stmt in exact t).
Proof. exact sec_gbb_spec__body. Qed.
End CANSEC2.
End TwB.
End F_agbb.

(* [comment removed for export] *)
Module F_aalloc2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition hdr_b1_mid (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 16.

Notation allocBC_W L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).



(* [comment removed for export] *)







End WithDepot.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition hdr_b1_mid (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 16.

Notation allocBC_W L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).



(* [comment removed for export] *)







End WithDepot.
End CANSEC1.
End TwB.
End F_aalloc2.

(* [comment removed for export] *)
Module F_aalloc2g.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition hdr_b1_mid (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 16.

Notation allocBC_WG L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_postG (L : alayout) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t AB UB PG pgw lo b0 b1 : Z) (pj : byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x34154) fc None m' (seg_rom asegs)
    /\ munch (allocBC_WG L sp UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
#[using="Type"] Lemma partial_specG : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  mem_inv asegs m ->
  1 <= n -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  ablk UB (UB + n) -> UB + n <= ATOP -> UB mod 8 = 0 ->          (* [comment removed for export] *)
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                             C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)] ->
  rw_cells asegs m 0xae5f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xaf2e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xade5c [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  rng_aimg RNG -> rng_atls RNG -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' m',
      ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 UB) s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34154) fc None m' (seg_rom asegs)
      /\ munch [(PG, PG + pgw)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 UB) s5 (Z_to_bv 64 (n - n mod 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x340c0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI N HPG HPW UBLO UBHI UB8 GOT SHB LAY CANP PP SHP RIMG RTLS RPG.
  pose proof (munch_refl [(PG, PG + pgw)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ablk, AIMG_HI, KLS in UBLO. atop_facts.                (* [comment removed for export] *)
  assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) /\ PG + 1 <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. Z.div_mod_to_equations. lia. }
  step. if_cases K0; zify_cond K0.                               (* [comment removed for export] *)
  { apply evtF_done. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. intros NE. exfalso. lia. }
  specialize (SHP ltac:(lia)). specialize (RPG ltac:(lia)).
  assert (PW1 : pgw = 1) by (rewrite HPW; destruct (Z.eqb_spec (n mod 8) 0); [lia|reflexivity]). clear HPW. subst pgw.
  step. callp can_poison_spec; [exact CANP|]. step. if_lit.      (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  2: step; step; step; step; step; step; zstep.                  (* [comment removed for export] *)
  2: step; if_cases K2; zify_cond K2; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; step; step; zstep; zstep.                             (* [comment removed for export] *)
  2: step; if_cases K3; zify_cond K3; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: step; step; lstep; zstep; zstep.                          (* [comment removed for export] *)
  all: setreg 10 (Z_to_bv 64 PG) ltac:(rewrite HPG; unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; f_equal; Z.div_mod_to_equations; lia).
  all: zstep; zstep; zstep.                                      (* [comment removed for export] *)
  all: rewrite (land_ones_r n) by lia; change 7 with (2^3 - 1) at 1; rewrite (zb_land_mask n 3) by lia; change (2^3) with 8.
  all: sstep.                                                    (* [comment removed for export] *)
  all: apply evtF_done; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
  all: intros _; assumption.
Qed.



Definition allocBC_gen__stmt : Prop := forall (L : alayout) RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (pj : byte) (sj : list byte)
    (tb : list word) (tr : list Z) (fr0 : list byte) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
  (al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
  (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> tclr AB 65536 -> sclr (al_store L) 8388608 ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  poison_cells m -> rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (allocBC_postG L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 14).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 15).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 16).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 17).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 21).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 22).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 23).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 24).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 25).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 26).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 27).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 28).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 29).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 30).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 31).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 32).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 33).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 34).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 36).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 37).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 38).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 40).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 41).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 42).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 43).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 44).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 45).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 46).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 47).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 48).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 49).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 50).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 51).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 52).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 53).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 54).
#[using="Type"] Lemma allocBC_gen__body : ltac:(let T := type of (fun (h : allocBC_gen__stmt) => h L RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sj tb tr fr0 ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (t, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (pc, (pj, (sj, (tb, (tr, (fr0, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, s11v))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS XTAB SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RTLS RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. clear -AB16 RZM. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  (nd_pre PC 7%nat; intros PC1 PC2 PC3 PC4 PC5 PC6 PC7; nd_post).
  pose proof (munch_refl (allocBC_WG L sp UB PG pgw n) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS.
  snapshot [(UB - 16, UB)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
            (shad UB, shad UB + shlen (n - n mod 8));
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  box SHP.
  step. step. if_cases K0; zify_cond K0. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. setreg 20 (Z_to_bv 64 UB) ltac:(rewrite HUB; reflexivity).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -UB16. Z.div_mod_to_equations. lia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }              (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }             (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros a Ha. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. lia. }
  clear MUh WMh. box HDR.
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  box SHA. box SHU.          (* [comment removed for export] *)
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ = 1 + _ => exact SZ
       | |- u64arr _ _ _ _ => exact TB
       | |- length _ = _ => exact LTB
       | |- map _ _ = _ => exact TRF
       | |- In _ _ => exact TRU
       | |- ADEPOT _ _ _ => exact DEP'
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (UB - 16, UB); (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; lia).
  carry SHA MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)). carry SHU MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step. zstep. zstep.                                (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (shad AB)) ltac:(unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. zstep. zstep.                                            (* [comment removed for export] *)
  rewrite (land_align8_48 n) by lia.
  step. if_cases K4; zify_cond K4.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa54a0 _ => exact PC1
         | |- rw_cells _ _ 0xae5f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf2e0 _ => exact PC5
         | |- rw_cells _ _ 0xade5c _ => exact PC6
         | |- rw_cells _ _ 0xabe4d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    (* [comment removed for export] *)
    rewrite K4. rewrite K4 in SHU. pose proof SHU as W0. destruct W0 as [[[WF X1] X2] X3]. cbn in WF. destruct sj; [exact SHU| cbn in WF; discriminate].
  - (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UB (n - n mod 8) 0 lo sj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ (shad _) _ => exact SHU
         end.
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- rng _ _ _ => solve_rng
         | |- ablk _ _ => unfold ablk; right; atop_facts; lia
         | |- _ => atop_facts; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa54a0 _ => exact PC1
         | |- rw_cells _ _ 0xae5f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf2e0 _ => exact PC5
         | |- rw_cells _ _ 0xade5c _ => exact PC6
         | |- rw_cells _ _ 0xabe4d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocBC_gen : ltac:(let t := eval cbv delta [allocBC_gen__stmt] in allocBC_gen__stmt in exact t).
Proof. exact allocBC_gen__body. Qed.
End WithDepot.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition hdr_b1_mid (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 16.

Notation allocBC_WG L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_postG (L : alayout) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t AB UB PG pgw lo b0 b1 : Z) (pj : byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x341bc) fc None m' (seg_rom asegs)
    /\ munch (allocBC_WG L sp UB PG pgw n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
#[using="Type"] Lemma partial_specG : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  mem_inv asegs m ->
  1 <= n -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  ablk UB (UB + n) -> UB + n <= ATOP -> UB mod 8 = 0 ->          (* [comment removed for export] *)
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                             C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)] ->
  rw_cells asegs m 0xae9f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xaf6e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xae25c [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  rng_aimg RNG -> rng_atls RNG -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' m',
      ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 UB) s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x341bc) fc None m' (seg_rom asegs)
      /\ munch [(PG, PG + pgw)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (n mod 8 <> 0 -> rw_cells asegs m' PG [C1 (Z_to_bv 8 (n mod 8))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 UB) s5 (Z_to_bv 64 (n - n mod 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x34128) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI N HPG HPW UBLO UBHI UB8 GOT SHB LAY CANP PP SHP RIMG RTLS RPG.
  pose proof (munch_refl [(PG, PG + pgw)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold ablk, AIMG_HI, KLS in UBLO. atop_facts.                (* [comment removed for export] *)
  assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) /\ PG + 1 <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. Z.div_mod_to_equations. lia. }
  step. if_cases K0; zify_cond K0.                               (* [comment removed for export] *)
  { apply evtF_done. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. intros NE. exfalso. lia. }
  specialize (SHP ltac:(lia)). specialize (RPG ltac:(lia)).
  assert (PW1 : pgw = 1) by (rewrite HPW; destruct (Z.eqb_spec (n mod 8) 0); [lia|reflexivity]). clear HPW. subst pgw.
  step. callp can_poison_spec; [exact CANP|]. step. if_lit.      (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  2: step; step; step; step; step; step; zstep.                  (* [comment removed for export] *)
  2: step; if_cases K2; zify_cond K2; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; step; step; zstep; zstep.                             (* [comment removed for export] *)
  2: step; if_cases K3; zify_cond K3; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: step; step; lstep; zstep; zstep.                          (* [comment removed for export] *)
  all: setreg 10 (Z_to_bv 64 PG) ltac:(rewrite HPG; unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; f_equal; Z.div_mod_to_equations; lia).
  all: zstep; zstep; zstep.                                      (* [comment removed for export] *)
  all: rewrite (land_ones_r n) by lia; change 7 with (2^3 - 1) at 1; rewrite (zb_land_mask n 3) by lia; change (2^3) with 8.
  all: sstep.                                                    (* [comment removed for export] *)
  all: apply evtF_done; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
  all: intros _; assumption.
Qed.



Definition allocBC_gen__stmt : Prop := forall (L : alayout) RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (pj : byte) (sj : list byte)
    (tb : list word) (tr : list Z) (fr0 : list byte) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
  (al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
  (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> tclr AB 65536 -> sclr (al_store L) 8388608 ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  poison_cells m -> rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (allocBC_postG L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 14).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 15).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 16).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 17).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 21).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 22).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 23).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 24).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 25).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 26).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 27).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 28).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 29).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 30).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 31).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 32).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 33).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 34).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 36).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 37).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 38).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 40).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 41).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 42).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 43).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 44).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 45).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 46).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 47).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 48).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 49).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 50).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 51).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 52).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 53).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen__stmt 54).
#[using="Type"] Lemma allocBC_gen__body : ltac:(let T := type of (fun (h : allocBC_gen__stmt) => h L RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sj tb tr fr0 ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (t, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (pc, (pj, (sj, (tb, (tr, (fr0, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, s11v))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS XTAB SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RTLS RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. clear -AB16 RZM. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  (nd_pre PC 7%nat; intros PC1 PC2 PC3 PC4 PC5 PC6 PC7; nd_post).
  pose proof (munch_refl (allocBC_WG L sp UB PG pgw n) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS.
  snapshot [(UB - 16, UB)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
            (shad UB, shad UB + shlen (n - n mod 8));
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  box SHP.
  step. step. if_cases K0; zify_cond K0. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. setreg 20 (Z_to_bv 64 UB) ltac:(rewrite HUB; reflexivity).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -UB16. Z.div_mod_to_equations. lia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }              (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }             (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros a Ha. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. lia. }
  clear MUh WMh. box HDR.
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  box SHA. box SHU.          (* [comment removed for export] *)
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ = 1 + _ => exact SZ
       | |- u64arr _ _ _ _ => exact TB
       | |- length _ = _ => exact LTB
       | |- map _ _ = _ => exact TRF
       | |- In _ _ => exact TRU
       | |- ADEPOT _ _ _ => exact DEP'
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (UB - 16, UB); (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; lia).
  carry SHA MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)). carry SHU MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step. zstep. zstep.                                (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (shad AB)) ltac:(unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. zstep. zstep.                                            (* [comment removed for export] *)
  rewrite (land_align8_48 n) by lia.
  step. if_cases K4; zify_cond K4.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa5880 _ => exact PC1
         | |- rw_cells _ _ 0xae9f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf6e0 _ => exact PC5
         | |- rw_cells _ _ 0xae25c _ => exact PC6
         | |- rw_cells _ _ 0xac24d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    (* [comment removed for export] *)
    rewrite K4. rewrite K4 in SHU. pose proof SHU as W0. destruct W0 as [[[WF X1] X2] X3]. cbn in WF. destruct sj; [exact SHU| cbn in WF; discriminate].
  - (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UB (n - n mod 8) 0 lo sj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ (shad _) _ => exact SHU
         end.
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- rng _ _ _ => solve_rng
         | |- ablk _ _ => unfold ablk; right; atop_facts; lia
         | |- _ => atop_facts; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa5880 _ => exact PC1
         | |- rw_cells _ _ 0xae9f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf6e0 _ => exact PC5
         | |- rw_cells _ _ 0xae25c _ => exact PC6
         | |- rw_cells _ _ 0xac24d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocBC_gen : ltac:(let t := eval cbv delta [allocBC_gen__stmt] in allocBC_gen__stmt in exact t).
Proof. exact allocBC_gen__body. Qed.
End WithDepot.
End CANSEC1.
End TwB.
End F_aalloc2g.

(* [comment removed for export] *)
Module F_aalloc2g0.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation allocBC_WG L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_gen0__stmt : Prop := forall (L : alayout) RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (pj : byte) (sj : list byte)
    (tb : list word) (tr : list Z) (fr0 : list byte) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
  (al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
  (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> tclr AB 65536 -> sclr (al_store L) 8388608 ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  poison_cells m -> rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (allocBC_postG DI L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 14).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 15).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 16).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 17).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 21).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 22).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 23).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 24).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 25).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 26).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 27).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 28).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 29).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 30).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 31).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 32).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 33).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 34).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 36).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 37).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 38).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 40).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 41).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 42).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 43).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 44).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 45).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 46).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 47).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 48).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 49).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 50).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 51).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 52).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 53).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 54).
#[using="Type"] Lemma allocBC_gen0__body : ltac:(let T := type of (fun (h : allocBC_gen0__stmt) => h L RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sj tb tr fr0 ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (t, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (pc, (pj, (sj, (tb, (tr, (fr0, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, s11v))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS XTAB SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RTLS RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. clear -AB16 RZM. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  (nd_pre PC 7%nat; intros PC1 PC2 PC3 PC4 PC5 PC6 PC7; nd_post).
  pose proof (munch_refl (allocBC_WG L sp UB PG pgw n) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS.
  snapshot [(UB - 16, UB)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
            (shad UB, shad UB + shlen (n - n mod 8));
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  box SHP.
  step. step. if_cases K0; zify_cond K0. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. setreg 20 (Z_to_bv 64 UB) ltac:(rewrite HUB; reflexivity).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -UB16. Z.div_mod_to_equations. lia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }              (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }             (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros a Ha. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. lia. }
  clear MUh WMh. box HDR.
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  box SHA. box SHU.          (* [comment removed for export] *)
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ = 1 + _ => exact SZ
       | |- u64arr _ _ _ _ => exact TB
       | |- length _ = _ => exact LTB
       | |- map _ _ = _ => exact TRF
       | |- In _ _ => exact TRU
       | |- ADEPOT _ _ _ => exact DEP'
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (UB - 16, UB); (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; lia).
  carry SHA MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)). carry SHU MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step. zstep. zstep.                                (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (shad AB)) ltac:(unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. zstep. zstep.                                            (* [comment removed for export] *)
  rewrite (land_align8_48 n) by lia.
  step. if_cases K4; zify_cond K4.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa54a0 _ => exact PC1
         | |- rw_cells _ _ 0xae5f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf2e0 _ => exact PC5
         | |- rw_cells _ _ 0xade5c _ => exact PC6
         | |- rw_cells _ _ 0xabe4d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    (* [comment removed for export] *)
    rewrite K4. rewrite K4 in SHU. pose proof SHU as W0. destruct W0 as [[[WF X1] X2] X3]. cbn in WF. destruct sj; [exact SHU| cbn in WF; discriminate].
  - (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UB (n - n mod 8) 0 lo sj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ (shad _) _ => exact SHU
         end.
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- rng _ _ _ => solve_rng
         | |- ablk _ _ => unfold ablk; right; atop_facts; lia
         | |- _ => atop_facts; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa54a0 _ => exact PC1
         | |- rw_cells _ _ 0xae5f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf2e0 _ => exact PC5
         | |- rw_cells _ _ 0xade5c _ => exact PC6
         | |- rw_cells _ _ 0xabe4d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocBC_gen0 : ltac:(let t := eval cbv delta [allocBC_gen0__stmt] in allocBC_gen0__stmt in exact t).
Proof. exact allocBC_gen0__body. Qed.
End WithDepot.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section WithDepot.
Variable DI : ADepotIface.

Notation allocBC_WG L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_gen0__stmt : Prop := forall (L : alayout) RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (pj : byte) (sj : list byte)
    (tb : list word) (tr : list Z) (fr0 : list byte) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n -> is_primary n = true ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
  (al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
  (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> tclr AB 65536 -> sclr (al_store L) 8388608 ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 8192 -> PG + 1 <= 0x10007fff8000 ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells asegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
  (n mod 8 <> 0 -> rw_cells asegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  poison_cells m -> rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF asegs RNG (allocBC_postG DI L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 7).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 8).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 14).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 15).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 16).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 17).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 21).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 22).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 23).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 24).
Variable AB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 25).
Variable UB : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 26).
Variable PG : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 27).
Variable pgw : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 28).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 29).
Variable b0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 30).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 31).
Variable szh : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 32).
Variable szl : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 33).
Variable ctxj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 34).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 35).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 36).
Variable pj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 37).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 38).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 40).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 41).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 42).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 43).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 44).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 45).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 46).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 47).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 48).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 49).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 50).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 51).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 52).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 53).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocBC_gen0__stmt 54).
#[using="Type"] Lemma allocBC_gen0__body : ltac:(let T := type of (fun (h : allocBC_gen0__stmt) => h L RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sj tb tr fr0 ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (t, (AB, (UB, (PG, (pgw, (lo, (b0, (b1, (szh, (szl, (ctxj, (sz, (pc, (pj, (sj, (tb, (tr, (fr0, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, s11v))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS XTAB SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RTLS RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. clear -AB16 RZM. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  (nd_pre PC 7%nat; intros PC1 PC2 PC3 PC4 PC5 PC6 PC7; nd_post).
  pose proof (munch_refl (allocBC_WG L sp UB PG pgw n) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS.
  snapshot [(UB - 16, UB)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
            (shad UB, shad UB + shlen (n - n mod 8));
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  box SHP.
  step. step. if_cases K0; zify_cond K0. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. setreg 20 (Z_to_bv 64 UB) ltac:(rewrite HUB; reflexivity).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -UB16. Z.div_mod_to_equations. lia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }              (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }             (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros a Ha. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. lia. }
  clear MUh WMh. box HDR.
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  box SHA. box SHU.          (* [comment removed for export] *)
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ = 1 + _ => exact SZ
       | |- u64arr _ _ _ _ => exact TB
       | |- length _ = _ => exact LTB
       | |- map _ _ = _ => exact TRF
       | |- In _ _ => exact TRU
       | |- ADEPOT _ _ _ => exact DEP'
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (UB - 16, UB); (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; lia).
  carry SHA MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)). carry SHU MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia_relc)).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step. zstep. zstep.                                (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (shad AB)) ltac:(unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. zstep. zstep.                                            (* [comment removed for export] *)
  rewrite (land_align8_48 n) by lia.
  step. if_cases K4; zify_cond K4.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa5880 _ => exact PC1
         | |- rw_cells _ _ 0xae9f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf6e0 _ => exact PC5
         | |- rw_cells _ _ 0xae25c _ => exact PC6
         | |- rw_cells _ _ 0xac24d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    (* [comment removed for export] *)
    rewrite K4. rewrite K4 in SHU. pose proof SHU as W0. destruct W0 as [[[WF X1] X2] X3]. cbn in WF. destruct sj; [exact SHU| cbn in WF; discriminate].
  - (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UB (n - n mod 8) 0 lo sj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ (shad _) _ => exact SHU
         end.
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- rng _ _ _ => solve_rng
         | |- ablk _ _ => unfold ablk; right; atop_facts; lia
         | |- _ => atop_facts; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells asegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia_relc)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_specG RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xa5880 _ => exact PC1
         | |- rw_cells _ _ 0xae9f8 _ => exact PC4
         | |- rw_cells _ _ 0xaf6e0 _ => exact PC5
         | |- rw_cells _ _ 0xae25c _ => exact PC6
         | |- rw_cells _ _ 0xac24d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_postG. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed.
End Zd1.
#[using="Type"] Lemma allocBC_gen0 : ltac:(let t := eval cbv delta [allocBC_gen0__stmt] in allocBC_gen0__stmt in exact t).
Proof. exact allocBC_gen0__body. Qed.
End WithDepot.
End CANSEC1.
End TwB.
End F_aalloc2g0.

(* [comment removed for export] *)
Module F_aunmap.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition unmap_entry := 0x69ae8.
End CANSEC1.
Abbreviation UNMAP_STACK := 48.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma adec_munmap_Some : forall addr len rsp a, adec_munmap addr len rsp = Some a ->
  a = 0 /\ exists ci : list (word * nat), rsp = eff0 (Z_to_bv 64 0)      (* [comment removed for export] *)
                   \/ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] ci.
Proof.
  intros addr len rsp a H. unfold adec_munmap in H.
  destruct (dec_munmap addr len rsp) as [[e|b]|] eqn:D; try discriminate. injection H as <-. split; [reflexivity|].
  pose proof (dec_munmap_Some _ _ _ _ D) as E. exists []. destruct b; [right| left]; exact E.
Qed.

(* [comment removed for export] *)
Section STUB.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).
#[using="Type"] Lemma rt_munmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len : Z) (x12 x13 x14 x15 x17 : word),
  @implF node asegs (at_nodeA asegs) (silA ASHM) (npeekA asegs) fst _ RNG (enode (NMunmap addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMunmap addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        (eff_ret rsp) (Z_to_bv 64 len) x12 x13 x14 x15 (Z_to_bv 64 215))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 addr) (Z_to_bv 64 len) x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x682a4) fc None m (seg_rom asegs)).
Proof.
  intros fst RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUB.

(* [comment removed for export] *)
#[using="Type"] Lemma munmap_keep : forall addr len rsp R R' lo n,
  fstepS (NMunmap addr len) rsp R R' -> rng R lo n ->
  (lo + n <= addr \/ addr + mmap_len len <= lo) -> 0 <= addr < 2^64 -> 0 <= len < 2^64 -> rng R' lo n.
Proof.
  intros addr len rsp R R' lo n HF HR HD HA HL. apply fstepS_fstepA in HF.
  eapply fstepA_munmap_rng; [exact HF | exact HR |].
  rewrite !unsigned_lit by lia. unfold mmap_len in HD. exact HD.
Qed.

(* [comment removed for export] *)
Definition unmap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128)]
  /\ rw_cells asegs m 0x1401b8 [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
#[using="Type"] Lemma unmap_or_die_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - UNMAP_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size ->
  AIMG_HI <= addr -> 0 < size -> size mod 4096 = 0 -> addr + size <= ATOP ->
  unmap_cells m ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap addr size) rsp RNG RNG' ->
      munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> unmap_cells m' ->
      implS asegs RNG' (K 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMunmap addr size) (adec_munmap addr size)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 unmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> APOS SPOS SAL ACE UC RA RIMG RTLS RSTK KONT.
  pose proof UC as [GOT LIM]. unfold AIMG_HI, unmap_entry in *. word_range sp SPR.
  pose proof (mmap_len_aligned size SAL) as ML.
  pose proof (munch_refl [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m) as MU.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => a = 0 /\ exists rsp m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fstepS (NMunmap addr size) rsp RNG RNG'
               /\ munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m'
               /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ unmap_cells m'
               /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' (-> & PO). destruct_exs PO. (nd_pre PO 6%nat; intros HF MU' MI' ST' UC' ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT; [exact HF | exact MU' | exact MI' | exact ST' | exact UC']. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 APOS ACE. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SPOS ACE APOS. lia. }   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_munmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  (destruct (adec_munmap_Some _ _ _ _ Hdec) as (-> & ndR1__); nd_pre ndR1__ 2%nat; intros ci SH; nd_post).
  assert (HA : 0 <= addr < 2^64) by (clear -ACE APOS SPOS; lia). assert (HL : 0 <= size < 2^64) by (clear -ACE APOS SPOS; lia).
  assert (D1 : lo + (bv_unsigned sp - lo) <= addr \/ addr + mmap_len size <= lo) by (clear -ACE CEIL APOS SPOS ML; lia).
  assert (D2 : 0x10000 + 0x5f3000 <= addr \/ addr + mmap_len size <= 0x10000) by (clear -ACE CEIL LO SPR APOS SPOS ML; lia).
  apply (munmap_keep _ _ _ _ _ _ _ HF) in RSTK; [| exact D1 | exact HA | exact HL].
  unfold rng_aimg in RIMG. apply (munmap_keep _ _ _ _ _ _ _ HF) in RIMG; [| exact D2 | exact HA | exact HL].
  fold (rng_aimg RNG') in RIMG. clear D1 D2.
  unfold rt_regs.
  replace (ret_pc (Z_to_bv 64 432920)) with (Z_to_bv 64 432920 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  destruct SH as [-> | ->];
    [ (* [comment removed for export] *) cbn [eff_ret]; rewrite eff_mem_eff0
    | (* [comment removed for export] *) cbn [eff_ret]; rewrite eff_mem_unmaps; rewrite ML; sys_mem_unmaps ].
  all: step; step; step; step.                                 (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; if_lit.                               (* [comment removed for export] *)
  all: zstep; step.                                            (* [comment removed for export] *)
  all: change (Z.b2z (18446744073709547520 <? 0)) with 0.
  all: step; if_lit.                                           (* [comment removed for export] *)
  all: step; step.                                             (* [comment removed for export] *)
  all: step; step; step; step; if_lit.                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; step; step; step.                     (* [comment removed for export] *)
  all: lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -48) _ |- _ =>
         lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; split; [reflexivity|].
  all: eexists (_ : resp); do 16 eexists; split; [exact HF|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: split; [split; eassumption| reflexivity].
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition unmap_entry := 0x69b50.
End CANSEC1.
Abbreviation UNMAP_STACK := 48.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma adec_munmap_Some : forall addr len rsp a, adec_munmap addr len rsp = Some a ->
  a = 0 /\ exists ci : list (word * nat), rsp = eff0 (Z_to_bv 64 0)      (* [comment removed for export] *)
                   \/ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] ci.
Proof.
  intros addr len rsp a H. unfold adec_munmap in H.
  destruct (dec_munmap addr len rsp) as [[e|b]|] eqn:D; try discriminate. injection H as <-. split; [reflexivity|].
  pose proof (dec_munmap_Some _ _ _ _ D) as E. exists []. destruct b; [right| left]; exact E.
Qed.

(* [comment removed for export] *)
Section STUB.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).
#[using="Type"] Lemma rt_munmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len : Z) (x12 x13 x14 x15 x17 : word),
  @implF node asegs (at_nodeA asegs) (silA ASHM) (npeekA asegs) fst _ RNG (enode (NMunmap addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMunmap addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        (eff_ret rsp) (Z_to_bv 64 len) x12 x13 x14 x15 (Z_to_bv 64 215))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 addr) (Z_to_bv 64 len) x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x6830c) fc None m (seg_rom asegs)).
Proof.
  intros fst RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUB.

(* [comment removed for export] *)
#[using="Type"] Lemma munmap_keep : forall addr len rsp R R' lo n,
  fstepS (NMunmap addr len) rsp R R' -> rng R lo n ->
  (lo + n <= addr \/ addr + mmap_len len <= lo) -> 0 <= addr < 2^64 -> 0 <= len < 2^64 -> rng R' lo n.
Proof.
  intros addr len rsp R R' lo n HF HR HD HA HL. apply fstepS_fstepA in HF.
  eapply fstepA_munmap_rng; [exact HF | exact HR |].
  rewrite !unsigned_lit by lia. unfold mmap_len in HD. exact HD.
Qed.

(* [comment removed for export] *)
Definition unmap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528)]
  /\ rw_cells asegs m 0x1405b8 [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
#[using="Type"] Lemma unmap_or_die_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - UNMAP_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size ->
  AIMG_HI <= addr -> 0 < size -> size mod 4096 = 0 -> addr + size <= ATOP ->
  unmap_cells m ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap addr size) rsp RNG RNG' ->
      munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> unmap_cells m' ->
      implS asegs RNG' (K 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMunmap addr size) (adec_munmap addr size)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 unmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> APOS SPOS SAL ACE UC RA RIMG RTLS RSTK KONT.
  pose proof UC as [GOT LIM]. unfold AIMG_HI, unmap_entry in *. word_range sp SPR.
  pose proof (mmap_len_aligned size SAL) as ML.
  pose proof (munch_refl [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m) as MU.
  eapply (implF_ebind _ _ _ _ _ _ _ _ _
            (fun a RNG' ms' => a = 0 /\ exists rsp m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fstepS (NMunmap addr size) rsp RNG RNG'
               /\ munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m'
               /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ unmap_cells m'
               /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' (-> & PO). destruct_exs PO. (nd_pre PO 6%nat; intros HF MU' MI' ST' UC' ndR1__; nd_post; revert ndR1__; intros ->).
       eapply KONT; [exact HF | exact MU' | exact MI' | exact ST' | exact UC']. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 APOS ACE. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SPOS ACE APOS. lia. }   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_munmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  (destruct (adec_munmap_Some _ _ _ _ Hdec) as (-> & ndR1__); nd_pre ndR1__ 2%nat; intros ci SH; nd_post).
  assert (HA : 0 <= addr < 2^64) by (clear -ACE APOS SPOS; lia). assert (HL : 0 <= size < 2^64) by (clear -ACE APOS SPOS; lia).
  assert (D1 : lo + (bv_unsigned sp - lo) <= addr \/ addr + mmap_len size <= lo) by (clear -ACE CEIL APOS SPOS ML; lia).
  assert (D2 : 0x10000 + 0x5f4000 <= addr \/ addr + mmap_len size <= 0x10000) by (clear -ACE CEIL LO SPR APOS SPOS ML; lia).
  apply (munmap_keep _ _ _ _ _ _ _ HF) in RSTK; [| exact D1 | exact HA | exact HL].
  unfold rng_aimg in RIMG. apply (munmap_keep _ _ _ _ _ _ _ HF) in RIMG; [| exact D2 | exact HA | exact HL].
  fold (rng_aimg RNG') in RIMG. clear D1 D2.
  unfold rt_regs.
  replace (ret_pc (Z_to_bv 64 433024)) with (Z_to_bv 64 433024 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  destruct SH as [-> | ->];
    [ (* [comment removed for export] *) cbn [eff_ret]; rewrite eff_mem_eff0
    | (* [comment removed for export] *) cbn [eff_ret]; rewrite eff_mem_unmaps; rewrite ML; sys_mem_unmaps ].
  all: step; step; step; step.                                 (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; if_lit.                               (* [comment removed for export] *)
  all: zstep; step.                                            (* [comment removed for export] *)
  all: change (Z.b2z (18446744073709547520 <? 0)) with 0.
  all: step; if_lit.                                           (* [comment removed for export] *)
  all: step; step.                                             (* [comment removed for export] *)
  all: step; step; step; step; if_lit.                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; step; step; step.                     (* [comment removed for export] *)
  all: lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -48) _ |- _ =>
         lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; split; [reflexivity|].
  all: eexists (_ : resp); do 16 eexists; split; [exact HF|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: split; [split; eassumption| reflexivity].
Qed.
End CANSEC2.
End TwB.
End F_aunmap.

(* [comment removed for export] *)
Module F_rsrvshadow.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ARSRV : Z := 0x6ffa8.
End CANSEC1.
Notation RSRV_STACK := 592 (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition got6 (m : amem) : Prop :=
  rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                            C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)].

Definition arelro0 (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

#[using="Type"] Lemma arelro0_munch : forall W m m', arelro0 m -> munch W m m' ->
  Forall (fun iv => ARELRO_HI <= fst iv \/ snd iv <= ARELRO_LO) W -> arelro0 m'.
Proof.
  intros W m m' RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
  rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia). apply E.
  clear -HW Hi. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *.
  split; [lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma remu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
  mul_div M_REMU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof.
  intros x y Hx Hy. unfold mul_div. rewrite !unsigned_lit by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  apply bv_eq. rewrite bv_modu_unsigned, !unsigned_lit; [reflexivity| | lia | lia].
  split; [apply Z.mod_pos_bound; lia|]. eapply Z.lt_trans; [apply Z.mod_pos_bound; lia| lia].
Qed.

#[using="Type"] Lemma premap_cells_frame : forall m m' W, premap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x603000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.

#[using="Type"] Lemma got6_frame : forall m m' W, got6 m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> got6 m'.
Proof.
  intros m m' W R MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x603000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold got6. eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia].
Qed.

(* [comment removed for export] *)
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ARSRV : Z := 0x70010.
End CANSEC1.
Notation RSRV_STACK := 592 (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition got6 (m : amem) : Prop :=
  rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                            C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)].

Definition arelro0 (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

#[using="Type"] Lemma arelro0_munch : forall W m m', arelro0 m -> munch W m m' ->
  Forall (fun iv => ARELRO_HI <= fst iv \/ snd iv <= ARELRO_LO) W -> arelro0 m'.
Proof.
  intros W m m' RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
  rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia). apply E.
  clear -HW Hi. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *.
  split; [lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma remu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
  mul_div M_REMU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof.
  intros x y Hx Hy. unfold mul_div. rewrite !unsigned_lit by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  apply bv_eq. rewrite bv_modu_unsigned, !unsigned_lit; [reflexivity| | lia | lia].
  split; [apply Z.mod_pos_bound; lia|]. eapply Z.lt_trans; [apply Z.mod_pos_bound; lia| lia].
Qed.

#[using="Type"] Lemma premap_cells_frame : forall m m' W, premap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x604000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.

#[using="Type"] Lemma got6_frame : forall m m' W, got6 m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> got6 m'.
Proof.
  intros m m' W R MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x604000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold got6. eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia].
Qed.

(* [comment removed for export] *)
End CANSEC2.
End TwB.
End F_rsrvshadow.

(* [comment removed for export] *)
Module F_aflush.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import SysStep.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF NodesA.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition flush_entry := 0x55e80.
End CANSEC1.
Abbreviation FLUSH_STACK := 64.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma mem_to_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p : Z),
  mem_inv asegs m -> poison_cells m ->
  (0 <= p /\ p + 1 <= 0x7fff8000 \/ 0x10007fff8000 <= p) -> p <= 0x7fffffffffff ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2' a3' a4' a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (shad p)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55ecc) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros MI PC PLO PHI RA RIMG RTLS.
  (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [exfalso; lia|].           (* [comment removed for export] *)
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: change (2147450880 + Z.shiftr p 3) with (shad p).
  all: step.                                           (* [comment removed for export] *)
  all: apply evtF_done; do 8 eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma zeros_same : forall (m : amem) A L a n x,
  rw_cells asegs m A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))] -> 0x603000 <= A -> 0 <= L ->
  A <= a -> a + n <= A + L -> 0 < n ->
  apply_zeros m [(wa a, Z_to_bv 64 n)] x = m x.
Proof.
  intros m A L a n x H HA HL Ha Han Hn.
  pose proof (rw_cells_bound asegs m A _ H) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  rewrite apply_zeros_spec by lia. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity.
  destruct H as [[Hwf Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  (nd_pre Hb 3%nat; intros _ _ Hb; nd_post). (nd_pre Hw 3%nat; intros _ _ Hw; nd_post). cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
  set (i := bv_unsigned x - A).
  specialize (Hb (Z.to_nat i) ltac:(rewrite repeat_length; subst i; lia)). specialize (Hw i ltac:(subst i; lia)).
  rewrite Z2Nat.id in Hb by (subst i; lia).
  replace (A + i) with (bv_unsigned x) in Hb, Hw by (subst i; lia). rewrite wa_unsigned_id in Hb, Hw.
  rewrite nth_error_repeat in Hb by (subst i; lia).
  rewrite ref_wview_overlay in Hw by lia. unfold mrd in Hb. destruct (m x) as [b|]; [| exfalso; apply Hw; reflexivity].
  exact (eq_sym Hb).
Qed.

#[using="Type"] Lemma munch_zeros_same : forall W (m0 m : amem) A L a n,
  rw_cells asegs m A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))] -> 0x603000 <= A -> 0 <= L ->
  A <= a -> a + n <= A + L -> 0 < n ->
  munch W m0 m -> munch W m0 (apply_zeros m [(wa a, Z_to_bv 64 n)]).
Proof. intros W m0 m A L a n H HA HL Ha Han Hn MU x Hx. rewrite (zeros_same m A L a n x H HA HL Ha Han Hn). apply MU. exact Hx. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align4096f : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma page_round_up_multf : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtS_evtF_or : forall (sil : footprint -> machine_state -> machine_state -> Prop) RNG (Q : machine_state -> Prop) ms,
  evtF asegs RNG (fun ms1 => Q ms1 \/ exists ms2, sil RNG ms1 ms2 /\ evtS asegs sil RNG Q ms2) ms -> evtS asegs sil RNG Q ms.
Proof.
  intros sil RNG Q ms H. eapply evtS_cut; [apply evtS_of_evtF; exact H|].
  intros ms1 [HQ|(ms2 & Hs & K)]; [apply evtS_done; exact HQ| eapply evtS_sil; eauto].
Qed.

Definition flush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition flush_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->        (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  ms mod 4096 = 0 ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->
  evtS asegs (silA ASHM) RNG (flush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)      (* [comment removed for export] *)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 flush_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 34).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 35).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 37).
Let SB := shad mb.
Let L := shlen ms.
#[using="SB L"] Lemma flush_spec__body : ltac:(let T := type of (fun (h : flush_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI PC PRM RR -> -> MLO MPOS MCE RA RIMG RTLS RSTK MSAL SHZ.
  unfold flush_entry in *. word_range sp SPR. pose proof MLO as MLO0. unfold ablk, AIMG_HI, KLS in MLO. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof PRM as PRM0. (nd_pre PRM0 7%nat; intros GPG PGSZ MLIM F216 F240 CAN LPG; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  chg (shad mb) SB. chg (shlen ms) L.
  assert (SHR : 0x800b8600 <= SB /\ SB + L <= 0x10007fff8000 /\ 0 < L /\ shad (mb + ms) = SB + L
                /\ ((SB + L <= 0x8fff7000) \/ 0x2008fff7000 <= SB)).
  { subst SB L. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -MLO MPOS MCE ATR MSAL. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (SEAL : rw_cells asegs m 0xa54f0 [C8 (Z_to_bv 64 1)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xa54f0 (le8 (Z_to_bv 64 1)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  box SHZ.
  apply evtS_evtF_or.
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG | exact RTLS].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & ->).
  replace (ret_pc (Z_to_bv 64 351904)) with (Z_to_bv 64 351904 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. zstep.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (mb + ms)) ltac:(f_equal; clear; lia).
  step.                                                        (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG | exact RTLS].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (b1' & b2' & b3' & b4' & b5' & b6' & b7' & u0' & ->).
  replace (ret_pc (Z_to_bv 64 351916)) with (Z_to_bv 64 351916 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. step.                                                  (* [comment removed for export] *)
  do 5 step.                                                   (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.                                                        (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  set (PB := SB + 4095 - (SB + 4095) mod 4096). set (PE := SB + L - (SB + L) mod 4096).      (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 PB) ltac:(rewrite land_align4096f by (clear -SHR; lia); reflexivity).
  setreg 11 (Z_to_bv 64 PE) ltac:(rewrite land_align4096f by (clear -SHR; lia); rewrite (proj1 (proj2 (proj2 (proj2 SHR)))); reflexivity).
  assert (PBR : SB <= PB /\ PB mod 4096 = 0 /\ PE <= SB + L /\ PE mod 4096 = 0) by (subst PB PE; clear -SHR; Z.div_mod_to_equations; lia).
  step. if_cases KR; zify_cond KR.                             (* [comment removed for export] *)
  - (* [comment removed for export] *)
    do 5 step.                                                 (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.                                                      (* [comment removed for export] *)
    apply evtF_done. left. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
  - zstep. step.                                               (* [comment removed for export] *)
    do 5 step.                                                 (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.                                                      (* [comment removed for export] *)
    step. step. step. if_lit.                                  (* [comment removed for export] *)
    step. step. if_lit.                                        (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    step_ecall.
    (* [comment removed for export] *)
    assert (PRU : page_round_up_Z (PE - PB) = PE - PB) by (apply page_round_up_multf; [clear -PBR; Z.div_mod_to_equations; lia | clear -KR; lia]).
    right. eexists. split.
    { exists PB, (PE - PB). split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|].
      split; [clear -SHR PBR; lia|]. split; [unfold page_size; exact (proj1 (proj2 PBR))|]. split; [clear -SHR PBR KR; lia|].
      split; [rewrite PRU; clear -SHR PBR; lia|]. split; [| reflexivity].
      rewrite PRU. unfold ASHM. (pose proof SHR as ndP__; nd_pre ndP__ 5%nat; intros S1 S2 _ _ [LOW|HIGH]; nd_post); clearbody PB PE;
        [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd]; cbn [fst snd]; first [clear -S1 S2 LOW PBR KR | clear -S1 S2 HIGH PBR KR]; lia. }
    apply evtS_of_evtF. unfold madv_rsp. sys_nret_raw. rewrite PRU.
    (* [comment removed for export] *)
    unbox SHZ. unfold zeros in SHZ.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (apply_zeros ?mm _) _) =>
      pose proof (rw_cells_transport asegs _ m mm _ _ SHZ MU WM
                    ltac:(cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR SPR CEIL LO ATR; lia)) as SHZ1;
      pose proof (munch_zeros_same _ m mm SB L PB (PE - PB) SHZ1 ltac:(clear -SHR; lia) ltac:(clear -SHR; lia)
                    ltac:(clear -PBR; lia) ltac:(clear -PBR; lia) ltac:(clear -KR; lia) MU) as MUz end.
    clear MU SHZ. clearbody PB PE.
    assert (PBB : 0 <= PB /\ PE <= 0x10007fff8000) by (clear -SHR PBR; lia).
    sys_mem_zeros.
    zstep. step.                                               (* [comment removed for export] *)
    apply evtF_done. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; destruct SHR as (S1 & _); destruct PBR as (S2 & _); lia).
Qed.
End Zd1.
#[using="Type"] Lemma flush_spec : ltac:(let t := eval cbv delta [flush_spec__stmt] in flush_spec__stmt in exact t).
Proof. exact flush_spec__body. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition flush_entry := 0x55ee8.
End CANSEC1.
Abbreviation FLUSH_STACK := 64.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma mem_to_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (p : Z),
  mem_inv asegs m -> poison_cells m ->
  (0 <= p /\ p + 1 <= 0x7fff8000 \/ 0x10007fff8000 <= p) -> p <= 0x7fffffffffff ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => exists a1' a2' a3' a4' a5' a6' a7' t0',
      ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (shad p)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55f34) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros MI PC PLO PHI RA RIMG RTLS.
  (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [exfalso; lia|].           (* [comment removed for export] *)
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: change (2147450880 + Z.shiftr p 3) with (shad p).
  all: step.                                           (* [comment removed for export] *)
  all: apply evtF_done; do 8 eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma zeros_same : forall (m : amem) A L a n x,
  rw_cells asegs m A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))] -> 0x604000 <= A -> 0 <= L ->
  A <= a -> a + n <= A + L -> 0 < n ->
  apply_zeros m [(wa a, Z_to_bv 64 n)] x = m x.
Proof.
  intros m A L a n x H HA HL Ha Han Hn.
  pose proof (rw_cells_bound asegs m A _ H) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  rewrite apply_zeros_spec by lia. unfold in_range.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity.
  destruct H as [[Hwf Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  (nd_pre Hb 3%nat; intros _ _ Hb; nd_post). (nd_pre Hw 3%nat; intros _ _ Hw; nd_post). cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
  set (i := bv_unsigned x - A).
  specialize (Hb (Z.to_nat i) ltac:(rewrite repeat_length; subst i; lia)). specialize (Hw i ltac:(subst i; lia)).
  rewrite Z2Nat.id in Hb by (subst i; lia).
  replace (A + i) with (bv_unsigned x) in Hb, Hw by (subst i; lia). rewrite wa_unsigned_id in Hb, Hw.
  rewrite nth_error_repeat in Hb by (subst i; lia).
  rewrite ref_wview_overlay in Hw by lia. unfold mrd in Hb. destruct (m x) as [b|]; [| exfalso; apply Hw; reflexivity].
  exact (eq_sym Hb).
Qed.

#[using="Type"] Lemma munch_zeros_same : forall W (m0 m : amem) A L a n,
  rw_cells asegs m A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))] -> 0x604000 <= A -> 0 <= L ->
  A <= a -> a + n <= A + L -> 0 < n ->
  munch W m0 m -> munch W m0 (apply_zeros m [(wa a, Z_to_bv 64 n)]).
Proof. intros W m0 m A L a n H HA HL Ha Han Hn MU x Hx. rewrite (zeros_same m A L a n x H HA HL Ha Han Hn). apply MU. exact Hx. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align4096f : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma page_round_up_multf : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtS_evtF_or : forall (sil : footprint -> machine_state -> machine_state -> Prop) RNG (Q : machine_state -> Prop) ms,
  evtF asegs RNG (fun ms1 => Q ms1 \/ exists ms2, sil RNG ms1 ms2 /\ evtS asegs sil RNG Q ms2) ms -> evtS asegs sil RNG Q ms.
Proof.
  intros sil RNG Q ms H. eapply evtS_cut; [apply evtS_of_evtF; exact H|].
  intros ms1 [HQ|(ms2 & Hs & K)]; [apply evtS_done; exact HQ| eapply evtS_sil; eauto].
Qed.

Definition flush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition flush_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FLUSH_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 mb -> a1 = Z_to_bv 64 ms ->
  ablk mb (mb + ms) -> 0 < ms -> mb + ms <= ATOP ->        (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  ms mod 4096 = 0 ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->
  evtS asegs (silA ASHM) RNG (flush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)      (* [comment removed for export] *)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 flush_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 34).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 35).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 36).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'flush_spec__stmt 37).
Let SB := shad mb.
Let L := shlen ms.
#[using="SB L"] Lemma flush_spec__body : ltac:(let T := type of (fun (h : flush_spec__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, lo)))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI PC PRM RR -> -> MLO MPOS MCE RA RIMG RTLS RSTK MSAL SHZ.
  unfold flush_entry in *. word_range sp SPR. pose proof MLO as MLO0. unfold ablk, AIMG_HI, KLS in MLO. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof PRM as PRM0. (nd_pre PRM0 7%nat; intros GPG PGSZ MLIM F216 F240 CAN LPG; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - FLUSH_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  chg (shad mb) SB. chg (shlen ms) L.
  assert (SHR : 0x800b8800 <= SB /\ SB + L <= 0x10007fff8000 /\ 0 < L /\ shad (mb + ms) = SB + L
                /\ ((SB + L <= 0x8fff7000) \/ 0x2008fff7000 <= SB)).
  { subst SB L. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -MLO MPOS MCE ATR MSAL. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (SEAL : rw_cells asegs m 0xa58d0 [C8 (Z_to_bv 64 1)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xa58d0 (le8 (Z_to_bv 64 1)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  box SHZ.
  apply evtS_evtF_or.
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG | exact RTLS].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & ->).
  replace (ret_pc (Z_to_bv 64 352008)) with (Z_to_bv 64 352008 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. zstep.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (mb + ms)) ltac:(f_equal; clear; lia).
  step.                                                        (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (mem_to_shadow_spec RNG); [eassumption | | clear -MLO MPOS; lia | clear -MLO MPOS MCE ATR; lia | rewrite unsigned_lit by (clear; lia); clear; lia | exact RIMG | exact RTLS].
    eapply poison_cells_frame; [exact PC | exact MU | exact WM | apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPR CEIL LO; lia| apply Forall_nil]]. }
  cbv beta. intros ms' (b1' & b2' & b3' & b4' & b5' & b6' & b7' & u0' & ->).
  replace (ret_pc (Z_to_bv 64 352020)) with (Z_to_bv 64 352020 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. step.                                                  (* [comment removed for export] *)
  do 5 step.                                                   (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.                                                        (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  set (PB := SB + 4095 - (SB + 4095) mod 4096). set (PE := SB + L - (SB + L) mod 4096).      (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 PB) ltac:(rewrite land_align4096f by (clear -SHR; lia); reflexivity).
  setreg 11 (Z_to_bv 64 PE) ltac:(rewrite land_align4096f by (clear -SHR; lia); rewrite (proj1 (proj2 (proj2 (proj2 SHR)))); reflexivity).
  assert (PBR : SB <= PB /\ PB mod 4096 = 0 /\ PE <= SB + L /\ PE mod 4096 = 0) by (subst PB PE; clear -SHR; Z.div_mod_to_equations; lia).
  step. if_cases KR; zify_cond KR.                             (* [comment removed for export] *)
  - (* [comment removed for export] *)
    do 5 step.                                                 (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.                                                      (* [comment removed for export] *)
    apply evtF_done. left. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
  - zstep. step.                                               (* [comment removed for export] *)
    do 5 step.                                                 (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
      lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
    step.                                                      (* [comment removed for export] *)
    step. step. step. if_lit.                                  (* [comment removed for export] *)
    step. step. if_lit.                                        (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    step_ecall.
    (* [comment removed for export] *)
    assert (PRU : page_round_up_Z (PE - PB) = PE - PB) by (apply page_round_up_multf; [clear -PBR; Z.div_mod_to_equations; lia | clear -KR; lia]).
    right. eexists. split.
    { exists PB, (PE - PB). split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|].
      split; [clear -SHR PBR; lia|]. split; [unfold page_size; exact (proj1 (proj2 PBR))|]. split; [clear -SHR PBR KR; lia|].
      split; [rewrite PRU; clear -SHR PBR; lia|]. split; [| reflexivity].
      rewrite PRU. unfold ASHM. (pose proof SHR as ndP__; nd_pre ndP__ 5%nat; intros S1 S2 _ _ [LOW|HIGH]; nd_post); clearbody PB PE;
        [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd]; cbn [fst snd]; first [clear -S1 S2 LOW PBR KR | clear -S1 S2 HIGH PBR KR]; lia. }
    apply evtS_of_evtF. unfold madv_rsp. sys_nret_raw. rewrite PRU.
    (* [comment removed for export] *)
    unbox SHZ. unfold zeros in SHZ.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (apply_zeros ?mm _) _) =>
      pose proof (rw_cells_transport asegs _ m mm _ _ SHZ MU WM
                    ltac:(cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR SPR CEIL LO ATR; lia)) as SHZ1;
      pose proof (munch_zeros_same _ m mm SB L PB (PE - PB) SHZ1 ltac:(clear -SHR; lia) ltac:(clear -SHR; lia)
                    ltac:(clear -PBR; lia) ltac:(clear -PBR; lia) ltac:(clear -KR; lia) MU) as MUz end.
    clear MU SHZ. clearbody PB PE.
    assert (PBB : 0 <= PB /\ PE <= 0x10007fff8000) by (clear -SHR PBR; lia).
    sys_mem_zeros.
    zstep. step.                                               (* [comment removed for export] *)
    apply evtF_done. unfold flush_post. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; destruct SHR as (S1 & _); destruct PBR as (S2 & _); lia).
Qed.
End Zd1.
#[using="Type"] Lemma flush_spec : ltac:(let t := eval cbv delta [flush_spec__stmt] in flush_spec__stmt in exact t).
Proof. exact flush_spec__body. Qed.
End CANSEC2.
End TwB.
End F_aflush.

(* [comment removed for export] *)
Module F_apoison_remap.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Theorem poison_remap_proof : poison_remap_stmt.
Proof.
  unfold poison_remap_stmt.
  intros R k Q RNG. intros until junk. intros ST CEIL LO MI PC PRC RR -> -> -> AL SL SZ HI HE BIG DST RIMG RTLS RSTK RSH KONT.
  unfold PZR_STACK in *. word_range sp SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'. pose proof atop_range as ATR.
  assert (SHR : 0x800b8600 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -AL SL SZ HI' HE ATR. Z.div_mod_to_equations. lia. }
  change (poison0 addr size k) with k.      (* [comment removed for export] *)
  iprefix.
  eapply evtF_cut.
  { eapply (poison_shadow_spec RNG) with (addr := addr) (size := size) (v := 0) (lo := lo); try eassumption; try reflexivity.
    all: try (clear -CEIL LO LO0 SPR AL SL SZ HI HI' HE ATR; first [exact HI | lia]).
    intros _. clear -SHR. lia. }
  cbv beta. intros ms' PO. unfold poison_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUp WMp MIp STp SHZ; nd_post).
  apply evtF_done. eapply KONT. unfold premap_post, PZR_STACK.
  split; [apply fp_le_refl|]. split; [exact (fun H => H)|].
  split. { eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
  split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
  split. { unfold zeros. rewrite ?unsigned_lit in SHZ by (clear; lia). exact SHZ. }
  split; [exact RSH|].
  split; [eapply poison_cells_frame; [exact PC | exact MUp | exact WMp |] | eapply premap_cells_frame; [exact PRC | exact MUp | exact WMp |]];
    (repeat (apply Forall_cons; [cbn; unfold AIMG_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil).
Qed.

(* [comment removed for export] *)
Definition poison_remap : poison_remap_stmt := poison_remap_proof.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Theorem poison_remap_proof : poison_remap_stmt.
Proof.
  unfold poison_remap_stmt.
  intros R k Q RNG. intros until junk. intros ST CEIL LO MI PC PRC RR -> -> -> AL SL SZ HI HE BIG DST RIMG RTLS RSTK RSH KONT.
  unfold PZR_STACK in *. word_range sp SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'. pose proof atop_range as ATR.
  assert (SHR : 0x800b8800 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -AL SL SZ HI' HE ATR. Z.div_mod_to_equations. lia. }
  change (poison0 addr size k) with k.      (* [comment removed for export] *)
  iprefix.
  eapply evtF_cut.
  { eapply (poison_shadow_spec RNG) with (addr := addr) (size := size) (v := 0) (lo := lo); try eassumption; try reflexivity.
    all: try (clear -CEIL LO LO0 SPR AL SL SZ HI HI' HE ATR; first [exact HI | lia]).
    intros _. clear -SHR. lia. }
  cbv beta. intros ms' PO. unfold poison_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUp WMp MIp STp SHZ; nd_post).
  apply evtF_done. eapply KONT. unfold premap_post, PZR_STACK.
  split; [apply fp_le_refl|]. split; [exact (fun H => H)|].
  split. { eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
  split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
  split. { unfold zeros. rewrite ?unsigned_lit in SHZ by (clear; lia). exact SHZ. }
  split; [exact RSH|].
  split; [eapply poison_cells_frame; [exact PC | exact MUp | exact WMp |] | eapply premap_cells_frame; [exact PRC | exact MUp | exact WMp |]];
    (repeat (apply Forall_cons; [cbn; unfold AIMG_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil).
Qed.

(* [comment removed for export] *)
Definition poison_remap : poison_remap_stmt := poison_remap_proof.
End CANSEC2.
End TwB.
End F_apoison_remap.

(* [comment removed for export] *)
Module F_apoisonz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed AsanCtrlProps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma poison_cells_frameD : forall W m m', poison_cells m -> munch W m m' ->
  disjoint_from W 0xa54a0 48 -> disjoint_from W 0xa54d0 8 -> disjoint_from W 0xa7358 16 -> disjoint_from W 0xae5f8 8 ->
  disjoint_from W 0xaf2e0 24 -> disjoint_from W 0xade5c 1 -> disjoint_from W 0x1401a0 8 -> poison_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU D1 D2 D3 D4 D5 D6 D7. unfold poison_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]).
Qed.
#[using="Type"] Lemma premap_cells_frameD : forall W m m', premap_cells m -> munch W m m' ->
  disjoint_from W 0xa5490 8 -> disjoint_from W 0x13e0a0 8 -> disjoint_from W 0x1401b8 8 -> disjoint_from W 0x140200 8 ->
  disjoint_from W 0x140218 8 -> disjoint_from W 0x6015f8 8 -> disjoint_from W 0x601878 8 -> premap_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU D1 D2 D3 D4 D5 D6 D7. unfold premap_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any      (* [comment removed for export] *)
          | (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]) ].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma poison_cells_highD : forall W m m', poison_cells m -> munch W m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros W m m' PC MU HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU PC. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| apply IH]. }
  unfold AIMG_HI in D. eapply poison_cells_frameD; [exact PC | exact MU | ..]; apply D; lia.
Qed.
#[using="Type"] Lemma premap_cells_highD : forall W m m', premap_cells m -> munch W m m' ->
  Forall (fun iv => AIMG_HI <= fst iv /\ (snd iv <= 0x6015f8 \/ 0x60dc48 <= fst iv)) W -> premap_cells m'.
Proof.
  intros W m m' PC MU HW.
  assert (D : forall A n, (A + n <= AIMG_HI \/ (0x6015f8 <= A /\ A + n <= 0x60dc48)) -> 0 < n -> disjoint_from W A n).
  { intros A n HA HN. clear MU PC. induction HW as [|[lo hi] W [H1 H1'] H2 IH]; cbn in *; [exact I|]. split; [unfold AIMG_HI in *; lia| apply IH]. }
  unfold AIMG_HI in D. eapply premap_cells_frameD; [exact PC | exact MU | ..]; apply D; lia.
Qed.

Definition poison0_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono asegs m m'
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]
  /\ poison_cells m' /\ premap_cells m' /\ arelro0 m'.

#[using="Type"] Lemma poison0_spec : forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= ATOP ->     (* [comment removed for export] *)
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      poison0_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5759c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC PRM RR -> -> -> AL SL SPOS HI HCE DST RIMG RTLS RSTK RSH KONT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR. unfold PZR_STACK in *.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'. pose proof atop_range as ATR.   (* [comment removed for export] *)
  assert (SHR : 0x800b8600 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -AL SL SPOS HI' HCE ATR. Z.div_mod_to_equations. lia. }
  destruct (Z.lt_ge_cases size 524288) as [SMALL | BIG].
  - (* [comment removed for export] *)
    rewrite (poison0_small _ addr size k AL) by (clear -SPOS SMALL; lia).
    iprefix.
    eapply evtF_cut.
    { eapply (poison_shadow_spec RNG) with (addr := addr) (size := size) (v := 0) (lo := lo); try eassumption; try reflexivity.
      all: try (clear -CEIL LO LO0 SPR AL SL SPOS HI HI' HCE SMALL ATR; first [exact HI | lia]).
      intros _. unfold shlen. rewrite Z.shiftr_div_pow2 by (clear; lia). clear -SMALL SPOS. Z.div_mod_to_equations. lia. }
    cbv beta. intros ms' PO. unfold poison_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUp WMp MIp STp SHZ; nd_post).
    apply evtF_done. eapply KONT. unfold poison0_post, PZR_STACK.
    split; [apply fp_le_refl|].
    split. { eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
    split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
    split. { unfold zeros. rewrite ?unsigned_lit in SHZ by (clear; lia). exact SHZ. }
    split; [eapply poison_cells_highD; [exact PC | exact MUp |] | split; [eapply premap_cells_highD; [exact PRM | exact MUp |] | eapply arelro0_munch; [exact RR | exact MUp |]]];
      (repeat (apply Forall_cons; [cbn; unfold AIMG_HI, ARELRO_LO, ARELRO_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil).
  - (* [comment removed for export] *)
    pose proof poison_remap as PR. unfold poison_remap_stmt in PR.
    eapply (PR R k Q RNG) with (addr := addr) (size := size) (lo := lo); try eassumption; try reflexivity.
    all: try (unfold PZR_STACK; clear -CEIL LO LO0 SPR AL SL SPOS HI HI' HCE BIG ATR; first [exact HI | lia]).
    { unfold shlen. rewrite Z.shiftr_div_pow2 by (clear; lia). clear -BIG SL. Z.div_mod_to_equations. lia. }
    intros RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PP.
    unfold premap_post in PP. (nd_pre PP 10%nat; intros LE BW MUp WMp MIp STp SHZ RSH' PC' PRM'; nd_post).
    eapply KONT. unfold poison0_post. unfold PZR_STACK in MUp.
    split; [exact LE|]. split; [exact MUp|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
    split; [exact SHZ|]. split; [exact PC'|]. split; [exact PRM'|].
    eapply arelro0_munch; [exact RR | exact MUp |].
    repeat (apply Forall_cons; [cbn; unfold ARELRO_LO, ARELRO_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma poison_cells_frameD : forall W m m', poison_cells m -> munch W m m' ->
  disjoint_from W 0xa5880 48 -> disjoint_from W 0xa58b0 8 -> disjoint_from W 0xa7738 16 -> disjoint_from W 0xae9f8 8 ->
  disjoint_from W 0xaf6e0 24 -> disjoint_from W 0xae25c 1 -> disjoint_from W 0x1405a0 8 -> poison_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU D1 D2 D3 D4 D5 D6 D7. unfold poison_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]).
Qed.
#[using="Type"] Lemma premap_cells_frameD : forall W m m', premap_cells m -> munch W m m' ->
  disjoint_from W 0xa5870 8 -> disjoint_from W 0x13e4a0 8 -> disjoint_from W 0x1405b8 8 -> disjoint_from W 0x140600 8 ->
  disjoint_from W 0x140618 8 -> disjoint_from W 0x6019f8 8 -> disjoint_from W 0x601c78 8 -> premap_cells m'.
Proof.
  intros W m m' (P1 & P2 & P3 & P4 & P5 & P6 & P7) MU D1 D2 D3 D4 D5 D6 D7. unfold premap_cells.
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any      (* [comment removed for export] *)
          | (eapply cells_frameD; [eassumption | exact MU | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]) ].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma poison_cells_highD : forall W m m', poison_cells m -> munch W m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros W m m' PC MU HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU PC. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| apply IH]. }
  unfold AIMG_HI in D. eapply poison_cells_frameD; [exact PC | exact MU | ..]; apply D; lia.
Qed.
#[using="Type"] Lemma premap_cells_highD : forall W m m', premap_cells m -> munch W m m' ->
  Forall (fun iv => AIMG_HI <= fst iv /\ (snd iv <= 0x6019f8 \/ 0x60dc48 <= fst iv)) W -> premap_cells m'.
Proof.
  intros W m m' PC MU HW.
  assert (D : forall A n, (A + n <= AIMG_HI \/ (0x6019f8 <= A /\ A + n <= 0x60dc48)) -> 0 < n -> disjoint_from W A n).
  { intros A n HA HN. clear MU PC. induction HW as [|[lo hi] W [H1 H1'] H2 IH]; cbn in *; [exact I|]. split; [unfold AIMG_HI in *; lia| apply IH]. }
  unfold AIMG_HI in D. eapply premap_cells_frameD; [exact PC | exact MU | ..]; apply D; lia.
Qed.

Definition poison0_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono asegs m m'
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]
  /\ poison_cells m' /\ premap_cells m' /\ arelro0 m'.

#[using="Type"] Lemma poison0_spec : forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> arelro0 m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= ATOP ->     (* [comment removed for export] *)
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      poison0_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x57604) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC PRM RR -> -> -> AL SL SPOS HI HCE DST RIMG RTLS RSTK RSH KONT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR. unfold PZR_STACK in *.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'. pose proof atop_range as ATR.   (* [comment removed for export] *)
  assert (SHR : 0x800b8800 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -AL SL SPOS HI' HCE ATR. Z.div_mod_to_equations. lia. }
  destruct (Z.lt_ge_cases size 524288) as [SMALL | BIG].
  - (* [comment removed for export] *)
    rewrite (poison0_small _ addr size k AL) by (clear -SPOS SMALL; lia).
    iprefix.
    eapply evtF_cut.
    { eapply (poison_shadow_spec RNG) with (addr := addr) (size := size) (v := 0) (lo := lo); try eassumption; try reflexivity.
      all: try (clear -CEIL LO LO0 SPR AL SL SPOS HI HI' HCE SMALL ATR; first [exact HI | lia]).
      intros _. unfold shlen. rewrite Z.shiftr_div_pow2 by (clear; lia). clear -SMALL SPOS. Z.div_mod_to_equations. lia. }
    cbv beta. intros ms' PO. unfold poison_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUp WMp MIp STp SHZ; nd_post).
    apply evtF_done. eapply KONT. unfold poison0_post, PZR_STACK.
    split; [apply fp_le_refl|].
    split. { eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
    split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
    split. { unfold zeros. rewrite ?unsigned_lit in SHZ by (clear; lia). exact SHZ. }
    split; [eapply poison_cells_highD; [exact PC | exact MUp |] | split; [eapply premap_cells_highD; [exact PRM | exact MUp |] | eapply arelro0_munch; [exact RR | exact MUp |]]];
      (repeat (apply Forall_cons; [cbn; unfold AIMG_HI, ARELRO_LO, ARELRO_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil).
  - (* [comment removed for export] *)
    pose proof poison_remap as PR. unfold poison_remap_stmt in PR.
    eapply (PR R k Q RNG) with (addr := addr) (size := size) (lo := lo); try eassumption; try reflexivity.
    all: try (unfold PZR_STACK; clear -CEIL LO LO0 SPR AL SL SPOS HI HI' HCE BIG ATR; first [exact HI | lia]).
    { unfold shlen. rewrite Z.shiftr_div_pow2 by (clear; lia). clear -BIG SL. Z.div_mod_to_equations. lia. }
    intros RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PP.
    unfold premap_post in PP. (nd_pre PP 10%nat; intros LE BW MUp WMp MIp STp SHZ RSH' PC' PRM'; nd_post).
    eapply KONT. unfold poison0_post. unfold PZR_STACK in MUp.
    split; [exact LE|]. split; [exact MUp|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
    split; [exact SHZ|]. split; [exact PC'|]. split; [exact PRM'|].
    eapply arelro0_munch; [exact RR | exact MUp |].
    repeat (apply Forall_cons; [cbn; unfold ARELRO_LO, ARELRO_HI; clear -CEIL LO SPR SHR; lia|]); apply Forall_nil.
Qed.
End CANSEC1.
End TwB.
End F_apoisonz.
