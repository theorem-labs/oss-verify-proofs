From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof reac_frame_inspect_c reac_decode_c reac_upstream_decode_c ReacDecodeLib reac_upstream_decode reac_upstream_decode_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_upstream_decode_holds (A image, entry 0x81b20, frame 48 bytes). The proof follows
   reac_upstream_decode.v step for step, with StepF's step; the pure lemmas of reac_upstream_decode.v are used as they
   are. The run's data accesses (each checked by a StepF access side goal) are:
     - 0x81b20-0x81b3c: sd ra, s0-s4 into [sp-48, sp); 0x81b78-0x81b8c: ld of them back;
     - 0x81b54: ld of the 8-byte constant at DIV36_MAGIC_AT;
     - 0x81bb0, 0x81bb4: ld of the GOT cell GOT_CELL_K, then of CELL_K (the shadow offset ASAN_K);
     - 0x81bc4-0x81c30: lb of the shadow byte and lbu of raw+12, raw+13, raw+len-2, raw+len-1;
     - the loop 0x81c90-0x81d24: lb of the shadow byte and lbu of input bytes raw+50+..., lb of the shadow byte and
       sb of output bytes out+q, 0 <= q < 36 * nch. *)

(* ---- pure footprint facts ---- *)

Lemma up_rng_byte : forall RNG p n a, ExecF.rng RNG p n -> p <= a < p + n -> ExecF.rng RNG a 1.
Proof. intros RNG p n a H Ha. eapply ExecF.rng_sub; [exact H | lia | lia]. Qed.

Lemma up_rng_shadow : forall RNG K p n a,
  ExecF.rng RNG (p / 8 + K) ((p + n - 1) / 8 - p / 8 + 1) -> p <= a < p + n -> ExecF.rng RNG (a / 8 + K) 1.
Proof.
  intros RNG K p n a H Ha. eapply ExecF.rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p a 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono a (p + n - 1) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* A one-byte access whose address a proof-context equation names: closed by a term, with no arithmetic goal. These
   feed acc_hint, so that StepF's access side goals of the instrumented checks never call lia. *)
Lemma acc1_var : forall RNG (x : word) (E : Z) (n : nat),
  ExecF.rng RNG E 1 -> bv_unsigned x = E -> Z.of_nat n = 1 -> ExecF.acc_in RNG (x, n).
Proof.
  intros RNG x E n H Hx Hn.
  eapply ExecF.rng_acc_varZ; [exact H | exact Hn | rewrite Hx; split; apply Z.le_refl].
Qed.

Lemma acc1_lit : forall RNG (E : Z) (n : nat),
  ExecF.rng RNG E 1 -> Z.of_nat n = 1 -> ExecF.acc_in RNG (Z_to_bv 64 E, n).
Proof.
  intros RNG E n H Hn.
  eapply ExecF.rng_acc_litZ; [exact H | exact Hn | apply Z.le_refl | split; apply Z.le_refl].
Qed.

Lemma acc1_var0 : forall RNG (x : word) (E : Z) (n : nat),
  ExecF.rng RNG E 1 -> bv_unsigned x = E -> Z.of_nat n = 1 ->
  ExecF.acc_in RNG (Z_to_bv 64 (bv_unsigned x + 0), n).
Proof.
  intros RNG x E n H Hx Hn. rewrite Z.add_0_r, Z_to_bv_lit_self.
  eapply acc1_var; [exact H | exact Hx | exact Hn].
Qed.

(* StepF's hook: a one-byte access at an address a [rng _ E 1] hypothesis covers. *)
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- ExecF.acc_in ?RNG (Z_to_bv 64 (bv_unsigned ?x + 0), _) =>
      match goal with
      | HE : bv_unsigned x = ?E |- _ =>
          match goal with
          | HR : ExecF.rng RNG E 1 |- _ => eapply (acc1_var0 RNG x E); [exact HR | exact HE | reflexivity]
          end
      end
  | |- ExecF.acc_in ?RNG (Z_to_bv 64 ?E, _) =>
      match goal with
      | HR : ExecF.rng RNG E 1 |- _ => eapply (acc1_lit RNG E); [exact HR | reflexivity]
      end
  | |- ExecF.acc_in ?RNG (?x, _) =>
      is_var x;
      match goal with
      | HE : bv_unsigned x = ?E |- _ =>
          match goal with
          | HR : ExecF.rng RNG E 1 |- _ => eapply (acc1_var RNG x E); [exact HR | exact HE | reflexivity]
          end
      end
  end.

(* Drop the spent shadow-arithmetic facts, so that the remaining lia calls stay small. *)
Ltac clr8 :=
  repeat match goal with
  | H : context [Z.div _ 8] |- _ => lazymatch type of H with ExecF.rng _ _ _ => fail | _ => clear H end
  | H : context [Z.modulo _ 8] |- _ => lazymatch type of H with ExecF.rng _ _ _ => fail | _ => clear H end
  end.

(* ---- the shadow-check segments of the loop body ---- *)

Lemma shld1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x31 + bv_unsigned x28 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y11 y13 y19 : word, bv_unsigned y13 = A ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x11 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81ca8) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81c90) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RS CONT.
  pose proof (u64_range x31) as R31. pose proof (u64_range x28) as R28.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_add x31 x28 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step. step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT; exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT; exact U.
Qed.

Lemma shst1F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (Q0 A3 : Z),
  bv_unsigned x12 = Q0 -> Q0 < 2^64 -> bv_unsigned x13 = A3 ->
  mrd rsegs mm (wa (Q0 / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ Q0 mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  ExecF.rng RNG A3 1 -> ExecF.rng RNG (Q0 / 8 + 2147450880) 1 ->
  (forall y13 y19 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cbc) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81ca8) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b Q0 A3 EQ0 RQ EA3 M SK Fsrc RD RS CONT.
  pose proof (u64_range x12) as R12. pose proof (Z.mod_pos_bound Q0 8 ltac:(lia)) as MB.
  step. gen_shr x12 g G. rewrite EQ0 in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x13 _ _ Fsrc EA3) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, EQ0. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma shld2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x11 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y13 y19 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cd8) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cc8) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RS CONT.
  pose proof (u64_range x11) as R11. pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_shr x11 g G. rewrite EA in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, EA. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma shst2F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (Q0 A2 : Z),
  bv_unsigned x12 = Q0 -> Q0 + 1 < 2^64 -> bv_unsigned x11 = A2 ->
  mrd rsegs mm (wa ((Q0 + 1) / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ (Q0 + 1) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A2) = Some b ->
  ExecF.rng RNG A2 1 -> ExecF.rng RNG ((Q0 + 1) / 8 + 2147450880) 1 ->
  (forall y13 y19 y20 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (zxb b) x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cf0) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cd8) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b Q0 A2 EQ0 RQ EA2 M SK Fsrc RD RS CONT.
  pose proof (u64_range x12) as R12. pose proof (Z.mod_pos_bound (Q0 + 1) 8 ltac:(lia)) as MB.
  step. gen_addi x12 w U. rewrite EQ0 in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x11 _ _ Fsrc EA2) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

Lemma shld3F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x8 + bv_unsigned x28 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y11 y13 y19 : word, bv_unsigned y13 = A ->
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81d08) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81cf4) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k A EA RA M SK RS CONT.
  pose proof (u64_range x8) as R8. pose proof (u64_range x28) as R28.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  step. gen_add x8 x28 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT; exact U.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT; exact U.
Qed.

Lemma shst3F : forall (RNG : ExecF.footprint) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (Q0 A3 : Z),
  bv_unsigned x12 = Q0 -> Q0 + 2 < 2^64 -> bv_unsigned x13 = A3 ->
  mrd rsegs mm (wa ((Q0 + 2) / 8 + 2147450880)) = Some k ->
  (bv_signed k = 0 \/ (Q0 + 2) mod 8 < bv_signed k) ->
  mrd rsegs mm (wa A3) = Some b ->
  ExecF.rng RNG A3 1 -> ExecF.rng RNG ((Q0 + 2) / 8 + 2147450880) 1 ->
  (forall y11 y19 y20 : word,
     ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y11 x12 (zxb b) x14 x15 (Z_to_bv 64 2147450880) x17 x18 y19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81d20) fc None mm (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x81d08) fc None mm (seg_rom rsegs)).
Proof.
  intros RNG x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc mm Q k b Q0 A3 EQ0 RQ EA3 M SK Fsrc RD RS CONT.
  pose proof (u64_range x12) as R12. pose proof (Z.mod_pos_bound (Q0 + 2) 8 ltac:(lia)) as MB.
  step. gen_addi x12 w U. rewrite EQ0 in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H. rewrite G in H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x13 _ _ Fsrc EA3) as R. step. clear R.
  step.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. rewrite land7, U. step. rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* ---- the exit, the inner loop (12 samples of one channel) and the outer loop (channels) ---- *)

Section UPF.
Variables (RNG : ExecF.footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len lo : Z).

Local Notation PostUF := (PostU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m bs raw out len lo).
Local Notation SP := (bv_unsigned sp).
Local Notation FRU mk := (rw_cells rsegs mk (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

Hypothesis Hsp : lo + 48 <= SP.
Hypothesis Hlo : 0 <= lo.
Hypothesis RFR : ExecF.rng RNG (SP + -48) 48.

Lemma up_exitF : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  FRU m1 -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 ->
  r = (if up_ok raw out len bs then 12 else -1) ->
  (if up_ok raw out len bs
   then munch [(SP - 48, SP); (out, out + 36 * up_nch len)] m m1 /\
        bytes_at rsegs m1 out (braid_out bs (up_nch len) 12)
   else munch [(SP - 48, SP)] m m1) ->
  ExecF.evtF rsegs RNG PostUF (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 r) x14 x15 x16 x17
      x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81b74) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 9 step.
  apply ExecF.evtF_done. unfold PostU. exists x5, x6, x7, x11, x12, (Z_to_bv 64 r), x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -48) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -48 + Z.of_nat 48) with SP in ST2 by lia. exact ST2.
  - exact HM.
Qed.

Lemma up_failF : forall (m1 : word -> option byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  FRU m1 -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 -> munch [(SP - 48, SP)] m m1 ->
  up_ok raw out len bs = false ->
  ExecF.evtF rsegs RNG PostUF (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (-1)) x14 x15 x16 x17
      x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81b74) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 HF ST WM MU E.
  eapply up_exitF; [exact HF | exact ST | exact WM | rewrite E; reflexivity | rewrite E; exact MU].
Qed.

Variable nch : Z.
Hypothesis Hnchdef : up_nch len = nch.
Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hlen52 : len = 52 + 36 * nch.
Hypothesis Hlen : length bs = Z.to_nat len.
Hypothesis Hraw : 0 < raw.
Hypothesis Hraw2 : raw + len <= 2^64.
Hypothesis Hout : 0 < out.
Hypothesis HoutN : out + 36 * nch < 2^64.
Hypothesis DOR : out + 36 * nch <= raw \/ raw + len <= out.
Hypothesis DOS : out + 36 * nch <= SP - 48 \/ SP <= out.
Hypothesis AR : addressable m raw len.
Hypothesis AO : addressable m out (36 * nch).
Hypothesis APW : forall x, SP - 48 <= x < SP -> app_mem x.
Hypothesis OK : up_ok raw out len bs = true.
Hypothesis RIN : ExecF.rng RNG raw len.
Hypothesis RINS : ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + len - 1) / 8 - raw / 8 + 1).
Hypothesis ROUT : ExecF.rng RNG out (36 * nch).
Hypothesis ROUTS : ExecF.rng RNG (out / 8 + ASAN_K) ((out + 36 * nch - 1) / 8 - out / 8 + 1).

Local Notation N := (36 * nch).
(* The pure lemmas of reac_upstream_decode.v, at this section's variables and hypotheses. *)
Local Notation INV := (INVU ra sp s0 s1 s2 s3 s4 m bs raw out lo nch).
Local Notation INV_idx := (INVU_idx ra sp s0 s1 s2 s3 s4 m bs raw out len lo nch Hnchdef Hlen52 Hlen Hraw2 DOR AR OK).
Local Notation src_bnd :=
  (src_bound sp bs raw out len lo Hsp Hlo nch Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS).
Local Notation INV_rd :=
  (INVU_rd ra sp s0 s1 s2 s3 s4 m bs raw out len lo Hsp Hlo nch Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS).
Local Notation INV_shr :=
  (INVU_shr ra sp s0 s1 s2 s3 s4 m bs raw out len lo Hsp Hlo nch Hnch Hev Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS
     AR AO APW).
Local Notation INV_sho := (INVU_sho ra sp s0 s1 s2 s3 s4 m bs raw out len lo nch Hlen AO APW).
Local Notation INV_wr := (INVU_wr ra sp s0 s1 s2 s3 s4 m bs raw out len lo nch Hlen).
Local Notation INV_store :=
  (INVU_store ra sp s0 s1 s2 s3 s4 m bs raw out len lo Hsp Hlo nch Hnch Hlen52 Hlen Hraw Hraw2 Hout HoutN DOR DOS).
Local Notation INV_out := (INVU_out ra sp s0 s1 s2 s3 s4 m bs raw out len lo nch Hnchdef Hnch Hlen52 Hlen Hraw2 Hout HoutN).

Ltac do_storeF I0 I1 jj :=
  rewrite ?le1_zxb;
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mk ?a ?b) _) =>
    assert (I1 : INV (write_to_mem mk a b) (jj + 1)) by (eapply INV_store; [exact I0 | lia | lia | lia]);
    let m2 := fresh "m" in set (m2 := write_to_mem mk a b) in *; clearbody m2; clear I0
  end.

(* The shadow byte of input byte [raw + i] and of output byte [out + q]; the input byte [raw + i]. *)
Ltac rng_in_sh := apply (up_rng_shadow RNG _ raw len); [exact RINS | lia].
Ltac rng_out_sh := apply (up_rng_shadow RNG _ out N); [exact ROUTS | lia].
Ltac rng_in := apply (up_rng_byte RNG raw len); [exact RIN | lia].

Lemma up_innerF : forall (ch : Z) (x5 x6 x8 x9 x14 x15 x17 x29 x30 x31 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = 3 * nch -> bv_unsigned x6 = raw + 50 ->
  bv_unsigned x8 = raw + 50 + (1 + ch mod 2) -> bv_unsigned x9 = 5 * (ch mod 2) ->
  bv_unsigned x14 = ch -> bv_unsigned x15 = nch -> bv_unsigned x17 = ch ->
  bv_unsigned x29 = ch mod 2 + 1 -> bv_unsigned x30 = ch mod 2 + 3 ->
  bv_unsigned x31 = raw + 50 + (3 + ch mod 2) ->
  (forall (m2 : word -> option byte) (y7 y10 y11 y12 y13 y18 y19 y20 y28 : word),
     bv_unsigned y12 = out + 3 * (ch * 12 + 12) -> INV m2 (3 * (ch * 12 + 12)) ->
     ExecF.evtF rsegs RNG PostUF (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 y7 x8 x9 y10 y11 y12 y13 x14 x15 (Z_to_bv 64 2147450880) x17 y18 y19 y20 s5 s6 s7 s8 s9 s10 s11 y28 x29 x30 x31) F (Z_to_bv 64 0x81d88) fc None m2 (seg_rom rsegs))) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x7 x10 x11 x12 x13 x18 x19 x20 x28 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 -> bv_unsigned x7 = 12 - s ->
  bv_unsigned x11 = out + 3 * (ch * 12 + s) -> bv_unsigned x12 = out + 3 * (ch * 12 + s) ->
  bv_unsigned x28 = 3 * (ch - ch mod 2) + 3 * nch * s ->
  INV m1 (3 * (ch * 12 + s)) ->
  ExecF.evtF rsegs RNG PostUF (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 2147450880) x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81c90) fc None m1 (seg_rom rsegs)).
Proof.
  intros ch x5 x6 x8 x9 x14 x15 x17 x29 x30 x31 Hch H5 H6 H8 H9 H14 H15 H17 H29 H30 H31 CONT K.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (Hc2 : ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (Hc0 : 0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (ch * 12 <= (nch - 1) * 12) by lia.
  apply wv in H14, H15, H17, H29, H30. subst x14 x15 x17 x29 x30.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x7 x10 x11 x12 x13 x18 x19 x20 x28 HK Hs H7 H11 H12 H28 I0.
  apply wv in H11. subst x11.
  assert (Hsn : s * nch <= 11 * nch) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hsn0 : 0 <= s * nch) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hq0 : 0 <= 3 * (ch * 12 + s) /\ 3 * (ch * 12 + s) + 2 < 36 * nch) by lia.
  (* L1: the shadow byte of the source byte k0, then L2: that source byte and the shadow byte of the output byte *)
  pose proof (src_bnd ch s 0 (3 + ch mod 2) Hch Hs ltac:(lia) ltac:(reflexivity)) as SB0.
  pose proof (INV_shr m1 _ ch s 0 (3 + ch mod 2) I0 Hch Hs ltac:(lia) ltac:(reflexivity)) as (k0 & MK0 & SK0).
  unfold ASAN_K in MK0.
  eapply shld1F; [ | | exact MK0 | exact SK0 | rng_in_sh | intros y11a y13a y19a Ey13a ].
  { rewrite H31, H28. ring. }
  { lia. }
  clear MK0 SK0.
  pose proof (INV_sho m1 _ (3 * (ch * 12 + s)) I0 ltac:(lia)) as (ks0 & MS0 & SKs0).
  unfold ASAN_K in MS0.
  pose proof (INV_rd m1 _ ch s 0 (3 + ch mod 2) I0 Hch Hs ltac:(lia) ltac:(reflexivity)) as RD0.
  eapply shst1F; [ exact H12 | lia | exact Ey13a | exact MS0 | exact SKs0 | exact RD0 | rng_in | rng_out_sh
                 | intros y13b y19b ].
  clear MS0 SKs0 RD0 SB0.
  (* store k0: add a3,t3,s1 ; sb a1,0(s2) ; add a1,t1,a3 *)
  pose proof (INV_wr m1 _ (3 * (ch * 12 + s)) I0 ltac:(lia)) as HWok0.
  step. gen_add x28 x9 wa3 Ua3.
  step. clear HWok0.
  replace (3 * (ch * 12 + s) + 0) with (3 * (ch * 12 + s)) by lia.
  do_storeF I0 I1 (3 * (ch * 12 + s)).
  step. gen_add x6 wa3 wa1 Ua1.
  (* L3/L4: the source byte k1 at a1 = A2 and the output byte out + q + 1 *)
  pose proof (src_bnd ch s 1 (5 * (ch mod 2)) Hch Hs ltac:(lia) ltac:(reflexivity)) as SB1.
  pose proof (INV_shr _ _ ch s 1 (5 * (ch mod 2)) I1 Hch Hs ltac:(lia) ltac:(reflexivity)) as (k1 & MK1 & SK1).
  unfold ASAN_K in MK1.
  eapply shld2F; [ | | exact MK1 | exact SK1 | rng_in_sh | intros y13c y19c ].
  { rewrite Ua1, H6, Ua3, H28, H9. ring. }
  { lia. }
  clear MK1 SK1.
  pose proof (INV_sho _ _ (3 * (ch * 12 + s) + 1) I1 ltac:(lia)) as (ks1 & MS1 & SKs1).
  unfold ASAN_K in MS1.
  replace (out + (3 * (ch * 12 + s) + 1)) with (out + 3 * (ch * 12 + s) + 1) in MS1, SKs1 by lia.
  pose proof (INV_rd _ _ ch s 1 (5 * (ch mod 2)) I1 Hch Hs ltac:(lia) ltac:(reflexivity)) as RD1.
  eapply shst2F; [ exact H12 | lia | | exact MS1 | exact SKs1 | exact RD1 | rng_in | rng_out_sh
                 | intros y13d y19d y20d ].
  { rewrite Ua1, H6, Ua3, H28, H9. ring. }
  clear MS1 SKs1 RD1 SB1.
  (* store k1: sb a1,1(s2) *)
  pose proof (INV_wr _ _ (3 * (ch * 12 + s) + 1) I1 ltac:(lia)) as HWok1.
  step. clear HWok1.
  do_storeF I1 I2 (3 * (ch * 12 + s) + 1).
  (* L5/L6: the source byte k2 at a3 = s0 + t3 = A3 and the output byte out + q + 2 *)
  pose proof (src_bnd ch s 2 (1 + ch mod 2) Hch Hs ltac:(lia) ltac:(reflexivity)) as SB2.
  pose proof (INV_shr _ _ ch s 2 (1 + ch mod 2) I2 Hch Hs ltac:(lia) ltac:(reflexivity)) as (k2 & MK2 & SK2).
  unfold ASAN_K in MK2.
  eapply shld3F; [ | | exact MK2 | exact SK2 | rng_in_sh | intros y11e y13e y19e Ey13e ].
  { rewrite H8, H28. ring. }
  { lia. }
  clear MK2 SK2.
  pose proof (INV_sho _ _ (3 * (ch * 12 + s) + 2) I2 ltac:(lia)) as (ks2 & MS2 & SKs2).
  unfold ASAN_K in MS2.
  replace (out + (3 * (ch * 12 + s) + 2)) with (out + 3 * (ch * 12 + s) + 2) in MS2, SKs2 by lia.
  pose proof (INV_rd _ _ ch s 2 (1 + ch mod 2) I2 Hch Hs ltac:(lia) ltac:(reflexivity)) as RD2.
  eapply shst3F; [ exact H12 | lia | exact Ey13e | exact MS2 | exact SKs2 | exact RD2 | rng_in | rng_out_sh
                 | intros y11f y19f y20f ].
  clear MS2 SKs2 RD2 SB2.
  (* store k2: sb a3,2(s2) ; loop tail *)
  pose proof (INV_wr _ _ (3 * (ch * 12 + s) + 2) I2 ltac:(lia)) as HWok2.
  step. clear HWok2.
  do_storeF I2 I3 (3 * (ch * 12 + s) + 2).
  (* loop tail: add t3,t3,t0 ; addi t2,t2,-1 ; addi a2,a2,3 ; addi a1,s2,3 ; beqz t2 *)
  step. gen_add x28 x5 wt3 Ut3.
  step.
  step. gen_addi x12 wa2 Ua2.
  step.
  step.
  brq BR.
  - (* exit: s = 11 *)
    assert (Es : s = 11) by (rewrite H7 in BR; lia).
    step.
    eapply CONT.
    { rewrite !unsigned_lit by lia. lia. }
    { eapply INV_idx; [exact I3 | lia]. }
  - (* loop: s+1 *)
    step.
    eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1)).
    all: clear CONT IH Hsn Hsn0.
    { reflexivity. }
    { lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite Ua2, H12. lia. }
    { rewrite Ut3, H28, H5. ring. }
    { eapply INV_idx; [exact I3 | lia]. }
Qed.

Lemma up_outerF : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x19 x20 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = 3 * nch -> bv_unsigned x6 = raw + 50 -> bv_unsigned x12 = out + 3 * (ch * 12) ->
  INV m1 (3 * (ch * 12)) ->
  ExecF.evtF rsegs RNG PostUF (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13
        (Z_to_bv 64 ch) (Z_to_bv 64 nch) (Z_to_bv 64 2147450880) (Z_to_bv 64 ch) x18 x19 x20
        s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x81c58) fc None m1 (seg_rom rsegs)).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x19 x20 x28 x29 x30 x31 HK Hch H5 H6 H12 I0.
  pose proof (u64_range sp) as Rsp.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (Hc0 : 0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (ch * 12 <= (nch - 1) * 12) by lia.
  assert (P : ch mod 2 = 0 \/ ch mod 2 = 1) by lia.
  apply wv in H5, H6, H12. subst x5 x6 x12.
  do 14 step.
  rewrite (unsigned_lit ch) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (ch * 2 ^ 2)) by lia.
  rewrite land_m8, land_m2 by lia. rewrite !land1.
  assert (EQ5 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned
    (v_sltiu (Z_to_bv 64 (ch mod 2)) 1) + -1))) 5)) = 5 * (ch mod 2))
    by (destruct P as [P|P]; rewrite P; vm_compute; reflexivity).
  eapply (up_innerF ch) with (K := Z.to_nat (12 - 0)) (s := 0).
  all: lazymatch goal with
       | |- (forall _ : word -> option byte, _) => idtac
       | |- context [INVU] => eapply INV_idx; [exact I0 | lia]
       | _ => first
         [ lia
         | reflexivity
         | (rewrite unsigned_lit by lia; lia)
         | (rewrite unsigned_lit by lia; exact EQ5)
         | (rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8))) by (Z.div_mod_to_equations; lia);
            rewrite (unsigned_lit (2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
            rewrite unsigned_lit by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia) ]
       end.
  intros m2 y7 y10 y11 y12 y13 y18 y19 y20 y28 H12' I2.
  apply wv in H12'. subst y12.
  (* ch-tail at 0x81d88: sext.w a1,a5 ; addiw a7,a7,1 ; addi a4,a4,1 ; bne a7,a1 *)
  step. rewrite (unsigned_lit nch) by lia. rewrite swrap32_id by lia.
  step. step. step.
  rewrite (unsigned_lit ch) by lia. rewrite swrap32_id by lia.
  brq BR.
  - (* exit: ch = nch - 1 *)
    assert (Ec : ch = nch - 1) by lia.
    step. step.
    destruct I2 as (BB2 & FR2 & ST2 & WA2 & MU2 & WM2 & HP2).
    eapply up_exitF with (r := 12);
      [ exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. rewrite Hnchdef. split.
    + replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. exact MU2.
    + apply INV_out. eapply INV_idx;
        [ exact (conj BB2 (conj FR2 (conj ST2 (conj WA2 (conj MU2 (conj WM2 HP2)))))) | lia ].
  - (* loop: ch + 1 *)
    eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: try (clear IH).
    { reflexivity. }
    { lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite unsigned_lit by lia. lia. }
    { eapply INV_idx; [exact I2 | lia]. }
Qed.

End UPF.

(* ---- the entry: prologue, argument checks, the four marker checks, then the loop ---- *)

Ltac pshadowF m0 addrreg EA M k SK MB :=
  let g := fresh "g" in let h := fresh "h" in let G := fresh "G" in let H := fresh "H" in
  let R := fresh "R" in let C := fresh "C" in
  step; gen_shr addrreg g G; rewrite EA in G;
  step; gen_addi g h H; rewrite G in H;
  pose proof (rdw0 m0 h _ _ M ltac:(lia)) as R; step; clear R;
  step;
  destruct SK as [C|C];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
    step; rewrite land7, EA; step;
    rewrite (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

Ltac ufailF sp :=
  eapply up_failF; first
  [ eassumption
  | (replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; eassumption)
  | (apply not_true_iff_false; rewrite up_ok_true;
     intros (HUa & HUb & HUc & HUd & HUe & HUf & HUg);
     try (apply up_nch_pos in HUc; destruct HUc as (HVa & HVb & HVc & HVd & HVe));
     unfold inspect_byte in *; clr8; first [ lia | (Z.div_mod_to_equations; lia) ]) ].

Theorem reac_upstream_decode_holds_F : reac_upstream_decode_contract_F.
Proof.
  unfold reac_upstream_decode_contract_F, REAC_UPSTREAM_DECODE, REAC_UPSTREAM_DECODE_D, DIV36_MAGIC_AT, DIV36_MAGIC.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw out lo E0 E2 Rraw Rout Rlen HMG HB HO ST LO DR DO DM APS1 APS2 CELLS SGOT AR AO
    RFR RMG RGC RCK RIN RINS ROUT ROUTS.
  unfold GOT_CELL_K in RGC. unfold CELL_K in RCK. unfold ASAN_K in RINS, ROUTS.
  assert (Ea0 : bv_unsigned a0 = raw) by (rewrite E0; apply unsigned_lit; lia).
  assert (Ea2 : bv_unsigned a2 = out) by (rewrite E2; apply unsigned_lit; lia).
  pose proof (u64_range a1) as Ra1.
  set (len := bv_unsigned a1) in *.
  assert (A1 : a1 = Z_to_bv 64 len) by (symmetry; apply Z_to_bv_bv_unsigned).
  clearbody len. subst a1.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (conj HMG CELLS) as PK. clear HMG CELLS.
  carve_frame 48%nat ST.
  do 7 step.
  destruct PK as (HMG & CELLS).
  match goal with MU' : munch _ m ?mm |- _ => rename MU' into MU1; rename mm into m0 end.
  pose proof (bytes_tp m m0 _ _ 66360 (le8 (Z_to_bv 64 16397105843297379215)) MU1
    ltac:(rewrite length_le8; unfold off_stk in DM; lia) HMG) as HMG0.
  assert (CELLS0 : asan_cells m0) by
    (eapply asan_cells_munch; [exact CELLS | exact MU1 |
     unfold MIDEND, GOT_CELL_K; unfold off_stk, GOT_CELL_K, MIDEND in SGOT; lia]).
  pose proof CELLS0 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ HMG0) as HRM. rewrite length_le8 in HRM.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 2 step.
  step. brq B1. { ufailF sp. }
  step. if_cases B2. { zify_cond B2; ufailF sp. }
  step. if_cases B3. { zify_cond B3; ufailF sp. }
  step. step. step. step.
  replace (len + -52) with (len - 52) in * by lia.
  rewrite (unsigned_lit (len - 52)) by lia.
  step.
  rewrite (unsigned_lit (Z.shiftr _ 64)) by (rewrite Z.shiftr_div_pow2 by lia; split;
    [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; first [lia | nia]]).
  rewrite div36 by lia.
  assert (QB : 2 <= (len - 52) / 36 < 2^27) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  set (q := (len - 52) / 36) in *.
  step. step. step.
  rewrite ?(unsigned_lit q) by lia. rewrite ?(unsigned_lit (q * 36)) by lia.
  rewrite ?(unsigned_lit (len - 52)) by lia.
  rewrite ?(unsigned_lit (len - 52 - q * 36)) by (subst q; Z.div_mod_to_equations; lia).
  step. brq B4. 2:{ ufailF sp. }
  assert (M36 : (len - 52) mod 36 = 0) by (subst q; Z.div_mod_to_equations; lia).
  step. rewrite (unsigned_lit q) by lia. step. step.
  rewrite width_test by lia.
  destruct ((2 <=? q) && (q <=? 40)) eqn:B5; cbn [negb].
  2:{ ufailF sp. }
  apply andb_true_iff in B5. destruct B5 as [B5a B5b]. apply Z.leb_le in B5a, B5b.
  step. rewrite (unsigned_lit q) by lia. rewrite land1. step. brq B6.
  2:{ ufailF sp. }
  assert (UQ : up_nch len = q) by (apply up_nch_val; lia).
  step. step. step.
  zify_cond B2. zify_cond B3.
  assert (RN : raw <> 0) by (rewrite Ea0 in B2; lia).
  assert (ON : out <> 0) by (rewrite Ea2 in B3; lia).
  assert (UQ0 : 0 <= up_nch len) by (rewrite UQ; lia).
  destruct (HB RN ON UQ0) as [LEN BB].
  specialize (DR RN ON UQ0). unfold off_stk in DR.
  specialize (AR RN ON UQ0).
  specialize (RIN RN ON UQ0). specialize (RINS RN ON UQ0).
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN, Z2Nat.id in BBB by lia.
  pose proof (bytes_tp m m0 _ _ raw bs MU1 ltac:(rewrite LEN, Z2Nat.id by lia; lia) BB) as BB0.
  assert (AR0 : addressable m0 raw len).
  { eapply addr_munch; [exact AR | exact MU1 |].
    intros i Hi. destruct (addr_one m raw len i AR Hi) as (Hap & _).
    cbn [outside]. split; [|exact I]. intros W.
    apply (shadow_not_app (raw + i) Hap).
    apply (app_win (bv_unsigned sp) 48); [lia | exact APS1 | exact APS2 | lia]. }
  assert (RLT : raw + len <= 0x800000000000) by
    (destruct AR as (_ & _ & H & _); unfold APPMEM_END in H; exact H).
  destruct (addr_one m0 raw len 12 AR0 ltac:(lia)) as (_ & k12 & M12 & SK12). unfold ASAN_K in M12.
  destruct (addr_one m0 raw len 13 AR0 ltac:(lia)) as (_ & k13 & M13 & SK13). unfold ASAN_K in M13.
  destruct (addr_one m0 raw len (len - 2) AR0 ltac:(lia)) as (_ & k90 & M90 & SK90). unfold ASAN_K in M90.
  destruct (addr_one m0 raw len (len - 1) AR0 ltac:(lia)) as (_ & k91 & M91 & SK91). unfold ASAN_K in M91.
  pose proof (bytes_nth m0 raw bs 12 BB0 ltac:(rewrite LEN; lia)) as F12. change (Z.of_nat 12) with 12 in F12.
  pose proof (bytes_nth m0 raw bs 13 BB0 ltac:(rewrite LEN; lia)) as F13. change (Z.of_nat 13) with 13 in F13.
  pose proof (bytes_nth m0 raw bs (Z.to_nat (len - 2)) BB0 ltac:(rewrite LEN; lia)) as F90.
  rewrite Z2Nat.id in F90 by lia.
  pose proof (bytes_nth m0 raw bs (Z.to_nat (len - 1)) BB0 ltac:(rewrite LEN; lia)) as F91.
  rewrite Z2Nat.id in F91 by lia.
  pose proof (Z.mod_pos_bound (raw + 12) 8 ltac:(lia)) as MB12.
  pose proof (Z.mod_pos_bound (raw + 13) 8 ltac:(lia)) as MB13.
  pose proof (Z.mod_pos_bound (raw + (len - 2)) 8 ltac:(lia)) as MB90.
  pose proof (Z.mod_pos_bound (raw + (len - 1)) 8 ltac:(lia)) as MB91.
  (* the four marker bytes and their shadow bytes, each as a one-byte range: acc_hint closes the access side goals
     with them, and each pair goes as soon as its check is done. *)
  assert (RB91 : ExecF.rng RNG (raw + (len - 1)) 1) by (apply (up_rng_byte RNG raw len); [exact RIN | lia]).
  assert (RS91 : ExecF.rng RNG ((raw + (len - 1)) / 8 + 2147450880) 1)
    by (apply (up_rng_shadow RNG 2147450880 raw len); [exact RINS | lia]).
  assert (RB90 : ExecF.rng RNG (raw + (len - 2)) 1) by (apply (up_rng_byte RNG raw len); [exact RIN | lia]).
  assert (RS90 : ExecF.rng RNG ((raw + (len - 2)) / 8 + 2147450880) 1)
    by (apply (up_rng_shadow RNG 2147450880 raw len); [exact RINS | lia]).
  assert (RB13 : ExecF.rng RNG (raw + 13) 1) by (apply (up_rng_byte RNG raw len); [exact RIN | lia]).
  assert (RS13 : ExecF.rng RNG ((raw + 13) / 8 + 2147450880) 1)
    by (apply (up_rng_shadow RNG 2147450880 raw len); [exact RINS | lia]).
  assert (RB12 : ExecF.rng RNG (raw + 12) 1) by (apply (up_rng_byte RNG raw len); [exact RIN | lia]).
  assert (RS12 : ExecF.rng RNG ((raw + 12) / 8 + 2147450880) 1)
    by (apply (up_rng_shadow RNG 2147450880 raw len); [exact RINS | lia]).
  (* check 1: raw+12 *)
  step. gen_addi a0 w12 U12. rewrite Ea0 in U12.
  pshadowF m0 w12 U12 M12 k12 SK12 MB12.
  all: pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; step; clear R.
  all: step; step; rewrite eqb_zxb by lia; brq B7; [|ufailF sp].
  all: clear RB12 RS12 M12 F12 MB12.
  (* check 2: raw+13 *)
  all: step; gen_addi a0 w13 U13; rewrite Ea0 in U13.
  all: pshadowF m0 w13 U13 M13 k13 SK13 MB13.
  all: pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
  all: step; step; rewrite eqb_zxb by lia; brq B8; [|ufailF sp].
  all: clear RB13 RS13 M13 F13 MB13.
  (* check 3: raw+len-2 *)
  all: step; gen_addi a0 w3 U3; rewrite Ea0 in U3.
  all: step; gen_addi w3 w3b U3b; rewrite U3 in U3b;
       replace (raw + len + -2) with (raw + (len - 2)) in U3b by lia.
  all: pshadowF m0 w3b U3b M90 k90 SK90 MB90.
  all: pose proof (rdw0 m0 w3b _ _ F90 ltac:(lia)) as R; step; clear R.
  all: step; step; rewrite eqb_zxb by lia; brq B9; [|ufailF sp].
  all: clear RB90 RS90 M90 F90 MB90.
  (* check 4: raw+len-1 *)
  all: step; gen_addi w3 w4 U4; rewrite U3 in U4;
       replace (raw + len + -1) with (raw + (len - 1)) in U4 by lia.
  all: pshadowF m0 w4 U4 M91 k91 SK91 MB91.
  all: pose proof (rdw0 m0 w4 _ _ F91 ltac:(lia)) as R; step; clear R.
  all: step; step; rewrite eqb_zxb by lia; brq B10; [|ufailF sp].
  all: clear RB91 RS91 M91 F91 MB91.
  (* success: up_ok = true; set up INVU and run the loop *)
  all: assert (OK : up_ok raw out len bs = true) by
    (rewrite up_ok_true; unfold inspect_byte; rewrite UQ; repeat split; lia).
  all: destruct (HO OK) as (HW & HoutN' & DOR'); rewrite UQ in HW, HoutN', DOR'.
  all: specialize (DO OK); unfold off_stk in DO; rewrite UQ in DO.
  all: specialize (AO OK); rewrite UQ in AO.
  all: specialize (ROUT OK); specialize (ROUTS OK); rewrite UQ in ROUT, ROUTS.
  all: assert (HW1 : wr_at rsegs m0 out (36 * q)) by (eapply wr_at_transport; [exact HW | exact WM]).
  all: clr8.
  all: do 4 step.
  all: rewrite slli_srli33 by lia.
  all: do 3 step.
  all: eapply up_outerF with (nch := q) (K := Z.to_nat (q - 0)) (ch := 0)
    (m := m) (bs := bs) (raw := raw) (out := out) (len := len) (lo := lo).
  all: lazymatch goal with
       | |- context [INVU] =>
           replace (3 * (0 * 12)) with 0 by lia; unfold INVU;
           split; [exact BB0 | split; [exact FR | split; [exact ST |
           split; [exact HW1 | split; [apply munch_extend; exact MU1 |
           split; [exact WM | intros i Hi; lia ]]]]]]
       | |- ExecF.rng _ _ _ => first [ exact RFR | exact RIN | exact RINS | exact ROUT | exact ROUTS ]
       | _ => first
         [ exact OK | exact HW1 | exact AR | exact AO | exact DO | exact DOR' | exact HoutN'
         | exact B6 | exact UQ | exact LEN | exact LO | exact Hlo | reflexivity
         | (rewrite Ea2; lia)
         | (rewrite Ea0; rewrite unsigned_lit by lia; lia)
         | (rewrite (unsigned_lit q) by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite unsigned_lit by lia; lia)
         | lia
         | (intros x Hx; apply (app_win (bv_unsigned sp) 48); [lia | exact APS1 | exact APS2 | lia])
         | (subst q; Z.div_mod_to_equations; lia) ]
         || (lazymatch goal with |- ?g => fail 0 "UNSOLVED:" g end)
       end.
Qed.

(* The twin gives the old contract back: take the footprint that admits every access. *)
Theorem reac_upstream_decode_holds_of_F : reac_upstream_decode_contract.
Proof.
  unfold reac_upstream_decode_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw out lo E0 E2 Rraw Rout Rlen HMG HB HO ST LO DR DO DM APS1 APS2 CELLS SGOT AR AO.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a1) as Ra1.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof reac_upstream_decode_holds_F as HF. unfold reac_upstream_decode_contract_F in HF.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m bs raw out lo E0 E2 Rraw Rout Rlen HMG HB HO ST LO DR DO DM APS1 APS2 CELLS SGOT AR AO);
    unfold REAC_UPSTREAM_DECODE_D, DIV36_MAGIC_AT, GOT_CELL_K, CELL_K, ASAN_K in *;
    try (apply ExecF.rng_all; lia);
    [ intros H1 H2 H3; destruct (AR H1 H2 H3) as (_ & Hn & HA & _)
    | intros H1 H2 H3; destruct (AR H1 H2 H3) as (_ & Hn & HA & _)
    | intros H1; destruct (AO H1) as (_ & Hn & HA & _)
    | intros H1; destruct (AO H1) as (_ & Hn & HA & _) ];
    unfold APPMEM_END in HA; apply ExecF.rng_all; Z.div_mod_to_equations; lia.
Qed.
