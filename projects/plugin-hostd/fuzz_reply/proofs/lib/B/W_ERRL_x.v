(* rule 24: no function proved (kind: image law at the instance: errno's four bytes are readable and writable).
   Written for a Theorem Labs lane's reply-B top row ERRL_x (lib/B/ReplyBTop.v; a Theorem Labs lane's B W1 round, lead a Theorem Labs lane).

   The image-B twin of lib/A/W_ERRL_x.v (a Theorem Labs lane F1), the same script: errno's law is a fact of the IMAGE alone.
   errno's four bytes are bytes of reply B's segment table, so every memory's ASan view reads a value there (LPS's
   mbyte falls back to the segment byte for an absent byte), and they lie in a writable segment.  The relation is never
   read, so the fact is stated ONCE, relation-free ([errno_rw_core], for every W and mem), and the relation form is a
   2-line corollary:
   - [errno_law_x_holds] : errno_law_x B ARx for EVERY ARx (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v Section w,
     errno_law_x), in particular at reply B's top_x ARX (ARcf at CfParams_reply /\ Hp = [] /\ arodata_ok_cf), which is
     ReplyBTop's ERRL_x row: `forall rc fx, errno_law_x TfibB W_LLVMFuzzerTestOneInput_top_x.ARX`.
   Unit facts used: TfibSyms B (YF0m.ts_errno: as_errno B = TFIB_ERRNO = 0x5d994c, YF0m.v:21), reply B's segment table
   (seg_rom on errno's bytes, by vm_compute) and its writable-segment table (segwb, by vm_compute).  Image A's zz_ERRL
   helpers (lib/A/W_LLVMFuzzerTestOneInput_addI.v:220-246, image-free) are restated here as errl_*, since image B has
   no addI file. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m YD2l.
Import ListNotations.
Local Open Scope Z_scope.

Section p.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).

(* image-free byte helpers (image A's zz_byte_some / zz_bv_of_u / zz_v4 / zz_le4, the same proofs) *)
Lemma errl_byte_some : forall (m : word -> option byte) a, seg_rom segs (Z_to_bv 64 a) <> None ->
  exists b, mbyte segs m a = Some b.
Proof.
  intros m a H. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|]; [eauto|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [eauto | congruence].
Qed.
Lemma errl_bv_of_u : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as Hb.
  unfold bv_wrap, bv_modulus in *. cbn [Z.of_N] in *. change (2 ^ 8) with 256 in *. apply Z.mod_small. lia.
Qed.
Definition errl_v4 (v0 v1 v2 v3 : Z) : Z := v0 + 256 * (v1 + 256 * (v2 + 256 * v3)).
Lemma errl_le4 : forall v0 v1 v2 v3, 0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 ->
  le_byte (errl_v4 v0 v1 v2 v3) 4 0 = v0 /\ le_byte (errl_v4 v0 v1 v2 v3) 4 1 = v1 /\
  le_byte (errl_v4 v0 v1 v2 v3) 4 2 = v2 /\ le_byte (errl_v4 v0 v1 v2 v3) 4 3 = v3 /\
  0 <= errl_v4 v0 v1 v2 v3 < 2 ^ 32.
Proof.
  intros v0 v1 v2 v3 H0 H1 H2 H3. unfold le_byte.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
  change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 3)) with 16777216.
  change (2 ^ 32) with 4294967296.
  assert (Hv : 0 <= errl_v4 v0 v1 v2 v3 < 4294967296) by (unfold errl_v4; lia).
  rewrite (Z.mod_small (errl_v4 v0 v1 v2 v3)) by exact Hv.
  split; [|split; [|split; [|split]]]; try exact Hv; unfold errl_v4; Z.div_mod_to_equations; lia.
Qed.

(* errno's four bytes read a value and are writable, in every world and memory (relation-free). *)
Lemma errno_rw_core : forall B, TfibSyms B -> forall (W : world segs) (mem : word -> option byte),
  (exists v, val_mem segs (arm W mem) (as_errno B) 4 v /\ 0 <= v < 2 ^ 32) /\ awr W mem (as_errno B) 4.
Proof.
  intros B TS W mem. rewrite (@ts_errno B TS).
  assert (HS : forall j, 0 <= j < 8 -> seg_rom segs (Z_to_bv 64 (TFIB_ERRNO + j)) <> None).
  { intros j Hj.
    assert (Hb : forallb (fun i => match seg_rom segs (Z_to_bv 64 (TFIB_ERRNO + Z.of_nat i)) with
                                   Some _ => true | None => false end) (seq 0 8) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat j) ltac:(apply in_seq; lia)).
    rewrite Z2Nat.id in Hb by lia. destruct (seg_rom segs (Z_to_bv 64 (TFIB_ERRNO + j))); [discriminate | discriminate Hb]. }
  split.
  - destruct (errl_byte_some (arm W mem) (TFIB_ERRNO + 0) (HS 0 ltac:(lia))) as (b0 & E0).
    destruct (errl_byte_some (arm W mem) (TFIB_ERRNO + 1) (HS 1 ltac:(lia))) as (b1 & E1).
    destruct (errl_byte_some (arm W mem) (TFIB_ERRNO + 2) (HS 2 ltac:(lia))) as (b2 & E2).
    destruct (errl_byte_some (arm W mem) (TFIB_ERRNO + 3) (HS 3 ltac:(lia))) as (b3 & E3).
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
    pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
    unfold bv_modulus in R0, R1, R2, R3. cbn [Z.of_N] in R0, R1, R2, R3. change (2 ^ 8) with 256 in R0, R1, R2, R3.
    destruct (errl_le4 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3) R0 R1 R2 R3)
      as (L0 & L1 & L2 & L3 & Hv).
    exists (errl_v4 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) (bv_unsigned b3)). split; [|exact Hv].
    intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
    + change (Z.of_nat 0) with 0. rewrite E0. f_equal. rewrite <- (errl_bv_of_u b0) at 1. f_equal. symmetry. exact L0.
    + change (Z.of_nat 1) with 1. rewrite E1. f_equal. rewrite <- (errl_bv_of_u b1) at 1. f_equal. symmetry. exact L1.
    + change (Z.of_nat 2) with 2. rewrite E2. f_equal. rewrite <- (errl_bv_of_u b2) at 1. f_equal. symmetry. exact L2.
    + change (Z.of_nat 3) with 3. rewrite E3. f_equal. rewrite <- (errl_bv_of_u b3) at 1. f_equal. symmetry. exact L3.
  - intros i Hi. unfold arm. apply wr_of_seg. apply segwb_ok.
    apply (rng_all_in (segwb segs) [(TFIB_ERRNO, 4)]); [vm_compute; reflexivity|].
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* The ARx form (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v errno_law_x), ReplyBTop's ERRL_x, for every relation ARx. *)
Lemma errno_law_x_holds : forall B, TfibSyms B ->
  forall ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop,
  errno_law_x B ARx.
Proof. intros B TS ARx ly S Hp W mem md _. exact (errno_rw_core B TS W mem). Qed.
End p.

(* ReplyBTop's ERRL_x row at TfibB, for every RunCeil, FPState and relation (instantiate ARx := top_x.ARX) *)
Theorem errno_law_x_TfibB_all : forall (rc : YM05.RunCeil) (fx : YK11.FPState)
  (ARx : alayout -> astate -> list Z -> world (@pa_segs rc fr_prog_listing (@PB_fr rc)) -> (word -> option byte) -> Model -> Prop),
  @errno_law_x rc TfibB ARx.
Proof. intros rc fx ARx. exact (@errno_law_x_holds rc TfibB TfibB_syms ARx). Qed.
