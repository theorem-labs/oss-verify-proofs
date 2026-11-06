(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_runs: the footprint runs (lib/Lib/ExecF.v evtF) of the OWN CODE of image B's
   LLVMFuzzerTestOneInput segment crt1 (+0x5cc .. +0x6ec), i.e. every stretch between two calls:

     c1_run_head   +0x5cc .. the call of check_round_trip (+0x68c), of check_braid (+0x6bc) or of
                   __asan_memset (+0x6d4): the decode-result check (+0x5ec), the 0xa5 scan loop L1
                   (+0x5f4 .. +0x650) with its shadow slow path, the spill of copy + 50 (+0x658) and the two
                   dispatch tests (+0x65c, +0x668)
     c1_run_acrt   +0x690 .. the call of check_braid (+0x6bc)
     c1_run_abraid +0x6c0 .. the call of __asan_memset (+0x6d4)
     c1_run_amset  +0x6d8 .. the call of reac_decode_plain_le (+0x6ec)

   Refuted inside: the in-line __asan_report_load1 call of L1's slow path (+0x64c: it RETURNS, a Theorem Labs lane 2026-10-29
   02:13Z, and would fall into +0x650), the abort edges +0x5ec and +0x650 into +0xb88, and the five UBSan guards
   into +0xb84: +0x608 (buffer + i wraps), +0x66c and +0x69c (copy null), +0x678 and +0x6a8 (copy + 50 wraps).

   PORT. The same code is proved at the same addresses (this image's entry is 0x800b0, the donor's listing is the
   same binary) by the old footprint-era record on a working branch at 3ee4cb94cb5, in
   proofs/libreac/fuzz_decode/lib/B/Prog/afd_down_scan.v: Section CK1 (c1_head :518, c1_loop :479, c1_chk :451,
   c1_tail :392, at 0x8067c .. 0x80774 = +0x5cc .. +0x6c4) and Section CK2 (ck_braid :633, ck_ret :672, at
   0x8074c / 0x80740).  Those are Exec.evt runs; here they are ExecF.evtF runs, as that branch's own footprint
   twins are (afd_down_scanF.v, s2_chk_F :86 / s2_loop_F :122 / s2_evt_F :165 — the SAME loop at +0x6f0, with
   lib/Lib/StepF.v's step and one `rng` premise per region the run reads).  The shadow-word cover lemma below is
   afd_down_scanF.v:43 ads2_shadow_sub, the two munch-transport lemmas afd_down_scan.v:564 ck2_rdn_munch and
   :578 ck2_ovr_munch.  No new proof idea: only the engine (evt -> evtF) and the names changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes ZBridge Arr Image RegisterBridge Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA AsanKAProof ReacDecodeLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Local Open Scope Z_scope.

(* The addresses of this segment, as offsets from the listing's entry (lib/B/Prog/DecodeBAddr.v decodeb_text). *)
Definition C1 (o : Z) : Z := decodeb_text + o.
Definition C1_CRT : Z := decodeb_sigma DB_check_round_trip.
Definition C1_BRAID : Z := decodeb_sigma DB_check_braid.
Definition C1_MEMSET : Z := decodeb_sigma DB___asan_memset.
Definition C1_PLAIN : Z := decodeb_sigma DB_reac_decode_plain_le.

(* StepF's step reads the start pc, and the start pc of each statement here is a C1 name; compute it. *)
Ltac c1_pc := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let v := eval vm_compute in pc in change pc with v
  end.

(* The link register a call leaves: a C1 name, whose value is a literal of the listing. *)
Ltac c1_ra := unfold C1, decodeb_text; usub; lia.

(* afd_down_scan.v:278-301, verbatim (the branch conditions of this stretch). *)
Lemma c1_ltsw : forall (x y : word) u v, bv_signed x = u -> bv_signed y = v -> bv_lts x y = (u <? v).
Proof. intros x y u v Hx Hy. unfold bv_lts. rewrite Hx, Hy. reflexivity. Qed.
Lemma c1_ltuw : forall (x y : word) u v, bv_unsigned x = u -> bv_unsigned y = v -> bv_ltu x y = (u <? v).
Proof. intros x y u v Hx Hy. unfold bv_ltu. rewrite Hx, Hy. reflexivity. Qed.
Lemma c1_eqbw : forall (x y : word) u v, bv_unsigned x = u -> bv_unsigned y = v -> bv_eqb x y = (u =? v).
Proof. intros x y u v Hx Hy. unfold bv_eqb. rewrite Hx, Hy. reflexivity. Qed.

Ltac c1_sgn := first [ (apply signed_lit; lia) | reflexivity | (vm_compute; reflexivity) ].
Ltac c1_usg := first [ (apply unsigned_lit; lia) | reflexivity | (vm_compute; reflexivity) ].
Ltac blts u v :=
  lazymatch goal with
  | |- context [bv_lts ?x ?y] => rewrite (c1_ltsw x y u v ltac:(c1_sgn) ltac:(c1_sgn))
  end.
Ltac bltu u v :=
  lazymatch goal with
  | |- context [bv_ltu ?x ?y] => rewrite (c1_ltuw x y u v ltac:(c1_usg) ltac:(c1_usg))
  end.
Ltac beqb u v :=
  lazymatch goal with
  | |- context [bv_eqb ?x ?y] => rewrite (c1_eqbw x y u v ltac:(c1_usg) ltac:(c1_usg))
  end.
(* afd_down_scan.v:304-313, at ExecF: a branch whose condition is a closed term. *)
Ltac brv :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in
      lazymatch v with
      | true => replace c with true by (vm_compute; reflexivity)
      | false => replace c with false by (vm_compute; reflexivity)
      end; cbv iota
  end.

(* afd_down_scan.v:220-276, verbatim (the arithmetic of the decode-result compare). *)
Lemma c1_ub : forall b : bool, bv_unsigned (Z_to_bv 64 (if b then 1 else 0)) = if b then 1 else 0.
Proof. destruct b; reflexivity. Qed.

Lemma c1_land : forall a b : bool,
  Z.land (bv_unsigned (Z_to_bv 64 (if a then 1 else 0))) (bv_unsigned (Z_to_bv 64 (if b then 1 else 0))) =
  if (a && b)%bool then 1 else 0.
Proof. destruct a, b; reflexivity. Qed.

Lemma c1_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (Z.land_ones x 1 ltac:(lia)). Qed.

Lemma c1_mod2_wrap : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. pose proof (Z.div_mod x (2 ^ 64) ltac:(lia)) as D.
  replace (x mod 2 ^ 64) with (x - 2 ^ 64 * (x / 2 ^ 64)) by lia.
  rewrite <- (Z_mod_plus_full (x - 2 ^ 64 * (x / 2 ^ 64)) (2 ^ 63 * (x / 2 ^ 64)) 2).
  f_equal. lia.
Qed.

Lemma c1_seqz : forall n,
  PropExec.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 n)) 1)) 1 = Z_to_bv 64 (if n mod 2 =? 0 then 1 else 0).
Proof.
  intros n. pose proof (Z.mod_pos_bound n 2 ltac:(lia)) as Hb.
  rewrite v_sltiu_b2z.
  assert (E : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 n)) 1)) = n mod 2).
  { rewrite c1_land1, !unsigned_lit_wrap, c1_mod2_wrap. apply Z.mod_small. lia. }
  rewrite E. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (n mod 2) 0) as [Eq|Eq];
    [rewrite Eq | replace (n mod 2) with 1 by lia]; reflexivity.
Qed.

Lemma c1_lor_ones : forall q, 0 <= q < 2 ^ 64 -> Z.lor 18446744073709551615 q = 18446744073709551615.
Proof.
  intros q Hq. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.ltb_spec i 64) as [Hl|Hl].
  - rewrite !Z.ones_spec_low by lia. reflexivity.
  - rewrite !Z.ones_spec_high by lia. cbn [orb].
    apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec q 0) as [->|Hq0]; [rewrite Z.log2_nonpos by lia; lia|].
    assert (HL : Z.log2 q < 64)
      by (destruct (Z.log2_lt_pow2 q 64 ltac:(lia)) as [A1 A2]; first [apply A1; lia | apply A2; lia]).
    lia.
Qed.

Lemma c1_a1 : forall (b : bool) s,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 ((if b then 1 else 0) + -1))) (bv_unsigned (Z_to_bv 64 s))) =
  Z_to_bv 64 (if b then s else -1).
Proof.
  intros b s. pose proof (u64_range (Z_to_bv 64 s)) as R.
  destruct b; cbn [Z.add].
  - change ((1 + -1)%Z) with 0%Z. rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_l.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - change ((0 + -1)%Z) with (-1)%Z. rewrite unsigned_lit_wrap.
    change ((-1) mod 2 ^ 64)%Z with 18446744073709551615%Z.
    rewrite (c1_lor_ones (bv_unsigned (Z_to_bv 64 s)) R). apply bv_eq. reflexivity.
Qed.

(* afd_down_scanF.v:43-55, verbatim: the 8-aligned shadow-word cover of [p, p + n) holds the shadow word of p + i. *)
Lemma c1_shadow_sub : forall (RNG : ExecF.footprint) p n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr p / 8 * 8) (shadow_addr (p + n - 1) / 8 * 8 + 8 - shadow_addr p / 8 * 8) ->
  ExecF.rng RNG (shadow_addr (p + i) / 8 * 8) 8.
Proof.
  intros RNG p n i Hi R.
  assert (M1 : shadow_addr p / 8 <= shadow_addr (p + i) / 8).
  { apply Z.div_le_mono; [lia|]. unfold shadow_addr.
    pose proof (Z.div_le_mono p (p + i) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (M2 : shadow_addr (p + i) / 8 <= shadow_addr (p + n - 1) / 8).
  { apply Z.div_le_mono; [lia|]. unfold shadow_addr.
    pose proof (Z.div_le_mono (p + i) (p + n - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  eapply ExecF.rng_sub; [exact R | lia | lia].
Qed.

(* afd_down_scan.v:564-584, verbatim: a read of n bytes at A is kept by a change of memory outside its bytes. *)
Lemma c1_rdn_munch : forall W m m' (n : nat) A, munch W m m' -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> outside W (A + i)) ->
  rdn rsegs m' (wa A) n = rdn rsegs m (wa A) n.
Proof.
  intros W m m' n. induction n as [|n IH]; intros A MU H0 H1 HO; [reflexivity|].
  cbn [rdn]. rewrite (MU (wa A)).
  2:{ rewrite wa_unsigned by lia. replace A with (A + 0) by lia. apply HO. lia. }
  rewrite wa_succ. rewrite (IH (A + 1) MU).
  - reflexivity.
  - lia.
  - lia.
  - intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply HO. lia.
Qed.

Lemma c1_ovr_munch : forall W m m' A (n : nat) bs, munch W m m' -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> outside W (A + i)) ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) n = Some bs -> ov_read_bytes rsegs m' (Z_to_bv 64 A) n = Some bs.
Proof.
  intros W m m' A n bs MU H0 H1 HO R. rewrite ov_rdn in *. change (Z_to_bv 64 A) with (wa A) in *.
  rewrite (c1_rdn_munch W m m' n A MU H0 H1 HO). exact R.
Qed.

Section Runs.
Variable RNG : ExecF.footprint.
Variables (x3 x4 x8 x25 : word).                   (* gp, tp, s0, s9: kept through the whole segment *)
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variables (SB res out mode len olen nch ns : Z).
Variables (wf fits0 fits : bool).

(* s3 at +0x5d4 is the harness's `wellformed && fits0 && fits`, the plain check; a1 at +0x5dc adds the even-width
   test, the decode check (afd_down_scan.v:348 dok, :55 ads_cond_plain, :1858 ads_cond_decode). *)
Definition c1_pok : bool := (wf && fits0 && fits)%bool.
Definition c1_dok : bool := (wf && fits0 && fits && (nch mod 2 =? 0))%bool.

Hypothesis HSB : 0 <= SB /\ SB + 120 <= 18446744073709551616.
Hypothesis Hnch : -128 <= nch <= 127.
Hypothesis Hns : -128 <= ns <= 127.
Hypothesis Holen : 0 < olen < 2 ^ 32.
Hypothesis Hres : 4096 <= res /\ res + 1543 <= 18446744073709551616.
Hypothesis Hout : 0 <= out /\ out + olen + 1 <= 18446744073709551616.
Hypothesis Hlen : 0 <= len < 2 ^ 26.
Hypothesis Hmode : 0 <= mode < 2 ^ 64.
Hypothesis Hpos : fits0 = true -> 0 < nch /\ 0 < ns.

(* The regions the runs read: the s1 slot area [SB + 24, SB + 96), the decode buffer, and the 8-aligned
   shadow-word cover of the decode buffer (L1's instrumented check loads the shadow byte of each buffer byte). *)
Hypothesis RSTK : ExecF.rng RNG (SB + 24) 72.
Hypothesis RBUF : ExecF.rng RNG out olen.
Hypothesis RSH : ExecF.rng RNG (shadow_addr out / 8 * 8)
  (shadow_addr (out + olen - 1) / 8 * 8 + 8 - shadow_addr out / 8 * 8).

(* ---- the state at a call of this segment ---- *)
(* The registers the segment keeps live from +0x5cc to +0x6ec: s4 = len, s5 = mode, s7 = nch, s8 = fits0,
   s10 = olen, s11 = copy (callee-saved, and reloaded from 40(s1) after each call), and s9 / gp / tp / s0 / s1. *)
Definition c1_at (pc ra : Z) (a0 a1 a2 a3 s2v s3v s6v : word) (mm : word -> option byte) (ms : machine_state) : Prop :=
  exists (r1 t0 t1 t2 t3 t4 t5 t6 a4 a5 a6 a7 : word),
    ms = MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB) a0 a1 a2 a3 a4 a5 a6 a7
                 s2v s3v (Z_to_bv 64 len) (Z_to_bv 64 mode) s6v (Z_to_bv 64 nch)
                 (Z_to_bv 64 (if fits0 then 1 else 0)) x25 (Z_to_bv 64 olen) (Z_to_bv 64 res) t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs) /\
    bv_unsigned r1 = ra.

(* The memory of the segment's own writes: the single store of copy + 50 to 80(s1) at +0x658. *)
Definition c1_mem0 (m mm : word -> option byte) : Prop :=
  munch [(SB + 80, SB + 88)] m mm /\ wmono rsegs m mm /\
  ov_read_bytes rsegs mm (Z_to_bv 64 (SB + 80)) 8 = Some (le8 (Z_to_bv 64 (res + 50))).

(* The call of check_round_trip at +0x68c: a0 = copy + 50, a1 = buffer, a2 = nch, a3 = ns; s2 is dead here. *)
Definition c1_q_crt (mm : word -> option byte) (ms : machine_state) : Prop :=
  exists s2v : word,
    c1_at C1_CRT (C1 0x690) (Z_to_bv 64 (res + 50)) (Z_to_bv 64 out) (Z_to_bv 64 nch) (Z_to_bv 64 ns)
      s2v (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 out) mm ms.

(* The call of check_braid at +0x6bc: the same four arguments. *)
Definition c1_q_braid (mm : word -> option byte) (ms : machine_state) : Prop :=
  exists s2v : word,
    c1_at C1_BRAID (C1 0x6c0) (Z_to_bv 64 (res + 50)) (Z_to_bv 64 out) (Z_to_bv 64 nch) (Z_to_bv 64 ns)
      s2v (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 out) mm ms.

(* The call of __asan_memset at +0x6d4: a0 = buffer, a1 = 0xa5, a2 = olen; a3 is dead here. *)
Definition c1_q_memset (mm : word -> option byte) (ms : machine_state) : Prop :=
  exists a3 : word,
    c1_at C1_MEMSET (C1 0x6d8) (Z_to_bv 64 out) (Z_to_bv 64 165) (Z_to_bv 64 olen) a3
      (Z_to_bv 64 out) (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 out) mm ms.

(* The call of reac_decode_plain_le at +0x6ec: a0 = copy, a1 = len, a2 = mode, a3 = buffer. *)
Definition c1_q_plain (mm : word -> option byte) (ms : machine_state) : Prop :=
  c1_at C1_PLAIN (C1 0x6f0) (Z_to_bv 64 res) (Z_to_bv 64 len) (Z_to_bv 64 mode) (Z_to_bv 64 out)
    (Z_to_bv 64 out) (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 len) mm ms.

(* The three exits of the head run. *)
Definition c1_q_head (m : word -> option byte) (ms : machine_state) : Prop :=
  exists mm : word -> option byte, c1_mem0 m mm /\
    ((c1_q_crt mm ms /\ c1_dok = true /\ 0 < ns <= 12) \/
     (c1_q_braid mm ms /\ c1_dok = true /\ 12 < ns) \/
     (c1_q_memset mm ms /\ c1_dok = false)).

Section Head.
Variable m : word -> option byte.
Hypothesis RD32 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 32)) 8 = Some (le8 (Z_to_bv 64 ASAN_K)).
Hypothesis RD40 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 40)) 8 = Some (le8 (Z_to_bv 64 res)).
Hypothesis RD72 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 72)) 8 = Some (le8 (Z_to_bv 64 ns)).
Hypothesis RD88 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 88)) 8 = Some (le8 (Z_to_bv 64 out)).
Hypothesis HW80 : store_ok rsegs m (Z_to_bv 64 (SB + 80)) 8 = true.
Hypothesis AD : addressable m out olen.
Hypothesis HA5 : c1_dok = false -> forall i, 0 <= i < olen -> mrd rsegs m (wa (out + i)) = Some (Z_to_bv 8 165).

(* ---- +0x654 .. the three calls: the spill of copy + 50 and the two dispatch tests
   (afd_down_scan.v:392 c1_tail at 0x80704, and :633 ck_braid / :672 ck_ret for +0x698 .. +0x6bc) ---- *)
Lemma c1_tail : forall (d : bool) (r1 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 : word),
  c1_dok = d ->
  ExecF.evtF rsegs RNG (c1_q_head m)
    (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB)
             (Z_to_bv 64 (if d then ns else -1)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (if fits then 1 else 0)) (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 len)
             (Z_to_bv 64 mode) (Z_to_bv 64 out) (Z_to_bv 64 nch) (Z_to_bv 64 (if fits0 then 1 else 0)) x25
             (Z_to_bv 64 olen) (Z_to_bv 64 res) t3 t4 t5 t6)
        F (Z_to_bv 64 (C1 0x654)) fc None m (seg_rom rsegs)).
Proof.
  intros d r1 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 Ed.
  c1_pc.
  (* +0x654 addi a1,s11,50 ; +0x658 sd a1,80(s1) *)
  step. step.
  set (m1 := write_to_mem m (Z_to_bv 64 (SB + 80)) (le8 (Z_to_bv 64 (res + 50)))).
  assert (MU : munch [(SB + 80, SB + 88)] m m1).
  { unfold m1. change (Z_to_bv 64 (SB + 80)) with (wa (SB + 80)).
    apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [inside]. left. lia. }
  assert (WM : wmono rsegs m m1) by (unfold m1; apply wmono_write, wmono_refl).
  assert (R80 : ov_read_bytes rsegs m1 (Z_to_bv 64 (SB + 80)) 8 = Some (le8 (Z_to_bv 64 (res + 50)))).
  { pose proof (rd_all m1 (SB + 80) (le8 (Z_to_bv 64 (res + 50)))) as R. rewrite length_le8 in R. apply R.
    unfold m1. change (Z_to_bv 64 (SB + 80)) with (wa (SB + 80)).
    apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
  assert (R40 : ov_read_bytes rsegs m1 (Z_to_bv 64 (SB + 40)) 8 = Some (le8 (Z_to_bv 64 res)))
    by (apply (c1_ovr_munch [(SB + 80, SB + 88)] m m1 (SB + 40) 8); [exact MU | lia | lia | intros i Hi; cbn [outside]; split; [lia|exact I] | exact RD40]).
  assert (R72 : ov_read_bytes rsegs m1 (Z_to_bv 64 (SB + 72)) 8 = Some (le8 (Z_to_bv 64 ns)))
    by (apply (c1_ovr_munch [(SB + 80, SB + 88)] m m1 (SB + 72) 8); [exact MU | lia | lia | intros i Hi; cbn [outside]; split; [lia|exact I] | exact RD72]).
  assert (R88 : ov_read_bytes rsegs m1 (Z_to_bv 64 (SB + 88)) 8 = Some (le8 (Z_to_bv 64 out)))
    by (apply (c1_ovr_munch [(SB + 80, SB + 88)] m m1 (SB + 88) 8); [exact MU | lia | lia | intros i Hi; cbn [outside]; split; [lia|exact I] | exact RD88]).
  assert (MEM0 : c1_mem0 m m1) by (split; [exact MU | split; [exact WM | exact R80]]).
  clearbody m1.
  destruct d; cbv iota.
  - assert (Hp : fits0 = true) by (unfold c1_dok in Ed; rewrite !andb_true_iff in Ed; tauto).
    destruct (Hpos Hp) as [Pn Ps].
    (* +0x65c blez a0: a0 = ns > 0, not taken *)
    step. blts 0 ns. rewrite (proj2 (Z.ltb_lt 0 ns) Ps). cbn [negb].
    (* +0x660 li a1,12 ; +0x664 ld a2,72(s1) ; +0x668 blt a1,a2 *)
    step. step. step. blts 12 ns.
    destruct (Z.ltb_spec 12 ns) as [L|L]; cbv iota.
    + (* +0x698 blez a0: not taken; +0x69c .. +0x6bc the check_braid call *)
      step. blts 0 ns. rewrite (proj2 (Z.ltb_lt 0 ns) Ps). cbn [negb].
      step. beqb res 0. rewrite (proj2 (Z.eqb_neq res 0) ltac:(lia)). cbv iota.
      step. step. step. bltu 18446744073709551565 res.
      rewrite (proj2 (Z.ltb_ge 18446744073709551565 res) ltac:(lia)). cbv iota.
      step. step. step. step. step.
      apply ExecF.evtF_done. unfold c1_q_head. exists m1. split; [exact MEM0|].
      right; left. split; [| split; [exact Ed | lia]].
      unfold c1_q_braid, c1_at. eexists. do 12 eexists. split; [reflexivity | c1_ra].
    + (* +0x66c .. +0x68c the check_round_trip call *)
      step. beqb res 0. rewrite (proj2 (Z.eqb_neq res 0) ltac:(lia)). cbv iota.
      step. step. step. bltu 18446744073709551565 res.
      rewrite (proj2 (Z.ltb_ge 18446744073709551565 res) ltac:(lia)). cbv iota.
      step. step. step. step. step.
      apply ExecF.evtF_done. unfold c1_q_head. exists m1. split; [exact MEM0|].
      left. split; [| split; [exact Ed | lia]].
      unfold c1_q_crt, c1_at. eexists. do 12 eexists. split; [reflexivity | c1_ra].
  - (* +0x65c blez a0 and +0x698 blez a0: a0 = -1, both taken; +0x6c4 .. +0x6d4 the memset call *)
    step. brv. step. brv.
    step. step. step. step. step.
    apply ExecF.evtF_done. unfold c1_q_head. exists m1. split; [exact MEM0|].
    right; right. split; [| exact Ed].
    unfold c1_q_memset, c1_at. eexists. do 12 eexists. split; [reflexivity | c1_ra].
Qed.

(* ---- +0x614 .. +0x628: the instrumented check of the buffer byte at A (afd_down_scan.v:451 c1_chk, in
   afd_down_scanF.v:86 s2_chk_F's footprint form) ---- *)
Lemma c1_chk : forall (Q : machine_state -> Prop)
    (r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 s2v s3v : word) (k b : byte) (A : Z),
  bv_unsigned a1 = A ->
  mrd rsegs m (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  mrd rsegs m (wa A) = Some b ->
  ExecF.rng RNG A 1 ->
  ExecF.rng RNG (shadow_addr A / 8 * 8) 8 ->
  (forall y5 y6 : word,
     ExecF.evtF rsegs RNG Q
       (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB) a0 (zxb b) a2 a3 a4 y5 y6
                (Z_to_bv 64 ASAN_K) s2v s3v (Z_to_bv 64 len) (Z_to_bv 64 mode) (Z_to_bv 64 out) (Z_to_bv 64 nch)
                (Z_to_bv 64 (if fits0 then 1 else 0)) x25 (Z_to_bv 64 olen) (Z_to_bv 64 res) t3 t4 t5 t6)
           F (Z_to_bv 64 (C1 0x628)) fc None m (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 ASAN_K)
             s2v s3v (Z_to_bv 64 len) (Z_to_bv 64 mode) (Z_to_bv 64 out) (Z_to_bv 64 nch)
             (Z_to_bv 64 (if fits0 then 1 else 0)) x25 (Z_to_bv 64 olen) (Z_to_bv 64 res) t3 t4 t5 t6)
        F (Z_to_bv 64 (C1 0x614)) fc None m (seg_rom rsegs)).
Proof.
  intros Q r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 s2v s3v k b A EA M SK MD RA RS CONT.
  c1_pc. unfold ASAN_K in *.
  pose proof (u64_range a1) as RU.
  assert (RA1 : ExecF.rng RNG (bv_unsigned a1) 1) by (rewrite EA; exact RA).
  (* +0x614 srli a5,a1,3 *)
  step. gen_shr a1 g G. rewrite EA in G.
  (* +0x618 add a5,a5,a7 *)
  step. gen_addi g h H.
  assert (EH : bv_unsigned h = shadow_addr A) by (unfold shadow_addr, ASAN_K in *; lia).
  assert (RH : ExecF.rng RNG (bv_unsigned h) 1).
  { pose proof (Z.div_mod (shadow_addr A) 8 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (shadow_addr A) 8 ltac:(lia)) as MB8.
    eapply ExecF.rng_sub; [exact RS | lia | lia]. }
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  (* +0x620 bnez a5 *)
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    pose proof (rdw0 m a1 _ _ MD EA) as R. step. clear R.
    apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    (* +0x640 andi a6,a1,7 ; +0x644 blt a6,a5 *)
    step. step.
    rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    pose proof (rdw0 m a1 _ _ MD EA) as R. step. clear R.
    apply CONT.
Qed.

(* ---- +0x608 .. +0x650: the 0xa5 scan loop L1 (afd_down_scan.v:479 c1_loop, afd_down_scanF.v:122 s2_loop_F) ---- *)
Lemma c1_loop : c1_dok = false ->
  forall (K : nat) (i : Z) (r1 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 : word),
  Z.to_nat (olen - i) = K -> 0 <= i < olen ->
  bv_unsigned a2 = 0 -> bv_unsigned a3 = i -> bv_unsigned a4 = 18446744073709551615 - out ->
  bv_unsigned a7 = ASAN_K ->
  ExecF.evtF rsegs RNG (c1_q_head m)
    (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (if fits then 1 else 0)) (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 len)
             (Z_to_bv 64 mode) (Z_to_bv 64 out) (Z_to_bv 64 nch) (Z_to_bv 64 (if fits0 then 1 else 0)) x25
             (Z_to_bv 64 olen) (Z_to_bv 64 res) t3 t4 t5 t6)
        F (Z_to_bv 64 (C1 0x608)) fc None m (seg_rom rsegs)).
Proof.
  intros Ed. pose proof (HA5 Ed) as A5.
  pose proof AD as (D0 & N0 & DE & _). unfold APPMEM_END in DE.
  induction K as [K IH] using lt_wf_ind.
  intros i r1 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 HK Hi H2 H3 H4 H7.
  unfold ASAN_K in *.
  apply wv in H2, H3, H4, H7. subst a2 a3 a4 a7.
  destruct (addr_one m out olen i AD Hi) as (APP & k & MK & SK).
  pose proof (A5 i Hi) as MB.
  assert (RB1 : ExecF.rng RNG (out + i) 1) by (eapply ExecF.rng_sub; [exact RBUF | lia | lia]).
  pose proof (c1_shadow_sub RNG out olen i Hi RSH) as RS1.
  c1_pc.
  (* +0x608 bltu a4,a3 *)
  step. rewrite ltu_lit by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv iota.
  (* +0x60c ld a1,88(s1) ; +0x610 add a1,a1,a3 *)
  step. step.
  eapply c1_chk;
    [ apply unsigned_lit; lia | exact MK | exact SK | exact MB | exact RB1 | exact RS1 | intros y5 y6 ].
  (* +0x628 addi a1,a1,-165 ; +0x62c snez a1,a1 ; +0x630 addi a3,a3,1 ; +0x634 or a2,a2,a1 ; +0x638 bne s10,a3 *)
  step. step. step. step. step.
  assert (Z1 : PropExec.v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 165)) + -165))
               = Z_to_bv 64 0)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Z1.
  assert (Z2 : Z_to_bv 64 (Z.lor 0 (bv_unsigned (Z_to_bv 64 0))) = Z_to_bv 64 0)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Z2.
  rewrite eqb_lit by lia.
  destruct (Z.eqb_spec olen (i + 1)) as [E|E]; cbn [negb].
  - (* +0x63c j +0x650 ; +0x650 bnez a2: a2 = 0, not taken *)
    step. step. rewrite (eqb_lit 0 0) by lia. cbn [negb Z.eqb].
    eapply (c1_tail false); exact Ed.
  - eapply (IH (Z.to_nat (olen - (i + 1))) ltac:(lia) (i + 1)); try lia; try (apply unsigned_lit; lia).
Qed.

(* ---- +0x5cc .. the three calls: the decode-result compare, the branch on its sign, and L1 ---- *)
Lemma c1_run_head : forall (d : bool) (r1 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 : word),
  c1_dok = d ->
  ExecF.evtF rsegs RNG (c1_q_head m)
    (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB)
             (Z_to_bv 64 (if d then ns else -1)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (if fits then 1 else 0)) (Z_to_bv 64 (if wf then 1 else 0)) (Z_to_bv 64 len)
             (Z_to_bv 64 mode) (Z_to_bv 64 out) (Z_to_bv 64 nch) (Z_to_bv 64 (if fits0 then 1 else 0)) x25
             (Z_to_bv 64 olen) (Z_to_bv 64 res) t3 t4 t5 t6)
        F (Z_to_bv 64 (C1 0x5cc)) fc None m (seg_rom rsegs)).
Proof.
  intros d r1 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 Ed.
  assert (Ed' : (wf && fits0 && fits && (nch mod 2 =? 0))%bool = d) by exact Ed.
  c1_pc.
  (* +0x5cc and a1,s3,s8 ; +0x5d0 andi a2,s7,1 ; +0x5d4 and s3,a1,s2 ; +0x5d8 seqz a1,a2 ; +0x5dc and a1,s3,a1 ;
     +0x5e0 addi a1,a1,-1 ; +0x5e4 ld a2,72(s1) ; +0x5e8 or a1,a1,a2 *)
  step. step. step. step. step. step. step. step.
  rewrite (c1_seqz nch), !c1_land, c1_a1.
  change ((wf && fits0)%bool && fits && (nch mod 2 =? 0))%bool with c1_dok.
  change ((wf && fits0)%bool && fits)%bool with c1_pok.
  rewrite Ed.
  (* +0x5ec bne a0,a1: a1 = a0, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb].
  (* +0x5f0 bgez a0 *)
  step.
  destruct d; cbv iota.
  - assert (Hp : fits0 = true) by (rewrite !andb_true_iff in Ed'; tauto).
    destruct (Hpos Hp) as [Pn Ps].
    blts ns 0. rewrite (proj2 (Z.ltb_ge ns 0) ltac:(lia)). cbn [negb].
    eapply (c1_tail true). exact Ed.
  - brv.
    pose proof AD as (D0 & N0 & DE & _). unfold APPMEM_END in DE.
    (* +0x5f4 li a3,0 ; +0x5f8 li a2,0 ; +0x5fc ld a1,88(s1) ; +0x600 not a4,a1 ; +0x604 ld a7,32(s1) *)
    step. step. step. step. step.
    eapply (c1_loop Ed (Z.to_nat (olen - 0)) 0); try lia; ufin.
Qed.
End Head.

(* ---- +0x690 .. +0x6bc: the return of check_round_trip to the check_braid call ---- *)
Section ACrt.
Variable m : word -> option byte.
Hypothesis RD40 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 40)) 8 = Some (le8 (Z_to_bv 64 res)).
Hypothesis RD72 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 72)) 8 = Some (le8 (Z_to_bv 64 ns)).
Hypothesis RD80 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 80)) 8 = Some (le8 (Z_to_bv 64 (res + 50))).
Hypothesis RD88 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 88)) 8 = Some (le8 (Z_to_bv 64 out)).

Lemma c1_run_acrt : forall (r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 a7 s2v s11v : word),
  ExecF.evtF rsegs RNG (c1_q_braid m)
    (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB) a0 a1 a2 a3 a4 a5 a6 a7
             s2v (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 len) (Z_to_bv 64 mode) (Z_to_bv 64 out)
             (Z_to_bv 64 nch) (Z_to_bv 64 (if fits0 then 1 else 0)) x25 (Z_to_bv 64 olen) s11v t3 t4 t5 t6)
        F (Z_to_bv 64 (C1 0x690)) fc None m (seg_rom rsegs)).
Proof.
  intros r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 a7 s2v s11v.
  c1_pc.
  (* +0x690 ld s11,40(s1) ; +0x694 j +0x69c *)
  step. step.
  (* +0x69c beqz s11 ; +0x6a0 li a0,-51 ; +0x6a4 ld a1,40(s1) ; +0x6a8 bltu a0,a1 *)
  step. beqb res 0. rewrite (proj2 (Z.eqb_neq res 0) ltac:(lia)). cbv iota.
  step. step. step. bltu 18446744073709551565 res.
  rewrite (proj2 (Z.ltb_ge 18446744073709551565 res) ltac:(lia)). cbv iota.
  (* +0x6ac ld a0,80(s1) ; +0x6b0 ld a1,88(s1) ; +0x6b4 mv a2,s7 ; +0x6b8 ld a3,72(s1) ; +0x6bc jal check_braid *)
  step. step. step. step. step.
  apply ExecF.evtF_done. unfold c1_q_braid, c1_at. eexists. do 12 eexists. split; [reflexivity | c1_ra].
Qed.
End ACrt.

(* ---- +0x6c0 .. +0x6d4: the return of check_braid to the __asan_memset call ---- *)
Section ABraid.
Variable m : word -> option byte.
Hypothesis RD40 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 40)) 8 = Some (le8 (Z_to_bv 64 res)).
Hypothesis RD88 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 88)) 8 = Some (le8 (Z_to_bv 64 out)).

Lemma c1_run_abraid : forall (r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 a7 s2v s11v : word),
  ExecF.evtF rsegs RNG (c1_q_memset m)
    (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB) a0 a1 a2 a3 a4 a5 a6 a7
             s2v (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 len) (Z_to_bv 64 mode) (Z_to_bv 64 out)
             (Z_to_bv 64 nch) (Z_to_bv 64 (if fits0 then 1 else 0)) x25 (Z_to_bv 64 olen) s11v t3 t4 t5 t6)
        F (Z_to_bv 64 (C1 0x6c0)) fc None m (seg_rom rsegs)).
Proof.
  intros r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 a7 s2v s11v.
  c1_pc.
  (* +0x6c0 ld s11,40(s1) ; +0x6c4 li a1,0xa5 ; +0x6c8 ld s2,88(s1) ; +0x6cc mv a0,s2 ; +0x6d0 mv a2,s10 ;
     +0x6d4 jal __asan_memset *)
  step. step. step. step. step. step.
  apply ExecF.evtF_done. unfold c1_q_memset, c1_at. eexists. do 12 eexists. split; [reflexivity | c1_ra].
Qed.
End ABraid.

(* ---- +0x6d8 .. +0x6ec: the return of __asan_memset to the reac_decode_plain_le call ---- *)
Section AMset.
Variable m : word -> option byte.
Hypothesis RD24 : ov_read_bytes rsegs m (Z_to_bv 64 (SB + 24)) 8 = Some (le8 (Z_to_bv 64 len)).

Lemma c1_run_amset : forall (r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 a7 s6v : word),
  ExecF.evtF rsegs RNG (c1_q_plain m)
    (MS (mkR r1 (Z_to_bv 64 SB) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 SB) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 out) (Z_to_bv 64 (if c1_pok then 1 else 0)) (Z_to_bv 64 len) (Z_to_bv 64 mode) s6v
             (Z_to_bv 64 nch) (Z_to_bv 64 (if fits0 then 1 else 0)) x25 (Z_to_bv 64 olen) (Z_to_bv 64 res)
             t3 t4 t5 t6)
        F (Z_to_bv 64 (C1 0x6d8)) fc None m (seg_rom rsegs)).
Proof.
  intros r1 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 a7 s6v.
  c1_pc.
  (* +0x6d8 mv a0,s11 ; +0x6dc ld s6,24(s1) ; +0x6e0 mv a1,s6 ; +0x6e4 mv a2,s5 ; +0x6e8 mv a3,s2 ;
     +0x6ec jal reac_decode_plain_le *)
  step. step. step. step. step. step.
  apply ExecF.evtF_done. unfold c1_q_plain, c1_at. do 12 eexists. split; [reflexivity | c1_ra].
Qed.
End AMset.
End Runs.
