(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: the footprint walk of reac-repacer/fuzz_uci's rp_hot_clamp in image A, against the frozen
   lib/A/Prog/rp_hot_clamp_F_c.v rp_hot_clamp_contract_F. It follows lib/Prog/rp_hot_clamp.v (the plain walk: one
   continuation-style lemma per field; its f_pf .. f_sv, model_split, f_mn_range, sx32_int and lts_lit / ltu_lit reused
   by name, its mcase / br / join tactics copied, join extended to the walk's invariant) in the footprint style of
   proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F.v and reac_decode_F.v (origin/ossv/recipes 88154566652a:
   StepF's step, one rng fact per access; rd_all, addr_four, lts_sm and the one-byte shadow window copied from that
   unit's ReacDecodeLib.v and reac_decode_F.v; rw_cells_app from lib/Prog/check_clamp.v). *)
(* Modified by Theorem Labs, 2026-10: copied from this unit's lib/A/Prog/rp_hot_clamp_FW.v (commit e89702c42a3) for
   image B, against the frozen lib/B/Prog/rp_hot_clamp_F_c.v rp_hot_clamp_contract_F: Img0 / AsanCells / AsanKA /
   AsanKAProof / rp_hot_clamp_c / rp_hot_clamp_F_c are lib/B's; every pc is fuzz_uci.asan-ubsan's (the body 0xe0 above
   image A's, the check targets 0xe4 above); the entry steps over image B's UBSan checks of p, refuted from the
   statement's premises `bv_unsigned a0 <> 0` and `bv_unsigned a0 mod 4 = 0`. *)
(* rp_hot_clamp of fuzz_uci.asan-ubsan (entry 0x7fd38, 0x29c bytes): `addi sp, sp, -0x10`, `sd ra, 8(sp)`, then the
   UBSan checks of p, `beqz a0, 0x7feb4` and `andi a2, a0, 3` / `bnez a2, 0x7feb4` (`unimp` at 0x7feb4): a0 <> 0 and
   a0 mod 4 = 0 make both fall through. Then the shadow base through the GOT word 0x97128 and the cell 0x9f0f8, then the
   five int fields of *a0. Before each 4-byte load or store of a field at x it loads the shadow byte k of x,
   (x >> 3) + 0x7fff8000, and when k <> 0 runs `andi t, x, 7`; `addi t, t, 3`; `blt t, k, back`, else falls into
   `jal __asan_report_load4` (8 sites, 0x7fec4 .. 0x7ff4c) or `jal __asan_report_store4` (7 sites, 0x7ff5c ..
   0x7ffd0). The premise `addressable m a0 20` gives every field's shadow byte with k = 0 \/ x mod 8 + 3 < k
   (addr_four), so each check returns to `back`: the lemmas ck_<pc>, one per check, prove it, and no report call is
   reached. The fields follow lib/Spec/UciModel.v's rp_hot_clamp_m, as in the plain walk, except that adapt_max_ms is
   clamped in two steps (mx1, then against adapt_min_ms read back from memory) and adapt_margin likewise (mg1, then
   against margin_max). No shadow byte lies in the frame or the struct, so the stores leave them unchanged and each
   segment reads them from the entry memory through its munch fact (shrd). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import AsanKA AsanKAProof rp_hot_clamp_c rp_hot_clamp_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c rp_hot_clamp.
Import ListNotations.
Open Scope Z_scope.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.
Module PW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp.

(* ---- memory and arithmetic helpers ---- *)

Lemma rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma rhc_app : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in Hn, Hw.
  split; (split; [split; assumption|]).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma rhc_app_merge : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hn1 & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

(* struct rp_hot as five one-field cells, and back *)
Lemma rw5_split : forall m A (v0 v1 v2 v3 v4 : word),
  rw_cells rsegs m A [C4 v0; C4 v1; C4 v2; C4 v3; C4 v4] ->
  rw_cells rsegs m A [C4 v0] /\ rw_cells rsegs m (A + 4) [C4 v1] /\ rw_cells rsegs m (A + 8) [C4 v2] /\
  rw_cells rsegs m (A + 12) [C4 v3] /\ rw_cells rsegs m (A + 16) [C4 v4].
Proof.
  intros m A v0 v1 v2 v3 v4 H.
  apply (rhc_app m A [C4 v0] _) in H as [H0 H]. apply (rhc_app m _ [C4 v1] _) in H as [H1 H].
  apply (rhc_app m _ [C4 v2] _) in H as [H2 H]. apply (rhc_app m _ [C4 v3] [C4 v4]) in H as [H3 H4].
  cbn [cells_size csize Nat.add] in H1, H2, H3, H4. change (Z.of_nat 4) with 4 in H1, H2, H3, H4.
  replace (A + 4 + 4) with (A + 8) in H2 by lia.
  replace (A + 4 + 4 + 4) with (A + 12) in H3 by lia.
  replace (A + 4 + 4 + 4 + 4) with (A + 16) in H4 by lia.
  exact (conj H0 (conj H1 (conj H2 (conj H3 H4)))).
Qed.

Lemma rw5_merge : forall m A (v0 v1 v2 v3 v4 : word),
  rw_cells rsegs m A [C4 v0] -> rw_cells rsegs m (A + 4) [C4 v1] -> rw_cells rsegs m (A + 8) [C4 v2] ->
  rw_cells rsegs m (A + 12) [C4 v3] -> rw_cells rsegs m (A + 16) [C4 v4] ->
  rw_cells rsegs m A [C4 v0; C4 v1; C4 v2; C4 v3; C4 v4].
Proof.
  intros m A v0 v1 v2 v3 v4 H0 H1 H2 H3 H4.
  apply (rhc_app_merge m A [C4 v0] [C4 v1; C4 v2; C4 v3; C4 v4]); [exact H0|].
  apply (rhc_app_merge m _ [C4 v1] [C4 v2; C4 v3; C4 v4]); [exact H1|].
  cbn [cells_size csize Nat.add]; change (Z.of_nat 4) with 4.
  apply (rhc_app_merge m _ [C4 v2] [C4 v3; C4 v4]);
    [replace (A + 4 + 4) with (A + 8) by lia; exact H2|].
  cbn [cells_size csize Nat.add]; change (Z.of_nat 4) with 4.
  apply (rhc_app_merge m _ [C4 v3] [C4 v4]).
  - replace (A + 4 + 4 + 4) with (A + 12) by lia. exact H3.
  - cbn [cells_size csize Nat.add]; change (Z.of_nat 4) with 4.
    replace (A + 4 + 4 + 4 + 4) with (A + 16) by lia. exact H4.
Qed.

(* the shadow byte of a 4-byte access inside an addressable range (ReacDecodeLib.v addr_four) *)
Lemma addr_four : forall m p n a, addressable m p n -> p <= a -> a + 4 <= p + n ->
  exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\ (bv_signed k = 0 \/ a mod 8 + 3 < bv_signed k).
Proof.
  intros m p n a (H0 & H1 & H2 & H) Ha Hn.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Mb.
  destruct (Z_le_gt_dec (a mod 8) 4) as [L|L].
  - destruct (H (a + 3 - p) ltac:(lia)) as (Hap & k & Hk & Hok).
    replace (p + (a + 3 - p)) with (a + 3) in Hk, Hok by lia.
    assert (E1 : (a + 3) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (a + 3) mod 8 = a mod 8 + 3) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
    exists k. split; [exact Hk | lia].
  - destruct (H (a + (7 - a mod 8) - p) ltac:(lia)) as (Hap & k & Hk & Hok).
    replace (p + (a + (7 - a mod 8) - p)) with (a + (7 - a mod 8)) in Hk, Hok by lia.
    assert (E1 : (a + (7 - a mod 8)) / 8 = a / 8) by (Z.div_mod_to_equations; lia).
    assert (E2 : (a + (7 - a mod 8)) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    unfold shadow_addr in Hk. rewrite E1 in Hk. unfold shadow_ok in Hok. rewrite E2 in Hok.
    exists k. split; [exact Hk | lia].
Qed.

(* the one-byte window of the shadow range of [p, p + n) at the shadow byte of a (reac_decode_F.v rng_shadow_one) *)
Lemma rng_one_shadow : forall RNG p n a,
  rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> rng RNG (shadow_addr a) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in *.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply rng_sub; [exact H | lia | lia].
Qed.

Lemma lts_sm : forall (x : Z) (k : byte), 0 <= x < 2^63 -> bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

(* `srli r, x, 3`; `add r, r, base`: the shadow address of x *)
Lemma shreg : forall x a, x = a -> 0 <= a < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftr x 3 + 2147450880)) = shadow_addr a.
Proof.
  intros x a -> Ha. unfold shadow_addr, ASAN_K. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply unsigned_lit. Z.div_mod_to_equations. lia.
Qed.

(* a shadow byte outside the window W of a run keeps its entry value *)
Lemma shrd : forall W m0 m S k (h : word), munch W m0 m -> outside W S ->
  mrd rsegs m0 (wa S) = Some k -> bv_unsigned h = S -> ov_read_bytes rsegs m h 1 = Some [k].
Proof.
  intros W m0 m S k h MU OUT M U. apply (rdw0 m h S k); [|exact U].
  unfold mrd in *. rewrite MU; [exact M|]. rewrite wa_unsigned; [exact OUT|]. rewrite <- U. apply u64_range.
Qed.

(* shadow bytes are not application memory: none lies in the struct or in the frame *)
Lemma shadow_disj : forall A i, app_mem A -> app_mem (A + 19) -> 0 <= i <= 19 ->
  ~ (A <= shadow_addr (A + i) < A + 20).
Proof.
  unfold app_mem, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros A i HA HB Hi.
  Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_frame : forall s x, app_mem (s + -16) -> app_mem (s - 1) -> app_mem x ->
  ~ (s + -16 <= shadow_addr x < s).
Proof.
  unfold app_mem, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros s x HA HB Hx.
  Z.div_mod_to_equations. lia.
Qed.

(* the shadow check of a 4-byte access at X passes on shadow byte k *)
Definition shok (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 + 3 < bv_signed k.

(* adapt_max_ms and adapt_margin after their first clamp (the lets of PW.f_mx and PW.f_mg) *)
Definition mx1 (x : Z) : Z := if RP_ADAPT_MS_MAX <? x then RP_ADAPT_MS_MAX else x.
Definition mg1 (x : Z) : Z := if x <? 0 then 0 else x.

Lemma mx1_range : forall x, -2^31 <= x < 2^31 -> -2^31 <= mx1 x < 2^31.
Proof. intros x Hx. unfold mx1, RP_ADAPT_MS_MAX. destruct (Z.ltb_spec 1000 x); lia. Qed.

Lemma mg1_range : forall x, -2^31 <= x < 2^31 -> 0 <= mg1 x < 2^31.
Proof. intros x Hx. unfold mg1. destruct (Z.ltb_spec x 0); lia. Qed.

(* ---- tactics ---- *)

(* lib/Prog/rp_hot_clamp.v mcase: split the innermost comparison first and reduce *)
Local Ltac mcase :=
  unfold PW.f_pf, PW.f_mn, PW.f_mx, PW.f_mg, PW.f_sv, mx1, mg1, RP_PREFILL_MS_MIN, RP_PREFILL_MS_MAX,
    RP_ADAPT_MS_MIN, RP_ADAPT_MS_MAX, RP_SERVO_CLAMP_PPM_MAX; cbv zeta;
  repeat (match goal with
          | |- context [Z.ltb ?a ?b] =>
              lazymatch a with context [Z.ltb _ _] => fail | _ =>
              lazymatch b with context [Z.ltb _ _] => fail | _ => destruct (Z.ltb_spec a b) end end
          end; cbv beta iota);
  lia.

Local Ltac zc := rewrite ?PW.lts_lit, ?PW.ltu_lit by lia.

(* both orientations of [wa e = x] (lib/Prog/rp_hot_clamp.v) *)
Local Ltac addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* the pc after a conditional branch, with the condition stated over Z and split on [a <? b] *)
Local Ltac br a b P := zc; destruct (Z.ltb_spec a b) as [P|P]; cbv beta iota delta [negb].

(* the shadow address register after `srli; add`, named h with U : bv_unsigned h = shadow_addr a *)
Local Ltac shprep a h U :=
  lazymatch goal with |- context [Some (Z_to_bv 64 (Z.shiftr ?x 3 + 2147450880))] =>
    assert (U : bv_unsigned (Z_to_bv 64 (Z.shiftr x 3 + 2147450880)) = shadow_addr a)
      by (apply shreg; [first [reflexivity | apply unsigned_lit; lia] | lia]);
    let Eh := fresh "Eh" in
    remember (Z_to_bv 64 (Z.shiftr x 3 + 2147450880)) as h eqn:Eh; clear Eh
  end.

(* `lb` of the shadow byte at h: its value from the entry memory (shrd), its access from rng *)
Local Ltac shstep h U OUT M RS :=
  let R := fresh "R" in let RH := fresh "RH" in
  lazymatch goal with MUh : munch _ _ _ |- _ => pose proof (shrd _ _ _ _ _ h MUh OUT M U) as R end;
  pose proof RS as RH; rewrite <- U in RH;
  step; clear R RH.

(* the shadow check from its `bnez` back to the access *)
Local Ltac chk_proof HX C K :=
  unfold shok in C;
  lazymatch type of C with bv_signed ?k = 0 \/ _ =>
  lazymatch type of HX with bv_unsigned _ = ?X =>
    step; rewrite sxb_eq0; destruct C as [C|C];
    [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply K
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
      step; step; step;
      let MB := fresh "MB" in
      pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
      rewrite land7, HX; rewrite (lts_sm (X mod 8 + 3) k) by lia;
      rewrite (proj2 (Z.ltb_lt _ _) C); apply K ]
  end end.

(* apply a check lemma at its `bnez`: the access address is X, the check passes by C *)
Local Ltac ckapp L X C v :=
  refine (L _ _ _ _ _ _ _ _ _ _ X _ C _); first [intros v | reflexivity | apply unsigned_lit; lia].

Section Walk.
Variables (RNG : footprint) (Q : machine_state -> Prop)
  (ra sp1 gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32).

(* the states of the walk: sp1 is the frame's sp; r0 .. r7 are a0 .. a7 and rt is t0 *)
Local Abbreviation ST pc m r0 r1 r2 r3 r4 r5 r6 r7 rt :=
  (MS (mkR ra sp1 gp tp rt t1 t2 s0 s1 r0 r1 r2 r3 r4 r5 r6 r7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* ---- the fifteen shadow checks ---- *)

(* 0x7fd64: `bnez a3` on the shadow byte of the 4-byte load at a0; its check (`andi a5, a0, 7`;
   `addi a5, a5, 3`; `blt a5, a3`) returns to 0x7fd68: the `jal __asan_report_load4` at 0x7fec4 is not reached. *)
Lemma ck_7fd64 : forall m (r0 r1 r2 r4 r5 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r0 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fd68 m r0 r1 r2 (sxb k) r4 v r6 r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fd64 m r0 r1 r2 (sxb k) r4 r5 r6 r7 rt).
Proof. intros m r0 r1 r2 r4 r5 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fd88: `bnez a2` on the shadow byte of the 4-byte store at a0; its check (`andi a5, a0, 7`;
   `addi a5, a5, 3`; `blt a5, a2`) returns to 0x7fd8c: the `jal __asan_report_store4` at 0x7ff5c is not reached. *)
Lemma ck_7fd88 : forall m (r0 r1 r3 r4 r5 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r0 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fd8c m r0 r1 (sxb k) r3 r4 v r6 r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fd88 m r0 r1 (sxb k) r3 r4 r5 r6 r7 rt).
Proof. intros m r0 r1 r3 r4 r5 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fda0: `bnez a3` on the shadow byte of the 4-byte load at a2; its check (`andi a6, a2, 7`;
   `addi a6, a6, 3`; `blt a6, a3`) returns to 0x7fda4: the `jal __asan_report_load4` at 0x7fed8 is not reached. *)
Lemma ck_7fda0 : forall m (r0 r1 r2 r4 r5 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r2 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fda4 m r0 r1 r2 (sxb k) r4 r5 v r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fda0 m r0 r1 r2 (sxb k) r4 r5 r6 r7 rt).
Proof. intros m r0 r1 r2 r4 r5 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fdc4: `bnez a6` on the shadow byte of the 4-byte store at a2; its check (`andi a7, a2, 7`;
   `addi a7, a7, 3`; `blt a7, a6`) returns to 0x7fdc8: the `jal __asan_report_store4` at 0x7ff70 is not reached. *)
Lemma ck_7fdc4 : forall m (r0 r1 r2 r3 r4 r5 r7 rt : word) (k : byte) X,
  bv_unsigned r2 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fdc8 m r0 r1 r2 r3 r4 r5 (sxb k) v rt)) ->
  evtF rsegs RNG Q (ST 0x7fdc4 m r0 r1 r2 r3 r4 r5 (sxb k) r7 rt).
Proof. intros m r0 r1 r2 r3 r4 r5 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fddc: `bnez a7` on the shadow byte of the 4-byte load at a3; its check (`andi t0, a3, 7`;
   `addi t0, t0, 3`; `blt t0, a7`) returns to 0x7fde0: the `jal __asan_report_load4` at 0x7feec is not reached. *)
Lemma ck_7fddc : forall m (r0 r1 r2 r3 r4 r5 r6 rt : word) (k : byte) X,
  bv_unsigned r3 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fde0 m r0 r1 r2 r3 r4 r5 r6 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x7fddc m r0 r1 r2 r3 r4 r5 r6 (sxb k) rt).
Proof. intros m r0 r1 r2 r3 r4 r5 r6 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fdf0: `bnez a7` on the shadow byte of the 4-byte store at a3; its check (`andi t0, a3, 7`;
   `addi t0, t0, 3`; `blt t0, a7`) returns to 0x7fdf4: the `jal __asan_report_store4` at 0x7ff94 is not reached. *)
Lemma ck_7fdf0 : forall m (r0 r1 r2 r3 r4 r5 r6 rt : word) (k : byte) X,
  bv_unsigned r3 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fdf4 m r0 r1 r2 r3 r4 r5 r6 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x7fdf0 m r0 r1 r2 r3 r4 r5 r6 (sxb k) rt).
Proof. intros m r0 r1 r2 r3 r4 r5 r6 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe00: `bnez a7` on the shadow byte of the 4-byte load at a3; its check (`andi t0, a3, 7`;
   `addi t0, t0, 3`; `blt t0, a7`) returns to 0x7fe04: the `jal __asan_report_load4` at 0x7ff00 is not reached. *)
Lemma ck_7fe00 : forall m (r0 r1 r2 r3 r4 r5 r6 rt : word) (k : byte) X,
  bv_unsigned r3 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe04 m r0 r1 r2 r3 r4 r5 r6 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x7fe00 m r0 r1 r2 r3 r4 r5 r6 (sxb k) rt).
Proof. intros m r0 r1 r2 r3 r4 r5 r6 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe0c: `bnez a7` on the shadow byte of the 4-byte load at a2; its check (`andi t0, a2, 7`;
   `addi t0, t0, 3`; `blt t0, a7`) returns to 0x7fe10: the `jal __asan_report_load4` at 0x7ff14 is not reached. *)
Lemma ck_7fe0c : forall m (r0 r1 r2 r3 r4 r5 r6 rt : word) (k : byte) X,
  bv_unsigned r2 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe10 m r0 r1 r2 r3 r4 r5 r6 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x7fe0c m r0 r1 r2 r3 r4 r5 r6 (sxb k) rt).
Proof. intros m r0 r1 r2 r3 r4 r5 r6 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe1c: `bnez a5` on the shadow byte of the 4-byte store at a3; its check (`andi a6, a3, 7`;
   `addi a6, a6, 3`; `blt a6, a5`) returns to 0x7fe20: the `jal __asan_report_store4` at 0x7ffa8 is not reached. *)
Lemma ck_7fe1c : forall m (r0 r1 r2 r3 r4 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r3 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe20 m r0 r1 r2 r3 r4 (sxb k) v r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe1c m r0 r1 r2 r3 r4 (sxb k) r6 r7 rt).
Proof. intros m r0 r1 r2 r3 r4 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe34: `bnez a5` on the shadow byte of the 4-byte load at a2; its check (`andi a6, a2, 7`;
   `addi a6, a6, 3`; `blt a6, a5`) returns to 0x7fe38: the `jal __asan_report_load4` at 0x7ff28 is not reached. *)
Lemma ck_7fe34 : forall m (r0 r1 r2 r3 r4 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r2 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe38 m r0 r1 r2 r3 r4 (sxb k) v r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe34 m r0 r1 r2 r3 r4 (sxb k) r6 r7 rt).
Proof. intros m r0 r1 r2 r3 r4 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe44: `bnez a5` on the shadow byte of the 4-byte store at a2; its check (`andi a6, a2, 7`;
   `addi a6, a6, 3`; `blt a6, a5`) returns to 0x7fe48: the `jal __asan_report_store4` at 0x7ffd0 is not reached. *)
Lemma ck_7fe44 : forall m (r0 r1 r2 r3 r4 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r2 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe48 m r0 r1 r2 r3 r4 (sxb k) v r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe44 m r0 r1 r2 r3 r4 (sxb k) r6 r7 rt).
Proof. intros m r0 r1 r2 r3 r4 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe50: `bnez a5` on the shadow byte of the 4-byte load at a2; its check (`andi a6, a2, 7`;
   `addi a6, a6, 3`; `blt a6, a5`) returns to 0x7fe54: the `jal __asan_report_load4` at 0x7ff3c is not reached. *)
Lemma ck_7fe50 : forall m (r0 r1 r2 r3 r4 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r2 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe54 m r0 r1 r2 r3 r4 (sxb k) v r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe50 m r0 r1 r2 r3 r4 (sxb k) r6 r7 rt).
Proof. intros m r0 r1 r2 r3 r4 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe60: `bnez a3` on the shadow byte of the 4-byte store at a2; its check (`andi a5, a2, 7`;
   `addi a5, a5, 3`; `blt a5, a3`) returns to 0x7fe64: the `jal __asan_report_store4` at 0x7ffbc is not reached. *)
Lemma ck_7fe60 : forall m (r0 r1 r2 r4 r5 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r2 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe64 m r0 r1 r2 (sxb k) r4 v r6 r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe60 m r0 r1 r2 (sxb k) r4 r5 r6 r7 rt).
Proof. intros m r0 r1 r2 r4 r5 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fe78: `bnez a1` on the shadow byte of the 4-byte load at a0; its check (`andi a2, a0, 7`;
   `addi a2, a2, 3`; `blt a2, a1`) returns to 0x7fe7c: the `jal __asan_report_load4` at 0x7ff4c is not reached. *)
Lemma ck_7fe78 : forall m (r0 r2 r3 r4 r5 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r0 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fe7c m r0 (sxb k) v r3 r4 r5 r6 r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe78 m r0 (sxb k) r2 r3 r4 r5 r6 r7 rt).
Proof. intros m r0 r2 r3 r4 r5 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* 0x7fea0: `bnez a2` on the shadow byte of the 4-byte store at a0; its check (`andi a3, a0, 7`;
   `addi a3, a3, 3`; `blt a3, a2`) returns to 0x7fea4: the `jal __asan_report_store4` at 0x7ff80 is not reached. *)
Lemma ck_7fea0 : forall m (r0 r1 r3 r4 r5 r6 r7 rt : word) (k : byte) X,
  bv_unsigned r0 = X -> shok k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x7fea4 m r0 r1 (sxb k) v r4 r5 r6 r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fea0 m r0 r1 (sxb k) r3 r4 r5 r6 r7 rt).
Proof. intros m r0 r1 r3 r4 r5 r6 r7 rt k X HX C K. chk_proof HX C K. Qed.

(* ---- the struct walk, one segment per field (two for adapt_max_ms and adapt_margin) ---- *)

Variables (a0 : word) (mm : Z) (m0 : word -> option byte) (lo fb fe : Z) (jk : list byte)
  (k0 k1 k2 k3 k4 : byte).
Hypotheses (HA : bv_unsigned a0 + 20 <= 2^64) (HMM : 0 <= mm < 2^31)
  (DFR : bv_unsigned a0 + 20 <= fb \/ fb + 16 <= bv_unsigned a0)
  (RBUF : rng RNG (bv_unsigned a0) 20)
  (RS0 : rng RNG (shadow_addr (bv_unsigned a0)) 1) (RS1 : rng RNG (shadow_addr (bv_unsigned a0 + 4)) 1)
  (RS2 : rng RNG (shadow_addr (bv_unsigned a0 + 8)) 1) (RS3 : rng RNG (shadow_addr (bv_unsigned a0 + 12)) 1)
  (RS4 : rng RNG (shadow_addr (bv_unsigned a0 + 16)) 1)
  (M0 : mrd rsegs m0 (wa (shadow_addr (bv_unsigned a0))) = Some k0)
  (M1 : mrd rsegs m0 (wa (shadow_addr (bv_unsigned a0 + 4))) = Some k1)
  (M2 : mrd rsegs m0 (wa (shadow_addr (bv_unsigned a0 + 8))) = Some k2)
  (M3 : mrd rsegs m0 (wa (shadow_addr (bv_unsigned a0 + 12))) = Some k3)
  (M4 : mrd rsegs m0 (wa (shadow_addr (bv_unsigned a0 + 16))) = Some k4)
  (OUT0 : outside [(fb, fe); (bv_unsigned a0, bv_unsigned a0 + 20)] (shadow_addr (bv_unsigned a0)))
  (OUT1 : outside [(fb, fe); (bv_unsigned a0, bv_unsigned a0 + 20)] (shadow_addr (bv_unsigned a0 + 4)))
  (OUT2 : outside [(fb, fe); (bv_unsigned a0, bv_unsigned a0 + 20)] (shadow_addr (bv_unsigned a0 + 8)))
  (OUT3 : outside [(fb, fe); (bv_unsigned a0, bv_unsigned a0 + 20)] (shadow_addr (bv_unsigned a0 + 12)))
  (OUT4 : outside [(fb, fe); (bv_unsigned a0, bv_unsigned a0 + 20)] (shadow_addr (bv_unsigned a0 + 16)))
  (C0 : shok k0 (bv_unsigned a0)) (C1 : shok k1 (bv_unsigned a0 + 4)) (C2 : shok k2 (bv_unsigned a0 + 8))
  (C3 : shok k3 (bv_unsigned a0 + 12)) (C4' : shok k4 (bv_unsigned a0 + 16)).

(* the five fields as one-field cells, the frame (fb .. fb + 16, ra saved at fb + 8), the stack below it, and the
   footprint of the run so far *)
Definition hinv (m : word -> option byte) (y0 y1 y2 y3 y4 : Z) : Prop :=
  rw_cells rsegs m (bv_unsigned a0) [C4 (Z_to_bv 64 y0)] /\
  rw_cells rsegs m (bv_unsigned a0 + 4) [C4 (Z_to_bv 64 y1)] /\
  rw_cells rsegs m (bv_unsigned a0 + 8) [C4 (Z_to_bv 64 y2)] /\
  rw_cells rsegs m (bv_unsigned a0 + 12) [C4 (Z_to_bv 64 y3)] /\
  rw_cells rsegs m (bv_unsigned a0 + 16) [C4 (Z_to_bv 64 y4)] /\
  rw_cells rsegs m fb [CB 8 jk; C8 ra] /\ stk rsegs m lo fb /\
  munch [(fb, fe); (bv_unsigned a0, bv_unsigned a0 + 20)] m0 m /\ wmono rsegs m0 m.

(* a join point: the field now holds [v], which is the model's [f] on this path *)
Local Ltac hv := unfold hinv; repeat (split; [eassumption|]); eassumption.
Local Ltac join K v f := replace f with v in K by mcase; eapply K; try eassumption; hv.

(* 0x7fd58-0x7fd8c: prefill_ms; 0 < x < 1001 skips the store *)
Lemma seg_pf : forall m (r2 r3 r5 r6 r7 rt : word) y0 y1 y2 y3 y4,
  -2^31 <= y0 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (r2' r3' r5' : word), hinv m' (PW.f_pf y0) y1 y2 y3 y4 ->
     evtF rsegs RNG Q (ST 0x7fd90 m' a0 (Z_to_bv 64 mm) r2' r3' (Z_to_bv 64 2147450880) r5' r6 r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fd58 m a0 (Z_to_bv 64 mm) r2 r3 (Z_to_bv 64 2147450880) r5 r6 r7 rt).
Proof.
  intros m r2 r3 r5 r6 r7 rt y0 y1 y2 y3 y4 R (CH0 & CH1 & CH2 & CH3 & CH4 & FR & SK & MU & WM) K.
  pose proof (u64_range a0) as Ra0.
  step. step. shprep (bv_unsigned a0) h U.
  shstep h U OUT0 M0 RS0.
  ckapp ck_7fd64 (bv_unsigned a0) C0 v.
  step. rewrite (PW.sx32_int y0) by lia.
  step. br 0 y0 P.
  - step. step. br y0 1001 P2.
    + join K y0 (PW.f_pf y0).
    + step. step. shstep h U OUT0 M0 RS0.
      ckapp ck_7fd88 (bv_unsigned a0) C0 v'.
      step. join K 1000 (PW.f_pf y0).
  - step. shstep h U OUT0 M0 RS0.
    ckapp ck_7fd88 (bv_unsigned a0) C0 v'.
    step. join K 1 (PW.f_pf y0).
Qed.

(* 0x7fd90-0x7fdc8: adapt_min_ms; a2 keeps the field's address and a5 its shadow address for adapt_max_ms *)
Lemma seg_mn : forall m (r2 r3 r5 r6 r7 rt : word) y0 y1 y2 y3 y4,
  -2^31 <= y1 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (h1 r3' r6' r7' : word), bv_unsigned h1 = shadow_addr (bv_unsigned a0 + 4) ->
     hinv m' y0 (PW.f_mn y1) y2 y3 y4 ->
     evtF rsegs RNG Q (ST 0x7fdcc m' a0 (Z_to_bv 64 mm) (Z_to_bv 64 (bv_unsigned a0 + 4)) r3'
                         (Z_to_bv 64 2147450880) h1 r6' r7' rt)) ->
  evtF rsegs RNG Q (ST 0x7fd90 m a0 (Z_to_bv 64 mm) r2 r3 (Z_to_bv 64 2147450880) r5 r6 r7 rt).
Proof.
  intros m r2 r3 r5 r6 r7 rt y0 y1 y2 y3 y4 R (CH0 & CH1 & CH2 & CH3 & CH4 & FR & SK & MU & WM) K.
  pose proof (u64_range a0) as Ra0.
  step. step. step. shprep (bv_unsigned a0 + 4) h U.
  shstep h U OUT1 M1 RS1.
  ckapp ck_7fda0 (bv_unsigned a0 + 4) C1 v.
  step. rewrite (PW.sx32_int y1) by lia.
  step. br 0 y1 P.
  - step. step. br y1 1001 P2.
    + join K y1 (PW.f_mn y1).
    + step. step. shstep h U OUT1 M1 RS1.
      ckapp ck_7fdc4 (bv_unsigned a0 + 4) C1 v'.
      step. join K 1000 (PW.f_mn y1).
  - step. shstep h U OUT1 M1 RS1.
    ckapp ck_7fdc4 (bv_unsigned a0 + 4) C1 v'.
    step. join K 1 (PW.f_mn y1).
Qed.

(* 0x7fdcc-0x7fdf8: adapt_max_ms against 1000; x < 1001 skips the store *)
Lemma seg_mx1 : forall m (h1 r3 r6 r7 rt : word) y0 y1 y2 y3 y4,
  -2^31 <= y2 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (h2 r7' rt' : word), bv_unsigned h2 = shadow_addr (bv_unsigned a0 + 8) ->
     hinv m' y0 y1 (mx1 y2) y3 y4 ->
     evtF rsegs RNG Q (ST 0x7fdfc m' a0 (Z_to_bv 64 mm) (Z_to_bv 64 (bv_unsigned a0 + 4))
                         (Z_to_bv 64 (bv_unsigned a0 + 8)) (Z_to_bv 64 2147450880) h1 h2 r7' rt')) ->
  evtF rsegs RNG Q (ST 0x7fdcc m a0 (Z_to_bv 64 mm) (Z_to_bv 64 (bv_unsigned a0 + 4)) r3
                      (Z_to_bv 64 2147450880) h1 r6 r7 rt).
Proof.
  intros m h1 r3 r6 r7 rt y0 y1 y2 y3 y4 R (CH0 & CH1 & CH2 & CH3 & CH4 & FR & SK & MU & WM) K.
  pose proof (u64_range a0) as Ra0.
  step. step. step. shprep (bv_unsigned a0 + 8) h U.
  shstep h U OUT2 M2 RS2.
  ckapp ck_7fddc (bv_unsigned a0 + 8) C2 v.
  step. rewrite (PW.sx32_int y2) by lia.
  step. step. br y2 1001 P.
  - join K y2 (mx1 y2).
  - shstep h U OUT2 M2 RS2.
    ckapp ck_7fdf0 (bv_unsigned a0 + 8) C2 v'.
    step. step. join K 1000 (mx1 y2).
Qed.

(* 0x7fdfc-0x7fe20: adapt_max_ms against adapt_min_ms, both read back; x >= adapt_min_ms skips the store *)
Lemma seg_mx2 : forall m (h1 h2 r7 rt : word) y0 y1 z y3 y4,
  bv_unsigned h1 = shadow_addr (bv_unsigned a0 + 4) -> bv_unsigned h2 = shadow_addr (bv_unsigned a0 + 8) ->
  -2^31 <= y1 < 2^31 -> -2^31 <= z < 2^31 -> hinv m y0 y1 z y3 y4 ->
  (forall m' (r2' r3' r5' r6' r7' rt' : word), hinv m' y0 y1 (if z <? y1 then y1 else z) y3 y4 ->
     evtF rsegs RNG Q (ST 0x7fe24 m' a0 (Z_to_bv 64 mm) r2' r3' (Z_to_bv 64 2147450880) r5' r6' r7' rt')) ->
  evtF rsegs RNG Q (ST 0x7fdfc m a0 (Z_to_bv 64 mm) (Z_to_bv 64 (bv_unsigned a0 + 4))
                      (Z_to_bv 64 (bv_unsigned a0 + 8)) (Z_to_bv 64 2147450880) h1 h2 r7 rt).
Proof.
  intros m h1 h2 r7 rt y0 y1 z y3 y4 U1 U2 R1 Rz (CH0 & CH1 & CH2 & CH3 & CH4 & FR & SK & MU & WM) K.
  pose proof (u64_range a0) as Ra0.
  shstep h2 U2 OUT2 M2 RS2.
  ckapp ck_7fe00 (bv_unsigned a0 + 8) C2 v.
  shstep h1 U1 OUT1 M1 RS1.
  step. rewrite (PW.sx32_int z) by lia.
  ckapp ck_7fe0c (bv_unsigned a0 + 4) C1 v'.
  step. rewrite (PW.sx32_int y1) by lia.
  step. br z y1 P.
  - shstep h2 U2 OUT2 M2 RS2.
    ckapp ck_7fe1c (bv_unsigned a0 + 8) C2 v''.
    step. join K y1 (if z <? y1 then y1 else z).
  - join K z (if z <? y1 then y1 else z).
Qed.

(* 0x7fe24-0x7fe48: adapt_margin against 0; x >= 0 skips the store *)
Lemma seg_mg1 : forall m (r2 r3 r5 r6 r7 rt : word) y0 y1 y2 y3 y4,
  -2^31 <= y3 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (h3 r5' r6' : word), bv_unsigned h3 = shadow_addr (bv_unsigned a0 + 12) ->
     hinv m' y0 y1 y2 (mg1 y3) y4 ->
     evtF rsegs RNG Q (ST 0x7fe4c m' a0 (Z_to_bv 64 mm) (Z_to_bv 64 (bv_unsigned a0 + 12)) h3
                         (Z_to_bv 64 2147450880) r5' r6' r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe24 m a0 (Z_to_bv 64 mm) r2 r3 (Z_to_bv 64 2147450880) r5 r6 r7 rt).
Proof.
  intros m r2 r3 r5 r6 r7 rt y0 y1 y2 y3 y4 R (CH0 & CH1 & CH2 & CH3 & CH4 & FR & SK & MU & WM) K.
  pose proof (u64_range a0) as Ra0.
  step. step. step. shprep (bv_unsigned a0 + 12) h U.
  shstep h U OUT3 M3 RS3.
  ckapp ck_7fe34 (bv_unsigned a0 + 12) C3 v.
  step. rewrite (PW.sx32_int y3) by lia.
  step. br y3 0 P.
  - shstep h U OUT3 M3 RS3.
    ckapp ck_7fe44 (bv_unsigned a0 + 12) C3 v'.
    step. join K 0 (mg1 y3).
  - join K y3 (mg1 y3).
Qed.

(* 0x7fe4c-0x7fe64: adapt_margin against margin_max = a1; x <= margin_max skips the store *)
Lemma seg_mg2 : forall m (h3 r5 r6 r7 rt : word) y0 y1 y2 z y4,
  bv_unsigned h3 = shadow_addr (bv_unsigned a0 + 12) -> -2^31 <= z < 2^31 -> hinv m y0 y1 y2 z y4 ->
  (forall m' (r2' r3' r5' r6' : word), hinv m' y0 y1 y2 (if mm <? z then mm else z) y4 ->
     evtF rsegs RNG Q (ST 0x7fe68 m' a0 (Z_to_bv 64 mm) r2' r3' (Z_to_bv 64 2147450880) r5' r6' r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe4c m a0 (Z_to_bv 64 mm) (Z_to_bv 64 (bv_unsigned a0 + 12)) h3
                      (Z_to_bv 64 2147450880) r5 r6 r7 rt).
Proof.
  intros m h3 r5 r6 r7 rt y0 y1 y2 z y4 U3 Rz (CH0 & CH1 & CH2 & CH3 & CH4 & FR & SK & MU & WM) K.
  pose proof (u64_range a0) as Ra0.
  shstep h3 U3 OUT3 M3 RS3.
  ckapp ck_7fe50 (bv_unsigned a0 + 12) C3 v.
  step. rewrite (PW.sx32_int z) by lia.
  step. br mm z P.
  - shstep h3 U3 OUT3 M3 RS3.
    ckapp ck_7fe60 (bv_unsigned a0 + 12) C3 v'.
    step. join K mm (if mm <? z then mm else z).
  - join K z (if mm <? z then mm else z).
Qed.

(* 0x7fe68-0x7fea4: servo_clamp_ppm against [0, 50000]; 0 <= x < 50001 skips the store *)
Lemma seg_sv : forall m (r1 r2 r3 r5 r6 r7 rt : word) y0 y1 y2 y3 y4,
  -2^31 <= y4 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (r1' r2' r3' r4' : word), hinv m' y0 y1 y2 y3 (PW.f_sv y4) ->
     evtF rsegs RNG Q (ST 0x7fea8 m' (Z_to_bv 64 (bv_unsigned a0 + 16)) r1' r2' r3' r4' r5 r6 r7 rt)) ->
  evtF rsegs RNG Q (ST 0x7fe68 m a0 r1 r2 r3 (Z_to_bv 64 2147450880) r5 r6 r7 rt).
Proof.
  intros m r1 r2 r3 r5 r6 r7 rt y0 y1 y2 y3 y4 R (CH0 & CH1 & CH2 & CH3 & CH4 & FR & SK & MU & WM) K.
  pose proof (u64_range a0) as Ra0.
  step. step. step. shprep (bv_unsigned a0 + 16) h U.
  shstep h U OUT4 M4 RS4.
  ckapp ck_7fe78 (bv_unsigned a0 + 16) C4' v.
  step. rewrite (PW.sx32_int y4) by lia.
  step. br y4 0 P.
  - step. shstep h U OUT4 M4 RS4.
    ckapp ck_7fea0 (bv_unsigned a0 + 16) C4' v'.
    step. join K 0 (PW.f_sv y4).
  - step. step. step. br y4 50001 P2.
    + join K y4 (PW.f_sv y4).
    + step. step. shstep h U OUT4 M4 RS4.
      ckapp ck_7fea0 (bv_unsigned a0 + 16) C4' v'.
      step. join K 50000 (PW.f_sv y4).
Qed.

(* 0x7fd58-0x7fea4: the five fields, from p's to rp_hot_clamp_m p mm's *)
Lemma body : forall m (r2 r3 r5 r6 r7 rt : word) (p : rp_hot),
  PHC.hot_int p ->
  hinv m (prefill_ms p) (adapt_min_ms p) (adapt_max_ms p) (adapt_margin p) (servo_clamp_ppm p) ->
  (forall m' (r0' r1' r2' r3' r4' r5' r6' r7' rt' : word),
     hinv m' (prefill_ms (rp_hot_clamp_m p mm)) (adapt_min_ms (rp_hot_clamp_m p mm))
       (adapt_max_ms (rp_hot_clamp_m p mm)) (adapt_margin (rp_hot_clamp_m p mm))
       (servo_clamp_ppm (rp_hot_clamp_m p mm)) ->
     evtF rsegs RNG Q (ST 0x7fea8 m' r0' r1' r2' r3' r4' r5' r6' r7' rt')) ->
  evtF rsegs RNG Q (ST 0x7fd58 m a0 (Z_to_bv 64 mm) r2 r3 (Z_to_bv 64 2147450880) r5 r6 r7 rt).
Proof.
  intros m r2 r3 r5 r6 r7 rt p HI H0 K.
  unfold PHC.hot_int, INT_MIN, INT_MAX in HI. destruct HI as (R0 & R1 & R2 & R3 & R4).
  rewrite PW.model_split in K. cbn [prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm] in K.
  pose proof (PW.f_mn_range (adapt_min_ms p)) as RMN.
  pose proof (mx1_range (adapt_max_ms p) ltac:(lia)) as RMX.
  pose proof (mg1_range (adapt_margin p) ltac:(lia)) as RMG.
  refine (seg_pf _ _ _ _ _ _ _ _ _ _ _ _ _ H0 _); [lia|]. intros m1 r2a r3a r5a H1.
  refine (seg_mn _ _ _ _ _ _ _ _ _ _ _ _ _ H1 _); [lia|]. intros m2 h1 r3b r6b r7b U1 H2.
  refine (seg_mx1 _ _ _ _ _ _ _ _ _ _ _ _ H2 _); [lia|]. intros m3 h2 r7c rtc U2 H3.
  refine (seg_mx2 _ _ _ _ _ _ _ _ _ _ U1 U2 _ RMX H3 _); [lia|]. intros m4 r2d r3d r5d r6d r7d rtd H4.
  refine (seg_mg1 _ _ _ _ _ _ _ _ _ _ _ _ _ H4 _); [lia|]. intros m5 h3 r5e r6e U3 H5.
  refine (seg_mg2 _ _ _ _ _ _ _ _ _ _ _ U3 _ H5 _); [lia|]. intros m6 r2f r3f r5f r6f H6.
  refine (seg_sv _ _ _ _ _ _ _ _ _ _ _ _ _ _ H6 _); [lia|]. intros m7 r1g r2g r3g r4g H7.
  apply K. exact H7.
Qed.

End Walk.

(* ---- the contract ---- *)

Theorem rp_hot_clamp_holds_F : rp_hot_clamp_contract_F.
Proof.
  unfold rp_hot_clamp_contract_F, RP_HOT_CLAMP, RP_HOT_CLAMP_FRAME, PHC.RP_HOT_SIZE.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p mm lo
    HNZ HAL HI HM HA1 CH ST HLO HOFF APS1 APS2 HAC HOG HOC HADDR RFR RGOT RCELL RBUF RSH.
  assert (E1 : a1 = Z_to_bv 64 mm) by (rewrite <- HA1; symmetry; apply Z_to_bv_lit_self). subst a1.
  unfold INT_MAX in HM.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0.
  (* the struct, one cell per field *)
  unfold PHC.hot_cells, PHC.c4z in CH. apply rw5_split in CH. destruct CH as (CH0 & CH1 & CH2 & CH3 & CH4).
  (* each field's shadow byte passes its check; no shadow byte lies in the frame or the struct *)
  pose proof HADDR as (HP0 & _ & HPE & HPB).
  destruct (HPB 0 ltac:(lia)) as (AP0 & _). destruct (HPB 19 ltac:(lia)) as (AP19 & _).
  rewrite Z.add_0_r in AP0.
  destruct (addr_four m _ _ (bv_unsigned a0) HADDR ltac:(lia) ltac:(lia)) as (k0 & M0 & C0).
  destruct (addr_four m _ _ (bv_unsigned a0 + 4) HADDR ltac:(lia) ltac:(lia)) as (k1 & M1 & C1).
  destruct (addr_four m _ _ (bv_unsigned a0 + 8) HADDR ltac:(lia) ltac:(lia)) as (k2 & M2 & C2).
  destruct (addr_four m _ _ (bv_unsigned a0 + 12) HADDR ltac:(lia) ltac:(lia)) as (k3 & M3 & C3).
  destruct (addr_four m _ _ (bv_unsigned a0 + 16) HADDR ltac:(lia) ltac:(lia)) as (k4 & M4 & C4').
  change (bv_unsigned a0 / 8 + ASAN_K) with (shadow_addr (bv_unsigned a0)) in M0.
  change ((bv_unsigned a0 + 4) / 8 + ASAN_K) with (shadow_addr (bv_unsigned a0 + 4)) in M1.
  change ((bv_unsigned a0 + 8) / 8 + ASAN_K) with (shadow_addr (bv_unsigned a0 + 8)) in M2.
  change ((bv_unsigned a0 + 12) / 8 + ASAN_K) with (shadow_addr (bv_unsigned a0 + 12)) in M3.
  change ((bv_unsigned a0 + 16) / 8 + ASAN_K) with (shadow_addr (bv_unsigned a0 + 16)) in M4.
  change (shok k0 (bv_unsigned a0)) in C0. change (shok k1 (bv_unsigned a0 + 4)) in C1.
  change (shok k2 (bv_unsigned a0 + 8)) in C2. change (shok k3 (bv_unsigned a0 + 12)) in C3.
  change (shok k4 (bv_unsigned a0 + 16)) in C4'.
  pose proof (rng_one_shadow RNG _ 20 (bv_unsigned a0) RSH ltac:(lia)) as RS0.
  pose proof (rng_one_shadow RNG _ 20 (bv_unsigned a0 + 4) RSH ltac:(lia)) as RS1.
  pose proof (rng_one_shadow RNG _ 20 (bv_unsigned a0 + 8) RSH ltac:(lia)) as RS2.
  pose proof (rng_one_shadow RNG _ 20 (bv_unsigned a0 + 12) RSH ltac:(lia)) as RS3.
  pose proof (rng_one_shadow RNG _ 20 (bv_unsigned a0 + 16) RSH ltac:(lia)) as RS4.
  clear RSH.
  unfold off_stk in HOFF, HOG, HOC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HAC as (CK & GCK & _).
  unfold GOT_CELL_K, CELL_K in HOG, HOC, CK, GCK, RGOT, RCELL. unfold ASAN_K in CK.
  carve_frame 16%nat ST.
  assert (OUT : forall i, 0 <= i <= 19 ->
    outside [(bv_unsigned sp + -16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 20)]
      (shadow_addr (bv_unsigned a0 + i))).
  { intros i Hi. cbn [outside]. split; [|split; [|exact I]].
    - apply shadow_frame; [exact APS1 | exact APS2 |].
      destruct (HPB i ltac:(lia)) as (APi & _). exact APi.
    - apply shadow_disj; assumption. }
  pose proof (OUT 0 ltac:(lia)) as OUT0. rewrite Z.add_0_r in OUT0.
  pose proof (OUT 4 ltac:(lia)) as OUT1. pose proof (OUT 8 ltac:(lia)) as OUT2.
  pose proof (OUT 12 ltac:(lia)) as OUT3. pose proof (OUT 16 ltac:(lia)) as OUT4.
  clear OUT.
  (* addi sp, sp, -16; sd ra, 8(sp) *)
  step. step.
  (* the UBSan checks of p: `beqz a0` and `andi a2, a0, 3` / `bnez a2` fall through, by HNZ and HAL *)
  step. if_false.
  assert (L3 : Z.land (bv_unsigned a0) 3 = 0)
    by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact HAL).
  step. rewrite ?L3.
  step. if_false.
  (* the shadow base through its GOT word *)
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  step. step. step.
  clear RDG RDS CK GCK.
  lazymatch goal with FR : rw_cells _ _ _ [CB 8 ?j; C8 ra] |- _ => set (jk := j) in FR end.
  eapply body with (jk := jk) (k0 := k0) (k1 := k1) (k2 := k2) (k3 := k3) (k4 := k4) (m0 := m) (lo := lo)
    (fb := bv_unsigned sp + -16) (fe := bv_unsigned sp) (p := p).
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- context [hinv] => unfold hinv; repeat (split; [eassumption|]); eassumption
       | _ => first [ assumption | unfold APPMEM_END in HPE; lia ]
       end.
  intros m' r0' r1' r2' r3' r4' r5' r6' r7' rt' (CH0' & CH1' & CH2' & CH3' & CH4' & FR' & ST' & MU' & WM').
  (* ld ra, 8(sp); addi sp, sp, 16; ret *)
  step. step. step.
  apply evtF_done.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|].
  split; [release_frame FR' ST' (bv_unsigned sp); exact ST'|].
  unfold PHC.hot_cells, PHC.c4z. apply rw5_merge; assumption.
Qed.
