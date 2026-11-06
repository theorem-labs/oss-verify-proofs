(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the walk of rp_hot_clamp (src/repace_conf.c), the plain
   image's leaf at 0x1309c (45 instructions, no call, no frame), against lib/Prog/rp_hot_clamp_c.v.
   The walk has five segments, one per int field of struct rp_hot, each a lemma in continuation style (as
   libreac/fuzz_decode's released check_braid.v `body`): it ends at the next field's `lw`, or at `ret`, with the
   field equal to the matching `let` of lib/Spec/UciModel.v's rp_hot_clamp_m. When the field already holds its
   clamped value the binary skips the `sw`, and the cell is left as it was. The function has no abort site. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require Import rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.

Lemma signed_lit_small : forall x, -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.leb_spec 0 x).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec x (2^63)); lia.
  - rewrite <- (Z.mod_unique x (2^64) (-1) (x + 2^64)) by lia.
    destruct (Z.ltb_spec (x + 2^64) (2^63)); lia.
Qed.

Lemma sx32_int : forall x, -2^31 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32).
  change (2^32 `div` 2) with (2^31).
  destruct (Z.leb_spec 0 x).
  - rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique x (2^64) (-1) (x + 2^64)) by lia.
    rewrite <- (Z.mod_unique (x + 2^64 + 2^31) (2^32) (2^32) (x + 2^31)) by lia. lia.
Qed.

Lemma lts_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.

Lemma ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Definition f_pf (x : Z) : Z :=
  let pf1 := if x <? RP_PREFILL_MS_MIN then RP_PREFILL_MS_MIN else x in
  if RP_PREFILL_MS_MAX <? pf1 then RP_PREFILL_MS_MAX else pf1.
Definition f_mn (x : Z) : Z :=
  let mn1 := if x <? RP_ADAPT_MS_MIN then RP_ADAPT_MS_MIN else x in
  if RP_ADAPT_MS_MAX <? mn1 then RP_ADAPT_MS_MAX else mn1.
Definition f_mx (x mn : Z) : Z :=
  let mx1 := if RP_ADAPT_MS_MAX <? x then RP_ADAPT_MS_MAX else x in
  if mx1 <? mn then mn else mx1.
Definition f_mg (x mm : Z) : Z :=
  let mg1 := if x <? 0 then 0 else x in
  if mm <? mg1 then mm else mg1.
Definition f_sv (x : Z) : Z :=
  let sv1 := if x <? 0 then 0 else x in
  if RP_SERVO_CLAMP_PPM_MAX <? sv1 then RP_SERVO_CLAMP_PPM_MAX else sv1.

Lemma model_split : forall p mm, rp_hot_clamp_m p mm =
  RpHot (f_pf (prefill_ms p)) (f_mn (adapt_min_ms p)) (f_mx (adapt_max_ms p) (f_mn (adapt_min_ms p)))
        (f_mg (adapt_margin p) mm) (f_sv (servo_clamp_ppm p)).
Proof. reflexivity. Qed.

(* split the innermost comparison first and reduce, so no hypothesis carries an [if] *)
Local Ltac mcase :=
  unfold f_pf, f_mn, f_mx, f_mg, f_sv, RP_PREFILL_MS_MIN, RP_PREFILL_MS_MAX, RP_ADAPT_MS_MIN, RP_ADAPT_MS_MAX,
    RP_SERVO_CLAMP_PPM_MAX; cbv zeta;
  repeat (match goal with
          | |- context [Z.ltb ?a ?b] =>
              lazymatch a with context [Z.ltb _ _] => fail | _ =>
              lazymatch b with context [Z.ltb _ _] => fail | _ => destruct (Z.ltb_spec a b) end end
          end; cbv beta iota);
  lia.

Local Ltac zc := rewrite ?lts_lit, ?ltu_lit by lia.

(* the kit's addr_eq_tac proves [wa e = x] for a register base [x] in one orientation only; a [sw] at offset 0 of
   the register a0 needs the other one (Step.v's solve_store [replace ... by (f_equal; addr_eq_tac)]) *)
Local Ltac addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Local Ltac hv := split; [eassumption|]; split; [eassumption|]; split; eassumption.
(* the pc after a conditional branch, with the condition stated over Z and split on [a <? b] *)
Local Ltac br a b P := zc; destruct (Z.ltb_spec a b) as [P|P]; cbv beta iota delta [negb].
(* a join point: the field now holds [v], which is the model's [f] on this path *)
Local Ltac join K v f := replace f with v in K by mcase; eapply K; hv.

(* sgtz / negw / and at 0x13108-0x13110: adapt_margin < 0 ? 0 : adapt_margin *)
Lemma sgtz_and : forall g, -2^31 <= g < 2^31 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 g))))))
                     (bv_unsigned (Z_to_bv 64 g)))
  = Z_to_bv 64 (if g <? 0 then 0 else g).
Proof.
  intros g Hg. unfold v_slt, c_lts. rewrite lts_lit by lia.
  destruct (Z.ltb_spec 0 g); destruct (Z.ltb_spec g 0); try lia.
  - replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 1))))) with (Z.ones 64)
      by (vm_compute; reflexivity).
    rewrite unsigned_lit by lia. rewrite Z.land_comm, Z.land_ones by lia. f_equal. apply Z.mod_small. lia.
  - replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 0))))) with 0
      by (vm_compute; reflexivity).
    reflexivity.
  - replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 0))))) with 0
      by (vm_compute; reflexivity).
    replace g with 0 by lia. reflexivity.
Qed.

Section Walk.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (mm : Z) (Q : machine_state -> Prop).

Local Abbreviation ST pc m a1 a2 a3 a4 a5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition hinv (m : word -> option byte) (y0 y1 y2 y3 y4 : Z) : Prop :=
  rw_cells rsegs m (bv_unsigned a0)
    [C4 (Z_to_bv 64 y0); C4 (Z_to_bv 64 y1); C4 (Z_to_bv 64 y2); C4 (Z_to_bv 64 y3); C4 (Z_to_bv 64 y4)] /\
  mem_inv rsegs m /\ munch [(bv_unsigned a0, bv_unsigned a0 + 20)] m0 m /\ wmono rsegs m0 m.

(* 0x1309c-0x130b8: prefill_ms; 0 < x < 1001 skips the sw *)
Lemma seg_pf : forall m (a2 a3 a4 a5 : word) y0 y1 y2 y3 y4,
  -2^31 <= y0 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (a2' a3' : word), hinv m' (f_pf y0) y1 y2 y3 y4 ->
     evt rsegs Q (ST 0x130bc m' (Z_to_bv 64 mm) a2' a3' a4 a5)) ->
  evt rsegs Q (ST 0x1309c m (Z_to_bv 64 mm) a2 a3 a4 a5).
Proof.
  intros m a2 a3 a4 a5 y0 y1 y2 y3 y4 R (CH & MI & MU & WM) K.
  step. rewrite (sx32_int y0) by lia.
  step. br 0 y0 P.
  - do 2 step. br y0 1001 P2.
    + join K y0 (f_pf y0).
    + do 3 step. join K 1000 (f_pf y0).
  - do 2 step. join K 1 (f_pf y0).
Qed.

(* 0x130bc-0x130d8: adapt_min_ms; a2 keeps the clamped value for adapt_max_ms's lower bound *)
Lemma seg_mn : forall m (a2 a3 a4 a5 : word) y0 y1 y2 y3 y4,
  -2^31 <= y1 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (a3' : word), hinv m' y0 (f_mn y1) y2 y3 y4 ->
     evt rsegs Q (ST 0x130dc m' (Z_to_bv 64 mm) (Z_to_bv 64 (f_mn y1)) a3' a4 a5)) ->
  evt rsegs Q (ST 0x130bc m (Z_to_bv 64 mm) a2 a3 a4 a5).
Proof.
  intros m a2 a3 a4 a5 y0 y1 y2 y3 y4 R (CH & MI & MU & WM) K.
  step. rewrite (sx32_int y1) by lia.
  step. br 0 y1 P.
  - do 2 step. br y1 1001 P2.
    + join K y1 (f_mn y1).
    + do 3 step. join K 1000 (f_mn y1).
  - do 2 step. join K 1 (f_mn y1).
Qed.

(* 0x130dc-0x13100: adapt_max_ms against [a2, 1000]; y1 <= x <= 1000 skips the sw *)
Lemma seg_mx : forall m (a3 a4 a5 : word) y0 y1 y2 y3 y4,
  1 <= y1 <= 1000 -> -2^31 <= y2 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (a3' a4' a5' : word), hinv m' y0 y1 (f_mx y2 y1) y3 y4 ->
     evt rsegs Q (ST 0x13104 m' (Z_to_bv 64 mm) (Z_to_bv 64 y1) a3' a4' a5')) ->
  evt rsegs Q (ST 0x130dc m (Z_to_bv 64 mm) (Z_to_bv 64 y1) a3 a4 a5).
Proof.
  intros m a3 a4 a5 y0 y1 y2 y3 y4 R1 R (CH & MI & MU & WM) K.
  step. rewrite (sx32_int y2) by lia.
  do 3 step. br y2 1000 P.
  - step. br 1000 y2 P2; [exfalso; lia|].
    step. br y2 y1 P3.
    + step. br y1 y2 P4; [exfalso; lia|].
      do 2 step. join K y1 (f_mx y2 y1).
    + join K y2 (f_mx y2 y1).
  - do 2 step. br 1000 y2 P2.
    + step. br y1 1000 P3.
      * step. join K 1000 (f_mx y2 y1).
      * do 2 step. join K y1 (f_mx y2 y1).
    + step. br 1000 y1 P3; [exfalso; lia|].
      join K y2 (f_mx y2 y1).
Qed.

(* 0x13104-0x13124: adapt_margin against [0, margin_max = a1]; 0 <= x <= margin_max skips the sw *)
Lemma seg_mg : forall m (a2 a3 a4 a5 : word) y0 y1 y2 y3 y4,
  0 <= mm < 2^31 -> -2^31 <= y3 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (a2' a3' : word), hinv m' y0 y1 y2 (f_mg y3 mm) y4 ->
     evt rsegs Q (ST 0x13128 m' (Z_to_bv 64 mm) a2' a3' a4 a5)) ->
  evt rsegs Q (ST 0x13104 m (Z_to_bv 64 mm) a2 a3 a4 a5).
Proof.
  intros m a2 a3 a4 a5 y0 y1 y2 y3 y4 RM R (CH & MI & MU & WM) K.
  step. rewrite (sx32_int y3) by lia.
  do 3 step. rewrite (sgtz_and y3) by lia.
  step. br y3 0 P.
  - step. br 0 mm P2.
    + step. join K 0 (f_mg y3 mm).
    + do 2 step. join K mm (f_mg y3 mm).
  - step. br mm y3 P2.
    + step. br y3 mm P3; [exfalso; lia|].
      do 2 step. join K mm (f_mg y3 mm).
    + join K y3 (f_mg y3 mm).
Qed.

(* 0x13128-0x13148: servo_clamp_ppm against [0, 50000]; 0 <= x < 50001 skips the sw and reaches ret *)
Lemma seg_sv : forall m (a1 a2 a3 a4 a5 : word) y0 y1 y2 y3 y4,
  -2^31 <= y4 < 2^31 -> hinv m y0 y1 y2 y3 y4 ->
  (forall m' (a1' a2' a3' : word), hinv m' y0 y1 y2 y3 (f_sv y4) ->
     evt rsegs Q (ST 0x1314c m' a1' a2' a3' a4 a5)) ->
  evt rsegs Q (ST 0x13128 m a1 a2 a3 a4 a5).
Proof.
  intros m a1 a2 a3 a4 a5 y0 y1 y2 y3 y4 R (CH & MI & MU & WM) K.
  step. rewrite (sx32_int y4) by lia.
  step. br y4 0 P.
  - do 2 step. join K 0 (f_sv y4).
  - do 3 step. br y4 50001 P2.
    + join K y4 (f_sv y4).
    + do 3 step. join K 50000 (f_sv y4).
Qed.

End Walk.

Lemma f_mn_range : forall x, 1 <= f_mn x <= 1000.
Proof. intros x. mcase. Qed.

Theorem rp_hot_clamp_holds : rp_hot_clamp_contract.
Proof.
  unfold rp_hot_clamp_contract, RP_HOT_CLAMP, RP_HOT_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p mm
    HI HM HA1 CH MI.
  assert (E1 : a1 = Z_to_bv 64 mm) by (rewrite <- HA1; symmetry; apply Z_to_bv_lit_self). subst a1.
  unfold hot_int, INT_MIN, INT_MAX in HI. unfold INT_MAX in HM. destruct HI as (R0 & R1 & R2 & R3 & R4).
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 20)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold hot_cells, c4z in CH.
  pose proof (f_mn_range (adapt_min_ms p)) as RMN.
  (* the hinv premise first: it fixes the field values the range premises are about *)
  eapply seg_pf; [| split; [exact CH | split; [exact MI | split; [exact MU | exact WM]]] |]; [lia |].
  intros m1 a2' a3' H1.
  eapply seg_mn; [| exact H1 |]; [lia |].
  intros m2 a3'' H2.
  eapply seg_mx; [| | exact H2 |]; [lia | lia |].
  intros m3 a3''' a4' a5' H3.
  eapply seg_mg; [| | exact H3 |]; [lia | lia |].
  intros m4 a2'' a3'''' H4.
  eapply seg_sv; [| exact H4 |]; [lia |].
  intros m5 a1' a2''' a3''''' (CH5 & MI5 & MU5 & WM5).
  step.
  apply evt_done.
  exists t0, t1, t2, a0, a1', a2''', a3''''', a4', a5', a6, a7, t3, t4, t5, t6, m5.
  split; [reflexivity|]. split; [exact MU5|]. split; [exact WM5|]. split; [exact MI5|].
  rewrite model_split. unfold hot_cells, c4z. cbn [prefill_ms adapt_min_ms adapt_max_ms adapt_margin servo_clamp_ppm].
  exact CH5.
Qed.
