From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Prog Require Import reac_knock_struct.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Prog Require Import reac_knock_init_c reac_knock_heard_c
  reac_knock_step_c memset_c knock_lib LLVMFuzzerTestOneInput_c reac_knock_init reac_knock_heard reac_knock_step.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Lemma iw_succ : forall x, 0 <= x <= 4094 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 (x + 1))) = x + 1.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite (Z.mod_small (x + 1 + 2^31) (2^32)) by lia.
  replace (x + 1 + 2 ^ 31 - 2 ^ 31) with (x + 1) by lia. apply unsigned_lit. lia.
Qed.

Ltac refute_trap T := exfalso; zify_cond T; repeat (rewrite Z.mod_small in T by lia); lia.

Section KnockRun.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z).
Hypothesis LO : lo + 176 <= bv_unsigned sp.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HMI0 : mem_inv rsegs m.
Hypothesis ST0 : stk rsegs m lo (bv_unsigned sp).

Definition saved : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition Qk (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp).

Lemma knock_exit : forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' : word)
                          (m1 : word -> option byte) (cs40 : list cell),
  cells_size cs40 = 40%nat ->
  rw_cells rsegs m1 (bv_unsigned sp + -144) (cs40 ++ saved) ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1 ->
  wmono rsegs m m1 ->
  mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12d04) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
         t3' t4' t5' t6' m1 cs40 HS FR ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  apply rw_cells_app_split in FR. destruct FR as [F40 FS]. rewrite HS in FS.
  replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) in FS by lia.
  unfold saved in FS.
  do 15 zstep.
  assert (FR : rw_cells rsegs m1 (bv_unsigned sp + -144) (cs40 ++ saved)).
  { apply rw_cells_app_join; [exact F40|]. rewrite HS.
    replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) by lia. exact FS. }
  clear F40 FS.
  eapply stk_release in FR; [ | exact ST | lia ].
  rewrite cells_size_app, HS in FR. cbn [saved cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -144 + Z.of_nat 144) with (bv_unsigned sp) in FR by lia.
  clear ST.
  zstep.
  finish.
Qed.

Variables (p : word) (data : list byte).
Hypothesis DJ : bv_unsigned p + Z.of_nat (length data) <= lo \/ bv_unsigned sp <= bv_unsigned p.
Hypothesis HPB : bv_unsigned p + Z.of_nat (length data) < 2 ^ 63.
Hypothesis HPNZ : 0 < Z.of_nat (length data) -> 0 < bv_unsigned p.

Ltac side :=
  first [ eassumption | lia | (left; reflexivity) | (right; reflexivity) | (intros; split; [reflexivity | lia])
        | (intros; reflexivity) | (intros; lia) | (intros; discriminate)
        | (eapply (mem_inv_from_entry m _ lo (bv_unsigned sp) 176); [exact HMI0 | exact ST0 | lia | eassumption])
        | (rewrite unsigned_lit by lia; lia) | (split; assumption) | (split; eassumption)
        | (cbn; lia)
        | (rewrite Z.shiftl_mul_pow2 by lia; rewrite unsigned_lit by lia; lia)
        | (rewrite unsigned_lit by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); rewrite ?Z.shiftl_mul_pow2 by lia; lia) ].

Definition st_of (d h : Z) : Z := if Z.eqb d 1 then 1 else if Z.eqb h 1 then 2 else 0.

Definition loop_ok (fuel : nat) : Prop :=
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x26 t3' t4' t5' t6' : word)
    (now cur rem iw quiet t0w due hns : word) (d h c : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned rem) <= fuel)%nat ->
  1 <= bv_unsigned rem ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  bv_unsigned iw <= 4095 ->
  (d = 0 \/ d = 1) -> (h = 0 \/ h = 1) ->
  bv_unsigned t0w < 2 ^ 63 ->
  (d = 0 -> h = 0 -> quiet = t0w /\ bv_unsigned due = bv_unsigned t0w + 500000000) ->
  (d = 0 -> h = 1 -> hns = quiet) ->
  bv_unsigned quiet <= bv_unsigned now ->
  bv_unsigned now <= 2 ^ 63 + bv_unsigned iw * 2 ^ 23 ->
  rw_cells rsegs m1 (bv_unsigned sp + -144)
    (knock_cells (st_of d h) (Z_to_bv 64 0) t0w due hns d (Z_to_bv 64 0)) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' cur now a0' a1' a2' a3' a4' a5' a6' a7'
             rem iw (Z_to_bv 64 1) (Z_to_bv 64 h) (Z_to_bv 64 4094) (Z_to_bv 64 500000000) (Z_to_bv 64 d)
             (Z_to_bv 64 499999999) x26 quiet t3' t4' t5' t6')
        F (Z_to_bv 64 0x12bf4) fc None m1 (seg_rom rsegs)).

Lemma knock_checks : forall (fuel : nat), loop_ok fuel ->
  forall (ra' t0' t1' t2' x26 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (now cur' rem' iw quiet t0w due hns : word) (d h c' : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned rem') <= fuel)%nat ->
  bv_unsigned cur' = bv_unsigned p + c' -> 0 <= c' -> c' + bv_unsigned rem' = Z.of_nat (length data) ->
  bv_unsigned iw <= 4095 ->
  (d = 0 \/ d = 1) -> (h = 0 \/ h = 1) ->
  bv_unsigned t0w < 2 ^ 63 ->
  (d = 0 -> h = 0 -> quiet = t0w /\ bv_unsigned due = bv_unsigned t0w + 500000000) ->
  (d = 0 -> h = 1 -> hns = quiet) ->
  bv_unsigned quiet <= bv_unsigned now ->
  bv_unsigned now <= 2 ^ 63 + (bv_unsigned iw + 1) * 2 ^ 23 ->
  rw_cells rsegs m1 (bv_unsigned sp + -144)
    (knock_cells (st_of d h) (Z_to_bv 64 0) t0w due hns d (Z_to_bv 64 0)) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' cur' now a0' a1' a2' a3' a4' a5' a6' a7'
             rem' iw (Z_to_bv 64 1) (Z_to_bv 64 h) (Z_to_bv 64 4094) (Z_to_bv 64 500000000) (Z_to_bv 64 d)
             (Z_to_bv 64 499999999) x26 quiet t3' t4' t5' t6')
        F (Z_to_bv 64 0x12cd0) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' x26 a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    now cur' rem' iw quiet t0w due hns d h c' m1 HF HC HC0 HCN HI HD HH HT0 KI0 KI1 HQ HNOW HS HSV HDATA ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof ST as [Hlo _].
  pose proof (bv_unsigned_in_range 64 iw) as Riw.
  pose proof (bv_unsigned_in_range 64 rem') as Rrem.
  assert (CELLS : forall m2, rw_cells rsegs m2 (bv_unsigned sp + -144)
                     (knock_cells (st_of d h) (Z_to_bv 64 0) t0w due hns d (Z_to_bv 64 0)) ->
                   rw_cells rsegs m2 (bv_unsigned sp + -104) saved ->
                   rw_cells rsegs m2 (bv_unsigned sp + -144)
                     (knock_cells (st_of d h) (Z_to_bv 64 0) t0w due hns d (Z_to_bv 64 0) ++ saved)).
  { intros m2 H1 H2. apply rw_cells_app_join; [exact H1|]. cbn [knock_cells cells_size csize Nat.add].
    replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) by lia. exact H2. }
  destruct HD as [-> | ->]; destruct HH as [-> | ->]; unfold st_of in *; cbn [Z.eqb Pos.eqb] in *;
  unfold knock_cells in HS;
  zstep; zstep; zstep; if_false; zstep;
  first [ if_true; zstep; zstep | if_false; zstep; zstep ];
  zstep; zstep; if_false; zstep.
  all: if_cases G4;
    [ eapply knock_exit; [ | apply CELLS; [exact HS | exact HSV] | exact ST | exact MU | exact WM | exact HMI ];
      reflexivity
    | zify_cond G4; zstep; zstep; if_cases G5;
      [ zify_cond G5; eapply LOOP; [ | | exact HC | exact HC0 | exact HCN | | | | exact HT0 | | | exact HQ | |
          exact HS | exact HSV | exact HDATA | exact ST | exact MU | exact WM | exact HMI ]
      | eapply knock_exit; [ | apply CELLS; [exact HS | exact HSV] | exact ST | exact MU | exact WM | exact HMI ];
        reflexivity ] ].
  all: first [ exact HF | exact KI0 | exact KI1 | tauto | (unfold bv_modulus in Rrem; lia) | (rewrite iw_succ by lia; lia) ].
Qed.

Lemma knock_mid : forall (fuel : nat), loop_ok fuel ->
  forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (now evw cur' rem' iw quiet t0w due hns : word) (d h c' : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned rem') <= fuel)%nat ->
  bv_unsigned cur' = bv_unsigned p + c' -> 0 <= c' -> c' + bv_unsigned rem' = Z.of_nat (length data) ->
  bv_unsigned evw < 256 ->
  bv_unsigned iw <= 4095 ->
  (d = 0 \/ d = 1) -> (h = 0 \/ h = 1) ->
  bv_unsigned t0w < 2 ^ 63 ->
  (d = 0 -> h = 0 -> quiet = t0w /\ bv_unsigned due = bv_unsigned t0w + 500000000) ->
  (d = 0 -> h = 1 -> hns = quiet) ->
  bv_unsigned quiet <= bv_unsigned now ->
  bv_unsigned now <= 2 ^ 63 + (bv_unsigned iw + 1) * 2 ^ 23 ->
  rw_cells rsegs m1 (bv_unsigned sp + -144)
    (knock_cells (st_of d h) (Z_to_bv 64 0) t0w due hns d (Z_to_bv 64 0)) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' cur' now a0' a1' a2' a3' a4' a5' a6' a7'
             rem' iw (Z_to_bv 64 1) (Z_to_bv 64 h) (Z_to_bv 64 4094) (Z_to_bv 64 500000000) (Z_to_bv 64 d)
             (Z_to_bv 64 499999999) evw quiet t3' t4' t5' t6')
        F (Z_to_bv 64 0x12c80) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    now evw cur' rem' iw quiet t0w due hns d h c' m1 HF HC HC0 HCN HEV HI HD HH HT0 KI0 KI1 HQ HNOW HS HSV HDATA ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 now) as Rnow.
  pose proof (bv_unsigned_in_range 64 quiet) as Rq.
  pose proof ST as [Hlo _].
  assert (U144 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144)
    by (apply unsigned_lit; unfold bv_modulus in Rsp; lia).
  pose proof (bv_unsigned_in_range 64 iw) as Riw.
  zstep. zstep.
  if_cases E2.
  { eapply knock_checks; [exact LOOP | exact HF | exact HC | exact HC0 | exact HCN | exact HI | exact HD | exact HH
      | exact HT0 | exact KI0 | exact KI1 | exact HQ | exact HNOW | exact HS | exact HSV | exact HDATA | exact ST
      | exact MU | exact WM | exact HMI]. }
  zstep. zstep. zstep.
  destruct HD as [-> | ->]; destruct HH as [-> | ->]; unfold st_of in HS; cbn [Z.eqb Pos.eqb] in HS.
  all: call reac_knock_step_holds.
  all: try (rewrite U144; exact HS).
  all: try lia.
  all: unfold knock_step_f in MI; cbn [Z.eqb Pos.eqb] in MI.
  - destruct (KI0 eq_refl eq_refl) as [Eq Edue]. subst quiet.
    destruct (Z.ltb_spec (bv_unsigned now) (bv_unsigned due)) as [Hlt | Hge]; cbn in MI;
      destruct MI as [Ex HS2]; subst x; rewrite U144 in HS2; unfold knock_cells in HS2.
    + zstep. if_false. zstep. if_true. zstep. zstep. zstep. zstep. if_false. zstep. if_cases G6.
      { refute_trap G6. }
      eapply knock_checks; try eassumption; side.
    + zstep. if_false. zstep. if_false. zstep. if_false. zstep. zstep. if_false. zstep. zstep. zstep. zstep.
      if_cases G6.
      { refute_trap G6. }
      zstep. zstep. zstep. if_true.
      eapply knock_checks; try eassumption; side.
  - pose proof (KI1 eq_refl eq_refl) as Ehns. subst hns.
    destruct ((bv_unsigned now <=? bv_unsigned quiet) || (bv_unsigned now - bv_unsigned quiet <? L_NS)) eqn:Eb;
      cbn in MI; destruct MI as [Ex HS2]; subst x; rewrite U144 in HS2; unfold knock_cells in HS2.
    + apply orb_true_iff in Eb. unfold L_NS in Eb.
      assert (Hsm : bv_unsigned now - bv_unsigned quiet < 500000000)
        by (destruct Eb as [E | E]; [apply Z.leb_le in E | apply Z.ltb_lt in E]; lia).
      zstep. if_false. zstep. if_true. zstep. zstep. zstep. zstep. if_false. zstep. if_cases G6.
      { refute_trap G6. }
      eapply knock_checks; try eassumption; side.
    + apply orb_false_iff in Eb. destruct Eb as [Eb1 Eb2]. apply Z.leb_gt in Eb1. apply Z.ltb_ge in Eb2. unfold L_NS in Eb2.
      zstep. if_false. zstep. if_false. zstep. if_false. zstep. zstep. if_false. zstep. zstep. zstep. zstep.
      if_cases G6.
      { refute_trap G6. }
      zstep. zstep. zstep. if_true.
      eapply knock_checks; try eassumption; side.
  - cbn in MI; destruct MI as [Ex HS2]; subst x; rewrite U144 in HS2; unfold knock_cells in HS2.
    zstep. if_false. zstep. if_true. zstep. zstep. zstep. zstep. if_true.
    eapply knock_checks; try eassumption; side.
  - cbn in MI; destruct MI as [Ex HS2]; subst x; rewrite U144 in HS2; unfold knock_cells in HS2.
    zstep. if_false. zstep. if_true. zstep. zstep. zstep. zstep. if_true.
    eapply knock_checks; try eassumption; side.
Qed.

Lemma knock_tail : forall (fuel : nat), loop_ok fuel ->
  forall (ra' t0' t1' t2' a0v a1v a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (now evw cur' rem' iw quiet t0w due hns : word) (d h c' : Z) (m1 : word -> option byte),
  (Z.to_nat (bv_unsigned rem') <= fuel)%nat ->
  bv_unsigned cur' = bv_unsigned p + c' -> 0 <= c' -> c' + bv_unsigned rem' = Z.of_nat (length data) ->
  bv_unsigned evw < 256 ->
  bv_unsigned a0v < 2 ^ 16 -> bv_unsigned a1v < 2 ^ 16 ->
  bv_unsigned iw <= 4095 ->
  (d = 0 \/ d = 1) -> (h = 0 \/ h = 1) ->
  bv_unsigned t0w < 2 ^ 63 ->
  (d = 0 -> h = 0 -> quiet = t0w /\ bv_unsigned due = bv_unsigned t0w + 500000000) ->
  (d = 0 -> h = 1 -> hns = quiet) ->
  bv_unsigned quiet <= bv_unsigned now ->
  bv_unsigned now <= 2 ^ 63 + bv_unsigned iw * 2 ^ 23 ->
  rw_cells rsegs m1 (bv_unsigned sp + -144)
    (knock_cells (st_of d h) (Z_to_bv 64 0) t0w due hns d (Z_to_bv 64 0)) ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' cur' now a0v a1v a2' a3' a4' a5' a6' a7'
             rem' iw (Z_to_bv 64 1) (Z_to_bv 64 h) (Z_to_bv 64 4094) (Z_to_bv 64 500000000) (Z_to_bv 64 d)
             (Z_to_bv 64 499999999) evw quiet t3' t4' t5' t6')
        F (Z_to_bv 64 0x12c50) fc None m1 (seg_rom rsegs)).
Proof.
  intros fuel LOOP ra' t0' t1' t2' a0v a1v a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    now evw cur' rem' iw quiet t0w due hns d h c' m1 HF HC' HC0' HCN HEV HA0 HA1 HI HD HH HT0 KI0 KI1 HQ HNOW
    HS HSV HDATA ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 now) as Rnow.
  pose proof ST as [Hlo _].
  assert (U144 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144)
    by (apply unsigned_lit; unfold bv_modulus in Rsp; lia).
  pose proof (bv_unsigned_in_range 64 a0v) as Ra0. pose proof (bv_unsigned_in_range 64 a1v) as Ra1.
  pose proof (bv_unsigned_in_range 64 evw) as Rev.
  unfold bv_modulus in Ra0, Ra1, Rev, Rnow, Rsp.
  do 6 zstep.
  match goal with |- context [Z_to_bv 64 (?D + bv_unsigned now)] => remember D as dt eqn:Edt end.
  assert (Hdt : 0 <= dt < 2 ^ 23) by (subst dt; apply dt_bound; lia).
  remember (Z_to_bv 64 (dt + bv_unsigned now)) as now' eqn:Enow'.
  assert (Unow' : bv_unsigned now' = bv_unsigned now + dt) by (subst now'; rewrite unsigned_lit by lia; lia).
  clear Enow'.
  zstep.
  if_cases Eh.
  - eapply knock_mid; try eassumption; side.
  - zstep. zstep. zstep.
    destruct HD as [-> | ->]; destruct HH as [-> | ->]; unfold st_of in HS; cbn [Z.eqb Pos.eqb] in HS.
    all: call reac_knock_heard_holds.
    all: try (rewrite U144; exact HS).
    all: try lia.
    all: zstep; zstep.
    all: match goal with H1 : cells_at _ _ _ _, H2 : wr_at _ _ _ _ |- _ => rewrite U144 in H1, H2 end.
    all: eapply knock_mid; try eassumption; side.
Qed.

Lemma knock_loop : forall fuel, loop_ok fuel.
Proof.
  induction fuel as [|fuel IH]; unfold loop_ok; intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x26 t3' t4' t5' t6'
    now cur rem iw quiet t0w due hns d h c m1 HF HR1 HC HC0 HCN HI HD HH HT0 KI0 KI1 HQ HNOW HS HSV HDATA ST MU WM HMI.
  { exfalso. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 rem) as Rrem.
  pose proof (bv_unsigned_in_range 64 cur) as Rcur.
  pose proof (bv_unsigned_in_range 64 p) as Rp.
  pose proof (bytes_at_bound rsegs m1 (bv_unsigned p) data HDATA) as Bd.
  unfold bv_modulus in Rsp, Rrem, Rcur, Rp.
  assert (Hp1 : 0 < bv_unsigned p) by (apply HPNZ; lia).
  assert (HB0 : ov_read_bytes rsegs m1 cur 1 = Some [nth (Z.to_nat c) data (Z_to_bv 8 0)]).
  { rewrite <- (Z_to_bv_bv_unsigned cur). rewrite HC. apply (bytes_at_byte m1 (bv_unsigned p) data c); [exact HDATA | lia]. }
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat c) data (Z_to_bv 8 0))) as Rb0. unfold bv_modulus in Rb0.
  zstep. zstep.
  if_cases T0; [refute_trap T0 |].
  zstep. zstep.
  if_cases B1.
  - zify_cond B1.
    zstep. zstep.
    if_cases T1; [refute_trap T1 |].
    assert (HB1 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned cur + 1)) 1
                  = Some [nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0)]).
    { rewrite HC. replace (bv_unsigned p + c + 1) with (bv_unsigned p + (c + 1)) by lia.
      apply bytes_at_byte; [exact HDATA | lia]. }
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (c + 1)) data (Z_to_bv 8 0))) as Rb1. unfold bv_modulus in Rb1.
    zstep. zstep. zstep. zstep.
    if_cases B2.
    + zify_cond B2.
      zstep. zstep.
      if_cases T2; [refute_trap T2 |].
      assert (HB2 : ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned cur + 2)) 1
                    = Some [nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0)]).
      { rewrite HC. replace (bv_unsigned p + c + 2) with (bv_unsigned p + (c + 2)) by lia.
        apply bytes_at_byte; [exact HDATA | lia]. }
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (c + 2)) data (Z_to_bv 8 0))) as Rb2. unfold bv_modulus in Rb2.
      do 4 zstep.
      eapply (knock_tail fuel IH) with (c' := c + 3); try eassumption; side.
    + zify_cond B2.
      do 4 zstep.
      eapply (knock_tail fuel IH) with (c' := c + 2); try eassumption; side.
  - zify_cond B1.
    do 6 zstep.
    eapply (knock_tail fuel IH) with (c' := c + 1); try eassumption; side.
Qed.

Hypothesis MEMS : memset_contract.

Lemma knock_parsed : forall (ra' t0' t1' t2' x9 a0v a1v a2v a3v a4' a5' a6' a7' x19 x20 x21 x22 x23 x24 x25 x26 x27
    t3' t4' t5' t6' cur rem : word) (c : Z) (junk : list byte) (m1 : word -> option byte),
  bv_unsigned a0v < 2 ^ 16 -> bv_unsigned a1v < 2 ^ 16 -> bv_unsigned a2v < 2 ^ 16 -> bv_unsigned a3v < 2 ^ 16 ->
  bv_unsigned cur = bv_unsigned p + c -> 0 <= c -> c + bv_unsigned rem = Z.of_nat (length data) ->
  rw_cells rsegs m1 (bv_unsigned sp + -144) [CB 40 junk] ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  bytes_at rsegs m1 (bv_unsigned p) data ->
  stk rsegs m1 lo (bv_unsigned sp + -144) ->
  munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  evt rsegs Qk
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' cur x9 a0v a1v a2v a3v a4' a5' a6' a7'
             rem x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
        F (Z_to_bv 64 0x12b90) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x9 a0v a1v a2v a3v a4' a5' a6' a7' x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6'
    cur rem c junk m1 HA0 HA1 HA2 HA3 HC HC0 HCN H40 HSV HDATA ST MU WM HMI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof ST as [Hlo _].
  unfold bv_modulus in Rsp.
  assert (U144 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144)
    by (apply unsigned_lit; lia).
  pose proof (bv_unsigned_in_range 64 a0v) as R0. pose proof (bv_unsigned_in_range 64 a1v) as R1.
  pose proof (bv_unsigned_in_range 64 a2v) as R2. pose proof (bv_unsigned_in_range 64 a3v) as R3.
  unfold bv_modulus in R0, R1, R2, R3.
  do 5 zstep.
  match goal with |- context [Z_to_bv 64 (Z.lor ?X ?Y)] => remember (Z_to_bv 64 (Z.lor X Y)) as t0w eqn:Et0 end.
  assert (Ht0 : bv_unsigned t0w < 2 ^ 63).
  { subst t0w.
    pose proof (lor_lt_pow (bv_unsigned a1v) (bv_unsigned a3v) 16 ltac:(lia) ltac:(lia) ltac:(lia)) as L1.
    pose proof (lor_lt_pow (bv_unsigned a2v) (bv_unsigned a0v) 16 ltac:(lia) ltac:(lia) ltac:(lia)) as L2.
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (Z.lor (bv_unsigned a1v) (bv_unsigned a3v) * 2 ^ 47)) by lia.
    rewrite (Z.mod_small (Z.lor (bv_unsigned a2v) (bv_unsigned a0v) * 2 ^ 31)) by lia.
    pose proof (lor_lt_pow (Z.lor (bv_unsigned a1v) (bv_unsigned a3v) * 2 ^ 47)
                           (Z.lor (bv_unsigned a2v) (bv_unsigned a0v) * 2 ^ 31) 63 ltac:(lia) ltac:(lia) ltac:(lia)) as L3.
    rewrite unsigned_lit by lia. lia. }
  clear Et0.
  pose proof (reac_knock_init_holds MEMS) as INIT.
  unfold reac_knock_init_contract, REAC_KNOCK_INIT_FRAME, REAC_KNOCK_INIT in INIT.
  zstep. zstep. zstep.
  call INIT.
  all: try (rewrite U144; first [exact H40 | exact ST]).
  all: try exact HMI.
  all: try (rewrite !U144; lia).
  match goal with H : rw_cells _ _ _ (knock_cells _ _ _ _ _ _ _) |- _ => rename H into HK end.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rename H into ST2 end.
  rewrite U144 in HK, ST2.
  pose proof HK as HK0.
  unfold knock_cells in HK.
  zstep. zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false. zstep.
  if_cases RZ.
  - zify_cond RZ.
    eapply knock_exit with (cs40 := knock_cells 0 (Z_to_bv 64 0) t0w (Z_to_bv 64 (bv_unsigned t0w + L_NS))
                                     (Z_to_bv 64 0) 0 (Z_to_bv 64 0)); [reflexivity | | eassumption | eassumption | eassumption | eassumption].
    apply rw_cells_app_join; [exact HK0|]. cbn [knock_cells cells_size csize Nat.add].
    replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) by lia. eassumption.
  - zify_cond RZ.
    pose proof (bv_unsigned_in_range 64 rem) as Rrem. pose proof (bv_unsigned_in_range 64 t0w) as Rt0.
    unfold bv_modulus in Rrem, Rt0.
    do 10 zstep.
    eapply (knock_loop (Z.to_nat (bv_unsigned rem))) with (d := 0) (h := 0) (c := c) (t0w := t0w)
      (due := Z_to_bv 64 (bv_unsigned t0w + L_NS)) (hns := Z_to_bv 64 0);
      try eassumption; try (unfold L_NS; first [ lia | (left; reflexivity) | (intros; split; [reflexivity | rewrite unsigned_lit by lia; lia]) | (intros; discriminate) | (rewrite unsigned_lit by lia; lia) | (cbn; lia) ]).
Qed.

Lemma knock_entry : forall (m1 : word -> option byte), m1 = m -> forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m1 (bv_unsigned p) data ->
  bv_unsigned a1 = Z.of_nat (length data) ->
  evt rsegs Qk
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12ae4) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 Em t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HD HN.
  assert (MU : munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m1) by (rewrite Em; apply munch_refl).
  assert (WM : wmono rsegs m m1) by (rewrite Em; apply wmono_refl).
  pose proof HMI0 as HMI. rewrite <- Em in HMI. pose proof ST0 as ST. rewrite <- Em in ST.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  pose proof (bv_unsigned_in_range 64 p) as Rp.
  pose proof ST as [Hlo _].
  unfold bv_modulus in Rsp, Ra1, Rp.
  carve_frame 144%nat ST.
  do 16 zstep.
  if_cases EBIG.
  { eapply knock_exit with (cs40 := [CB 40 _]); [reflexivity | exact FR | exact ST | exact MU | exact WM | exact HMI]. }
  destruct (rw_cells_app_split _ (bv_unsigned sp + -144) [CB 40 _] saved ltac:(exact FR)) as [H40 HSV0].
  cbn [cells_size csize Nat.add] in HSV0.
  replace (bv_unsigned sp + -144 + Z.of_nat 40) with (bv_unsigned sp + -104) in HSV0 by lia.
  clear FR.
  match goal with HDm : bytes_at rsegs ?mm (bv_unsigned p) data |- _ =>
  assert (BYTE : forall k, 0 <= k < Z.of_nat (length data) ->
            ov_read_bytes rsegs mm (Z_to_bv 64 (bv_unsigned p + k)) 1 = Some [nth (Z.to_nat k) data (Z_to_bv 8 0)]
            /\ 0 <= bv_unsigned (nth (Z.to_nat k) data (Z_to_bv 8 0)) < 256)
  by (intros k Hk; split; [apply bytes_at_byte; [exact HDm | lia] |];
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) data (Z_to_bv 8 0))) as Rb; unfold bv_modulus in Rb; exact Rb)
  end.
  zstep. zstep.
  if_cases EN0.
  { zify_cond EN0. do 5 zstep.
    eapply knock_parsed with (c := 0); side. }
  zify_cond EN0.
  assert (Hp1 : 0 < bv_unsigned p) by (apply HPNZ; lia).
  zstep. zstep. zstep.
  if_cases T0; [refute_trap T0 |].
  destruct (BYTE 0 ltac:(lia)) as [HB0 Rb0]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in HB0.
  zstep. zstep.
  if_cases EN1.
  - zify_cond EN1.
    zstep. zstep. zstep.
    if_cases T1; [refute_trap T1 |].
    destruct (BYTE 1 ltac:(lia)) as [HB1 Rb1].
    do 5 zstep.
    if_cases EN2.
    + zify_cond EN2.
      zstep. zstep. zstep.
      if_cases T2; [refute_trap T2 |].
      destruct (BYTE 2 ltac:(lia)) as [HB2 Rb2].
      do 4 zstep.
      if_cases EN3.
      * zify_cond EN3.
        zstep. zstep. zstep.
        if_cases T3; [refute_trap T3 |].
        destruct (BYTE 3 ltac:(lia)) as [HB3 Rb3].
        do 5 zstep.
        eapply knock_parsed with (c := 4); side.
      * zify_cond EN3.
        do 4 zstep.
        eapply knock_parsed with (c := 3); side.
    + zify_cond EN2.
      do 4 zstep.
      eapply knock_parsed with (c := 2); side.
  - zify_cond EN1.
    do 6 zstep.
    eapply knock_parsed with (c := 1); side.
Qed.

End KnockRun.

Theorem knock_main_holds : memset_contract -> knock_main_contract.
Proof.
  intros MEMS. unfold knock_main_contract, LLVM_KNOCK, LLVM_KNOCK_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo data HD HN HMI ST LO SPA DJ HPB HPNZ.
  change (evt rsegs (Qk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x12ae4) fc None m (seg_rom rsegs))).
  eapply knock_entry; first [ exact eq_refl | eassumption ].
Qed.
