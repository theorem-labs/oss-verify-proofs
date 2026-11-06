(* Modified by Theorem Labs, 2026-10: new file, the prologue of the fuzz_transport harness establishes the simulation invariant (a Theorem Labs lane). *)
(* fuzz_transport.c (FT):1124-1166, the prologue of LLVMFuzzerTestOneInput up to the head of its loop (:1168):
   the config read from the input (:1133-1148, diginet_session_config_default first, DS:11-27), the scalars and
   the harness model M (:1150-1158), then diginet_session_init (DS:56-75), which accepts every config the
   prologue makes (FT:1165's abort is unreachable). The result: the run is the loop from a world where
   agree I 0 holds (Agree.v), with the input cursor in range (QueueFacts.fuzz_in_ok). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree SimLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Import ListNotations.
Open Scope Z_scope.

Lemma land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma shr2 : forall x, Z.shiftr x 2 = x / 4.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma shr3 : forall x, Z.shiftr x 3 = x / 8.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* the input cursor: each read moves to a cursor still in range and yields a byte / a u16 *)
Ltac cursor D :=
  repeat match goal with
  | |- context [fuzz_u8_m D ?c] =>
      match goal with
      | Hc : QueueFacts.fuzz_in_ok D c |- _ =>
          let c' := fresh "c" in let v := fresh "v" in let E := fresh "E" in
          let Hc' := fresh "Hc" in let R := fresh "R" in
          destruct (QueueFacts.fuzz_u8_ok D c Hc) as (c' & v & E & Hc' & R);
          rewrite E; cbv beta iota; clear E
      end
  | |- context [fuzz_u16_m D ?c] =>
      match goal with
      | Hc : QueueFacts.fuzz_in_ok D c |- _ =>
          let c' := fresh "c" in let v := fresh "v" in let E := fresh "E" in
          let Hc' := fresh "Hc" in let R := fresh "R" in
          destruct (QueueFacts.fuzz_u16_ok D c Hc) as (c' & v & E & Hc' & R);
          rewrite E; cbv beta iota; clear E
      end
  end.

(* decide the integer comparisons lia can *)
Ltac zdec :=
  repeat match goal with
  | |- context [?a =? ?b] =>
      first [ rewrite (proj2 (Z.eqb_neq a b)) by lia | rewrite (proj2 (Z.eqb_eq a b)) by lia ]
  | |- context [?a <? ?b] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  end;
  cbv beta iota delta [orb andb negb].

(* powers of two as numerals (lia sees numerals) *)
Ltac pnorm :=
  try change (2 ^ 32) with 4294967296 in *; try change (2 ^ 64) with 18446744073709551616 in *;
  try change (2 ^ 31) with 2147483648 in *.

Ltac pconst :=
  unfold S_IDLE, S_WAKING, S_ONLINE, S_CLOSED, DIGINET_S_IDLE, DIGINET_SUM_BODY, DIGINET_SUM_ZERO, QUEUE_MAX,
    OPS_MAX, SPEC_CMD_MAX, SPEC_MAX_BODY, DIGINET_CMD_MAX_LEN, DIGINET_MAX_BODY_LEN, SPEC_OK, DIGINET_OK,
    DIGINET_E_ARG, c2_keepalive, bit01 in *;
  pnorm.

(* bv_swrap 32 of a numeral, computed *)
Ltac swrapc :=
  repeat match goal with
  | |- context [bv_swrap 32 (Zpos ?p)] => let r := eval vm_compute in (bv_swrap 32 (Zpos p)) in change (bv_swrap 32 (Zpos p)) with r
  | |- context [bv_swrap 32 Z0] => change (bv_swrap 32 Z0) with 0
  end.

Ltac bitnorm :=
  repeat match goal with
  | |- context [Z.land ?x 1] => rewrite (land1 x)
  | |- context [Z.shiftr ?x 2] => rewrite (shr2 x)
  | |- context [Z.shiftr ?x 3] => rewrite (shr3 x)
  end.

(* the two sides are the same term (compared syntactically, never by conversion) *)
Ltac synrefl := match goal with |- ?a = ?b => wis a b; exact eq_refl end.

(* name every write layer of the goal, innermost first, once: W := upd X k v (SimLib's wsimp_once reads
   through such names) *)
Ltac wname :=
  repeat match goal with
  | |- context [upd ?X ?k ?v] =>
      wno_upd X; wno_upd v;
      let W := fresh "W" in set (W := upd X k v);
      let H := fresh "HW" in
      assert (H : length W = Z.to_nat W_LEN)
        by (refine (wl_eq_upd X k v _ _ _ _);
            [ match goal with H : length ?Y = Z.to_nat W_LEN |- _ => wis Y X; exact H end | wle | wlen_bnd ])
  end.

(* length of a named chain of writes on B, length B = Z.to_nat W_LEN *)
Ltac wlen_n :=
  lazymatch goal with
  | |- length ?X = ?L =>
      first
      [ match goal with H : length ?Y = ?M |- _ => wis Y X; wis M L; exact H end
      | match goal with Y := upd ?X' ?k ?v |- _ => wis Y X; refine (wl_eq_upd X' k v L _ _ _); [wlen_n | wle | wlen_bnd] end ]
  end.

(* drop what no clause needs (lia over a large context is slow) *)
Ltac pclear :=
  repeat match goal with
  | H : length _ = Z.to_nat W_LEN |- _ => clear H
  | H : QueueFacts.fuzz_in_ok _ _ |- _ => clear H
  end.

(* an implication whose premise reads false: refute the premise alone *)
Ltac vac :=
  lazymatch goal with
  | |- ?P -> _ =>
      let Hn := fresh "Hn" in
      assert (Hn : P -> False) by (repeat wsimp_once; pconst; pclear; intro; lia);
      let Hp := fresh "Hp" in intro Hp; exfalso; exact (Hn Hp)
  end.

(* one clause of agree over the prologue's world *)
Ltac pfin :=
  unfold c2_keepalive, bit01;
  repeat wsimp_once; pconst; pclear;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  swrapc;
  first [ synrefl | lia | (intros; synrefl) | (intros; exfalso; lia) | (intros; lia) ].

(* an input of FUZZ_INPUT_MAX bytes or more is not looked at (FT:1130-1131) *)
Lemma prologue_big : forall (I : timg) (B : list byte) (A : nat -> Z) (D : list byte),
  FUZZ_INPUT_MAX <= Z.of_nat (length D) -> LLVMFuzzerTestOneInput_m I B A D = Some (B, 0).
Proof.
  intros I B A D H. unfold LLVMFuzzerTestOneInput_m. cbv zeta.
  rewrite (proj2 (Z.leb_le FUZZ_INPUT_MAX (Z.of_nat (length D))) H). exact eq_refl.
Qed.

(* the cursor at the head of the loop: the prologue's ten reads (FT:1133, :1140-1148) *)
Definition prologue_cursor (D : list byte) : fuzz_in :=
  let c0 := fuzz_in_m (Z.of_nat (length D)) in
  let (c1, _) := fuzz_u8_m D c0 in
  let (c2, _) := fuzz_u8_m D c1 in
  let (c3, _) := fuzz_u8_m D c2 in
  let (c4, _) := fuzz_u16_m D c3 in
  let (c5, _) := fuzz_u8_m D c4 in
  let (c6, _) := fuzz_u16_m D c5 in
  let (c7, _) := fuzz_u16_m D c6 in
  let (c8, _) := fuzz_u16_m D c7 in
  let (c9, _) := fuzz_u8_m D c8 in
  let (c10, _) := fuzz_u16_m D c9 in
  c10.

(* every other input: the run is the loop of FT:1168 from prologue_cursor D and a world where agree I 0 holds *)
Theorem prologue_ok : forall (I : timg) (B : list byte) (A : nat -> Z) (D : list byte),
  timg_ok I -> length B = Z.to_nat W_LEN -> Z.of_nat (length D) < FUZZ_INPUT_MAX ->
  exists B0,
    LLVMFuzzerTestOneInput_m I B A D =
      match LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) I B0 A D (prologue_cursor D) O with
      | Some (B1, _) => Some (B1, 0)
      | None => None
      end /\
    agree I 0 B0 /\ QueueFacts.fuzz_in_ok D (prologue_cursor D).
Proof.
  intros I B A D HI HB HD.
  pose proof HI as [Hs Hr Hn Hno Hc24 Hpc Hcp Hpe].
  unfold LLVMFuzzerTestOneInput_m, prologue_cursor. cbv zeta.
  rewrite (proj2 (Z.leb_gt FUZZ_INPUT_MAX (Z.of_nat (length D))) HD).
  pose proof (QueueFacts.fuzz_in_m_ok D) as Hc0.
  cursor D.
  unfold diginet_session_config_default_m. cbv zeta beta iota.
  unfold diginet_session_init_m. cbv zeta.
  bitnorm. pnorm.
  wunfold_set.
  wname.
  (repeat wsimp_once).
  (* s->cfg = *cfg (DS:64): the 60 bytes of g_cfg as one value *)
  match goal with |- context [sub ?Y OFF_g_cfg (Z.to_nat SZ_g_cfg)] =>
    assert (Hcl : length (sub Y OFF_g_cfg (Z.to_nat SZ_g_cfg)) = 60%nat)
      by (apply length_sub; [apply Z.leb_le; vm_compute; reflexivity|];
          match goal with H : length ?Y' = Z.to_nat W_LEN |- _ => wis Y' Y; rewrite H end;
          apply Z.leb_le; vm_compute; reflexivity);
    remember (sub Y OFF_g_cfg (Z.to_nat SZ_g_cfg)) as cfg eqn:Ecfg
  end.
  pconst. zdec.
  match goal with |- context [(?x / 4) mod 2 =? 0] => destruct (Z.eqb_spec ((x / 4) mod 2) 0) as [Hds|Hds] end.
  all: cbv beta iota; zdec.
  all: wunfold_set.
  all: wname.
  all: eexists _; split; [reflexivity|].
  all: split; [|assumption].
  all: constructor; [constructor|..].
  all: try (lazymatch goal with |- timg_ok _ => exact HI end).
  all: try (lazymatch goal with |- length _ = Z.to_nat W_LEN => wlen_n end).
  all: try (lazymatch goal with |- agree_cfg _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_io _ _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_st _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_fly _ => constructor end; try vac; try pfin).
  all: try (lazymatch goal with |- agree_time _ _ => constructor end; try pfin).
  all: try (lazymatch goal with |- agree_misc _ _ => constructor end; try pfin).
  all: try (lazymatch goal with |- c2_keepalive _ => pfin end).
  all: try (lazymatch goal with |- g_rx _ = 0 => pfin end).
  all: try (lazymatch goal with |- agree_q _ _ => constructor end; try pfin).
  (* A2 (DS:64): the copy is the 60 bytes of g_cfg *)
  all: try (lazymatch goal with |- sub _ A_S_cfg_host_mac 60 = sub _ OFF_g_cfg 60 =>
              repeat wsimp_once; rewrite Ecfg; change (Z.to_nat SZ_g_cfg) with 60%nat; synrefl end).
Qed.
