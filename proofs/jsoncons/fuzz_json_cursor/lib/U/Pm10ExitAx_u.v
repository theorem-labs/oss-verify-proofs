(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Frame.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10ExitBase_u Pm10_code_a5000_a6000_u Pm10_code_b6000_b7000_u  .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition AX : Z := 0xf6848%Z.

Definition LIBENV_LO : Z := 0xd4de0%Z.
Definition LIBENV_LEN : Z := 0x1188%Z.
Definition HSCR : Z := 80%Z.

Section FPX_1. Context {fx : PropExec.FPState}.

Definition atexit_state (mem : word -> option byte) (hs : list (Z * Z)) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xf684c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ match hs with
     | [] => rdn RSEGS mem (Z_to_bv 64 0xf6858) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
     | _ => (Z.of_nat (length hs) <= 32)%Z
            /\ rdn RSEGS mem (Z_to_bv 64 0xf6858) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf6860))
            /\ rdn RSEGS mem (Z_to_bv 64 0xf6850) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat (length hs))))
            /\ rdn RSEGS mem (Z_to_bv 64 0xf6860) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
            /\ (forall i f a, nth_error hs i = Some (f, a) ->
                   rdn RSEGS mem (Z_to_bv 64 (0xf6868 + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 f))
                /\ rdn RSEGS mem (Z_to_bv 64 (0xf6968 + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 a)))
     end.

Definition cs_regs : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition handler_ok (HInv : (word -> option byte) -> Prop) (f a : Z) : Prop :=
  (0 <= f < 2 ^ 64)%Z /\ (f mod 2 = 0)%Z /\ (0 <= a < 2 ^ 64)%Z /\
  forall regs mem rom (sp ra : word),
    getr regs 2 = sp -> getr regs 1 = ra -> getr regs 10 = Z_to_bv 64 a -> ret_ok ra ->
    (4294967296 <= bv_unsigned sp - HSCR)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
    store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - HSCR)) (Z.to_nat HSCR) = true ->
    HInv mem ->
    exists regs' mem',
      msteps RSEGS (mkst regs (Z_to_bv 64 f) mem rom) (mkst regs' ra mem' rom)
      /\ getr regs' 2 = sp
      /\ (forall r, In r cs_regs -> getr regs' r = getr regs r)
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HSCR), HSCR); (Z_to_bv 64 LIBENV_LO, LIBENV_LEN)]
      /\ HInv mem'.

Definition mem_wF0 (mem : word -> option byte) (sp s0v s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xa71c4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 s0v))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0xf6848) [Z_to_bv 8 1].

Lemma wF0 : forall regs mem rom (sp s0v s1v s2v s3v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 1 = Z_to_bv 64 0xa71c4 ->
  getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xf6a93) 1%nat = Some [Z_to_bv 8 0] ->
  atexit_state mem [] ->
  exists regs',
    msteps RSEGS (mkst regs (0xa6eb4 : word) mem rom)
                 (mkst regs' (0xa71c4 : word) (mem_wF0 mem sp s0v s1v s2v s3v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp s0v s1v s2v s3v Hsp Hra Hs0 Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl (Mlock & Mhead).
  unfold mem_wF0. eexists. split.
  - stepn F_a50c4 D_a50c4. rewrite Hsp. sp_renorm.
    stepST F_a50c8 D_a50c8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xa71c4) ltac:(sok_stack SOK).
    stepST F_a50cc D_a50cc (Z_to_bv 64 (bv_unsigned sp - 32)) s0v ltac:(sok_stack SOK).
    stepST F_a50d0 D_a50d0 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepST F_a50d4 D_a50d4 (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
    stepST F_a50d8 D_a50d8 (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
    stepn F_a50dc D_a50dc.
    stepn F_a50e0 D_a50e0.
    stepn F_a50e4 D_a50e4.
    stepn F_a50e8 D_a50e8.

    stepn F_a50ec D_a50ec.
    stepn F_b6694 D_b6694.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_b6698 | reflexivity | exact D_b6698 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_b669c D_b669c ltac:(cond_compute).
    stepret F_b688c D_b688c (0xa6ee0 : word) ltac:(bveq).

    stepLD8 F_a50f0 D_a50f0 (Z_to_bv 64 0).
    stepb_tk F_a50f4 D_a50f4 ltac:(cond_compute).

    stepn F_a5164 D_a5164.
    stepST F_a5168 D_a5168 (Z_to_bv 64 0xf6848) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_a516c D_a516c.
    stepLD8 F_a5170 D_a5170 (Z_to_bv 64 0xa71c4).
    stepLD8 F_a5174 D_a5174 s0v.
    stepLD8 F_a5178 D_a5178 s1v.
    stepLD8 F_a517c D_a517c s2v.
    stepLD8 F_a5180 D_a5180 s3v.
    stepn F_a5184 D_a5184. sp_renorm.

    stepn F_a5188 D_a5188.
    stepLD F_b691c D_b691c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_b6920 D_b6920 ltac:(cond_compute).
    stepret F_b6924 D_b6924 (0xa71c4 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; assumption.
Qed.

Lemma v_addiw_m1 : forall i, (1 <= i < 2147483648)%Z -> v_addiw (Z_to_bv 64 i) (-1) = Z_to_bv 64 (i - 1).
Proof.
  intros i Hi. unfold v_addiw. rewrite u_Z2bv by lia. f_equal.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. lia.
Qed.
Lemma v_slli3 : forall i, (0 <= i < 2147483648)%Z -> v_slli (Z_to_bv 64 i) 3 = Z_to_bv 64 (8 * i).
Proof. intros i Hi. unfold v_slli. rewrite u_Z2bv by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

Record foe_mem (m : word -> option byte) (sp s0v s1v s2v s3v : word) (hs : list (Z * Z)) : Prop := {
  fm_ra : rdn RSEGS m (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa71c4));
  fm_s0 : rdn RSEGS m (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 s0v);
  fm_s1 : rdn RSEGS m (Z_to_bv 64 (bv_unsigned sp - 40)) 8%nat = Some (word_to_le_bytes 8 s1v);
  fm_s2 : rdn RSEGS m (Z_to_bv 64 (bv_unsigned sp - 48)) 8%nat = Some (word_to_le_bytes 8 s2v);
  fm_s3 : rdn RSEGS m (Z_to_bv 64 (bv_unsigned sp - 56)) 8%nat = Some (word_to_le_bytes 8 s3v);
  fm_nl : rdn RSEGS m (Z_to_bv 64 0xf6a93) 1%nat = Some [Z_to_bv 8 0];
  fm_lock : rdn RSEGS m (Z_to_bv 64 0xf684c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  fm_head : rdn RSEGS m (Z_to_bv 64 0xf6858) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf6860));
  fm_next : rdn RSEGS m (Z_to_bv 64 0xf6860) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  fm_tab : forall i f a, nth_error hs i = Some (f, a) ->
             rdn RSEGS m (Z_to_bv 64 (0xf6868 + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 f))
          /\ rdn RSEGS m (Z_to_bv 64 (0xf6968 + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 a));
  fm_sok : store_ok RSEGS m (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
}.

End FPX_1.

Ltac outside_tac :=
  intros; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; cbn [outside]; unfold in_rng, LIBENV_LO, LIBENV_LEN, HSCR, AX in *;
  unorm; repeat split; try exact I; lia.
Ltac nowrap_tac := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia.

Section FPX_2. Context {fx : PropExec.FPState}.

Lemma foe_mem_frame : forall m m' sp s0v s1v s2v s3v hs,
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z -> (Z.of_nat (length hs) <= 32)%Z ->
  foe_mem m sp s0v s1v s2v s3v hs ->
  frame_mod m m' [(Z_to_bv 64 (bv_unsigned sp - 64 - HSCR), HSCR); (Z_to_bv 64 LIBENV_LO, LIBENV_LEN)] ->
  foe_mem m' sp s0v s1v s2v s3v hs.
Proof.
  intros m m' sp s0v s1v s2v s3v hs SPlo SPhi LEN [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11] FM.
  constructor.
  1-9: (erewrite frame_mod_rdn; [eassumption | exact FM | outside_tac | nowrap_tac]).
  - intros i f a Hi. destruct (A10 i f a Hi) as [B1 B2].
    assert (Z.of_nat i < 32)%Z by (pose proof (proj1 (nth_error_Some hs i) ltac:(congruence)); lia).
    split; (erewrite frame_mod_rdn; [eassumption | exact FM | outside_tac | nowrap_tac]).
  - eapply frame_mod_store_ok; eassumption.
Qed.

Lemma atexit_state_nonempty : forall mem hs, hs <> [] -> atexit_state mem hs ->
  rdn RSEGS mem (Z_to_bv 64 0xf684c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0xf6858) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf6860))
  /\ rdn RSEGS mem (Z_to_bv 64 0xf6850) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat (length hs))))
  /\ rdn RSEGS mem (Z_to_bv 64 0xf6860) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ (forall i f a, nth_error hs i = Some (f, a) ->
         rdn RSEGS mem (Z_to_bv 64 (0xf6868 + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 f))
      /\ rdn RSEGS mem (Z_to_bv 64 (0xf6968 + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 a))).
Proof. intros mem [|h t] H; [congruence|]. intros (A & _ & B & C & D & E). auto. Qed.

Lemma atexit_state_frame : forall m m' hs rs,
  (Z.of_nat (length hs) <= 32)%Z -> atexit_state m hs -> frame_mod m m' rs ->
  (forall x : word, (0xf6848 <= bv_unsigned x < 0xf6a68)%Z -> outside x rs) ->
  atexit_state m' hs.
Proof.
  intros m m' hs rs LEN (A & B) FM OUT.
  assert (X : forall (a : Z) (n : nat) v, (0xf6848 <= a)%Z -> (a + Z.of_nat n <= 0xf6a68)%Z ->
                rdn RSEGS m (Z_to_bv 64 a) n = Some v -> rdn RSEGS m' (Z_to_bv 64 a) n = Some v).
  { intros a n v Ha Hb H. erewrite frame_mod_rdn; [exact H | exact FM | | u_norm; lia].
    intros i Hi. apply OUT. unorm. lia. }
  split; [apply X; [lia | cbn; lia | exact A]|].
  destruct hs as [|h t]; [apply X; [lia | cbn; lia | exact B]|].
  destruct B as (B0 & B1 & B2 & B3 & B4).
  split; [exact B0|]. split; [apply X; [lia | cbn; lia | exact B1]|]. split; [apply X; [lia | cbn; lia | exact B2]|].
  split; [apply X; [lia | cbn; lia | exact B3]|].
  intros i f a Hi. destruct (B4 i f a Hi) as [C1 C2].
  assert (Z.of_nat i < 32)%Z by (pose proof (proj1 (nth_error_Some (h :: t) i) ltac:(congruence)); lia).
  split; apply X; try assumption; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma atexit_state_agree : forall m m' hs,
  (Z.of_nat (length hs) <= 32)%Z -> atexit_state m hs ->
  (forall a, (0xf6848 <= a < 0xf6a68)%Z -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  atexit_state m' hs.
Proof.
  intros m m' hs LEN (A & B) AG.
  assert (X : forall (a : Z) (n : nat) v, (0xf6848 <= a)%Z -> (a + Z.of_nat n <= 0xf6a68)%Z ->
                rdn RSEGS m (Z_to_bv 64 a) n = Some v -> rdn RSEGS m' (Z_to_bv 64 a) n = Some v).
  { intros a n v Ha Hb H. rewrite <- H. apply rdn_ext; [u_norm; lia|].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG. revert Hx. u_norm. lia. }
  split; [apply X; [lia | cbn; lia | exact A]|].
  destruct hs as [|h t]; [apply X; [lia | cbn; lia | exact B]|].
  destruct B as (B0 & B1 & B2 & B3 & B4).
  split; [exact B0|]. split; [apply X; [lia | cbn; lia | exact B1]|]. split; [apply X; [lia | cbn; lia | exact B2]|].
  split; [apply X; [lia | cbn; lia | exact B3]|].
  intros i f a Hi. destruct (B4 i f a Hi) as [C1 C2].
  assert (Z.of_nat i < 32)%Z by (pose proof (proj1 (nth_error_Some (h :: t) i) ltac:(congruence)); lia).
  split; apply X; try assumption; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma fm_wb : forall (m m1 : word -> option byte) base bs rs,
  frame_mod m m1 rs -> (bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  frame_mod m (wbytes m1 base bs) (rs ++ [(base, Z.of_nat (length bs))]).
Proof. intros m m1 base bs rs H Hb. eapply frame_mod_trans; [exact H|]. apply frame_mod_wbytes. exact Hb. Qed.

Section Loop.
Variable HInv : (word -> option byte) -> Prop.

Hypothesis HInv_stable : forall (m m' : word -> option byte) (spw : word),
  (4294967296 <= bv_unsigned spw - 144)%Z ->
  HInv m -> frame_mod m m' [(Z_to_bv 64 (bv_unsigned spw - 144), 144%Z); (Z_to_bv 64 AX, 0x224%Z)] -> HInv m'.
Variables (sp s0v s1v s2v s3v : word) (hs : list (Z * Z)) (rom : word -> option byte).
Hypothesis SPlo : (4294967296 <= bv_unsigned sp - 144)%Z.
Hypothesis SPhi : (bv_unsigned sp <= 0x800000000000)%Z.
Hypothesis LEN : (Z.of_nat (length hs) <= 32)%Z.
Hypothesis HOK : Forall (fun h => handler_ok HInv (fst h) (snd h)) hs.

Definition RS_all : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp - 144), 128%Z); (Z_to_bv 64 AX, 0x224%Z); (Z_to_bv 64 LIBENV_LO, LIBENV_LEN)].

Lemma foe_body : forall n regs m,
  (n < length hs)%nat ->
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0xf684c -> getr regs 18 = Z_to_bv 64 0xf6848 ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
  foe_mem m sp s0v s1v s2v s3v hs ->
  rdn RSEGS m (Z_to_bv 64 0xf6850) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat n))) ->
  HInv m ->
  exists regs' m',
    msteps RSEGS (mkst regs (0xa6f10 : word) m rom) (mkst regs' (0xa6f48 : word) m' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0xf684c /\ getr regs' 18 = Z_to_bv 64 0xf6848
    /\ getr regs' 10 = Z_to_bv 64 (Z.of_nat n)
    /\ getr regs' 12 = v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1)
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3
    /\ foe_mem m' sp s0v s1v s2v s3v hs
    /\ rdn RSEGS m' (Z_to_bv 64 0xf6850) 4%nat = Some (word_to_le_bytes 4 (v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1)))
    /\ frame_mod m m' RS_all /\ HInv m'.
Proof.
  intros n regs m Hn Hsp Hs0 Hs2 Ha2 FM Mslot HI.
  destruct (nth_error hs n) as [[f a]|] eqn:E; [|exfalso; apply nth_error_None in E; lia].
  pose proof FM as [Mra Ms0 Ms1 Ms2 Ms3 Mnl Mlock Mhead Mnext Mtab SOK].
  destruct (Mtab n f a E) as [Tf Ta].
  rewrite Forall_forall in HOK. destruct (HOK (f, a) (nth_error_In _ _ E)) as (Hf0 & Hfe & Ha0 & HC). cbn [fst snd] in *.
  assert (Hn32 : (Z.of_nat n < 32)%Z) by lia.

  assert (P1 : exists regsH,
     msteps RSEGS (mkst regs (0xa6f10 : word) m rom) (mkst regsH (Z_to_bv 64 f) m rom)
     /\ getr regsH 2 = Z_to_bv 64 (bv_unsigned sp - 64) /\ getr regsH 1 = Z_to_bv 64 0xa6f34
     /\ getr regsH 10 = Z_to_bv 64 a
     /\ getr regsH 8 = Z_to_bv 64 0xf684c /\ getr regsH 18 = Z_to_bv 64 0xf6848
     /\ getr regsH 4 = getr regs 4 /\ getr regsH 3 = getr regs 3).
  { eexists. split.
    - stepLD8 F_a5120 D_a5120 (Z_to_bv 64 0xf6860).
      stepn F_a5124 D_a5124. rewrite Ha2, v_slli3 by lia.
      stepn F_a5128 D_a5128.
      replace (v_add (Z_to_bv 64 0xf6860) (Z_to_bv 64 (8 * Z.of_nat n))) with (Z_to_bv 64 (0xf6860 + 8 * Z.of_nat n))
        by (unfold v_add; unorm; reflexivity).
      stepLD F_a512c D_a512c (word_to_le_bytes 8 (Z_to_bv 64 f)) (Z_to_bv 64 f)
        ltac:(replace (v_addi (Z_to_bv 64 (0xf6860 + 8 * Z.of_nat n)) 8) with (Z_to_bv 64 (0xf6868 + 8 * Z.of_nat n))
                by (unfold v_addi; unorm; f_equal; lia); exact Tf)
        ltac:(apply bytes_le_to_Z_8).
      stepLD F_a5130 D_a5130 (word_to_le_bytes 8 (Z_to_bv 64 a)) (Z_to_bv 64 a)
        ltac:(replace (v_addi (Z_to_bv 64 (0xf6860 + 8 * Z.of_nat n)) 264) with (Z_to_bv 64 (0xf6968 + 8 * Z.of_nat n))
                by (unfold v_addi; unorm; f_equal; lia); exact Ta)
        ltac:(apply bytes_le_to_Z_8).
      stepn F_a5134 D_a5134. rewrite Hs0.

      stepn F_a5138 D_a5138.
      stepLD F_b691c D_b691c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_b6920 D_b6920 ltac:(cond_compute).
      stepret F_b6924 D_b6924 (0xa6f2c : word) ltac:(bveq).
      stepn F_a513c D_a513c.

      eapply mst_step; [reflexivity
        | eapply step_jalr_link with (tgt := Z_to_bv 64 f); [exact F_a5140 | reflexivity | exact D_a5140 | reflexivity | gres; reflexivity]
        | ].
      imm_norm.
      rewrite (ret_ok_even (Z_to_bv 64 f) ltac:(rewrite u_Z2bv by lia; exact Hfe) : v_jalr (Z_to_bv 64 f) 0 = Z_to_bv 64 f).
      apply mst_refl.
    - repeat split; gres; try reflexivity; try assumption. }
  destruct P1 as (regsH & RUN1 & H2 & H1 & H10 & H8 & H18 & H4 & H3).

  destruct (HC regsH m rom (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xa6f34) H2 H1 H10)
    as (regs2 & m2 & RUN2 & R2sp & R2cs & FM2 & HI2).
  { apply ret_ok_even. reflexivity. }
  { unfold HSCR. u_norm. lia. }
  { u_norm. lia. }
  { unfold HSCR. rewrite u_Z2bv by lia. store_ok_peel.
    eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia. }
  { exact HI. }
  rewrite u_Z2bv in FM2 by lia.
  pose proof (foe_mem_frame m m2 sp s0v s1v s2v s3v hs SPlo SPhi LEN FM FM2) as FMm2.
  destruct FMm2 as [Mra2 Ms02 Ms12 Ms22 Ms32 Mnl2 Mlock2 Mhead2 Mnext2 Mtab2 SOK2].
  assert (Mslot2 : rdn RSEGS m2 (Z_to_bv 64 0xf6850) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat n)))).
  { erewrite frame_mod_rdn; [exact Mslot | exact FM2 | outside_tac | nowrap_tac]. }
  assert (R28 : getr regs2 8 = Z_to_bv 64 0xf684c) by (rewrite (R2cs 8%bv) by (cbn; tauto); exact H8).
  assert (R218 : getr regs2 18 = Z_to_bv 64 0xf6848) by (rewrite (R2cs 18%bv) by (cbn; tauto); exact H18).
  assert (R24 : getr regs2 4 = getr regs 4) by (rewrite (R2cs 4%bv) by (cbn; tauto); exact H4).
  assert (R23 : getr regs2 3 = getr regs 3) by (rewrite (R2cs 3%bv) by (cbn; tauto); exact H3).

  assert (P3 : exists regs3,
     msteps RSEGS (mkst regs2 (Z_to_bv 64 0xa6f34) m2 rom)
                  (mkst regs3 (0xa6f48 : word)
                        (wbytes m2 (Z_to_bv 64 0xf6850) (word_to_le_bytes 4 (v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1)))) rom)
     /\ getr regs3 2 = Z_to_bv 64 (bv_unsigned sp - 64)
     /\ getr regs3 8 = Z_to_bv 64 0xf684c /\ getr regs3 18 = Z_to_bv 64 0xf6848
     /\ getr regs3 10 = Z_to_bv 64 (Z.of_nat n)
     /\ getr regs3 12 = v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1)
     /\ getr regs3 4 = getr regs 4 /\ getr regs3 3 = getr regs 3).
  { eexists. split.
    - replace (Z_to_bv 64 0xa6f34) with (0xa6f34 : word) by (apply bv_eq; reflexivity).
      stepn F_a5144 D_a5144. rewrite R28.
      stepn F_a5148 D_a5148.
      stepn F_b6694 D_b6694.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_b6698 | reflexivity | exact D_b6698 | gres; imm_norm; addr_norm; rdn_solve]
        | step_simpl]; vnorm.
      stepb_tk F_b669c D_b669c ltac:(cond_compute).
      stepret F_b688c D_b688c (0xa6f3c : word) ltac:(bveq).
      stepLD F_a514c D_a514c (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat n))) (Z_to_bv 64 (Z.of_nat n))
        ltac:(addr_norm; exact Mslot2) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small (Z.of_nat n)) by lia.
      stepn F_a5150 D_a5150.
      stepST F_a5154 D_a5154 (Z_to_bv 64 0xf6850) (v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1)) ltac:(sok_data).
      apply mst_refl.
    - repeat split; gres; try reflexivity; try assumption. }
  destruct P3 as (regs3 & RUN3 & G2 & G8 & G18 & G10 & G12 & G4 & G3).
  set (m3 := wbytes m2 (Z_to_bv 64 0xf6850) (word_to_le_bytes 4 (v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1)))) in *.
  assert (FM3 : frame_mod m2 m3 [(Z_to_bv 64 0xf6850, 4%Z)]).
  { subst m3. pose proof (frame_mod_wbytes m2 (Z_to_bv 64 0xf6850) (word_to_le_bytes 4 (v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1)))) as W.
    rewrite length_N_to_le_bytes in W. apply W. u_norm. lia. }
  exists regs3, m3.
  split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2| exact RUN3]. }
  split; [exact G2|]. split; [exact G8|]. split; [exact G18|]. split; [exact G10|]. split; [exact G12|].
  split; [exact G4|]. split; [exact G3|].
  split.
  { constructor.
    1-9: (erewrite frame_mod_rdn; [eassumption | exact FM3 | outside_tac | nowrap_tac]).
    - intros i f' a' Hi. destruct (Mtab2 i f' a' Hi) as [B1 B2].
      assert (Z.of_nat i < 32)%Z by (pose proof (proj1 (nth_error_Some hs i) ltac:(congruence)); lia).
      split; (erewrite frame_mod_rdn; [eassumption | exact FM3 | outside_tac | nowrap_tac]).
    - eapply frame_mod_store_ok; eassumption. }
  split.
  { subst m3. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (v_addiw (Z_to_bv 64 (Z.of_nat n)) (-1))) m2 (Z_to_bv 64 0xf6850)) as W.
    rewrite length_N_to_le_bytes in W. apply W. u_norm. lia. }
  split.
  { eapply frame_mod_weaken; [| exact (frame_mod_trans _ _ _ _ _ FM2 FM3)].
    unfold RS_all. intros x Hx. cbn [outside app] in *. unfold in_rng, LIBENV_LO, LIBENV_LEN, HSCR, AX in *.
    revert Hx. unorm. intros Hx. repeat split; try exact I; lia. }
  { eapply (HInv_stable m2 m3 sp); [exact SPlo | exact HI2|].
    eapply frame_mod_weaken; [| exact FM3]. intros x Hx. cbn [outside] in *. unfold in_rng, AX in *.
    revert Hx. unorm. intros Hx. repeat split; try exact I; lia. }
Qed.

Lemma foe_fin : forall regs m,
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0xf684c -> getr regs 18 = Z_to_bv 64 0xf6848 ->
  getr regs 10 = Z_to_bv 64 0 ->
  foe_mem m sp s0v s1v s2v s3v hs ->
  exists regs' m',
    msteps RSEGS (mkst regs (0xa6f48 : word) m rom) (mkst regs' (0xa71c4 : word) m' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3
    /\ frame_mod m m' [(Z_to_bv 64 AX, 0x224%Z)].
Proof.
  intros regs m Hsp Hs0 Hs2 Ha0 [Mra Ms0 Ms1 Ms2 Ms3 Mnl Mlock Mhead Mnext Mtab SOK].
  eexists.
  exists (wbytes (wbytes (wbytes m (Z_to_bv 64 0xf6850) (word_to_le_bytes 4 (Z_to_bv 64 32)))
                          (Z_to_bv 64 0xf6858) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                 (Z_to_bv 64 0xf6848) [Z_to_bv 8 1]).
  split.
  - stepb_ft F_a5158 D_a5158 ltac:(rewrite Ha0; vm_compute; reflexivity).
    stepLD8 F_a515c D_a515c (Z_to_bv 64 0xf6860).
    stepn F_a5160 D_a5160.
    stepLD8 F_a5100 D_a5100 (Z_to_bv 64 0).
    stepn F_a5104 D_a5104.
    stepST F_a5108 D_a5108 (Z_to_bv 64 0xf6850) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_a510c D_a510c (Z_to_bv 64 0xf6858) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_a5110 D_a5110 ltac:(cond_compute).
    stepn F_a5164 D_a5164.
    stepST F_a5168 D_a5168 (Z_to_bv 64 0xf6848) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_a516c D_a516c. rewrite Hs0.
    stepLD8 F_a5170 D_a5170 (Z_to_bv 64 0xa71c4).
    stepLD8 F_a5174 D_a5174 s0v.
    stepLD8 F_a5178 D_a5178 s1v.
    stepLD8 F_a517c D_a517c s2v.
    stepLD8 F_a5180 D_a5180 s3v.
    stepn F_a5184 D_a5184. sp_renorm.
    stepn F_a5188 D_a5188.
    stepLD F_b691c D_b691c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_b6920 D_b6920 ltac:(cond_compute).
    stepret F_b6924 D_b6924 (0xa71c4 : word) ltac:(bveq).
    apply mst_refl.
  - repeat (split; [solve [gres; first [reflexivity | assumption | rewrite Hsp; unfold v_addi; f_equal; u_norm; lia]] |]).
    eapply frame_mod_weaken; [| eapply frame_mod_trans; [eapply frame_mod_trans|]; apply frame_mod_wbytes; zsimp; lia].
    intros x Hx. cbn [outside app] in *. unfold in_rng, AX in *. revert Hx. zsimp. unorm. intros Hx. repeat split; try exact I; lia.
Qed.

Ltac fm_to_all :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold RS_all in *; cbn [outside app] in *; unfold in_rng, LIBENV_LO, LIBENV_LEN, HSCR, AX in *;
  revert Hx; zsimp; unorm; intros Hx; repeat split; try exact I; lia.

Lemma foe_loop : forall n regs m,
  (n < length hs)%nat ->
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0xf684c -> getr regs 18 = Z_to_bv 64 0xf6848 ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
  foe_mem m sp s0v s1v s2v s3v hs ->
  rdn RSEGS m (Z_to_bv 64 0xf6850) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat n))) ->
  HInv m ->
  exists regs' m',
    msteps RSEGS (mkst regs (0xa6f10 : word) m rom) (mkst regs' (0xa71c4 : word) m' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3
    /\ frame_mod m m' RS_all /\ HInv m'.
Proof.
  induction n as [|n IH]; intros regs m Hn Hsp Hs0 Hs2 Ha2 FM Mslot HI;
    destruct (foe_body _ regs m Hn Hsp Hs0 Hs2 Ha2 FM Mslot HI)
      as (regs1 & m1 & RUN1 & G2 & G8 & G18 & G10 & G12 & G4 & G3 & FM1 & Mslot1 & FR1 & HI1).
  -
    destruct (foe_fin regs1 m1 G2 G8 G18 G10 FM1) as (regs2 & m2 & RUN2 & Q2 & Q8 & Q9 & Q18 & Q19 & Q4 & Q3 & FR2).
    exists regs2, m2.
    split; [eapply msteps_trans; eassumption|].
    split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|].
    split; [congruence|]. split; [congruence|].
    split.
    + eapply frame_mod_trans_same; [exact FR1|]. eapply frame_mod_weaken; [| exact FR2]. fm_to_all.
    + eapply (HInv_stable m1 m2 sp); [exact SPlo | exact HI1|]. eapply frame_mod_weaken; [| exact FR2].
      intros x Hx. cbn [outside] in *. unfold in_rng, AX in *. revert Hx. unorm. intros Hx. repeat split; try exact I; lia.
  -
    assert (HnZ : (1 <= Z.of_nat (S n) < 2147483648)%Z) by lia.
    rewrite (v_addiw_m1 _ HnZ) in G12, Mslot1.
    replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n) in G12, Mslot1 by lia.
    assert (B : msteps RSEGS (mkst regs1 (0xa6f48 : word) m1 rom) (mkst regs1 (0xa6f10 : word) m1 rom)).
    { stepb_tk F_a5158 D_a5158 ltac:(rewrite G10; apply c_lts_0_pos; u_norm; lia). apply mst_refl. }
    destruct (IH regs1 m1 ltac:(lia) G2 G8 G18 G12 FM1 Mslot1 HI1) as (regs2 & m2 & RUN2 & Q2 & Q8 & Q9 & Q18 & Q19 & Q4 & Q3 & FR2 & HI2).
    exists regs2, m2.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; eassumption|].
    split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|].
    split; [congruence|]. split; [congruence|].
    split; [eapply frame_mod_trans_same; eassumption | exact HI2].
Qed.

Theorem wF : forall regs mem,
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 1 = Z_to_bv 64 0xa71c4 ->
  getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xf6a93) 1%nat = Some [Z_to_bv 8 0] ->
  atexit_state mem hs -> HInv mem ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0xa6eb4 : word) mem rom) (mkst regs' (0xa71c4 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3
    /\ frame_mod mem mem' RS_all /\ HInv mem'.
Proof.
  intros regs mem Hsp Hra Hs0 Hs1 Hs2 Hs3 SOK Mnl AS HI.
  destruct (Nat.eq_dec (length hs) 0) as [E0|E0].
  -
    apply length_zero_iff_nil in E0. rewrite E0 in AS.
    destruct (wF0 regs mem rom sp s0v s1v s2v s3v Hsp Hra Hs0 Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl AS)
      as (regs1 & RUN & Q2 & Q8 & Q9 & Q18 & Q19 & Q4 & Q3).
    exists regs1, (mem_wF0 mem sp s0v s1v s2v s3v).
    split; [exact RUN|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|].
    split; [exact Q4|]. split; [exact Q3|].
    eassert (FR : frame_mod mem (mem_wF0 mem sp s0v s1v s2v s3v) _).
    { unfold mem_wF0. repeat (apply fm_wb; [| zsimp; lia]). apply (frame_mod_refl _ []). }
    split.
    + eapply frame_mod_weaken; [| exact FR]. fm_to_all.
    + eapply (HInv_stable mem _ sp); [exact SPlo | exact HI|]. eapply frame_mod_weaken; [| exact FR].
      intros x Hx. cbn [outside app] in *. unfold in_rng, AX in *. revert Hx. zsimp. unorm. intros Hx. repeat split; try exact I; lia.
  -
    destruct (atexit_state_nonempty mem hs ltac:(intros ->; apply E0; reflexivity) AS) as (Mlock & Mhead & Mslot & Mnext & Mtab).
    assert (K1 : (1 <= Z.of_nat (length hs) <= 32)%Z) by lia.
    set (k := Z.of_nat (length hs)) in *.
    set (m0 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
          (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xa71c4)))
          (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 s0v))
          (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
          (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
          (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
          (Z_to_bv 64 0xf6850) (word_to_le_bytes 4 (Z_to_bv 64 (k - 1)))).
    assert (P0 : exists regs0,
       msteps RSEGS (mkst regs (0xa6eb4 : word) mem rom) (mkst regs0 (0xa6f10 : word) m0 rom)
       /\ getr regs0 2 = Z_to_bv 64 (bv_unsigned sp - 64)
       /\ getr regs0 8 = Z_to_bv 64 0xf684c /\ getr regs0 18 = Z_to_bv 64 0xf6848
       /\ getr regs0 12 = Z_to_bv 64 (k - 1)
       /\ getr regs0 4 = getr regs 4 /\ getr regs0 3 = getr regs 3).
    { subst m0. eexists. split.
      - stepn F_a50c4 D_a50c4. rewrite Hsp. sp_renorm.
        stepST F_a50c8 D_a50c8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xa71c4) ltac:(sok_stack SOK).
        stepST F_a50cc D_a50cc (Z_to_bv 64 (bv_unsigned sp - 32)) s0v ltac:(sok_stack SOK).
        stepST F_a50d0 D_a50d0 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
        stepST F_a50d4 D_a50d4 (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
        stepST F_a50d8 D_a50d8 (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
        stepn F_a50dc D_a50dc.
        stepn F_a50e0 D_a50e0.
        stepn F_a50e4 D_a50e4.
        stepn F_a50e8 D_a50e8.
        stepn F_a50ec D_a50ec.
        stepn F_b6694 D_b6694.
        chain_step; [reflexivity
          | eapply step_lb with (b := Z_to_bv 8 0);
            [exact F_b6698 | reflexivity | exact D_b6698 | gres; imm_norm; addr_norm; rdn_solve]
          | step_simpl]; vnorm.
        stepb_tk F_b669c D_b669c ltac:(cond_compute).
        stepret F_b688c D_b688c (0xa6ee0 : word) ltac:(bveq).

        stepLD8 F_a50f0 D_a50f0 (Z_to_bv 64 0xf6860).
        stepb_ft F_a50f4 D_a50f4 ltac:(cond_compute).
        stepLD F_a50f8 D_a50f8 (word_to_le_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 64 k)
          ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
        rewrite (v_lw_small k) by lia.
        stepn F_a50fc D_a50fc.

        stepn F_a5114 D_a5114. rewrite (v_addiw_m1 k) by lia.
        stepST F_a5118 D_a5118 (Z_to_bv 64 0xf6850) (Z_to_bv 64 (k - 1)) ltac:(sok_data).
        stepb_ft F_a511c D_a511c ltac:(apply c_lts_0_pos; u_norm; lia).
        apply mst_refl.
      - repeat (split; [solve [gres; first [reflexivity | assumption]] |]). gres; reflexivity. }
    destruct P0 as (regs0 & RUN0 & G2 & G8 & G18 & G12 & G4 & G3).
    eassert (FR0 : frame_mod mem m0 _).
    { subst m0. repeat (apply fm_wb; [| zsimp; lia]). apply (frame_mod_refl _ []). }
    assert (FM0 : foe_mem m0 sp s0v s1v s2v s3v hs).
    { subst m0. constructor; try rdn_solve.
      - intros i f a Hi. destruct (Mtab i f a Hi) as [B1 B2].
        assert (Z.of_nat i < 32)%Z by (pose proof (proj1 (nth_error_Some hs i) ltac:(congruence)); lia).
        split; repeat rdn_peel1; assumption.
      - store_ok_peel. exact SOK. }
    assert (Mslot0 : rdn RSEGS m0 (Z_to_bv 64 0xf6850) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (k - 1)))).
    { subst m0. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 (k - 1)))) as W.
      rewrite length_N_to_le_bytes in W. apply W. u_norm. lia. }
    assert (HI0 : HInv m0).
    { eapply (HInv_stable mem m0 sp); [exact SPlo | exact HI|]. eapply frame_mod_weaken; [| exact FR0].
      intros x Hx. cbn [outside app] in *. unfold in_rng, AX in *. revert Hx. zsimp. unorm. intros Hx. repeat split; try exact I; lia. }
    replace (k - 1)%Z with (Z.of_nat (Nat.pred (length hs))) in G12, Mslot0 by (subst k; lia).
    destruct (foe_loop (Nat.pred (length hs)) regs0 m0 ltac:(subst k; lia) G2 G8 G18 G12 FM0 Mslot0 HI0)
      as (regs2 & m2 & RUN2 & Q2 & Q8 & Q9 & Q18 & Q19 & Q4 & Q3 & FR2 & HI2).
    exists regs2, m2.
    split; [eapply msteps_trans; eassumption|].
    split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|].
    split; [congruence|]. split; [congruence|].
    split; [| exact HI2].
    eapply frame_mod_trans_same; [| exact FR2]. eapply frame_mod_weaken; [| exact FR0]. fm_to_all.
Qed.

End Loop.

End FPX_2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
