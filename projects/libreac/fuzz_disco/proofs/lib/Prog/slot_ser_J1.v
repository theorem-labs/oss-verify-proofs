From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import json_scalar_c jtok_is_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb slot_ser_Pq slot_ser_ws slot_ser_J0.
Import ListNotations.
Open Scope Z_scope.

Definition img8 (a : Z) : list byte :=
  map (fun k => match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat k)) with Some x => x | None => Z_to_bv 8 0 end) (seq 0 8).

Lemma img8_len : forall a, length (img8 a) = 8%nat.
Proof. intros a. unfold img8. rewrite length_map, length_seq. reflexivity. Qed.

Definition nm_at (m : word -> option byte) (TA : Z) (txt : list Z) : Prop :=
  bytes_at rsegs m TA (pf_bytes txt ++ Z_to_bv 8 0 :: img8 (TA + Z.of_nat (length txt) + 1)).

Ltac nm_tac := intros m MI; unfold nm_at; apply ro_at;
  [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity].

Lemma nm_mac : forall m, mem_inv rsegs m -> nm_at m 0x1049e k_mac. Proof. nm_tac. Qed.
Lemma nm_role : forall m, mem_inv rsegs m -> nm_at m 0x1029e k_role. Proof. nm_tac. Qed.
Lemma nm_model : forall m, mem_inv rsegs m -> nm_at m 0x10459 k_model. Proof. nm_tac. Qed.
Lemma nm_width : forall m, mem_inv rsegs m -> nm_at m 0x10429 k_width. Proof. nm_tac. Qed.
Lemma nm_owned : forall m, mem_inv rsegs m -> nm_at m 0x104cc k_owned. Proof. nm_tac. Qed.
Lemma nm_age : forall m, mem_inv rsegs m -> nm_at m 0x1042f k_age_ms. Proof. nm_tac. Qed.

Lemma pf_unsigned : forall B, Forall (fun c => 0 <= c < 256) B -> map bv_unsigned (pf_bytes B) = B.
Proof.
  induction B as [|x B IH]; intros F; [reflexivity|]. inversion F; subst.
  unfold pf_bytes in *. cbn [map]. rewrite IH by assumption. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma pf_text : forall m b B, bytes_at rsegs m b (pf_bytes (B ++ [0])) -> bytes_at rsegs m b (pf_bytes B).
Proof.
  intros m b B H. unfold pf_bytes in H. rewrite map_app in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma js_call : json_scalar_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo X b i V j k s l : Z) (B : list Z)
    (Q : machine_state -> Prop),
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 b -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 (jlen B) -> a3 = Z_to_bv 64 V ->
  jscalar B i = Some (j, k, s, l) -> 0 <= i ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  wr_at rsegs m V 20 -> X <= V -> V + 20 <= 2 ^ 63 ->
  bytes_at rsegs m JSON_SCALAR_L js_table -> 0x51d38 <= lo ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + JSON_SCALAR_K <= X ->
  (forall (m' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     munch [(X - JSON_SCALAR_K, X); (V, V + 20)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo X ->
     bytes_at rsegs m' V (le8 (Z_to_bv 64 (b + s)) ++ le8 (Z_to_bv 64 l) ++ le4 (Z_to_bv 64 k)) ->
     evt rsegs Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 j) y11 y12 y13 y14 y15 y16 y17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 JSON_SCALAR) fc None m (seg_rom rsegs)).
Proof.
  intros JS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b i V j k s l B Q Esp Ea0 Ea1 Ea2 Ea3 JSC Hi Hb Hbl FB BB WV HV1 HV2 JT HI MI ST HK K.
  pose proof (pf_text m b B BB) as BT.
  pose proof (bytes_at_bound rsegs m b _ BT) as BTb. rewrite length_pf_bytes in BTb.
  pose proof (js_rng B i j k s l JSC) as Hr.
  pose proof ST as (STa & STb & _).
  unfold JSON_SCALAR_K in *. unfold jlen in *.
  subst sp a0 a1 a2 a3.
  eapply evt_cut.
  { apply (JS ra (Z_to_bv 64 X) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 i) (Z_to_bv 64 (Z.of_nat (length B)))
              (Z_to_bv 64 V) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (pf_bytes B));
      rewrite ?(unsigned_lit X), ?(unsigned_lit b), ?(unsigned_lit i), ?(unsigned_lit V),
        ?(unsigned_lit (Z.of_nat (length B))) by lia; unfold JSON_SCALAR_K, JSON_SCALAR_L in *.
    - rewrite length_pf_bytes. reflexivity.
    - lia.
    - intros _. split; [exact BT | left; lia].
    - exact WV.
    - right; lia.
    - exact JT.
    - left; lia.
    - exact MI.
    - exact ST.
    - lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & WM & MI' & ST' & R).
  subst ms'. rewrite pf_unsigned, (unsigned_lit i), JSC in R by (first [exact FB | lia]).
  destruct R as (Ea & MU & BV). subst a0'.
  rewrite (unsigned_lit X) in MU, ST' by lia. rewrite (unsigned_lit V) in MU, BV by lia.
  rewrite (unsigned_lit b) in BV by lia.
  apply K; assumption.
Qed.

Lemma key_slot : forall m X b ks kl vpk, length vpk = 4%nat ->
  rw_cells rsegs m (X + 992) [CB 20 (le8 (Z_to_bv 64 (b + ks)) ++ le8 (Z_to_bv 64 kl) ++ le4 (Z_to_bv 64 1))] ->
  rw_cells rsegs m (X + 1012) [CB 4 vpk] -> bytes_at rsegs m (X + 992) (slot24 b vpk (1, ks, kl)).
Proof.
  intros m X b ks kl vpk L C1 C2. destruct C1 as [[_ B1] _]. destruct C2 as [[_ B2] _].
  cbn [cells_bytes cbytes] in B1, B2. rewrite app_nil_r in B1, B2.
  unfold slot24, tv_kind. cbn [fst snd Z.eqb]. rewrite !app_assoc.
  apply bytes_at_app. split; [rewrite <- !app_assoc; exact B1|].
  match goal with |- bytes_at _ _ ?a _ => replace a with (X + 1012) by (rewrite ?length_app, ?length_le8, ?length_le4; lia) end.
  exact B2.
Qed.

Ltac jt_side := unfold JTOK_IS_K in *; first
  [ reflexivity | assumption
  | (cbn [tv_kind fst snd]; lia)
  | (right; cbn [fst snd]; unfold jlen in *; lia)
  | (unfold k_mac, k_role, k_model, k_width, k_owned, k_age_ms; repeat (apply Forall_cons; [lia|]); apply Forall_nil)
  | (rewrite img8_len; unfold k_mac, k_role, k_model, k_width, k_owned, k_age_ms;
     cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
     match goal with |- ?a mod 8 <= _ => pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia end)
  | (left; rewrite ?img8_len; unfold k_mac, k_role, k_model, k_width, k_owned, k_age_ms;
     cbn [length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
  | (right; lia)
  | (unfold jlen in *; lia)
  | lia ].

Ltac jt_fin MU0 WM0 MI ST := apply evt_done; do 5 eexists; exists (Z_to_bv 64 0); do 11 eexists;
  split; [exact MU0|]; split; [exact WM0|]; split; [exact MI|]; split; [exact ST|].

Ltac jt_fin0 MU0 WM0 MI ST := apply evt_done; do 17 eexists; split; [exact MU0|]; split; [exact WM0|];
  split; [exact MI|]; split; [exact ST|].

Lemma slot_jt : jtok_is_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo X b cur ks kl : Z) (B : list Z) (vpk : list byte),
  sp = Z_to_bv 64 X -> s5 = Z_to_bv 64 cur -> s10 = Z_to_bv 64 (cur + 24) -> s9 = Z_to_bv 64 (cur + 48) ->
  s11 = Z_to_bv 64 (cur + 72) ->
  0 <= ks -> 0 <= kl -> ks + kl <= jlen B -> length vpk = 4%nat ->
  0 < b -> b + jlen B + 1 <= lo -> Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  rw_cells rsegs m (X + 992) [CB 20 (le8 (Z_to_bv 64 (b + ks)) ++ le8 (Z_to_bv 64 kl) ++ le4 (Z_to_bv 64 1))] ->
  rw_cells rsegs m (X + 1012) [CB 4 vpk] ->
  rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 (cur + 96))] -> rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (cur + 120))] ->
  mem_inv rsegs m -> stk rsegs m lo X -> lo + 112 <= X -> 0x51d38 <= lo -> X + 2592 < 2 ^ 63 ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte),
       munch [(X - 32, X)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0'
                     (match slot_of B (1, ks, kl) with Some k => Z_to_bv 64 (cur + 24 * Z.of_nat k) | None => a1' end)
                     a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 (match slot_of B (1, ks, kl) with Some _ => 0x13b7c | None => 0x13b9c end))
                fc None m' (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ad4) fc None m (seg_rom rsegs)).
Proof.
  intros JT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo X b cur ks kl B vpk Esp Es5 Es10 Es9 Es11 Hks Hkl Hkb LV Hb Hbl FB BB CK CV C216 C192 MI ST HK HI HX.
  subst sp s5 s10 s9 s11.
  assert (LBB : Z.of_nat (length (pf_bytes (B ++ [0]))) = jlen B + 1)
    by (rewrite length_pf_bytes, length_app; unfold jlen; cbn [length]; lia).
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(X - 32, X)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
  pose proof (nm_mac m MI) as N. unfold nm_at in N. pose proof (key_slot m X b ks kl vpk LV CK CV) as KB.
  step. step. step. step. step.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 992) (TA := 0x1049e) (buf := b) (kind := 1) (B := B)
    (text := k_mac) (t := (1, ks, kl)) (vpad := vpk) (slack := img8 (0x1049e + Z.of_nat (length k_mac) + 1));
    [jt_side .. | ].
  intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU1 WM1 MI1 ST1.
  rewrite (ret_pc_even 0x13ae8) by (first [lia | reflexivity]).
  unfold JTOK_IS_K in MU1. clear N KB. transport_after_call rsegs m m1 MU1 WM1. clear MU1 WM1 MI.
  step. step.
  destruct (jtok_is B (1, ks, kl) 1 k_mac) eqn:J1; cbn [Z.b2z]; rewrite eqb_lit by lia; cbn [Z.eqb negb]; cbv iota.
  { assert (SO : slot_of B (1, ks, kl) = Some 0%nat) by (unfold slot_of, slot_from, keys; rewrite J1; reflexivity).
    rewrite SO. jt_fin MU0 WM0 MI1 ST1. replace (Z_to_bv 64 (cur + 24 * Z.of_nat 0)) with (Z_to_bv 64 cur) by (f_equal; lia).
    reflexivity. }
  pose proof (nm_role m1 MI1) as N. unfold nm_at in N. pose proof (key_slot m1 X b ks kl vpk LV CK CV) as KB.
  step. step. step. step. step.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 992) (TA := 0x1029e) (buf := b) (kind := 1) (B := B)
    (text := k_role) (t := (1, ks, kl)) (vpad := vpk) (slack := img8 (0x1029e + Z.of_nat (length k_role) + 1));
    [jt_side .. | ].
  intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU2 WM2 MI2 ST2.
  rewrite (ret_pc_even 0x13b04) by (first [lia | reflexivity]).
  unfold JTOK_IS_K in MU2. clear N KB. transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
  step. step.
  destruct (jtok_is B (1, ks, kl) 1 k_role) eqn:J2; cbn [Z.b2z]; rewrite eqb_lit by lia; cbn [Z.eqb negb]; cbv iota.
  { assert (SO : slot_of B (1, ks, kl) = Some 1%nat) by (unfold slot_of, slot_from, keys; rewrite J1, J2; reflexivity).
    rewrite SO. jt_fin MU0 WM0 MI2 ST2. cbn [Z.of_nat Pos.of_succ_nat]. reflexivity. }
  pose proof (nm_model m2 MI2) as N. unfold nm_at in N. pose proof (key_slot m2 X b ks kl vpk LV CK CV) as KB.
  step. step. step. step. step.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 992) (TA := 0x10459) (buf := b) (kind := 1) (B := B)
    (text := k_model) (t := (1, ks, kl)) (vpad := vpk) (slack := img8 (0x10459 + Z.of_nat (length k_model) + 1));
    [jt_side .. | ].
  intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU3 WM3 MI3 ST3.
  rewrite (ret_pc_even 0x13b20) by (first [lia | reflexivity]).
  unfold JTOK_IS_K in MU3. clear N KB. transport_after_call rsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
  step. step.
  destruct (jtok_is B (1, ks, kl) 1 k_model) eqn:J3; cbn [Z.b2z]; rewrite eqb_lit by lia; cbn [Z.eqb negb]; cbv iota.
  { assert (SO : slot_of B (1, ks, kl) = Some 2%nat) by (unfold slot_of, slot_from, keys; rewrite J1, J2, J3; reflexivity).
    rewrite SO. jt_fin MU0 WM0 MI3 ST3. cbn [Z.of_nat Pos.of_succ_nat]. reflexivity. }
  pose proof (nm_width m3 MI3) as N. unfold nm_at in N. pose proof (key_slot m3 X b ks kl vpk LV CK CV) as KB.
  step. step. step. step. step.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 992) (TA := 0x10429) (buf := b) (kind := 1) (B := B)
    (text := k_width) (t := (1, ks, kl)) (vpad := vpk) (slack := img8 (0x10429 + Z.of_nat (length k_width) + 1));
    [jt_side .. | ].
  intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU4 WM4 MI4 ST4.
  rewrite (ret_pc_even 0x13b3c) by (first [lia | reflexivity]).
  unfold JTOK_IS_K in MU4. clear N KB. transport_after_call rsegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
  step. step.
  destruct (jtok_is B (1, ks, kl) 1 k_width) eqn:J4; cbn [Z.b2z]; rewrite eqb_lit by lia; cbn [Z.eqb negb]; cbv iota.
  { assert (SO : slot_of B (1, ks, kl) = Some 3%nat) by (unfold slot_of, slot_from, keys; rewrite J1, J2, J3, J4; reflexivity).
    rewrite SO. jt_fin MU0 WM0 MI4 ST4. cbn [Z.of_nat Pos.of_succ_nat]. reflexivity. }
  pose proof (nm_owned m4 MI4) as N. unfold nm_at in N. pose proof (key_slot m4 X b ks kl vpk LV CK CV) as KB.
  step. step. step. step. step.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 992) (TA := 0x104cc) (buf := b) (kind := 1) (B := B)
    (text := k_owned) (t := (1, ks, kl)) (vpad := vpk) (slack := img8 (0x104cc + Z.of_nat (length k_owned) + 1));
    [jt_side .. | ].
  intros m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU5 WM5 MI5 ST5.
  rewrite (ret_pc_even 0x13b58) by (first [lia | reflexivity]).
  unfold JTOK_IS_K in MU5. clear N KB. transport_after_call rsegs m4 m5 MU5 WM5. clear MU5 WM5 MI4.
  step. step.
  destruct (jtok_is B (1, ks, kl) 1 k_owned) eqn:J5; cbn [Z.b2z]; rewrite eqb_lit by lia; cbn [Z.eqb negb]; cbv iota.
  { assert (SO : slot_of B (1, ks, kl) = Some 4%nat) by (unfold slot_of, slot_from, keys; rewrite J1, J2, J3, J4, J5; reflexivity).
    rewrite SO. jt_fin MU0 WM0 MI5 ST5. cbn [Z.of_nat Pos.of_succ_nat]. reflexivity. }
  pose proof (nm_age m5 MI5) as N. unfold nm_at in N. pose proof (key_slot m5 X b ks kl vpk LV CK CV) as KB.
  step. step. step. step. step.
  eapply (jt_call JT) with (lo := lo) (S := X) (SA := X + 992) (TA := 0x1042f) (buf := b) (kind := 1) (B := B)
    (text := k_age_ms) (t := (1, ks, kl)) (vpad := vpk) (slack := img8 (0x1042f + Z.of_nat (length k_age_ms) + 1));
    [jt_side .. | ].
  intros m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? MU6 WM6 MI6 ST6.
  rewrite (ret_pc_even 0x13b74) by (first [lia | reflexivity]).
  unfold JTOK_IS_K in MU6. clear N KB. transport_after_call rsegs m5 m6 MU6 WM6. clear MU6 WM6 MI5.
  step. step.
  destruct (jtok_is B (1, ks, kl) 1 k_age_ms) eqn:J6; cbn [Z.b2z]; rewrite eqb_lit by lia; cbn [Z.eqb negb]; cbv iota.
  { assert (SO : slot_of B (1, ks, kl) = Some 5%nat) by (unfold slot_of, slot_from, keys; rewrite J1, J2, J3, J4, J5, J6; reflexivity).
    rewrite SO. jt_fin MU0 WM0 MI6 ST6. cbn [Z.of_nat Pos.of_succ_nat]. reflexivity. }
  assert (SO : slot_of B (1, ks, kl) = None) by (unfold slot_of, slot_from, keys; rewrite J1, J2, J3, J4, J5, J6; reflexivity).
  rewrite SO. jt_fin0 MU0 WM0 MI6 ST6. reflexivity.
Qed.
