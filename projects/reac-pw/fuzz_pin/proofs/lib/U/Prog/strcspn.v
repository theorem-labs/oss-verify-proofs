(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/Ref/F_strspn.v, with its module paths, module names, addresses and numbers changed; 344 of its 454 lines of code are new or changed and 231 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import Tac Arr Bytes Frame.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import memset_c strchrnul_c strcspn_c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac addr_tac := first [ symmetry; apply wa_of_var; lia | unfold wa; f_equal; lia ].
Ltac weq := first [ reflexivity | f_equal; lia | rewrite ?unsigned_lit by lia; f_equal; lia
                  | symmetry; apply wa_of_var; rewrite ?unsigned_lit by lia; lia ].
Ltac beta_goal := lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
Ltac ret_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

Definition memb (set : list byte) (x : byte) : bool :=
  existsb (fun c => Z.eqb (bv_unsigned c) (bv_unsigned x)) set.

Lemma cspn_cons : forall set x s, cspn_len set (x :: s) = if memb set x then O else S (cspn_len set s).
Proof. reflexivity. Qed.

Lemma cspn_le : forall set s, (cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; [cbn; lia|]. rewrite cspn_cons. cbn [length]. destruct (memb set x); lia. Qed.

Lemma cspn_prefix : forall set s i, (i <= length s)%nat ->
  (forall j x, (j < i)%nat -> nth_error s j = Some x -> memb set x = false) ->
  (forall x, nth_error s i = Some x -> memb set x = true) ->
  cspn_len set s = i.
Proof.
  intros set s. induction s as [|y s IH]; intros i Hi IN OUT; cbn [length] in Hi.
  - cbn. lia.
  - rewrite cspn_cons. destruct i as [|i].
    + rewrite (OUT y eq_refl). reflexivity.
    + rewrite (IN 0%nat y ltac:(lia) eq_refl). f_equal. apply IH; [lia| |].
      * intros j x Hj Hx. exact (IN (S j) x ltac:(lia) Hx).
      * intros x Hx. exact (OUT x Hx).
Qed.

Lemma cspn_nil : forall s, cspn_len [] s = length s.
Proof. intros s. induction s as [|x s IH]; [reflexivity|]. rewrite cspn_cons. cbn. rewrite IH. reflexivity. Qed.

Lemma cspn_one : forall c s, cspn_len [c] s = strchrnul_idx (bv_unsigned c) s.
Proof.
  intros c s. induction s as [|x s IH]; [reflexivity|].
  rewrite cspn_cons. unfold memb. cbn [existsb]. rewrite orb_false_r.
  unfold strchrnul_idx in *. cbn [find_byte]. rewrite Z.eqb_sym.
  destruct (bv_unsigned x =? bv_unsigned c); [reflexivity|].
  rewrite IH. destruct (find_byte (bv_unsigned c) s); reflexivity.
Qed.

Lemma cspn_small : forall set cb str, (length set <= 1)%nat -> ~ In (Z_to_bv 8 0) set ->
  nth_error (set ++ [Z_to_bv 8 0]) 0 = Some cb ->
  strchrnul_off (bv_unsigned cb) str = Z.of_nat (cspn_len set str).
Proof.
  intros set cb str HL NZ HC. destruct set as [|x [|y r]].
  - cbn in HC. injection HC as <-. rewrite cspn_nil. reflexivity.
  - cbn in HC. injection HC as <-. unfold strchrnul_off.
    assert (X0 : bv_unsigned x <> 0).
    { intros E. apply NZ. left. apply bv_eq. rewrite E. reflexivity. }
    rewrite (proj2 (Z.eqb_neq _ _) X0). rewrite cspn_one. reflexivity.
  - cbn in HL. lia.
Qed.

Definition setw (l : list byte) (k : Z) : Z :=
  fold_left (fun w (b : byte) => if (bv_unsigned b / 64 =? k)%Z then Z.lor w (Z.shiftl 1 (bv_unsigned b mod 64)) else w) l 0%Z.

Lemma setw_nil : forall k, setw [] k = 0%Z. Proof. reflexivity. Qed.
Lemma setw_snoc : forall l b k,
  setw (l ++ [b]) k = (if (bv_unsigned b / 64 =? k)%Z then Z.lor (setw l k) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l k).
Proof. intros. unfold setw. rewrite fold_left_app. reflexivity. Qed.

Lemma lor_range64 : forall a b, (0 <= a < 2^64)%Z -> (0 <= b < 2^64)%Z -> (0 <= Z.lor a b < 2^64)%Z.
Proof. intros. apply lor_lt_pow2; assumption. Qed.

Lemma setw_range : forall l k, (0 <= setw l k < 2^64)%Z.
Proof.
  intros l k. induction l as [|b l IH] using rev_ind; [rewrite setw_nil; lia|].
  rewrite setw_snoc. destruct (bv_unsigned b / 64 =? k)%Z; [| exact IH].
  pose proof (byte_range b). apply lor_range64; [exact IH|].
  rewrite Z.shiftl_1_l. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; Z.div_mod_to_equations; lia].
Qed.

Lemma setw_testbit : forall l k j, (0 <= j < 64)%Z ->
  Z.testbit (setw l k) j = existsb (fun a => (bv_unsigned a / 64 =? k)%Z && (bv_unsigned a mod 64 =? j)%Z) l.
Proof.
  intros l k j Hj. induction l as [|b l IH] using rev_ind; [rewrite setw_nil; apply Z.bits_0|].
  rewrite setw_snoc, existsb_app. cbn [existsb]. rewrite orb_false_r.
  pose proof (byte_range b).
  destruct (Z.eqb_spec (bv_unsigned b / 64) k) as [E|NE].
  - rewrite Z.lor_spec, IH, Z.shiftl_1_l, Z.pow2_bits_eqb by (Z.div_mod_to_equations; lia). cbn [andb]. reflexivity.
  - rewrite IH. cbn [andb]. rewrite orb_false_r. reflexivity.
Qed.

Lemma memb_testbit : forall l x, memb l x = Z.testbit (setw l (bv_unsigned x / 64)) (bv_unsigned x mod 64).
Proof.
  intros l x. pose proof (byte_range x). rewrite setw_testbit by (Z.div_mod_to_equations; lia). unfold memb.
  induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH. f_equal. pose proof (byte_range a).
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned x)) as [E|NE].
  - rewrite E, !Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned a / 64) (bv_unsigned x / 64)); destruct (Z.eqb_spec (bv_unsigned a mod 64) (bv_unsigned x mod 64)); cbn; try reflexivity.
    exfalso. apply NE. Z.div_mod_to_equations. lia.
Qed.

Lemma bidx : forall b, (0 <= b < 256)%Z -> Z.land (Z.shiftr b 3) 18446744073709551608 = (8 * (b / 64))%Z.
Proof.
  intros b Hb. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
  assert (R : (0 <= b / 8 < 32)%Z) by (Z.div_mod_to_equations; lia).
  replace (b / 64)%Z with (b / 8 / 8)%Z by (rewrite Z.div_div by lia; reflexivity).
  set (q := (b / 8)%Z) in *. clearbody q.
  assert (E : exists n, (n < 32)%nat /\ q = Z.of_nat n) by (exists (Z.to_nat q); split; lia).
  destruct E as (n & Hn & ->).
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma bit_of : forall w j, (0 <= w)%Z -> (0 <= j)%Z -> Z.land (Z.shiftr w j) 1 = (if Z.testbit w j then 1 else 0)%Z.
Proof.
  intros w j Hw Hj. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  pose proof (Z.testbit_spec' w j Hj) as E. destruct (Z.testbit w j); cbn [Z.b2z] in E; lia.
Qed.

Lemma firstn_snoc : forall (l : list byte) i b, nth_error l i = Some b -> firstn (S i) l = firstn i l ++ [b].
Proof.
  induction l as [|x l IHl]; intros [|i] b H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IHl i b H). reflexivity.
Qed.

Lemma ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. unfold ro_cells, cells_at. split; [split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma cstr_at : forall (l rest : list byte) i, ~ In (Z_to_bv 8 0) l -> (0 <= i <= Z.of_nat (length l))%Z ->
  exists b, nth_error (l ++ Z_to_bv 8 0 :: rest) (Z.to_nat i) = Some b /\
            ((i < Z.of_nat (length l))%Z -> nth_error l (Z.to_nat i) = Some b) /\
            (bv_unsigned b = 0%Z <-> i = Z.of_nat (length l)).
Proof.
  intros l rest i NZ Hi. destruct (Z.eq_dec i (Z.of_nat (length l))) as [E|NE].
  - exists (Z_to_bv 8 0). subst i. rewrite Nat2Z.id, nth_error_app2, Nat.sub_diag by lia.
    split; [reflexivity|]. split; [lia|]. split; [intros _; reflexivity| intros _; reflexivity].
  - destruct (nth_error l (Z.to_nat i)) as [b|] eqn:E.
    + exists b. split; [rewrite nth_error_app1 by lia; first [exact E| reflexivity]|]. split; [intros _; first [exact E| reflexivity]|].
      split; [|intros X; lia]. intros Hb. exfalso. apply NZ. replace (Z_to_bv 8 0) with b.
      { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hb. reflexivity.
    + apply nth_error_None in E. lia.
Qed.

Lemma nth_none_len : forall (l : list byte), nth_error l (length l) = None.
Proof. intros l. apply nth_error_None. lia. Qed.

Lemma rw_cells_split1 : forall m A c cs B, rw_cells rsegs m A (c :: cs) -> B = A + Z.of_nat (csize c) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m B cs.
Proof.
  intros m A c cs B [[Hwf Hb] (Ha & Hn & Hw)] ->. cbn [cells_wf] in Hwf. destruct Hwf as [Hc Hcs].
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  rewrite cbytes_length in Hb2 by exact Hc.
  cbn [cells_size] in Hn, Hw. split.
  - split. { split. { cbn. split; [exact Hc | exact I]. } cbn [cells_bytes]. rewrite app_nil_r. exact Hb1. }
    cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split. { split; [exact Hcs| exact Hb2]. }
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Hw. lia.
Qed.

Lemma bytes_eq_u : forall l1 l2 : list byte, map (fun b : byte => bv_unsigned b) l1 = map (fun b : byte => bv_unsigned b) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Definition bm (l : list byte) : list cell :=
  [C8 (Z_to_bv 64 (setw l 0)); C8 (Z_to_bv 64 (setw l 1)); C8 (Z_to_bv 64 (setw l 2)); C8 (Z_to_bv 64 (setw l 3))].

Lemma bm0_of : forall m A n bs, rw_cells rsegs m A [CB n bs] -> n = 32%nat ->
  map (fun b : byte => bv_unsigned b) bs = repeat 0 32 -> rw_cells rsegs m A (bm []).
Proof.
  intros m A n bs [[Hwf Hb] Hw] -> HB. split; [split|].
  - cbn. tauto.
  - replace (cells_bytes (bm [])) with (cells_bytes [CB 32 bs]); [exact Hb|].
    apply bytes_eq_u. cbn [cells_bytes cbytes]. rewrite app_nil_r, HB. vm_compute. reflexivity.
  - exact Hw.
Qed.

Lemma bm_snoc : forall l (b : byte) (q : Z), q = (bv_unsigned b / 64)%Z ->
  bm (l ++ [b]) =
    [C8 (Z_to_bv 64 (if (q =? 0)%Z then Z.lor (setw l 0) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 0));
     C8 (Z_to_bv 64 (if (q =? 1)%Z then Z.lor (setw l 1) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 1));
     C8 (Z_to_bv 64 (if (q =? 2)%Z then Z.lor (setw l 2) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 2));
     C8 (Z_to_bv 64 (if (q =? 3)%Z then Z.lor (setw l 3) (Z.shiftl 1 (bv_unsigned b mod 64)) else setw l 3))].
Proof. intros l b q ->. unfold bm. rewrite !setw_snoc. reflexivity. Qed.

Section W.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack set : list byte) (lo : Z) (can : word).
  Hypothesis MSET : memset_contract.
  Hypothesis CHR : strchrnul_contract.
  Notation Sa := (bv_unsigned a0).
  Notation Ca := (bv_unsigned a1).
  Notation SP := (bv_unsigned sp).
  Notation L := (Z.of_nat (length str)).
  Notation K := (Z.of_nat (length set)).
  Notation sfull := (str ++ Z_to_bv 8 0 :: slack).
  Notation afull := (set ++ [Z_to_bv 8 0]).
  Hypothesis SNONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis ANONUL : ~ In (Z_to_bv 8 0) set.
  Hypothesis SLK : (length set <= 1)%nat -> (- (Sa + L + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis LO0 : 0 <= lo.
  Hypothesis LOS : lo + 96 <= SP.
  Hypothesis DS : Sa + L + 1 + Z.of_nat (length slack) <= lo \/ SP <= Sa.
  Hypothesis DC : Ca + K + 1 <= lo \/ SP <= Ca.
  Hypothesis DG : 0x1d590 + 8 <= lo \/ SP <= 0x1d590.
  Hypothesis DK : 0x4eb80 + 8 <= lo \/ SP <= 0x4eb80.
  Hypothesis SB : Sa + L + 1 + Z.of_nat (length slack) <= 2^64.
  Hypothesis CB0 : Ca + K + 1 <= 2^64.

  Notation POST := (strcspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str set lo m).

  Definition MEMS (m1 : word -> option byte) : Prop :=
    mem_inv rsegs m1 /\ bytes_at rsegs m1 Sa sfull /\ bytes_at rsegs m1 Ca afull
    /\ ro_cells rsegs m1 0x1d590 [C8 (Z_to_bv 64 0x4eb80)] /\ ro_cells rsegs m1 0x4eb80 [C8 can]
    /\ stk rsegs m1 lo (SP + -80) /\ munch [(SP - 96, SP)] m m1 /\ wmono rsegs m m1
    /\ rw_cells rsegs m1 (SP + -48) [C8 can; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Ltac mems_tac := unfold MEMS; repeat (lazymatch goal with |- _ /\ _ => split end); assumption.

  Notation STc pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -80)) gp tp x5 x6 x7 a0 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x4eb80) x19
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Lemma fin_ret : forall m1 cs x1 x5 x6 x7 x9 (w : word) x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) cs -> cells_size cs = 32%nat ->
    w = Z_to_bv 64 (Z.of_nat (cspn_len set str)) ->
    evt rsegs POST (STc 0x1b224 m1 x1 x5 x6 x7 x9 w x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof using All.
    intros m1 cs x1 x5 x6 x7 x9 w x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1 & FT) FB CS ->.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FB ST1 (bv_unsigned sp + -48).
    release_frame FT ST1 (bv_unsigned sp).
    finish.
  Qed.

  Lemma fin_sub : forall m1 cs x1 x5 x6 x7 x9 (w : word) x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (r : Z),
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) cs -> cells_size cs = 32%nat ->
    w = Z_to_bv 64 (Sa + r) -> r = Z.of_nat (cspn_len set str) ->
    evt rsegs POST (STc 0x1b220 m1 x1 x5 x6 x7 x9 w x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof using All.
    intros m1 cs x1 x5 x6 x7 x9 w x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 r MM FB CS -> ->.
    pose proof (cspn_le set str) as SL.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    zstep.
    eapply fin_ret; [exact MM| exact FB| exact CS| weq].
  Qed.

  Lemma fin : forall m1 cs x1 x5 x6 x7 x9 (w : word) x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (r : Z),
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) cs -> cells_size cs = 32%nat ->
    w = Z_to_bv 64 (Sa + r) -> r = Z.of_nat (cspn_len set str) ->
    evt rsegs POST (STc 0x1b214 m1 x1 x5 x6 x7 x9 w x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof using All.
    intros m1 cs x1 x5 x6 x7 x9 w x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 r MM FB CS HW HR.
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1 & FT).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    zstep. zstep. zstep. if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }
    eapply fin_sub with (r := r); [exact MM| exact FB| exact CS| exact HW| exact HR].
  Qed.

  Lemma fin2 : forall m1 cs x1 x5 x6 x7 x9 x10 x11 x12 (w : word) x14 x15 x16 x17 x19 x28 x29 x30 x31 (r : Z),
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) cs -> cells_size cs = 32%nat ->
    w = Z_to_bv 64 (Sa + r) -> r = Z.of_nat (cspn_len set str) ->
    evt rsegs POST (STc 0x1b240 m1 x1 x5 x6 x7 x9 x10 x11 x12 w x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof using All.
    intros m1 cs x1 x5 x6 x7 x9 x10 x11 x12 w x14 x15 x16 x17 x19 x28 x29 x30 x31 r MM FB CS -> HR.
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1 & FT).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    pose proof (cspn_le set str) as SL.
    zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC; [| exfalso; apply KC; reflexivity].
    eapply fin_sub with (r := r); [exact MM| exact FB| exact CS| subst r; weq| exact HR].
  Qed.

  Lemma via_chrnul : forall m1 (cb : byte) junk x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    (length set <= 1)%nat -> nth_error afull 0 = Some cb ->
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) [CB 32 junk] ->
    evt rsegs POST (STc 0x1b20c m1 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (bv_unsigned cb)) x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof using All.
    intros m1 cb junk x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 HL HCB
      (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1 & FT) FB.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    pose proof (byte_range cb) as CBR.
    pose proof CHR as CH. unfold strchrnul_contract in CH.
    zstep. zstep.
    eapply evt_cut.
    { eapply CH with (str := str) (slack := slack) (lo := lo); rewrite ?unsigned_lit by lia;
        first [exact ST1 | exact STR1 | exact SNONUL | exact (SLK HL) | exact MI1 | lia]. }
    intros ms' PO. unfold strchrnul_post in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & E & MUc & WMc & MIc & STK2 & BYc).
    subst ms'.
    rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in STK2 by lia.
    transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI1.
    ret_lit.
    eapply fin with (r := strchrnul_off (bv_unsigned (Z_to_bv 64 (bv_unsigned cb)) mod 256) str).
    - mems_tac.
    - exact FB.
    - reflexivity.
    - reflexivity.
    - rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. apply cspn_small; assumption.
  Qed.

  Lemma scan_loop : forall (k : nat) (i : Z) m1 (b : byte) x1 x5 x6 x7 x9 x10 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w : word),
    Z.to_nat (L - i) = k -> (0 <= i < L)%Z -> nth_error str (Z.to_nat i) = Some b ->
    (forall j x, (j < Z.to_nat i)%nat -> nth_error str j = Some x -> memb set x = false) ->
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) (bm set) -> w = Z_to_bv 64 (Sa + i) ->
    evt rsegs POST (STc 0x1b1dc m1 x1 x5 x6 x7 x9 x10 (Z_to_bv 64 (SP + -80)) (Z_to_bv 64 (bv_unsigned b)) w
                        x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof using All.
    induction k as [|k IH]; intros i m1 b x1 x5 x6 x7 x9 x10 x14 x15 x16 x17 x19 x28 x29 x30 x31 w Hk Hi HB IN MM FR Hw; [lia|].
    subst w.
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1 & FT).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    pose proof (byte_range b) as BR. pose proof (setw_range set (bv_unsigned b / 64)) as WR.
    pose proof (cspn_le set str) as SL.
    unfold bm in FR.
    zstep. zstep. zstep. rewrite ?unsigned_lit by lia. rewrite (bidx (bv_unsigned b)) by lia.
    set (q := (bv_unsigned b / 64)%Z) in *.
    assert (KQ : evt rsegs POST (STc 0x1b1ec m1 x1 x5 x6 x7 x9 (Z_to_bv 64 (setw set q)) (Z_to_bv 64 (SP + -80))
                                     (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (Sa + i)) x14 x15 x16 x17 x19 x28 x29 x30 x31)).
    { zstep. zstep.
      replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
      rewrite bit_of by lia. unfold q. rewrite <- memb_testbit.
      zstep. destruct (memb set b) eqn:INB.
      - if_true.
        eapply fin2 with (r := i); [exact MM| exact FR| reflexivity| reflexivity|].
        rewrite (cspn_prefix set str (Z.to_nat i)); [lia| lia| exact IN|].
        intros x Hx. rewrite HB in Hx. inversion Hx. subst. exact INB.
      - if_false.
        destruct (cstr_at str slack (i + 1) SNONUL ltac:(lia)) as (b' & HN & HB' & NZ'). pose proof (byte_range b') as BR'.
        pose proof (u8ro_read rsegs m1 Sa sfull (i + 1) _ (Z_to_bv 64 (Sa + i + 1)) STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
        zstep. clear RD. beta_goal.
        zstep. zstep. zstep. if_cases K1; zify_cond K1.
        + assert (NE : i + 1 <> L) by (intros EQ; apply K1; apply NZ'; exact EQ).
          apply (IH (i + 1)%Z m1 b'); [lia| lia| exact (HB' ltac:(lia))| | exact MM| unfold bm; exact FR| weq].
          intros j x Hj Hx. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NEj]; [rewrite HB in Hx; inversion Hx; subst; exact INB|].
          apply (IN j x); [lia| exact Hx].
        + assert (EQ : i + 1 = L) by (apply NZ'; exact K1).
          zstep.
          eapply fin with (r := i + 1); [exact MM| exact FR| reflexivity| weq|].
          rewrite (cspn_prefix set str (length str)); [lia| lia| |].
          * intros j x Hj Hx. destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NEj]; [rewrite HB in Hx; inversion Hx; subst; exact INB|].
            apply (IN j x); [lia| exact Hx].
          * intros x Hx. rewrite nth_none_len in Hx. discriminate. }
    assert (Q4 : q = 0%Z \/ q = 1%Z \/ q = 2%Z \/ q = 3%Z) by (subst q; clear -BR; Z.div_mod_to_equations; lia).
    clearbody q.
    destruct Q4 as [Eq|[Eq|[Eq|Eq]]]; rewrite Eq in KQ |- *.
    - replace (bv_unsigned sp + -80 + 8 * 0)%Z with (bv_unsigned sp + -80)%Z by lia. zstep. exact KQ.
    - replace (bv_unsigned sp + -80 + 8 * 1)%Z with (bv_unsigned sp + -72)%Z by lia. zstep. exact KQ.
    - replace (bv_unsigned sp + -80 + 8 * 2)%Z with (bv_unsigned sp + -64)%Z by lia. zstep. exact KQ.
    - replace (bv_unsigned sp + -80 + 8 * 3)%Z with (bv_unsigned sp + -56)%Z by lia. zstep. exact KQ.
  Qed.

  Lemma scan_entry : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) (bm set) ->
    evt rsegs POST (STc 0x1b1c8 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31).
  Proof using All.
    intros m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 MM FR.
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1 & FT).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    pose proof (cspn_le set str) as SL.
    destruct (cstr_at str slack 0 SNONUL ltac:(lia)) as (b & HN & HB & NZ). pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs m1 Sa sfull 0 _ a0 STR1 HN ltac:(lia) ltac:(addr_tac)) as RD.
    zstep. clear RD. beta_goal.
    zstep. zstep. if_cases K0; zify_cond K0.
    - assert (EQ : 0 = L) by (apply NZ; exact K0).
      eapply fin with (r := 0); [exact MM| exact FR| reflexivity| weq| lia].
    - assert (NE : 0 <> L) by (intros EQ; apply K0; apply NZ; exact EQ).
      zstep. zstep.
      apply (scan_loop (Z.to_nat (L - 0)) 0 m1 b); [lia| lia| exact (HB ltac:(lia))| intros j x Hj; lia| exact MM| exact FR| weq].
  Qed.

  Lemma build_loop : forall (k : nat) (i : Z) m1 (b : byte) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    Z.to_nat (K - i) = k -> (0 <= i < K)%Z -> nth_error set (Z.to_nat i) = Some b ->
    MEMS m1 -> rw_cells rsegs m1 (SP + -80) (bm (firstn (Z.to_nat i) set)) ->
    evt rsegs POST (STc 0x1b1a0 m1 x1 x5 x6 x7 (Z_to_bv 64 (Ca + i + 1)) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 1)
                        x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (SP + -80)) x28 x29 x30 x31).
  Proof using All.
    induction k as [|k IH]; intros i m1 b x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi HB MM FR; [lia|].
    pose proof MM as (MI1 & STR1 & ACC1 & GOT1 & CAN1 & ST1 & MU1 & WM1 & FT). clear MM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (byte_range b) as BR.
    unfold bm in FR.
    zstep. zstep. zstep. rewrite ?unsigned_lit by lia. rewrite (bidx (bv_unsigned b)) by lia.
    set (q := (bv_unsigned b / 64)%Z) in *.
    destruct (cstr_at set [] (i + 1) ANONUL ltac:(lia)) as (b' & HN' & HB' & NZ'). pose proof (byte_range b') as BR'.
    assert (KQ : forall m2 x12' x13' x14', MEMS m2 -> rw_cells rsegs m2 (SP + -80) (bm (firstn (Z.to_nat (i + 1)) set)) ->
              evt rsegs POST (STc 0x1b1c0 m2 x1 x5 x6 x7 (Z_to_bv 64 (Ca + i + 1)) (Z_to_bv 64 (bv_unsigned b')) (Z_to_bv 64 1)
                                  x12' x13' x14' x15 x16 x17 (Z_to_bv 64 (SP + -80)) x28 x29 x30 x31)).
    { intros m2 x12' x13' x14' MM2 FR2.
      zstep. zstep. if_cases KZ; zify_cond KZ.
      - assert (NE : i + 1 <> K) by (intros EQ; apply KZ; apply NZ'; exact EQ).
        replace (Ca + i + 2)%Z with (Ca + (i + 1) + 1)%Z by lia.
        apply (IH (i + 1)%Z m2 b'); [lia| lia| exact (HB' ltac:(lia))| exact MM2| exact FR2].
      - assert (EQ : i + 1 = K) by (apply NZ'; exact KZ).
        replace (Z.to_nat (i + 1)) with (length set) in FR2 by lia. rewrite firstn_all in FR2.
        apply scan_entry; [exact MM2| exact FR2]. }
    pose proof (u8ro_read rsegs m1 Ca afull (i + 1) _ (Z_to_bv 64 (Ca + i + 1)) ACC1 HN' ltac:(lia) ltac:(addr_tac)) as RD.
    assert (EF : firstn (Z.to_nat (i + 1)) set = firstn (Z.to_nat i) set ++ [b]).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply firstn_snoc. exact HB. }
    assert (Q4 : q = 0%Z \/ q = 1%Z \/ q = 2%Z \/ q = 3%Z) by (subst q; clear -BR; Z.div_mod_to_equations; lia).
    pose proof (bm_snoc (firstn (Z.to_nat i) set) b q eq_refl) as FS. rewrite <- EF in FS.
    pose proof (setw_range (firstn (Z.to_nat i) set) q) as WR.
    clearbody q.
    assert (SR : (0 <= Z.shiftl 1 (bv_unsigned b mod 64) < 2^64)%Z).
    { rewrite Z.shiftl_1_l. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; Z.div_mod_to_equations; lia]. }
    destruct Q4 as [Eq|[Eq|[Eq|Eq]]]; rewrite Eq in FS, WR |- *; cbn [Z.eqb Pos.eqb] in FS; pose proof (lor_range64 _ _ WR SR) as LR;
    [ replace (bv_unsigned sp + -80 + 8 * 0)%Z with (bv_unsigned sp + -80)%Z by lia
    | replace (bv_unsigned sp + -80 + 8 * 1)%Z with (bv_unsigned sp + -72)%Z by lia
    | replace (bv_unsigned sp + -80 + 8 * 2)%Z with (bv_unsigned sp + -64)%Z by lia
    | replace (bv_unsigned sp + -80 + 8 * 3)%Z with (bv_unsigned sp + -56)%Z by lia ].
    all: zstep; zstep; zstep; clear RD; beta_goal.
    all: replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
    all: zstep; rewrite ?unsigned_lit by lia; zstep.
    all: lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned sp + -80) _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        replace (Z.land (bv_unsigned b) 63) with (bv_unsigned b mod 64)%Z in H by (change 63%Z with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity);
        rewrite <- FS in H; apply (KQ mc); [mems_tac| exact H] end.
  Qed.

  Lemma walk : forall m0,
    mem_inv rsegs m0 -> bytes_at rsegs m0 Sa sfull -> bytes_at rsegs m0 Ca afull ->
    ro_cells rsegs m0 0x1d590 [C8 (Z_to_bv 64 0x4eb80)] -> ro_cells rsegs m0 0x4eb80 [C8 can] ->
    stk rsegs m0 lo SP -> munch [(SP - 96, SP)] m m0 -> wmono rsegs m m0 ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b13c) fc None m0 (seg_rom rsegs)).
  Proof using All.
    intros m0 MI1 STR1 ACC1 GOT1 CAN1 ST1 MU WM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (bv_unsigned_in_range _ a0) as AR. change (bv_modulus 64) with (2^64)%Z in AR.
    pose proof (bv_unsigned_in_range _ a1) as A1R. change (bv_modulus 64) with (2^64)%Z in A1R.
    pose proof MSET as MS0. unfold memset_contract in MS0.
    zstep. carve_frame 80%nat ST1. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned sp + -80) _ |- _ =>
      destruct (rw_cells_split1 mc _ _ _ (bv_unsigned sp + -48) H ltac:(cbn [csize]; lia)) as [FB FT]; clear H end.
    destruct (cstr_at set [] 0 ANONUL ltac:(lia)) as (c0 & HC0 & HC0' & Z0). pose proof (byte_range c0) as C0R.
    pose proof (u8ro_read rsegs _ Ca afull 0 c0 a1 ACC1 HC0 ltac:(lia) ltac:(addr_tac)) as RD.
    zstep. clear RD. beta_goal.
    zstep. zstep. if_cases KZ0; zify_cond KZ0.
    - assert (EK : 0 = K) by (apply Z0; exact KZ0).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply (via_chrnul mc c0); [lia| exact HC0| mems_tac| exact FB] end.
    - assert (NK0 : 0 <> K) by (intros EQ; apply KZ0; apply Z0; exact EQ).
      destruct (cstr_at set [] 1 ANONUL ltac:(lia)) as (c1 & HC1 & HC1' & Z1). pose proof (byte_range c1) as C1R.
      pose proof (u8ro_read rsegs _ Ca afull 1 c1 (Z_to_bv 64 (Ca + 1)) ACC1 HC1 ltac:(lia) ltac:(addr_tac)) as RD.
      zstep. clear RD. beta_goal.
      zstep. if_cases KZ1; zify_cond KZ1.
      + assert (EK : 1 = K) by (apply Z1; exact KZ1).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          eapply (via_chrnul mc c0); [lia| exact HC0| mems_tac| exact FB] end.
      + assert (NK1 : 1 <> K) by (intros EQ; apply KZ1; apply Z1; exact EQ).
        zstep. zstep. zstep. zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        lazymatch type of FB with rw_cells _ _ _ [CB 32 ?jk] =>
          eapply evt_cut;
          [ eapply MS0 with (junk := jk); [rewrite ?unsigned_lit by lia; exact FB | exact MI1]
          | intros ms' PO; unfold memset_post in PO;
            destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & E & MUc & WMc & MIc & RWc);
            subst ms';
            rewrite ?unsigned_lit in MUc by lia; rewrite ?unsigned_lit in RWc by lia;
            transport_after_call rsegs mc m2 MUc WMc; clear MUc WMc ] end end.
        pose proof (bm0_of _ _ _ _ RWc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as FB0. clear RWc.
        ret_lit.
        pose proof (u8ro_read rsegs _ Ca afull 0 c0 a1 ACC1 HC0 ltac:(lia) ltac:(addr_tac)) as RD.
        zstep. clear RD. beta_goal.
        zstep. if_cases KZ2; zify_cond KZ2. { exfalso. exact (KZ0 KZ2). }
        zstep. zstep.
        replace (Ca + 1)%Z with (Ca + 0 + 1)%Z by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          apply (build_loop (Z.to_nat (K - 0)) 0 mc c0); [lia| lia| exact (HC0' ltac:(lia))| mems_tac| exact FB0] end.
  Qed.
End W.

Theorem strcspn_holds : memset_contract -> strchrnul_contract -> strcspn_contract.
Proof.
  intros MSET CHR. unfold strcspn_contract, STRCSPN, CSPN_SSP_GOT, CSPN_SSP_GUARD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack set lo can
    STR SNZ SLK ACC ANZ GOT CAN ST LOS DS DC DG DK MI.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. pose proof (bytes_at_bound _ _ _ _ ACC) as CB.
  rewrite length_app in SB, CB. cbn [length] in SB, CB.
  pose proof ST as (LO0 & _ & _).
  eapply walk; try eassumption; try lia; [apply ro8; exact GOT| apply ro8; exact CAN| apply munch_refl| apply wmono_refl].
Qed.
