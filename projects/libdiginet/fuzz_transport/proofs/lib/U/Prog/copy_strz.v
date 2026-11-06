(* proves copy_strz_contract, the walk of copy_strz in fuzz_transport.ubsan. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/copy_strz.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of copy_strz (src/diginet_frame.c:130-136 at 835f336c) in fuzz_transport.ubsan, 0x185e0..0x18640.
   The loop at 0x185ec copies the bytes of s at src to the field at dst up to the first NUL, at
   most 9 of them; 0x18630 writes the NUL. CS_INV is the state of memory at each loop head: the
   field holds i bytes of s, then the bytes i..9 of old.
   The five UBSan branches to the trap at 0x18640 are not taken: src + i and dst + i do not wrap
   (bytes_at gives src + 9 <= 2^64, rw_cells gives dst + 10 <= 2^64), and src is not 0. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import copy_strz_c.
Import ListNotations.
Open Scope Z_scope.

(** * Lists *)

Lemma cs_at8_ne : forall l i b, nth_error l i = Some b -> at8 l i = bz b.
Proof.
  induction l as [|x l IH]; intros [|i] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - unfold at8 in *. cbn [nth]. apply IH. exact H.
Qed.

Lemma cs_byte_at : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof.
  intros l i Hi. destruct (nth_error l i) eqn:N; [eexists; reflexivity|].
  apply nth_error_None in N. lia.
Qed.

Lemma cs_firstn_snoc_nth : forall (s : list byte) j b, nth_error s j = Some b -> firstn (S j) s = firstn j s ++ [b].
Proof.
  induction s as [|c s IH]; intros [|j] b H; cbn in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - cbn [firstn]. rewrite (IH j b H). reflexivity.
Qed.

Lemma cs_upd_at_end : forall (P R : list byte) i z, length P = i -> upd_bytes (P ++ R) i [z] = P ++ z :: skipn 1 R.
Proof.
  intros P R i z <-. unfold upd_bytes. rewrite firstn_app, skipn_app, Nat.sub_diag, firstn_all.
  rewrite (skipn_all2 (n := (length P + length [z])%nat) P) by (cbn [length]; lia).
  cbn [length]. replace (length P + 1 - length P)%nat with 1%nat by lia.
  cbn [firstn app]. rewrite app_nil_r. reflexivity.
Qed.

(* One turn of the loop: the field holds j bytes of s, then byte j of s is stored. *)
Lemma cs_upd_snoc : forall (s X : list byte) j b, nth_error s j = Some b ->
  upd_bytes (firstn j s ++ skipn j X) j [b] = firstn (S j) s ++ skipn (S j) X.
Proof.
  intros s X j b Hn.
  assert (Hj : (j < length s)%nat) by (apply nth_error_Some; congruence).
  rewrite cs_upd_at_end by (rewrite length_firstn; lia).
  rewrite (cs_firstn_snoc_nth s j b Hn), skipn_skipn.
  replace (1 + j)%nat with (S j) by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma cs_strz_len_le_len : forall src, (strz_len src <= length src)%nat.
Proof.
  intros src. unfold strz_len. pose proof (nz_run_le (firstn 9 src)) as H. rewrite length_firstn in H. lia.
Qed.

(* The NUL after the k = strz_len s bytes of s: the field is copy_strz 10 9 s old. *)
Lemma cs_nul : forall (s old : list byte),
  upd_bytes (firstn (strz_len s) s ++ skipn (strz_len s) old) (strz_len s) [b8 0] = copy_strz 10 9 s old.
Proof.
  intros s old. pose proof (cs_strz_len_le_len s) as H.
  rewrite cs_upd_at_end by (rewrite length_firstn; lia).
  unfold copy_strz. change (copy_len 10 9 s) with (strz_len s).
  rewrite skipn_skipn. replace (1 + strz_len s)%nat with (S (strz_len s)) by lia. reflexivity.
Qed.

(** * Memory *)

Lemma cs_firstn1_skipn : forall {X} (l : list X) i b, nth_error l i = Some b -> firstn 1 (skipn i l) = [b].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] b N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma cs_rdb : forall m A l (i : nat) b, bytes_at rsegs m A l -> nth_error l i = Some b ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m A l i b BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m A l i 1 BL ltac:(lia)). f_equal. apply cs_firstn1_skipn. exact N.
Qed.

(* The memory at a loop head: the field at dst is the byte cell L; the source is unchanged. *)
Definition CS_INV (m0 m1 : word -> option byte) (dst src : Z) (s L : list byte) : Prop :=
  rw_cells rsegs m1 dst [CB 10 L] /\
  munch [(dst, dst + 10)] m0 m1 /\ wmono rsegs m0 m1 /\ mem_inv rsegs m1 /\
  bytes_at rsegs m1 src s.

Lemma cs_inv_store_ok : forall m0 m1 dst src s L (i : nat) (w : word),
  CS_INV m0 m1 dst src s L -> (i < 10)%nat -> w = Z_to_bv 64 (dst + Z.of_nat i) ->
  store_ok rsegs m1 w 1 = true.
Proof.
  intros m0 m1 dst src s L i w (CA & _) Hi ->. destruct CA as [_ Hw].
  cbn [cells_size csize Nat.add] in Hw.
  exact (wr_at_store_ok rsegs m1 dst _ (Z.of_nat i) 1 Hw ltac:(lia) ltac:(lia)).
Qed.

Lemma cs_inv_rd : forall m0 m1 dst src s L (n : nat) b,
  CS_INV m0 m1 dst src s L -> nth_error s n = Some b ->
  ov_read_bytes rsegs m1 (wa (src + Z.of_nat n)) 1 = Some [b].
Proof. intros m0 m1 dst src s L n b (_ & _ & _ & _ & BS) N. eapply cs_rdb; eauto. Qed.

(* A byte store at dst + i inside the field. *)
Lemma cs_stb_inv : forall m0 m1 dst src s L (i : nat) (w : word) (b : byte),
  CS_INV m0 m1 dst src s L -> (i < 10)%nat -> w = Z_to_bv 64 (dst + Z.of_nat i) ->
  (dst + 10 <= src \/ src + Z.of_nat (length s) <= dst) ->
  CS_INV m0 (write_to_mem m1 w [b]) dst src s (upd_bytes L i [b]).
Proof.
  intros m0 m1 dst src s L i w b ([[[Hl Hwf] Hb] Hw] & MU & WM & MI & BS) Hi -> DJ.
  cbn [cells_bytes cbytes cells_size csize Nat.add] in Hb, Hw. cbn [cell_wf] in Hl.
  rewrite app_nil_r in Hb.
  pose proof (bytes_at_bound rsegs _ _ _ Hb) as HB. rewrite Hl in HB.
  assert (HS : store_ok rsegs m1 (wa (dst + Z.of_nat i)) 1 = true)
    by (apply (wr_at_store_ok rsegs m1 dst _ (Z.of_nat i) 1 Hw); lia).
  change (Z_to_bv 64 (dst + Z.of_nat i)) with (wa (dst + Z.of_nat i)).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - split; [split|].
    + cbn [cells_wf cell_wf]. split; [|exact I]. rewrite upd_bytes_length; cbn [length]; lia.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r.
      pose proof (bytes_at_write_inside rsegs m1 dst L (Z.of_nat i) [b] Hb ltac:(lia)
                    ltac:(cbn [length]; lia)) as W1.
      rewrite Nat2Z.id in W1. exact W1.
    + cbn [cells_size csize Nat.add]. apply wr_at_write. exact Hw.
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
  - apply bytes_at_write_other; [exact BS | lia | cbn [length]; lia | cbn [length]; lia].
Qed.

(** * Words *)

Lemma cs_not : forall dst, 0 <= dst < 2^64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 dst)) 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - dst).
Proof. intros dst H. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. Qed.

Lemma cs_snez : forall src, 0 < src < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 src) = Z_to_bv 64 1.
Proof.
  intros src H. rewrite v_sltu_b2z. rewrite !unsigned_lit by lia.
  replace (0 <? src) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma cs_seqz : forall x, 0 < x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x H. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma cs_zb_eq0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bz b =? 0).
Proof.
  intros b. pose proof (bz_range b) as R. unfold bz in *. unfold bv_eqb, zxb.
  rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma cs_le1_0 : le1 (Z_to_bv 64 0) = [b8 0].
Proof. vm_compute. reflexivity. Qed.

Ltac cs_uns := rewrite ?unsigned_lit by lia.
Ltac cs_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cs_uns; solve_cond_rec]
  end.
(* Decide a branch whose condition is a closed term. *)
Ltac cs_brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* After the store step of a byte at dst + i: the new memory is a fresh variable and I its CS_INV. *)
Ltac cs_stored I i DJ :=
  rewrite ?le1_zxb, ?cs_le1_0;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?w [?bv]) _) =>
      let I' := fresh "I" in
      pose proof (cs_stb_inv _ mm _ _ _ _ i w bv I ltac:(lia) ltac:(first [reflexivity | f_equal; lia]) DJ) as I';
      let mn := fresh "m" in
      set (mn := write_to_mem mm w [bv]) in *; clearbody mn; clear I; rename I' into I
  end.

Theorem copy_strz_holds : copy_strz_contract.
Proof.
  unfold copy_strz_contract, COPY_STRZ.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    dst src s old Hsrc Ls BS CA DJ0 MI.
  pose proof (rw_cells_bound rsegs m dst _ CA) as HA. cbn [cells_size csize] in HA.
  pose proof (bytes_at_bound rsegs m src s BS) as HB. rewrite Ls in HB.
  assert (DJ : dst + 10 <= src \/ src + Z.of_nat (length s) <= dst) by (rewrite Ls; lia).
  assert (Lold : length old = 10%nat) by (destruct CA as [[[Hl _] _] _]; exact Hl).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  (* 0x18630: the NUL at dst + k, the return *)
  assert (FIN : forall (m2 : word -> option byte) (x3 x4 x6 x7 : word) (v5 : Z),
    v5 = Z.of_nat (strz_len s) ->
    CS_INV m m2 dst src s (firstn (strz_len s) s ++ skipn (strz_len s) old) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 src)
                         (Z_to_bv 64 (18446744073709551615 - dst)) x3 x4 (Z_to_bv 64 v5) x6 x7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x18630) fc None m2 (seg_rom rsegs))).
  { intros m2 x3 x4 x6 x7 v5 -> I.
    pose proof (strz_len_le s) as K.
    step. cs_br false.
    step.
    assert (HS : store_ok rsegs m2 (Z_to_bv 64 (dst + Z.of_nat (strz_len s))) 1 = true)
      by (eapply (cs_inv_store_ok _ _ _ _ _ _ (strz_len s)); [exact I | lia | reflexivity]).
    step. clear HS.
    cs_stored I (strz_len s) DJ.
    rewrite cs_nul in I.
    step.
    apply evt_done. unfold QQ. cbv beta. do 8 eexists. split; [reflexivity|].
    destruct I as (CA2 & MU2 & WM2 & MI2 & _).
    exact (conj MU2 (conj WM2 (conj MI2 CA2))). }
  (* 0x185ec: the loop; i bytes copied *)
  assert (LOOP : forall (k i : nat) (m1 : word -> option byte) (x5 x6 x7 : word) (v3 : Z),
    (i + S k = 9)%nat -> v3 = Z.of_nat i ->
    (forall j, (j < i)%nat -> at8 s j <> 0) ->
    CS_INV m m1 dst src s (firstn i s ++ skipn i old) ->
    evt rsegs QQ (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 src)
                         (Z_to_bv 64 (18446744073709551615 - dst)) (Z_to_bv 64 v3) (Z_to_bv 64 1) x5 x6 x7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x185ec) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i m1 x5 x6 x7 v3 Hk -> Hnz I.
    all: destruct (cs_byte_at s i ltac:(lia)) as [b Nb].
    all: pose proof (cs_inv_rd _ _ _ _ _ _ _ _ I Nb) as HR.
    all: pose proof (cs_at8_ne _ _ _ Nb) as Ab.
    (* 0x185ec add a5; 0x185f0 src + i wraps *)
    all: step; step; cs_br false.
    (* 0x185f4 seqz; 0x185f8 xor; 0x185fc (src <> 0) xor (src + i = 0) *)
    all: step; rewrite ?cs_seqz by lia; step; step; cs_brc.
    (* 0x18600 src = 0 *)
    all: step; cs_br false.
    (* 0x18604 lbu; 0x18608 beqz *)
    all: step; clear HR; step; rewrite cs_zb_eq0.
    all: destruct (Z.eqb_spec (bz b) 0) as [Z0|Z0]; cbv iota.
    1, 3: assert (Ek : strz_len s = i) by (apply strz_len_char; [lia | lia | exact Hnz | intros; lia]);
          step; eapply FIN; [rewrite Ek; first [reflexivity | lia | cs_uns; lia] | rewrite Ek; exact I].
    (* 0x1860c dst + i wraps *)
    all: step; cs_br false.
    all: step; step; step.
    all: assert (HS : store_ok rsegs m1 (Z_to_bv 64 (dst + Z.of_nat i)) 1 = true)
           by (eapply (cs_inv_store_ok _ _ _ _ _ _ i); [exact I | lia | reflexivity]).
    all: step; clear HS.
    all: cs_stored I i DJ.
    all: rewrite (cs_upd_snoc s old i b Nb) in I.
    all: step; step.
    - cs_br false. step.
      assert (Ek : strz_len s = 9%nat).
      { apply strz_len_char; [lia | lia | | lia].
        intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia]. }
      eapply FIN; [rewrite Ek; reflexivity | rewrite Ek; replace (S i) with 9%nat in I by lia; exact I].
    - cs_br true. eapply (IH (S i)); [lia | first [lia | cs_uns; lia] | | exact I].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|NE]; [lia | apply Hnz; lia]. }
  (* 0x185e0: i = 0, a2 = ~dst, a4 = (src != 0) *)
  step. step. step.
  rewrite cs_not by lia. rewrite cs_snez by lia.
  eapply (LOOP 8%nat 0%nat); [lia | reflexivity | intros; lia |].
  cbn [firstn skipn app].
  exact (conj CA (conj (munch_refl _ m) (conj (wmono_refl rsegs m) (conj MI BS)))).
Qed.
