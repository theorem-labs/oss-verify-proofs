(** Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c / pinned 1696d6c34ffd):
    the SPLIT stretch 0x13fd0 .. 0x140c8 (UBSan binary), the inline m_split
    (fuzz_segconf.c:323-350): proof of [V01D.V01_SPLIT] from the contracts of strrchr and memcpy (MainB.K_V01).

    Code, by piece (the lemma that walks it):
      0x13fd0-0x13fd8 strrchr(name, '.')  [split_entry]: name = m + 256 i (s7), a cstr_enc 16 field of the mconf
           block (V01_env's mconf_at), below lo, so strrchr_contract holds with the field's slack; its answer is
           SegModel.strrchr of the name (SegBridge.bridge_strrchr).
      0x13fdc beqz a0 -> join (no dot); a4 = -10, a5 = 10; 0x13fe8 beq a0,s7 -> join (dot = name); 0x13fec beq a0,s4
           -> trap (dot + 1 wraps: dead); 0x13ff0 lbu a2,1(a0); 0x13ff4 beqz a2 -> join; s0 = 0; a1 = dot + 1.
      DIGIT LOOP 0x14000 [dloop] (induction on the bytes left): a2 - 0x3a <u -10 -> join (not a digit);
           s0 = s0 * 10 + (a2 & 15); 4094 <u s0 -> join; beq a1,s4 -> trap (dead); lbu a2,1(a1); a1++; bnez -> loop.
      0x14028 [post_dig] beqz s0 -> join (vid < 1); a1 = 0; s5 = dot - name; a0 = dot - name (s6 = -name) plus
           (a0 == 0) = pn (pn >= 1); a2 = ~name.
      PARENT LOOP 0x14044 [ploop] (induction on pn - j): bltu a2,a1 -> trap (dead); ch = name[j]; the character test
           (digits and ':' by (ch - 48) & 255 < 11, letters by ((ch & ~32) - 65) & 255 < 26, '-', '.', '_' by bit
           ch - 45 of the mask 2^50 + 3 at 0x30(sp)) equals SegModel.h_parent_ok ch: every branch outcome is checked
           on the 256 byte values ([byte_fact]); a refused byte -> join; j++; bne a0,a1 -> loop.
      0x1409c-0x140c8 [acc_tail] memcpy(sp + 0x60, name, pn) on the first pn bytes of the 20-byte buffer cell (cut
           in four before the call); bgeu s5,16 and bltu ~(sp+0x60),s5 -> trap (dead); sb zero at sp + 0x60 + pn;
           sw s0 at sp + 0x70: the 20 bytes are mvlan_enc (firstn pn name, vid); then V01_ACCat.
    Every refusal goes to the join 0x13fb8 (V01_JOINat with the same table and count: m_split .. = None makes
    m_decl_go skip segment i, [join_ok]).
    V01SplitPure holds the lemmas that name no address and no register (SegModel, lists, bytes).
    Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
    fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import memrchr_c strrchr_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import V01D MainB.
Import ListNotations.
Open Scope Z_scope.

Module V01SplitPure.

Lemma hd0_skipn : forall (l : list Z) k, hd0 (skipn k l) = nth k l 0.
Proof. induction l as [|x l IH]; intros [|k]; cbn; [reflexivity | reflexivity | reflexivity | apply IH]. Qed.

Lemma nth_app0 : forall (l : list Z) k, nth k (l ++ [0]) 0 = nth k l 0.
Proof.
  induction l as [|x l IH]; intros [|k]; cbn; [reflexivity | destruct k; reflexivity | reflexivity | apply IH].
Qed.

Lemma nth_firstn_lt : forall (l : list Z) n k, (k < n)%nat -> nth k (firstn n l) 0 = nth k l 0.
Proof.
  induction l as [|x l IH]; intros [|n] [|k] H; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma nth_nz : forall (l : list Z) k, ~ In 0 l -> (k < length l)%nat -> nth k l 0 <> 0.
Proof. intros l k Hn Hk E. apply Hn. rewrite <- E. apply nth_In. exact Hk. Qed.

Lemma skipn_cons_nth : forall {T} (l : list T) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros T l. induction l as [|x l IH]; intros [|k] d H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma firstn_S_app : forall {T} (A B : list T) (x : T), firstn (S (length A)) (A ++ x :: B) = A ++ [x].
Proof. intros T A. induction A as [|y A IH]; intros B x; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma forallb_firstn_S : forall (P : Z -> bool) (l : list Z) j, (j < length l)%nat ->
  forallb P (firstn (S j) l) = forallb P (firstn j l) && P (nth j l 0).
Proof.
  intros P l. induction l as [|x l IH]; intros [|j] H; cbn [length] in H; try lia.
  - cbn. destruct (P x); reflexivity.
  - change (forallb P (x :: firstn (S j) l) = forallb P (x :: firstn j l) && P (nth j l 0)).
    cbn [forallb]. rewrite IH by lia. apply andb_assoc.
Qed.

Lemma forallb_firstn_false : forall (P : Z -> bool) (l : list Z) d j, (j < d)%nat -> (d <= length l)%nat ->
  P (nth j l 0) = false -> forallb P (firstn d l) = false.
Proof.
  intros P l. induction l as [|x l IH]; intros d j Hj Hd Hp; cbn [length] in Hd; [lia|].
  destruct d as [|d]; [lia|]. destruct j as [|j].
  - cbn [nth] in Hp. change (forallb P (x :: firstn d l) = false). cbn [forallb]. rewrite Hp. reflexivity.
  - cbn [nth] in Hp. change (forallb P (x :: firstn d l) = false). cbn [forallb].
    rewrite (IH d j) by (try exact Hp; lia). apply andb_false_r.
Qed.

(** strrchr's index lies in the string. *)
Lemma last_idx_bound : forall c (l : list Z) i acc k, last_idx c l i acc = Some k ->
  (i <= k < i + length l)%nat \/ acc = Some k.
Proof.
  intros c l. induction l as [|x l IH]; intros i acc k H; cbn [last_idx length] in *.
  - right. exact H.
  - destruct (IH _ _ _ H) as [H1|H1]; [left; lia|].
    revert H1. destruct (x =? c); intros H1; [|right; exact H1].
    left. injection H1 as E. subst. lia.
Qed.

Lemma strrchr_bound : forall s c k, ~ In 0 s -> SegModel.strrchr s c = Some k -> (k < length s)%nat.
Proof.
  intros s c k Hn H. unfold SegModel.strrchr in H. rewrite cut_nul_id in H by exact Hn.
  destruct (last_idx_bound c s 0 None k H) as [H1|H1]; [lia | discriminate].
Qed.

(** m_split's exits. *)
Lemma split_none_r : forall s, SegModel.strrchr s 46 = None -> m_split s = None.
Proof. intros s H. unfold m_split. rewrite H. reflexivity. Qed.

Lemma split_none_d0 : forall s, SegModel.strrchr s 46 = Some 0%nat -> m_split s = None.
Proof. intros s H. unfold m_split. rewrite H. reflexivity. Qed.

Lemma split_none_h0 : forall s d, SegModel.strrchr s 46 = Some d -> nth (S d) s 0 = 0 -> m_split s = None.
Proof.
  intros s d H H0. unfold m_split. rewrite H. cbv beta iota.
  rewrite hd0_skipn, H0, Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma split_none_dig : forall s d, SegModel.strrchr s 46 = Some d -> (d <> 0)%nat -> nth (S d) s 0 <> 0 ->
  m_digits (skipn (S d) s) 0 = None -> m_split s = None.
Proof.
  intros s d H Hd H0 HD. unfold m_split. rewrite H. cbv beta iota.
  rewrite hd0_skipn, (proj2 (Nat.eqb_neq d 0) Hd), (proj2 (Z.eqb_neq _ 0) H0), HD. reflexivity.
Qed.

Lemma split_none_v0 : forall s d v, SegModel.strrchr s 46 = Some d -> (d <> 0)%nat -> nth (S d) s 0 <> 0 ->
  m_digits (skipn (S d) s) 0 = Some v -> v < 1 -> m_split s = None.
Proof.
  intros s d v H Hd H0 HD Hv. unfold m_split. rewrite H. cbv beta iota.
  rewrite hd0_skipn, (proj2 (Nat.eqb_neq d 0) Hd), (proj2 (Z.eqb_neq _ 0) H0), HD. cbv beta iota.
  rewrite (proj2 (Z.ltb_lt v 1) Hv). reflexivity.
Qed.

Lemma split_none_par : forall s d v, SegModel.strrchr s 46 = Some d -> (d <> 0)%nat -> nth (S d) s 0 <> 0 ->
  m_digits (skipn (S d) s) 0 = Some v -> 1 <= v -> forallb h_parent_ok (firstn d s) = false -> m_split s = None.
Proof.
  intros s d v H Hd H0 HD Hv HP. unfold m_split. rewrite H. cbv beta iota.
  rewrite hd0_skipn, (proj2 (Nat.eqb_neq d 0) Hd), (proj2 (Z.eqb_neq _ 0) H0), HD. cbv beta iota.
  rewrite (proj2 (Z.ltb_ge v 1) Hv), HP. reflexivity.
Qed.

Lemma split_some : forall s d v, SegModel.strrchr s 46 = Some d -> (d <> 0)%nat -> nth (S d) s 0 <> 0 ->
  m_digits (skipn (S d) s) 0 = Some v -> 1 <= v -> forallb h_parent_ok (firstn d s) = true ->
  m_split s = Some (firstn d s, v).
Proof.
  intros s d v H Hd H0 HD Hv HP. unfold m_split. rewrite H. cbv beta iota.
  rewrite hd0_skipn, (proj2 (Nat.eqb_neq d 0) Hd), (proj2 (Z.eqb_neq _ 0) H0), HD. cbv beta iota.
  rewrite (proj2 (Z.ltb_ge v 1) Hv), HP. reflexivity.
Qed.

(** One step of m_digits. *)
Lemma dig_bad : forall q r acc, (q <? 48) || (57 <? q) = true -> m_digits (q :: r) acc = None.
Proof. intros q r acc H. cbn [m_digits]. rewrite H. reflexivity. Qed.

Lemma dig_big : forall q r acc, 48 <= q <= 57 -> 4094 < acc * 10 + (q - 48) -> m_digits (q :: r) acc = None.
Proof.
  intros q r acc Hq Hv. cbn [m_digits].
  rewrite (proj2 (Z.ltb_ge q 48)) by lia. rewrite (proj2 (Z.ltb_ge 57 q)) by lia. cbv beta iota zeta.
  rewrite (proj2 (Z.ltb_lt 4094 (acc * 10 + (q - 48))) Hv). reflexivity.
Qed.

Lemma dig_ok : forall q r acc, 48 <= q <= 57 -> acc * 10 + (q - 48) <= 4094 ->
  m_digits (q :: r) acc = m_digits r (acc * 10 + (q - 48)).
Proof.
  intros q r acc Hq Hv. cbn [m_digits].
  rewrite (proj2 (Z.ltb_ge q 48)) by lia. rewrite (proj2 (Z.ltb_ge 57 q)) by lia. cbv beta iota zeta.
  rewrite (proj2 (Z.ltb_ge 4094 (acc * 10 + (q - 48))) Hv). reflexivity.
Qed.

(** `andi a2,a2,0xf` on a digit. *)
Lemma land15_dig : forall q, 48 <= q <= 57 -> Z.land q 15 = q - 48.
Proof.
  intros q H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
  Z.div_mod_to_equations. lia.
Qed.

(** m_decl_go skips a segment whose name m_split refuses. *)
Lemma decl_skip : forall segs k tb cap ad, (k < length segs)%nat -> ms_ignore (nth k segs mseg_d) = false ->
  m_split (ms_name (nth k segs mseg_d)) = None ->
  m_decl_go (skipn k segs) tb cap ad = m_decl_go (skipn (S k) segs) tb cap ad.
Proof.
  intros segs k tb cap ad Hk Hi Hs. rewrite (skipn_cons_nth segs k mseg_d Hk). cbn [m_decl_go].
  rewrite Hi, Hs. reflexivity.
Qed.

(** A boolean fact of a byte holds when it holds on the 256 values (a branch outcome of the character tests). *)
Lemma byte_all : forall g : byte -> bool,
  forallb (fun k => g (Z_to_bv 8 (Z.of_nat k))) (seq 0 256) = true -> forall b, g b = true.
Proof.
  intros g H b. rewrite forallb_forall in H.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  specialize (H (Z.to_nat (bv_unsigned b))). rewrite Z2Nat.id in H by lia.
  replace (Z_to_bv 8 (bv_unsigned b)) with b in H.
  - apply H. apply in_seq. lia.
  - apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(** The goal [c = true], c a boolean of the byte b and literals only. *)
Ltac byte_fact b :=
  lazymatch goal with
  | |- ?c = true =>
      let g := eval pattern b in c in
      lazymatch g with
      | ?f b => refine (byte_all f _ b); vm_compute; reflexivity
      end
  end.

(** The tested boolean of a branch hypothesis K : c = v (if_cases). *)
Ltac kc K := lazymatch type of K with ?c = _ => c end.

(** A struct mvlan buffer: the parent's bytes, the NUL, 15 - pn bytes not fixed, the vid. *)
Lemma fld_l : forall (A B : list byte) n, length A = n -> fld 0 n (A ++ B) = A.
Proof. intros A B n <-. unfold fld. rewrite skipn_O. apply firstn_app_exact. Qed.

Lemma fld_r : forall (A B : list byte) n k, length A = n -> length B = k -> fld n k (A ++ B) = B.
Proof. intros A B n k <- <-. unfold fld. rewrite skipn_app_exact. apply firstn_all. Qed.

Lemma mvlan_ok : forall d v (src tl : list byte) (p : list Z),
  zs src = p -> length src = d -> (d < 16)%nat -> ~ In 0 p -> length tl = (15 - d)%nat -> 0 <= v < 2 ^ 32 ->
  mvlan_enc (p, v) (src ++ [Z_to_bv 8 0] ++ (tl ++ le4 (Z_to_bv 64 v))).
Proof.
  intros d v src tl p Zs Ls Hd Hp Lt Hv.
  set (F := src ++ [Z_to_bv 8 0] ++ tl).
  assert (LF : length F = 16%nat) by (unfold F; rewrite !app_length; cbn [length]; lia).
  replace (src ++ [Z_to_bv 8 0] ++ (tl ++ le4 (Z_to_bv 64 v))) with (F ++ le4 (Z_to_bv 64 v))
    by (unfold F; rewrite <- !app_assoc; reflexivity).
  unfold mvlan_enc. cbn [fst snd]. split; [rewrite app_length, LF, length_le4; reflexivity|]. split.
  - rewrite (fld_l F _ 16 LF). unfold cstr_enc. split; [exact LF|].
    split; [rewrite <- Zs; unfold zs; rewrite map_length; lia|]. split; [exact Hp|].
    rewrite <- Zs. unfold F, zs. rewrite !map_app. cbn [map app]. rewrite firstn_S_app. reflexivity.
  - rewrite (fld_r F _ 16 4 LF (length_le4 _)). split; [exact Hv | reflexivity].
Qed.

End V01SplitPure.

Import V01SplitPure.

(** ** Byte views and cells (generic in the segment list) *)
Lemma bytes_at_eq' : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma bat_sub : forall segs m a (l : list byte) k n, bytes_at segs m a l -> (k + n <= length l)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros segs m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma bat_firstn : forall segs m A (l : list byte) d, bytes_at segs m A l -> bytes_at segs m A (firstn d l).
Proof. intros segs m A l d H. rewrite <- (firstn_skipn d l) in H. apply bytes_at_app in H as [H _]. exact H. Qed.

Lemma rw_cells_CB_eq : forall segs m A A' n n' (bs : list byte), rw_cells segs m A [CB n bs] -> A = A' -> n = n' ->
  rw_cells segs m A' [CB n' bs].
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_cut : forall segs m A n1 n2 (bs : list byte), rw_cells segs m A [CB (n1 + n2) bs] ->
  rw_cells segs m A [CB n1 (firstn n1 bs)] /\ rw_cells segs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros segs m A n1 n2 bs [[Hwf Hb] Hw].
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hwf, Hb, Hw.
  destruct Hwf as [Hl _]. rewrite ?app_nil_r in Hb.
  rewrite <- (firstn_skipn n1 bs) in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite firstn_length_le in B2 by lia.
  destruct Hw as (Hw1 & Hw2 & Hw3).
  split; split.
  - split; cbn [cells_wf cell_wf cells_bytes cbytes].
    + split; [rewrite firstn_length_le by lia; reflexivity | exact I].
    + rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros k Hk. apply Hw3. lia.
  - split; cbn [cells_wf cell_wf cells_bytes cbytes].
    + split; [rewrite skipn_length; lia | exact I].
    + rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros k Hk.
    replace (A + Z.of_nat n1 + k) with (A + (Z.of_nat n1 + k)) by lia. apply Hw3. lia.
Qed.

Lemma rw_cells_cat : forall segs m A A' n1 n2 (b1 b2 : list byte), A' = A + Z.of_nat n1 ->
  rw_cells segs m A [CB n1 b1] -> rw_cells segs m A' [CB n2 b2] -> rw_cells segs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros segs m A A' n1 n2 b1 b2 -> [[W1 B1] R1] [[W2 B2] R2].
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in W1, B1, R1, W2, B2, R2.
  destruct W1 as [L1 _]. destruct W2 as [L2 _]. rewrite ?app_nil_r in B1, B2.
  destruct R1 as (R1a & R1b & R1c). destruct R2 as (R2a & R2b & R2c).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite app_length; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|]. rewrite L1. exact B2.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros k Hk.
    destruct (Z.lt_ge_cases k (Z.of_nat n1)) as [Hlt|Hge]; [apply R1c; lia|].
    replace (A + k) with (A + Z.of_nat n1 + (k - Z.of_nat n1)) by lia. apply R2c. lia.
Qed.

Lemma rw_cells_overwrite : forall segs m A n (j bs : list byte), rw_cells segs m A [CB n j] -> length bs = n ->
  rw_cells segs (write_to_mem m (wa A) bs) A [CB n bs].
Proof.
  intros segs m A n j bs H L.
  pose proof (rw_cells_write segs m A [CB n j] 0 (CB n j) (CB n bs) H eq_refl eq_refl L) as W.
  replace (A + Z.of_nat 0) with A in W by lia. exact W.
Qed.

Lemma munch_write_self : forall m a (bs : list byte), 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  munch [(a, a + Z.of_nat (length bs))] m (write_to_mem m (wa a) bs).
Proof.
  intros m a bs H1 H2. apply munch_write; [apply munch_refl | exact H1 | exact H2 |]. cbn [inside]. left. lia.
Qed.

(** ** Tactics of the walk *)
(** A branch the context refutes: [br_n] not taken, [br_t] taken (a closed condition may be decided already). *)
Ltac br_n := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; cbv iota;
      [exfalso; zify_cond K; first [lia | Z.div_mod_to_equations; lia] | clear K]
  | _ => idtac end.
Ltac br_t := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; cbv iota;
      [clear K | exfalso; zify_cond K; first [lia | Z.div_mod_to_equations; lia]]
  | _ => idtac end.
(** A register equation at a lemma's entry. *)
Ltac weq := cbv delta [zxb]; zsimp;
  rewrite ?zb_lxor_ones by lia; rewrite ?land15_dig by lia;
  try decide_tests; cbn [Z.b2z];
  first [reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia].

(** ** The walk *)
Section Split.
Variable X : vctx.
Hypothesis GEO : V01_geo X.
Hypothesis HMC : memcpy_contract.
Hypothesis HSR : strrchr_contract.
Variable i : nat.
Hypothesis HJ : V01_JOINat X i.
Hypothesis HA : V01_ACCat X i.
Variables (tb : list (list Z * Z)) (a : Z).
Hypothesis HI : V01_inv X i tb a.
Hypothesis Hi : (i < length (v_segs X))%nat.
Hypothesis Hi32 : (i < 32)%nat.
Hypothesis Hign : ms_ignore (nth i (v_segs X) mseg_d) = false.
Variable f16 : list byte.
Hypothesis HF : cstr_enc 16 (ms_name (nth i (v_segs X) mseg_d)) f16.

Local Notation NA := (v_mm X + 256 * Z.of_nat i).
Local Notation nm := (ms_name (nth i (v_segs X) mseg_d)).
Local Notation nb := (firstn (length (ms_name (nth i (v_segs X) mseg_d))) f16).

(** The state of the stretch: s1 = s7 = name, s2 = ~m, s3 = m, s4 = -1, s6 = -name, s9 = i, s10 = 4094,
    s11 = m + MC_N as in V01_SPLITat; the other registers are named. *)
Local Abbreviation VST pc m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 :=
  (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i))
           x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 (18446744073709551615 - v_mm X)) (Z_to_bv 64 (v_mm X)) (Z_to_bv 64 18446744073709551615)
           x21 (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i))) (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x24
           (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
      (v_F X) (Z_to_bv 64 pc) (v_fc X) None m (seg_rom rsegs)).

Lemma bnd : 4096 <= v_mm X /\ v_mm X + 9236 <= v_lo X /\ 393216 < v_lo X /\ v_S X <= 140737488355328 /\
  v_lo X = v_S X - 65536 /\ v_sp X = v_S X - 240 /\ v_buf X = v_S X - 144 /\ NA + 16 <= v_lo X /\ 4096 <= NA.
Proof.
  pose proof GEO as G. unfold V01_geo in G.
  destruct G as (_ & Glo & GS & _ & _ & _ & _ & _ & Gm1 & _ & Gm2 & _).
  unfold v_buf, v_sp, v_lo, V01_FRAME, SEG_M_SIZE in *. change (2 ^ 47) with 140737488355328 in GS.
  repeat split; lia.
Qed.

Lemma mm16 : v_mm X mod 16 = 0.
Proof. pose proof GEO as G. unfold V01_geo in G. destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

(** Every cell of an interface point's memory but the 20-byte buffer. *)
Definition rest (m : word -> option byte) : Prop :=
  V01_env X m /\
  rw_cells rsegs m (v_sp X)
    (V01_cells X (Z_to_bv 64 (18446744073709551615 - v_buf X)) (Z_to_bv 64 MASK_PARENT)
       (Z_to_bv 64 (18446744073709551615 - v_mt X)) a (Z.of_nat (length tb))) /\
  (exists jn : list byte, rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; C4 (Z_to_bv 64 (Z.of_nat (v_n0 X)))]) /\
  rtab_at rsegs m (v_tab X) (v_tab0 X) /\
  guard_at rsegs m (v_tab X) (v_cap X) /\
  (exists ft : list byte, rw_cells rsegs m (v_tab X + RVLAN_SIZE * Z.of_nat (v_n0 X))
     [CB (Z.to_nat (RVLAN_SIZE * (v_cap X - Z.of_nat (v_n0 X)))) ft]) /\
  mtab_at rsegs m (v_mt X) tb /\
  (exists fm : list byte, rw_cells rsegs m (v_mt X + MVLAN_SIZE * Z.of_nat (length tb))
     [CB (Z.to_nat (MVLAN_SIZE * (v_cap X + 1 - Z.of_nat (length tb)))) fm]) /\
  Z.of_nat (length tb) <= v_cap X /\
  munch (V01_W X) (v_m0 X) m /\ wmono rsegs (v_m0 X) m.

Lemma lmem_rest : forall m, V01_lmem X a tb m -> rest m /\ exists jb, rw_cells rsegs m (v_buf X) [CB 20 jb].
Proof.
  intros m (E & C & J & B & R & G & F & T & M & L & MU & WM).
  split; [|exact B].
  exact (conj E (conj C (conj J (conj R (conj G (conj F (conj T (conj M (conj L (conj MU WM)))))))))).
Qed.

Lemma rest_lmem : forall m, rest m -> (exists jb, rw_cells rsegs m (v_buf X) [CB 20 jb]) -> V01_lmem X a tb m.
Proof.
  intros m (E & C & J & R & G & F & T & M & L & MU & WM) B.
  exact (conj E (conj C (conj J (conj B (conj R (conj G (conj F (conj T (conj M (conj L (conj MU WM))))))))))).
Qed.

Ltac dj := cbn [disjoint_from]; split; [lia | exact I].

(** [rest] across a write set [lo', hi') inside [lo, S - 124) that leaves main's frame cells alone (below sp, or in
    the buffer). *)
Lemma rest_transport : forall m m' lo' hi', rest m -> munch [(lo', hi')] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' (v_lo X) (v_sp X) -> v_lo X <= lo' -> hi' <= v_S X - 124 ->
  (hi' <= v_sp X \/ v_buf X <= lo') -> rest m'.
Proof.
  intros m m' lo' hi' (E & C & (jn & J) & (bt & BT & ET) & G & (ft & F) & (bm & BM & EM) & (fm & FM) & L & MU & WM)
    MU' WM' MI' ST' Hlo Hhi Hcase.
  destruct E as (_ & _ & ROM & GOT & (gv & GV) & (ev & EV) & ENP & (bc & BC & EC) & (bmm & BMM & EMM)).
  pose proof bnd as (Bm & Bml & Blo & BS & Elo & Esp & Ebuf & _ & _).
  pose proof GEO as GG. unfold V01_geo in GG.
  destruct GG as (_ & _ & _ & _ & Gcap & Gc1 & _ & Gc2 & _ & _ & _ & Gt1 & _ & Gt2 & Gu1 & _ & Gu2 & _).
  assert (Ln0 : Z.of_nat (length (v_tab0 X)) <= v_cap X).
  { unfold v_tab0, v_cap, seg_tab0, seg_cap. apply vlan_init_len. unfold v_cap, seg_cap in Gcap. lia. }
  pose proof ET as (LT & _). pose proof EM as (LM & _). pose proof EC as (LC & _). pose proof EMM as (LMM & _).
  assert (Egg : sa_got_guard SA = 0x221b0) by reflexivity.
  assert (Egd : sa_guard SA = 0x53820) by reflexivity.
  assert (LENP : length (zb (S_enp ++ [0])) = 7%nat) by (vm_compute; reflexivity).
  unfold v_ntab, v_nmt, v_n0, RVLAN_SIZE, MVLAN_SIZE, SEG_C_SIZE, SEG_M_SIZE, guard_at, V01_ERRNO, V01_ENP in *.
  assert (T_GOT : bytes_at rsegs m' (sa_got_guard SA) (le8 (Z_to_bv 64 (sa_guard SA)))).
  { eapply bytes_at_transport; [exact GOT | exact MU' |]. rewrite length_le8. dj. }
  assert (T_GV : bytes_at rsegs m' (sa_guard SA) (le8 gv)).
  { eapply bytes_at_transport; [exact GV | exact MU' |]. rewrite length_le8. dj. }
  assert (T_EV : rw_cells rsegs m' (0x335b0 - 164) [C4 ev]).
  { eapply rw_cells_transport; [exact EV | exact MU' | exact WM' |]. cbn [cells_size csize]. dj. }
  assert (T_ENP : bytes_at rsegs m' 0x10539 (zb (S_enp ++ [0]))).
  { eapply bytes_at_transport; [exact ENP | exact MU' |]. rewrite LENP. dj. }
  assert (T_BC : bytes_at rsegs m' (v_c X) bc).
  { eapply bytes_at_transport; [exact BC | exact MU' |]. dj. }
  assert (T_BMM : bytes_at rsegs m' (v_mm X) bmm).
  { eapply bytes_at_transport; [exact BMM | exact MU' |]. dj. }
  assert (T_C : rw_cells rsegs m' (v_sp X)
    (V01_cells X (Z_to_bv 64 (18446744073709551615 - v_buf X)) (Z_to_bv 64 MASK_PARENT)
       (Z_to_bv 64 (18446744073709551615 - v_mt X)) a (Z.of_nat (length tb)))).
  { eapply rw_cells_transport; [exact C | exact MU' | exact WM' |]. unfold V01_cells. cbn [cells_size csize]. dj. }
  assert (T_J : rw_cells rsegs m' (v_sp X + 0x58) [CB 4 jn; C4 (Z_to_bv 64 (Z.of_nat (length (v_tab0 X))))]).
  { eapply rw_cells_transport; [exact J | exact MU' | exact WM' |]. cbn [cells_size csize]. dj. }
  assert (T_BT : bytes_at rsegs m' (v_tab X) bt).
  { eapply bytes_at_transport; [exact BT | exact MU' |]. dj. }
  assert (T_G : bytes_at rsegs m' (v_tab X + 18 * v_cap X) GUARD_BYTES).
  { eapply bytes_at_transport; [exact G | exact MU' |]. unfold GUARD_BYTES. rewrite repeat_length. dj. }
  assert (T_F : rw_cells rsegs m' (v_tab X + 18 * Z.of_nat (length (v_tab0 X)))
     [CB (Z.to_nat (18 * (v_cap X - Z.of_nat (length (v_tab0 X))))) ft]).
  { eapply rw_cells_transport; [exact F | exact MU' | exact WM' |]. cbn [cells_size csize]. dj. }
  assert (T_BM : bytes_at rsegs m' (v_mt X) bm).
  { eapply bytes_at_transport; [exact BM | exact MU' |]. dj. }
  assert (T_FM : rw_cells rsegs m' (v_mt X + 20 * Z.of_nat (length tb))
     [CB (Z.to_nat (20 * (v_cap X + 1 - Z.of_nat (length tb)))) fm]).
  { eapply rw_cells_transport; [exact FM | exact MU' | exact WM' |]. cbn [cells_size csize]. dj. }
  assert (T_MU : munch (V01_W X) (v_m0 X) m').
  { apply (munch_trans (V01_W X) (v_m0 X) m m' MU). apply (munch_weaken [(lo', hi')] (V01_W X) m m'); [|exact MU'].
    intros x Hx. unfold V01_W in Hx. cbn [outside] in Hx |- *. destruct Hx as [H1 _]. split; [lia | exact I]. }
  pose proof (wmono_trans rsegs (v_m0 X) m m' WM WM') as T_WM.
  exact (conj (conj MI' (conj ST' (conj ROM (conj T_GOT (conj (ex_intro _ gv T_GV) (conj (ex_intro _ ev T_EV)
           (conj T_ENP (conj (ex_intro _ bc (conj T_BC EC)) (ex_intro _ bmm (conj T_BMM EMM))))))))))
         (conj T_C (conj (ex_intro _ jn T_J) (conj (ex_intro _ bt (conj T_BT ET)) (conj T_G
         (conj (ex_intro _ ft T_F) (conj (ex_intro _ bm (conj T_BM EM)) (conj (ex_intro _ fm T_FM)
         (conj L (conj T_MU T_WM)))))))))).
Qed.

(** A store into the buffer. *)
Lemma rest_store : forall m A (bs : list byte), rest m ->
  store_ok rsegs m (wa A) (length bs) = true -> v_buf X <= A -> A + Z.of_nat (length bs) <= v_S X - 124 ->
  rest (write_to_mem m (wa A) bs).
Proof.
  intros m A bs R HS H1 H2. pose proof bnd as (_ & _ & Blo & BS & Elo & Esp & Ebuf & _ & _).
  pose proof R as ((MI & ST & _) & _).
  apply (rest_transport m _ A (A + Z.of_nat (length bs))); [exact R | apply munch_write_self; lia |
    apply (wmono_write rsegs m m (wa A) bs (wmono_refl rsegs m)) | apply mem_inv_store; assumption |
    apply stk_write; [exact ST | lia | lia] | lia | lia | right; lia].
Qed.

(** A callee whose write set lies in the buffer (memcpy). *)
Lemma rest_buf_call : forall m m' lo' hi', rest m -> munch [(lo', hi')] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> v_buf X <= lo' -> hi' <= v_S X - 124 -> rest m'.
Proof.
  intros m m' lo' hi' R MU WM MI H1 H2. pose proof bnd as (_ & _ & _ & _ & Elo & Esp & Ebuf & _ & _).
  pose proof R as ((_ & ST & _) & _).
  apply (rest_transport m m' lo' hi'); try assumption.
  - eapply stk_transport_disjoint; [exact ST | exact MU | exact WM | dj].
  - lia.
  - right; lia.
Qed.

(** A callee whose write set lies below sp (strrchr). *)
Lemma lmem_stack_call : forall m m' lo' hi', V01_lmem X a tb m -> munch [(lo', hi')] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' (v_lo X) (v_sp X) -> v_lo X <= lo' -> hi' <= v_sp X -> V01_lmem X a tb m'.
Proof.
  intros m m' lo' hi' HL MU WM MI ST H1 H2. pose proof bnd as (_ & _ & _ & _ & Elo & Esp & Ebuf & _ & _).
  destruct (lmem_rest m HL) as [R (jb & B)].
  apply rest_lmem.
  - apply (rest_transport m m' lo' hi'); try assumption; [lia | left; lia].
  - exists jb. eapply rw_cells_transport; [exact B | exact MU | exact WM |]. cbn [cells_size csize]. dj.
Qed.

(** The join after a refusal: m_split .. = None skips segment i. *)
Lemma join_ok : m_split nm = None -> V01_inv X (S i) tb a.
Proof.
  intros Hs. destruct HI as (H1 & H2 & H3). split; [lia|]. split; [lia|].
  rewrite <- H3. symmetry. apply decl_skip; assumption.
Qed.

(** ** The name: nm in the 16-byte field f16 at name = m + 256 i *)
Lemma nm_facts : (length nm < 16)%nat /\ ~ In 0 nm /\ length f16 = 16%nat /\
  firstn (S (length nm)) (zs f16) = nm ++ [0].
Proof. destruct HF as (H1 & H2 & H3 & H4). exact (conj H2 (conj H3 (conj H1 H4))). Qed.

Lemma nm_val : forall k, (k <= length nm)%nat -> bv_unsigned (nth k f16 ZERO) = nth k nm 0.
Proof.
  intros k Hk. destruct nm_facts as (L & _ & L16 & E).
  assert (E2 : nth k (firstn (S (length nm)) (zs f16)) 0 = nth k (nm ++ [0]) 0) by (rewrite E; reflexivity).
  rewrite nth_firstn_lt in E2 by lia. rewrite nth_app0 in E2. rewrite <- E2.
  unfold zs. change 0 with (bv_unsigned ZERO). rewrite map_nth. reflexivity.
Qed.

Lemma nm_read : forall m k, bytes_at rsegs m NA f16 -> (k < 16)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (NA + Z.of_nat k)) 1 = Some [nth k f16 ZERO].
Proof.
  intros m k H Hk. destruct nm_facts as (_ & _ & L16 & _).
  apply (u8ro_read rsegs m NA f16 (Z.of_nat k)); [exact H | rewrite Nat2Z.id; apply nth_error_nth'; lia | lia |
    reflexivity].
Qed.

Lemma nb_facts : length nb = length nm /\ zs nb = nm /\ ~ In ZERO nb /\
  f16 = nb ++ Z_to_bv 8 0 :: skipn (S (length nm)) f16.
Proof.
  destruct nm_facts as (L & HN & L16 & E).
  assert (Lnb : length nb = length nm) by (rewrite firstn_length_le; lia).
  assert (Znb : zs nb = nm).
  { unfold zs. rewrite <- firstn_map.
    replace (length nm) with (Nat.min (length nm) (S (length nm))) at 1 by lia.
    rewrite <- firstn_firstn. change (map bv_unsigned f16) with (zs f16). rewrite E.
    rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r. }
  assert (Nnb : ~ In ZERO nb).
  { apply SegBridge.nul_free_bytes. rewrite Znb. exact HN. }
  assert (Ez : nth (length nm) f16 ZERO = Z_to_bv 8 0).
  { apply bv_eq. rewrite nm_val by lia. rewrite nth_overflow by lia. reflexivity. }
  split; [exact Lnb|]. split; [exact Znb|]. split; [exact Nnb|].
  rewrite <- Ez. rewrite <- (firstn_skipn (length nm) f16) at 1. f_equal.
  apply skipn_cons_nth. lia.
Qed.

Lemma src_facts : forall d, (d <= length nm)%nat -> zs (firstn d f16) = firstn d nm /\ length (firstn d f16) = d.
Proof.
  intros d Hd. destruct nm_facts as (L & _ & L16 & _). destruct nb_facts as (_ & Znb & _ & _).
  split; [|rewrite firstn_length_le; lia].
  rewrite <- Znb. unfold zs. rewrite !firstn_map, firstn_firstn.
  replace (Nat.min d (length nm)) with d by lia. reflexivity.
Qed.

(** main's frame: the mask at 0x30(sp) and ~(sp + 0x60) at 8(sp). *)
Lemma fr_mask : forall m, rest m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (v_sp X + 48)) 8 = Some (le8 (Z_to_bv 64 MASK_PARENT)).
Proof.
  intros m (_ & C & _).
  exact (rw_cells_read_at rsegs m (v_sp X) _ 48 (C8 (Z_to_bv 64 MASK_PARENT)) 8 _ C eq_refl eq_refl eq_refl).
Qed.

Lemma fr_w8 : forall m, rest m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (v_sp X + 8)) 8 = Some (le8 (Z_to_bv 64 (18446744073709551615 - v_buf X))).
Proof.
  intros m (_ & C & _).
  exact (rw_cells_read_at rsegs m (v_sp X) _ 8 (C8 (Z_to_bv 64 (18446744073709551615 - v_buf X))) 8 _ C
           eq_refl eq_refl eq_refl).
Qed.

(** 0x1409c .. 0x140c8: memcpy(sp + 0x60, name, pn), the two traps, v.parent[pn] = 0, v.vid = vid; then ACC. *)
Lemma acc_tail : forall m di, V01_lmem X a tb m -> bytes_at rsegs m NA f16 -> SegModel.strrchr nm 46 = Some di ->
  (1 <= di)%nat -> nth (S di) nm 0 <> 0 ->
  forall v (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 w8 w21 : word),
  forallb h_parent_ok (firstn di nm) = true -> m_digits (skipn (S di) nm) 0 = Some v -> 1 <= v <= 4094 ->
  w8 = Z_to_bv 64 v -> w21 = Z_to_bv 64 (Z.of_nat di) ->
  evt rsegs (V01_post X) (VST 0x1409c m x1 x5 x6 x7 w8 x10 x11 x12 x13 x14 x15 x16 x17 w21 x24 x28 x29 x30 x31).
Proof.
  intros m di HL HB SR Hd1 Hnz1 v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 w8 w21
    HP HD Hv E8 E21.
  subst w8 w21.
  pose proof bnd as (Bm & Bml & Blo & BS & Elo & Esp & Ebuf & BNA & BNA2).
  destruct nm_facts as (L16 & HN & Lf & _).
  assert (Hdl : (di < length nm)%nat) by (apply (strrchr_bound nm 46); assumption).
  destruct (src_facts di ltac:(lia)) as (Zsrc & Lsrc).
  destruct (lmem_rest m HL) as [R (jb & B)].
  pose proof R as ((MI & _) & _).
  assert (Ljb : length jb = 20%nat) by (destruct B as [[W _] _]; cbn [cells_wf cell_wf] in W; tauto).
  replace 20%nat with (di + (1 + ((15 - di) + 4)))%nat in B by lia.
  apply rw_cells_cut in B as [P1 B]. apply rw_cells_cut in B as [P2 B]. apply rw_cells_cut in B as [P3 P4].
  (* 0x1409c addi a0,sp,0x60 ; mv a1,s7 ; mv a2,s5 ; jal memcpy *)
  step. step. step. step.
  eapply evt_cut.
  { eapply HMC with (src := firstn di f16) (junk := firstn di jb).
    - eapply bytes_at_eq'; [apply bat_firstn; exact HB | rewrite unsigned_lit by lia; lia].
    - rewrite unsigned_lit by lia. rewrite Lsrc. lia.
    - eapply rw_cells_CB_eq; [exact P1 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia].
    - rewrite !unsigned_lit by lia. lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU & WM &
    MI1 & CP & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite ?unsigned_lit in MU by lia.
  apply (rw_cells_CB_eq rsegs m1 _ (v_buf X) _ di) in CP;
    [| rewrite ?unsigned_lit by lia; lia | rewrite ?unsigned_lit by lia; lia].
  assert (R1 : rest m1) by (eapply rest_buf_call; [exact R | exact MU | exact WM | exact MI1 | lia | lia]).
  lazymatch type of MU with munch ?W _ _ =>
    apply (rw_cells_transport rsegs W m m1) in P2; [| exact MU | exact WM | cbn [cells_size csize]; dj];
    apply (rw_cells_transport rsegs W m m1) in P3; [| exact MU | exact WM | cbn [cells_size csize]; dj];
    apply (rw_cells_transport rsegs W m m1) in P4; [| exact MU | exact WM | cbn [cells_size csize]; dj]
  end.
  clear MU WM R P1 HL HB MI.
  (* 0x140ac a0 = 16 ; 0x140b0 bgeu s5,a0 -> trap (pn < 16) *)
  step. step. br_n.
  (* 0x140b4 ld a0,8(sp) ; 0x140b8 bltu a0,s5 -> trap (sp + 0x60 + pn does not wrap) *)
  pose proof (fr_w8 m1 R1) as RW8.
  step. step. br_n. clear RW8.
  (* 0x140bc a0 = sp + 0x60 + pn ; 0x140c4 sb zero,0(a0) *)
  assert (SO1 : store_ok rsegs m1 (wa (v_buf X + Z.of_nat di)) 1 = true).
  { eapply (rw_cells_store_ok_at rsegs m1 _ _ 0 _ 1); [exact P2 | reflexivity | reflexivity | unfold wa; f_equal; lia]. }
  step. step. step.
  lazymatch goal with |- context [write_to_mem m1 ?ad ?bs] =>
    replace (write_to_mem m1 ad bs) with (write_to_mem m1 (wa (v_buf X + Z.of_nat di)) [Z_to_bv 8 0])
      by (f_equal; first [reflexivity | unfold wa; f_equal; lia | vm_compute; reflexivity]) end.
  remember (write_to_mem m1 (wa (v_buf X + Z.of_nat di)) [Z_to_bv 8 0]) as m2 eqn:Em2.
  assert (R2 : rest m2) by (rewrite Em2; apply rest_store; [exact R1 | exact SO1 | lia | cbn [length]; lia]).
  assert (Q1 : rw_cells rsegs m2 (v_buf X) [CB di (firstn di f16)]).
  { rewrite Em2. apply rw_cells_frame; [exact CP | lia | cbn [length]; lia | cbn [cells_size csize length]; lia]. }
  assert (Q2 : rw_cells rsegs m2 (v_buf X + Z.of_nat di) [CB 1 [Z_to_bv 8 0]]).
  { rewrite Em2. apply rw_cells_overwrite with (j := firstn 1 (skipn di jb)); [exact P2 | reflexivity]. }
  assert (Q3 : rw_cells rsegs m2 (v_buf X + Z.of_nat di + Z.of_nat 1)
                 [CB (15 - di) (firstn (15 - di) (skipn 1 (skipn di jb)))]).
  { rewrite Em2. apply rw_cells_frame; [exact P3 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia]. }
  assert (Q4 : rw_cells rsegs m2 (v_buf X + 16) [CB 4 (skipn (15 - di) (skipn 1 (skipn di jb)))]).
  { rewrite Em2. apply rw_cells_frame; [eapply rw_cells_CB_eq; [exact P4 | lia | reflexivity] | lia |
      cbn [length]; lia | cbn [cells_size csize length]; lia]. }
  clear R1 SO1 CP P2 P3 P4.
  (* 0x140c8 sw s0,0x70(sp) *)
  assert (SO2 : store_ok rsegs m2 (wa (v_buf X + 16)) 4 = true).
  { eapply (rw_cells_store_ok_at rsegs m2 _ _ 0 _ 4); [exact Q4 | reflexivity | reflexivity | unfold wa; f_equal; lia]. }
  step.
  lazymatch goal with |- context [write_to_mem m2 ?ad ?bs] =>
    replace (write_to_mem m2 ad bs) with (write_to_mem m2 (wa (v_buf X + 16)) (le4 (Z_to_bv 64 v)))
      by (f_equal; first [reflexivity | unfold wa; f_equal; lia]) end.
  remember (write_to_mem m2 (wa (v_buf X + 16)) (le4 (Z_to_bv 64 v))) as m3 eqn:Em3.
  assert (R3 : rest m3).
  { rewrite Em3. apply rest_store; [exact R2 | rewrite length_le4; exact SO2 | lia | rewrite length_le4; lia]. }
  assert (Q1' : rw_cells rsegs m3 (v_buf X) [CB di (firstn di f16)]).
  { rewrite Em3. apply rw_cells_frame; [exact Q1 | lia | rewrite length_le4; lia |
      cbn [cells_size csize]; rewrite length_le4; lia]. }
  assert (Q2' : rw_cells rsegs m3 (v_buf X + Z.of_nat di) [CB 1 [Z_to_bv 8 0]]).
  { rewrite Em3. apply rw_cells_frame; [exact Q2 | lia | rewrite length_le4; lia |
      cbn [cells_size csize]; rewrite length_le4; lia]. }
  set (j3 := firstn (15 - di) (skipn 1 (skipn di jb))) in *.
  assert (Lj3 : length j3 = (15 - di)%nat).
  { unfold j3. rewrite firstn_length_le; [reflexivity|]. rewrite !skipn_length. lia. }
  assert (Q3' : rw_cells rsegs m3 (v_buf X + Z.of_nat di + Z.of_nat 1) [CB (15 - di) j3]).
  { rewrite Em3. apply rw_cells_frame; [exact Q3 | lia | rewrite length_le4; lia |
      cbn [cells_size csize]; rewrite length_le4; lia]. }
  assert (Q4' : rw_cells rsegs m3 (v_buf X + 16) [CB 4 (le4 (Z_to_bv 64 v))]).
  { rewrite Em3. eapply rw_cells_overwrite; [exact Q4 | apply length_le4]. }
  assert (T34 : rw_cells rsegs m3 (v_buf X + Z.of_nat di + Z.of_nat 1) [CB ((15 - di) + 4) (j3 ++ le4 (Z_to_bv 64 v))]).
  { eapply rw_cells_cat; [| exact Q3' | exact Q4']. lia. }
  assert (T234 : rw_cells rsegs m3 (v_buf X + Z.of_nat di)
                   [CB (1 + ((15 - di) + 4)) ([Z_to_bv 8 0] ++ (j3 ++ le4 (Z_to_bv 64 v)))]).
  { eapply rw_cells_cat; [| exact Q2' | exact T34]. lia. }
  assert (BUF : rw_cells rsegs m3 (v_buf X) [CB 20 (firstn di f16 ++ ([Z_to_bv 8 0] ++ (j3 ++ le4 (Z_to_bv 64 v))))]).
  { eapply rw_cells_CB_eq; [eapply rw_cells_cat; [| exact Q1' | exact T234] | reflexivity | lia]. lia. }
  destruct R3 as (E3 & C3 & J3 & T3 & G3 & F3 & M3 & FM3 & L3 & MU3 & WM3).
  eapply (HA tb a (firstn di nm) v); [exact E3 | exact C3 | exact J3 | exact BUF | | exact T3 | exact G3 | exact F3 |
    exact M3 | exact FM3 | exact L3 | exact MU3 | exact WM3 | exact HI | exact Hi | exact Hign | | lia].
  - apply (mvlan_ok di v (firstn di f16) j3 (firstn di nm)); [exact Zsrc | exact Lsrc | lia | | exact Lj3 | lia].
    intros Hin. apply HN. rewrite <- (firstn_skipn di nm). apply in_or_app. left. exact Hin.
  - apply (split_some nm di v); [exact SR | lia | exact Hnz1 | exact HD | lia | exact HP].
Qed.

(** The parent loop at byte j (n = pn - j bytes left): a0 = pn, a1 = j, a2 = ~name, s5 = pn, s0 = vid. *)
Lemma ploop : forall m di, V01_lmem X a tb m -> bytes_at rsegs m NA f16 -> SegModel.strrchr nm 46 = Some di ->
  (1 <= di)%nat -> nth (S di) nm 0 <> 0 ->
  forall n j v (x1 x5 x6 x7 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 w8 w10 w11 w12 w21 : word),
  (j + n = di)%nat -> (0 < n)%nat -> forallb h_parent_ok (firstn j nm) = true ->
  m_digits (skipn (S di) nm) 0 = Some v -> 1 <= v <= 4094 ->
  w8 = Z_to_bv 64 v -> w10 = Z_to_bv 64 (Z.of_nat di) -> w11 = Z_to_bv 64 (Z.of_nat j) ->
  w12 = Z_to_bv 64 (18446744073709551615 - NA) -> w21 = Z_to_bv 64 (Z.of_nat di) ->
  evt rsegs (V01_post X) (VST 0x14044 m x1 x5 x6 x7 w8 w10 w11 w12 x13 x14 x15 x16 x17 w21 x24 x28 x29 x30 x31).
Proof.
  intros m di HL HB SR Hd1 Hnz1.
  induction n as [|n IH]; intros j v x1 x5 x6 x7 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 w8 w10 w11 w12 w21
    Hjn Hn HP HD Hv E8 E10 E11 E12 E21; [lia|].
  subst w8 w10 w11 w12 w21.
  pose proof bnd as (Bm & Bml & Blo & BS & Elo & Esp & Ebuf & BNA & BNA2).
  destruct nm_facts as (L16 & HN & Lf & _).
  assert (Hdl : (di < length nm)%nat) by (apply (strrchr_bound nm 46); assumption).
  destruct (lmem_rest m HL) as [R _].
  pose proof (fr_mask m R) as RM. clear R.
  pose proof (nm_read m j HB ltac:(lia)) as RD.
  pose proof (nm_val j ltac:(lia)) as Vj.
  (* NEXT 0x14094: byte j passed; a1 = j + 1; bne a0,a1 -> the next byte, else the copy *)
  assert (NEXT : h_parent_ok (nth j nm 0) = true -> forall (y13 y14 y15 : word),
    evt rsegs (V01_post X) (VST 0x14094 m x1 x5 x6 x7 (Z_to_bv 64 v) (Z_to_bv 64 (Z.of_nat di))
      (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (18446744073709551615 - NA)) y13 y14 y15 x16 x17
      (Z_to_bv 64 (Z.of_nat di)) x24 x28 x29 x30 x31)).
  { intros OK y13 y14 y15.
    assert (HP' : forallb h_parent_ok (firstn (S j) nm) = true).
    { rewrite forallb_firstn_S by lia. rewrite HP, OK. reflexivity. }
    step. step.
    if_cases KN; cbv iota.
    - destruct n as [|n].
      + exfalso. zify_cond KN. lia.
      + clear KN. eapply (IH (S j) v); [lia | lia | exact HP' | exact HD | exact Hv | reflexivity | reflexivity | weq |
          reflexivity | reflexivity].
    - assert (n = 0)%nat by (zify_cond KN; lia). subst n.
      replace (S j) with di in HP' by lia.
      eapply (acc_tail m di HL HB SR Hd1 Hnz1 v); [exact HP' | exact HD | exact Hv | reflexivity | reflexivity]. }
  (* 0x14044 bltu a2,a1 -> trap (name + j does not wrap) ; a3 = name + j ; lbu a3,0(a3) *)
  step. br_n.
  step. step.
  (* 0x14050 .. 0x1405c: (ch - 48) & 255 < 11 -> NEXT (digits and ':') *)
  step. step. step. step.
  if_cases K1; cbv iota.
  { let c := kc K1 in
    assert (P : implb c (h_parent_ok (bv_unsigned (nth j f16 ZERO))) = true) by byte_fact (nth j f16 ZERO).
    rewrite K1 in P. cbn [implb] in P. rewrite Vj in P. apply NEXT. exact P. }
  (* 0x14060 .. 0x14070: ((ch & ~32) - 65) & 255 < 26 -> NEXT (letters) *)
  step. step. step. step. step.
  if_cases K2; cbv iota.
  { let c := kc K2 in
    assert (P : implb c (h_parent_ok (bv_unsigned (nth j f16 ZERO))) = true) by byte_fact (nth j f16 ZERO).
    rewrite K2 in P. cbn [implb] in P. rewrite Vj in P. apply NEXT. exact P. }
  (* 0x14074 .. 0x14080: 50 <u (ch & 255) - 45 -> join *)
  step. step. step. step.
  if_cases K3; cbv iota.
  { let c1 := kc K1 in let c2 := kc K2 in let c3 := kc K3 in
    assert (P : implb (negb c1 && negb c2 && c3) (negb (h_parent_ok (bv_unsigned (nth j f16 ZERO)))) = true)
      by byte_fact (nth j f16 ZERO).
    rewrite K1, K2, K3 in P. cbn [negb andb implb] in P. rewrite Vj in P. apply Bool.negb_true_iff in P.
    eapply HJ; [exact HL | apply join_ok | lia].
    apply (split_none_par nm di v); [exact SR | lia | exact Hnz1 | exact HD | lia |].
    apply (forallb_firstn_false h_parent_ok nm di j); [lia | lia | exact P]. }
  (* 0x14084 .. 0x14090: bit ch - 45 of the mask 2^50 + 3 at 0x30(sp): clear -> join, set -> NEXT *)
  step. step. step. step.
  if_cases K4; cbv iota.
  - let c1 := kc K1 in let c2 := kc K2 in let c3 := kc K3 in let c4 := kc K4 in
    assert (P : implb (negb c1 && negb c2 && negb c3 && c4) (negb (h_parent_ok (bv_unsigned (nth j f16 ZERO)))) = true)
      by byte_fact (nth j f16 ZERO).
    rewrite K1, K2, K3, K4 in P. cbn [negb andb implb] in P. rewrite Vj in P. apply Bool.negb_true_iff in P.
    eapply HJ; [exact HL | apply join_ok | lia].
    apply (split_none_par nm di v); [exact SR | lia | exact Hnz1 | exact HD | lia |].
    apply (forallb_firstn_false h_parent_ok nm di j); [lia | lia | exact P].
  - let c1 := kc K1 in let c2 := kc K2 in let c3 := kc K3 in let c4 := kc K4 in
    assert (P : implb (negb c1 && negb c2 && negb c3 && negb c4) (h_parent_ok (bv_unsigned (nth j f16 ZERO))) = true)
      by byte_fact (nth j f16 ZERO).
    rewrite K1, K2, K3, K4 in P. cbn [negb andb implb] in P. rewrite Vj in P. apply NEXT. exact P.
Qed.

(** 0x14028, after the digit loop: beqz s0 -> join; then pn into a0, s5, 0 into a1, ~name into a2. *)
Lemma post_dig : forall m di, V01_lmem X a tb m -> bytes_at rsegs m NA f16 -> SegModel.strrchr nm 46 = Some di ->
  (1 <= di)%nat -> nth (S di) nm 0 <> 0 ->
  forall v (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 w8 w10 : word),
  m_digits (skipn (S di) nm) 0 = Some v -> 0 <= v <= 4094 ->
  w8 = Z_to_bv 64 v -> w10 = Z_to_bv 64 (NA + Z.of_nat di) ->
  evt rsegs (V01_post X) (VST 0x14028 m x1 x5 x6 x7 w8 w10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31).
Proof.
  intros m di HL HB SR Hd1 Hnz1 v x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 w8 w10 HD Hv E8 E10.
  subst w8 w10.
  pose proof bnd as (Bm & Bml & Blo & BS & Elo & Esp & Ebuf & BNA & BNA2).
  destruct nm_facts as (L16 & HN & Lf & _).
  assert (Hdl : (di < length nm)%nat) by (apply (strrchr_bound nm 46); assumption).
  step.
  if_cases K; cbv iota.
  - eapply HJ; [exact HL | apply join_ok | lia].
    apply (split_none_v0 nm di v); [exact SR | lia | exact Hnz1 | exact HD |]. zify_cond K. lia.
  - assert (Hv1 : 1 <= v) by (zify_cond K; lia). clear K.
    step. step. step. step. step. step.
    eapply (ploop m di HL HB SR Hd1 Hnz1 di 0 v); [lia | lia | reflexivity | exact HD | lia | reflexivity | weq | weq |
      weq | weq].
Qed.

(** The digit loop at byte k (n = length name - k bytes left): s0 = vid so far, a0 = dot, a1 = name + k,
    a2 = name[k] (not the NUL), a4 = -10, a5 = 10. *)
Lemma dloop : forall m di, V01_lmem X a tb m -> bytes_at rsegs m NA f16 -> SegModel.strrchr nm 46 = Some di ->
  (1 <= di)%nat -> nth (S di) nm 0 <> 0 ->
  forall n k acc (x1 x5 x6 x7 x13 x16 x17 x21 x24 x28 x29 x30 x31 w8 w10 w11 w12 w14 w15 : word),
  (k + n = length nm)%nat -> (S di <= k)%nat -> nth k nm 0 <> 0 -> 0 <= acc <= 4094 ->
  m_digits (skipn (S di) nm) 0 = m_digits (skipn k nm) acc ->
  w8 = Z_to_bv 64 acc -> w10 = Z_to_bv 64 (NA + Z.of_nat di) -> w11 = Z_to_bv 64 (NA + Z.of_nat k) ->
  w12 = zxb (nth k f16 ZERO) -> w14 = Z_to_bv 64 (-10) -> w15 = Z_to_bv 64 10 ->
  evt rsegs (V01_post X) (VST 0x14000 m x1 x5 x6 x7 w8 w10 w11 w12 x13 w14 w15 x16 x17 x21 x24 x28 x29 x30 x31).
Proof.
  intros m di HL HB SR Hd1 Hnz1.
  induction n as [|n IH]; intros k acc x1 x5 x6 x7 x13 x16 x17 x21 x24 x28 x29 x30 x31 w8 w10 w11 w12 w14 w15
    Hkn Hk Hnz Hacc HD E8 E10 E11 E12 E14 E15.
  { exfalso. apply Hnz. apply nth_overflow. lia. }
  subst w8 w10 w11 w12 w14 w15.
  pose proof bnd as (Bm & Bml & Blo & BS & Elo & Esp & Ebuf & BNA & BNA2).
  destruct nm_facts as (L16 & HN & Lf & _).
  pose proof (nm_val k ltac:(lia)) as Vk.
  rewrite (skipn_cons_nth nm k 0) in HD by lia.
  (* 0x14000 a3 = a2 - 0x3a ; 0x14004 bltu a3,a4 -> join (not a digit) *)
  step. step.
  if_cases K1; cbv iota.
  { let c := kc K1 in
    assert (P : implb c ((bv_unsigned (nth k f16 ZERO) <? 48) || (57 <? bv_unsigned (nth k f16 ZERO))) = true)
      by byte_fact (nth k f16 ZERO).
    rewrite K1 in P. cbn [implb] in P. rewrite Vk in P.
    eapply HJ; [exact HL | apply join_ok | lia].
    apply (split_none_dig nm di); [exact SR | lia | exact Hnz1 | rewrite HD; apply dig_bad; exact P]. }
  assert (Dg : 48 <= nth k nm 0 <= 57).
  { let c := kc K1 in
    assert (P : implb (negb c) ((48 <=? bv_unsigned (nth k f16 ZERO)) && (bv_unsigned (nth k f16 ZERO) <=? 57)) = true)
      by byte_fact (nth k f16 ZERO).
    rewrite K1 in P. cbn [negb implb] in P. apply andb_prop in P as [P1 P2].
    apply Z.leb_le in P1. apply Z.leb_le in P2. lia. }
  clear K1.
  (* 0x14008 s0 = s0 * 10 + (a2 & 15) ; 0x14014 bltu s10,s0 -> join (vid > 4094) *)
  step. step. step. step.
  if_cases K2; cbv iota.
  { assert (Big : 4094 < acc * 10 + (nth k nm 0 - 48)).
    { zify_cond K2. rewrite ?land15_dig in K2 by lia. first [lia | Z.div_mod_to_equations; lia]. }
    eapply HJ; [exact HL | apply join_ok | lia].
    apply (split_none_dig nm di); [exact SR | lia | exact Hnz1 | rewrite HD; apply dig_big; lia]. }
  assert (Sm : acc * 10 + (nth k nm 0 - 48) <= 4094).
  { zify_cond K2. rewrite ?land15_dig in K2 by lia. first [lia | Z.div_mod_to_equations; lia]. }
  clear K2.
  rewrite dig_ok in HD by lia.
  (* 0x14018 beq a1,s4 -> trap ; lbu a2,1(a1) ; a1 += 1 ; 0x14024 bnez a2 -> the next byte *)
  step. br_n.
  pose proof (nm_read m (S k) HB ltac:(lia)) as RD.
  pose proof (nm_val (S k) ltac:(lia)) as Vk'.
  step. step. step.
  if_cases K3; cbv iota.
  - let c := kc K3 in
    assert (P : implb c (negb (bv_unsigned (nth (S k) f16 ZERO) =? 0)) = true) by byte_fact (nth (S k) f16 ZERO).
    rewrite K3 in P. cbn [implb] in P. apply Bool.negb_true_iff, Z.eqb_neq in P. rewrite Vk' in P.
    eapply (IH (S k) (acc * 10 + (nth k nm 0 - 48))); [lia | lia | exact P | lia | exact HD | weq | reflexivity | weq |
      reflexivity | reflexivity | reflexivity].
  - let c := kc K3 in
    assert (P : implb (negb c) (bv_unsigned (nth (S k) f16 ZERO) =? 0) = true) by byte_fact (nth (S k) f16 ZERO).
    rewrite K3 in P. cbn [negb implb] in P. apply Z.eqb_eq in P. rewrite Vk' in P.
    assert (Ek : (S k = length nm)%nat).
    { destruct (Nat.lt_ge_cases (S k) (length nm)) as [H|H]; [|lia]. exfalso. exact (nth_nz nm (S k) HN H P). }
    eapply (post_dig m di HL HB SR Hd1 Hnz1 (acc * 10 + (nth k nm 0 - 48))); [| lia | weq | reflexivity].
    rewrite HD, skipn_all2 by lia. reflexivity.
Qed.

(** 0x13fd0: strrchr(name, '.'), the dot tests, then the digit loop at the byte after the dot. *)
Lemma split_entry : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word),
  V01_lmem X a tb m -> bytes_at rsegs m NA f16 ->
  evt rsegs (V01_post X) (VST 0x13fd0 m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31).
Proof.
  intros m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 HL HB.
  pose proof bnd as (Bm & Bml & Blo & BS & Elo & Esp & Ebuf & BNA & BNA2).
  destruct nm_facts as (L16 & HN & Lf & _).
  destruct nb_facts as (Lnb & Znb & Nnb & Ef).
  assert (HB' : bytes_at rsegs m NA (nb ++ Z_to_bv 8 0 :: skipn (S (length nm)) f16)) by (rewrite <- Ef; exact HB).
  destruct (lmem_rest m HL) as [R _].
  pose proof R as ((MI & ST & _) & _).
  (* 0x13fd0 a1 = '.' ; a0 = s7 ; jal strrchr *)
  step. step. step.
  eapply evt_cut.
  { eapply HSR with (str := nb) (slack := skipn (S (length nm)) f16) (lo := v_lo X).
    - eapply bytes_at_eq'; [exact HB' | rewrite unsigned_lit by lia; lia].
    - exact Nnb.
    - rewrite unsigned_lit by lia. rewrite Lnb, skipn_length, Lf. pose proof mm16. Z.div_mod_to_equations. lia.
    - exact MI.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold STRRCHR_K. lia.
    - rewrite !unsigned_lit by lia. unfold STRRCHR_K. rewrite Lnb, skipn_length, Lf. left. lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU & WM &
    MI1 & ST1 & BS1).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite ?unsigned_lit in MU, ST1 by lia. unfold STRRCHR_K in MU.
  assert (HL1 : V01_lmem X a tb m1).
  { eapply lmem_stack_call; [exact HL | exact MU | exact WM | exact MI1 | exact ST1 | lia | lia]. }
  assert (HB1 : bytes_at rsegs m1 NA f16).
  { rewrite Ef. eapply bytes_at_eq'; [exact BS1 | rewrite unsigned_lit by lia; lia]. }
  clear HL HB HB' MU WM MI1 ST1 BS1 R MI ST.
  rewrite !unsigned_lit by lia. rewrite (Z.mod_small 46 256) by lia.
  rewrite (SegBridge.bridge_strrchr _ 46 nb Nnb ltac:(lia)), Znb.
  destruct (SegModel.strrchr nm 46) as [di|] eqn:SR.
  - assert (Hdl : (di < length nm)%nat) by (apply (strrchr_bound nm 46); assumption).
    (* 0x13fdc beqz a0 ; a4 = -10 ; a5 = 10 ; 0x13fe8 beq a0,s7 -> join when the dot is the first byte *)
    step. br_n. step. step. step.
    destruct (Nat.eq_dec di 0) as [D0|D0].
    + subst di. br_t. eapply HJ; [exact HL1 | apply join_ok; apply split_none_d0; exact SR | lia].
    + br_n.
      (* 0x13fec beq a0,s4 -> trap ; lbu a2,1(a0) ; 0x13ff4 beqz a2 -> join *)
      step. br_n.
      pose proof (nm_read m1 (S di) HB1 ltac:(lia)) as RD.
      pose proof (nm_val (S di) ltac:(lia)) as V1.
      step. step.
      if_cases K; cbv iota.
      * let c := kc K in
        assert (P : implb c (bv_unsigned (nth (S di) f16 ZERO) =? 0) = true) by byte_fact (nth (S di) f16 ZERO).
        rewrite K in P. cbn [implb] in P. apply Z.eqb_eq in P. rewrite V1 in P.
        eapply HJ; [exact HL1 | apply join_ok; apply (split_none_h0 nm di); [exact SR | exact P] | lia].
      * let c := kc K in
        assert (P : implb (negb c) (negb (bv_unsigned (nth (S di) f16 ZERO) =? 0)) = true)
          by byte_fact (nth (S di) f16 ZERO).
        rewrite K in P. cbn [negb implb] in P. apply Bool.negb_true_iff, Z.eqb_neq in P. rewrite V1 in P.
        assert (Hd2 : (S di < length nm)%nat).
        { destruct (Nat.lt_ge_cases (S di) (length nm)) as [H|H]; [exact H|]. exfalso. apply P.
          apply nth_overflow. lia. }
        (* 0x13ff8 s0 = 0 ; a1 = dot + 1 ; the digit loop *)
        step. step.
        eapply (dloop m1 di HL1 HB1 SR ltac:(lia) P (length nm - S di) (S di) 0); [lia | lia | exact P | lia |
          reflexivity | weq | weq | weq | reflexivity | weq | weq].
  - (* no dot *)
    step. br_t. eapply HJ; [exact HL1 | apply join_ok; apply split_none_r; exact SR | lia].
Qed.

End Split.

Theorem v01_split : forall X : vctx, V01_geo X -> K_V01 -> V01_SPLIT X.
Proof.
  intros X GEO KV i HJ HA tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 HL HI Hi Hign.
  destruct KV as (_ & HMC & HSR & _).
  pose proof HL as ((_ & _ & _ & _ & _ & _ & _ & _ & (mb & BM & EM)) & _).
  pose proof EM as (LM & N32 & SEG & _).
  assert (Hi32 : (i < 32)%nat) by (unfold v_segs in Hi; lia).
  destruct (SEG i Hi) as (L256 & HF & _).
  assert (HB1 : bytes_at rsegs m (v_mm X + Z.of_nat (256 * i)) (fld (256 * i) 256 mb)).
  { unfold fld. apply bat_sub; [exact BM | unfold SEG_M_SIZE in LM; lia]. }
  assert (HB : bytes_at rsegs m (v_mm X + 256 * Z.of_nat i) (fld 0 16 (fld (256 * i) 256 mb))).
  { pose proof (bat_sub rsegs m _ _ 0 16 HB1) as H. rewrite L256 in H.
    eapply bytes_at_eq'; [exact (H ltac:(lia)) | lia]. }
  clear HB1 SEG.
  eapply split_entry; eassumption.
Qed.
