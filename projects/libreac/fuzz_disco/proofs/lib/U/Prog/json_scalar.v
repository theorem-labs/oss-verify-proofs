From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import strlen_c bcmp_c memchr_c json_scalar_c.
Import ListNotations.
Open Scope Z_scope.

Ltac uz := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
  first [rewrite (unsigned_lit e) by lia | rewrite (unsigned_lit_wrap e)] end.
Ltac zcb := unfold bv_eqb, bv_ltu; uz; cbn [negb];
  repeat match goal with
  | |- negb ?x = true => apply (proj2 (Bool.negb_true_iff x))
  | |- negb ?x = false => apply (proj2 (Bool.negb_false_iff x))
  end;
  first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq]; first [lia | Z.div_mod_to_equations; lia].
Ltac bt := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; zcb] end.
Ltac bf := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; zcb] end.

Lemma ju_z256 : forall (P : Z -> bool), forallb P (zseq 256) = true -> forall z, 0 <= z < 256 -> P z = true.
Proof. intros P H z Hz. exact (brute256_ok P H z Hz). Qed.

Lemma ju_nd : forall z, 0 <= z < 256 -> bv_ltu (Z_to_bv 64 (z + -58)) (Z_to_bv 64 (-10)) = negb (jdigit z).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (ju_z256 (fun z => Bool.eqb (bv_ltu (Z_to_bv 64 (z + -58)) (Z_to_bv 64 (-10))) (negb (jdigit z)))
           ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma ju_hx1 : forall z, 0 <= z < 256 -> bv_ltu (Z_to_bv 64 (-11)) (Z_to_bv 64 (z + -58)) = jdigit z.
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (ju_z256 (fun z => Bool.eqb (bv_ltu (Z_to_bv 64 (-11)) (Z_to_bv 64 (z + -58))) (jdigit z))
           ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma ju_hx2 : forall z, 0 <= z < 256 -> jdigit z = false ->
  bv_ltu (Z_to_bv 64 (Z.land z 223 + -71)) (Z_to_bv 64 (-6)) = negb (jhexd z).
Proof.
  intros z Hz D. apply Bool.eqb_prop.
  pose proof (ju_z256 (fun z => implb (negb (jdigit z))
                 (Bool.eqb (bv_ltu (Z_to_bv 64 (Z.land z 223 + -71)) (Z_to_bv 64 (-6))) (negb (jhexd z))))
           ltac:(vm_compute; reflexivity) z Hz) as H.
  cbv beta in H. rewrite D in H. exact H.
Qed.

Lemma ju_ee : forall z, 0 <= z < 256 ->
  bv_eqb (Z_to_bv 64 (Z.lor z 32)) (Z_to_bv 64 101) = (z =? 101) || (z =? 69).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (ju_z256 (fun z => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.lor z 32)) (Z_to_bv 64 101)) ((z =? 101) || (z =? 69)))
           ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma ju_minus : forall z, 0 <= z < 256 -> ((z + -45) mod 18446744073709551616 <? 1) = (z =? 45).
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (ju_z256 (fun z => Bool.eqb ((z + -45) mod 18446744073709551616 <? 1) (z =? 45))
           ltac:(vm_compute; reflexivity) z Hz).
Qed.

Definition ju_esc : list byte := map (Z_to_bv 8) [34; 92; 47; 98; 102; 110; 114; 116; 117; 0].
Definition ju_true : list byte := map (Z_to_bv 8) [116; 114; 117; 101].
Definition ju_false : list byte := map (Z_to_bv 8) [102; 97; 108; 115; 101].
Definition ju_null : list byte := map (Z_to_bv 8) [110; 117; 108; 108].

Lemma ju_mc : forall z, 0 <= z < 256 -> (negb (memchr_res 66297 z 10 ju_esc =? 0) && negb (z =? 0)) = jesc z.
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (ju_z256 (fun z => Bool.eqb (negb (memchr_res 66297 z 10 ju_esc =? 0) && negb (z =? 0)) (jesc z))
           ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma ju_mcr : forall z, 0 <= z < 256 -> 0 <= memchr_res 66297 z 10 ju_esc < 2^64.
Proof.
  intros z Hz.
  pose proof (ju_z256 (fun z => (0 <=? memchr_res 66297 z 10 ju_esc) && (memchr_res 66297 z 10 ju_esc <? 2^64))
           ltac:(vm_compute; reflexivity) z Hz) as H.
  cbv beta in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma ju_mok : forall A c, memchr_ok A c 10 ju_esc.
Proof. intros A c. unfold memchr_ok. destruct (find_byte _ _); [left|]; cbn; lia. Qed.

Lemma ju_ro : forall m1 A bs, mem_inv rsegs m1 -> ro_bytes_b rsegs A bs = true -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2^64 -> bytes_at rsegs m1 A bs.
Proof. intros m1 A bs MI H HA HL. apply ro_bytes_at; try assumption. apply ro_bytes_b_sound. exact H. Qed.

Lemma ju_nz : forall l : list Z, forallb (fun z => negb (z =? 0) && (0 <=? z) && (z <? 256)) l = true ->
  ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  induction l as [|a l IH]; intros H; cbn; [tauto|].
  cbn in H. apply andb_prop in H. destruct H as [H1 H2]. apply andb_prop in H1. destruct H1 as [H1 H3].
  apply andb_prop in H1. destruct H1 as [H1 H4]. apply Bool.negb_true_iff, Z.eqb_neq in H1.
  apply Z.leb_le in H4. apply Z.ltb_lt in H3.
  intros [E|E]; [|exact (IH H2 E)].
  apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. change (bv_unsigned (Z_to_bv 8 0)) with 0 in E.
  unfold bv_wrap, bv_modulus in E. change (2 ^ Z.of_N 8) with 256 in E. rewrite Z.mod_small in E by lia. lia.
Qed.

Lemma ju_memcmp : forall n (P T : list byte) v, length P = n -> length T = n -> memcmp_model P T n = Some v ->
  -255 <= v <= 255 /\ (v = 0 <-> P = T).
Proof.
  induction n as [|n IH]; intros P T v HP HT HM.
  - destruct P, T; cbn in *; try lia. injection HM as <-. split; [lia|]. tauto.
  - destruct P as [|a P], T as [|b T]; cbn in HP, HT; try lia.
    cbn in HM. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH P T v ltac:(lia) ltac:(lia) HM) as [R I]. split; [exact R|].
      rewrite I. split; intro H.
      * f_equal; [apply bv_eq; exact E | exact H].
      * injection H as _ H. exact H.
    + injection HM as <-. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
      unfold bv_modulus in Ra, Rb. change (Z.of_N 8) with 8 in Ra, Rb.
      split; [lia|]. split; intro H; [lia|]. injection H as H _. subst. contradiction.
Qed.

Lemma ju_prefix0 : forall (w r : list byte), (length w <= length r)%nat ->
  (jprefix (map bv_unsigned w) (map bv_unsigned r) = true <-> firstn (length w) r = w).
Proof.
  induction w as [|a w IH]; intros r Hl; [cbn; tauto|].
  destruct r as [|c r]; cbn in Hl; [lia|].
  cbn [map jprefix length firstn]. rewrite andb_true_iff, Z.eqb_eq, IH by lia. split.
  - intros [E1 E2]. rewrite E2. f_equal. apply bv_eq. symmetry. exact E1.
  - intros E. injection E as E1 E2. split; [rewrite E1; reflexivity | exact E2].
Qed.

Lemma ju_skipn_map : forall (l : list byte) k, skipn k (map bv_unsigned l) = map bv_unsigned (skipn k l).
Proof. induction l as [|a l IH]; intros [|k]; cbn; auto. Qed.

Lemma ju_prefix : forall (w B : list byte) k, (k + length w <= length B)%nat ->
  (jprefix (map bv_unsigned w) (skipn k (map bv_unsigned B)) = true <-> firstn (length w) (skipn k B) = w).
Proof.
  intros w B k H. rewrite ju_skipn_map. apply ju_prefix0. rewrite length_skipn. lia.
Qed.

Lemma ju_sub : forall m a (B : list byte) k l, bytes_at rsegs m a B -> (k + l <= length B)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn l (skipn k B)).
Proof.
  intros m a B k l H Hk. rewrite <- (firstn_skipn k B) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length B)) with k in H by lia.
  rewrite <- (firstn_skipn l (skipn k B)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma ju_eqb_z : forall z k, 0 <= z < 2^64 -> 0 <= k < 2^64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 k) = (z =? k).
Proof. intros z k Hz Hk. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ju_ltu_z : forall z k, 0 <= z < 2^64 -> 0 <= k < 2^64 -> bv_ltu (Z_to_bv 64 z) (Z_to_bv 64 k) = (z <? k).
Proof. intros z k Hz Hk. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ju_hexd_dig : forall z, jhexd z = false -> jdigit z = false.
Proof. intros z H. unfold jhexd in H. destruct (jdigit z); [discriminate | reflexivity]. Qed.

Ltac hex_tac extra :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    F fc Q m1 z Hz KT KF;
  zstep; rewrite (ju_hx1 z Hz);
  destruct (jdigit z) eqn:D; cbn [negb];
  [ apply KT; unfold jhexd; rewrite D; reflexivity
  | zstep; zstep; zstep; zstep; rewrite (ju_hx2 z Hz D);
    destruct (jhexd z) eqn:Hd; cbn [negb]; [ extra; apply KT; reflexivity | apply KF; reflexivity ] ].

Local Notation HEXL T N := (forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
     x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (Q : machine_state -> Prop) (m1 : word -> option byte) (z : Z),
  0 <= z < 256 ->
  (jhexd z = true -> forall y10 y11 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 (Z_to_bv 64 (-11))
     x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 N) fc None m1 (seg_rom rsegs))) ->
  (jhexd z = false -> forall y10 y11 : word, evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 (Z_to_bv 64 (-11))
     x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14b80) fc None m1 (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 z) (Z_to_bv 64 (z + -58)) x12 (Z_to_bv 64 (-11))
     x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 T) fc None m1 (seg_rom rsegs))).

Lemma ju_hex2 : HEXL 0x14a70 0x14a84. Proof. hex_tac idtac. Qed.
Lemma ju_hex3 : HEXL 0x14a98 0x14aac. Proof. hex_tac idtac. Qed.
Lemma ju_hex4 : HEXL 0x14ac0 0x14ad4. Proof. hex_tac idtac. Qed.
Lemma ju_hex5 : HEXL 0x14ae8 0x14b04. Proof. hex_tac zstep. Qed.

Lemma ju_byte_range : forall c : byte, 0 <= bv_unsigned c < 256.
Proof. intros c. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. change (Z.of_N 8) with 8 in R. lia. Qed.

Lemma ju_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma ju_word : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z H. subst z. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma ju_eqb_lit : forall (x : word) k, 0 <= k < 2^64 -> bv_eqb x (Z_to_bv 64 k) = (bv_unsigned x =? k).
Proof. intros x k Hk. unfold bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma ju_rec3 : forall m a (x y z : word),
  bytes_at rsegs m (a + 0) (le8 x) -> bytes_at rsegs m (a + 8) (le8 y) -> bytes_at rsegs m (a + 16) (le4 z) ->
  bytes_at rsegs m a (le8 x ++ le8 y ++ le4 z).
Proof.
  intros m a x y z H1 H2 H3. rewrite Z.add_0_r in H1.
  apply bytes_at_app. split; [exact H1|]. rewrite length_le8.
  apply bytes_at_app. split; [exact H2|]. rewrite length_le8.
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) by lia. exact H3.
Qed.

Lemma ju_firstn1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Ltac js_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
      let E := addr_expr a in
      (lazymatch a with
       | wa _ => idtac
       | Z_to_bv 64 _ => change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs)
       | _ => replace (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs)
                by (f_equal; first [apply wa_of_var; lia | symmetry; apply wa_of_var; lia | addr_eq_tac])
       end);
      let H := fresh "HW" in
      assert (H : bytes_at rsegs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; simpl_sizes; lia);
      store_done
  end.

Ltac js_hs x off len :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with
      | H : wr_at rsegs mm (bv_unsigned x) 20 |- _ =>
          let HS := fresh "HS" in
          pose proof (wr_at_store_ok rsegs mm (bv_unsigned x) 20 off len H ltac:(lia) ltac:(lia)) as HS;
          try (lazymatch off with 0 => rewrite (wa_of_var x (bv_unsigned x + 0)) in HS by lia end)
      end
  end.

Section JS.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (lo : Z) (b i n v : word) (B : list byte).
Hypothesis HL : Z.of_nat (length B) = bv_unsigned n.
Hypothesis HBN : bv_unsigned b + bv_unsigned n <= 2^64.
Hypothesis LO : lo + 112 <= bv_unsigned sp.
Hypothesis L0 : 0 <= lo.
Hypothesis DV : bv_unsigned v + 20 <= bv_unsigned sp + -112 \/ bv_unsigned sp <= bv_unsigned v.
Hypothesis DL : 132576 + 24 <= bv_unsigned sp + -112 \/ bv_unsigned sp <= 132576.
Hypothesis HA : bv_unsigned v mod 8 = 0.

Local Notation POST := (json_scalar_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m b i v B).
Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -112)).
Local Notation FRC jk := [CB 8 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation BZ := (map bv_unsigned B).
Local Notation LT := (le8 (Z_to_bv 64 0x103aa) ++ le8 (Z_to_bv 64 0x10298) ++ le8 (Z_to_bv 64 0x10326)).

Definition ju_res (m1 : word -> option byte) (r : word) : Prop :=
  match jscalar BZ (bv_unsigned i) with
  | Some (e, k, s, l) =>
      r = Z_to_bv 64 e /\
      munch [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)] m m1 /\
      bytes_at rsegs m1 (bv_unsigned v) (le8 (Z_to_bv 64 (bv_unsigned b + s)) ++ le8 (Z_to_bv 64 l) ++ le4 (Z_to_bv 64 k))
  | None => r = Z_to_bv 64 0 /\ munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m1
  end.

Lemma ju_epi : forall m1 jk (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31 : word),
  rw_cells rsegs m1 (bv_unsigned sp + -112) (FRC jk) -> stk rsegs m1 lo (bv_unsigned sp + -112) ->
  wmono rsegs m m1 -> mem_inv rsegs m1 -> ju_res m1 x10 ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14b84) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FR ST WM MI RES.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold json_scalar_post, JSON_SCALAR_K.
  do 16 eexists. split; [reflexivity|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia.
  unfold ju_res in RES. exact RES.
Qed.

Lemma ju_fail0 : forall m1 jk (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31 : word),
  rw_cells rsegs m1 (bv_unsigned sp + -112) (FRC jk) -> stk rsegs m1 lo (bv_unsigned sp + -112) ->
  munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  jscalar BZ (bv_unsigned i) = None ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14b80) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FR ST MU WM MI HJ.
  zstep. eapply ju_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold ju_res. rewrite HJ. split; [reflexivity | exact MU].
Qed.

Lemma ju_main_ge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bv_unsigned n <= bv_unsigned i -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 b i n v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14970) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 HGE MI ST.
  pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word i) as Ri. pose proof (zr_word n) as Rn. unfold inr64 in *.
  carve_frame 112%nat ST.
  do 14 zstep. zstep. bt.
  eapply ju_fail0; [eassumption | eassumption | eassumption | eassumption | eassumption |].
  unfold jscalar, jlen. rewrite length_map, HL.
  replace (bv_unsigned n <=? bv_unsigned i) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Hypothesis HI : bv_unsigned i < bv_unsigned n.
Hypothesis DB : bv_unsigned b + bv_unsigned n <= bv_unsigned sp + -112 \/ bv_unsigned sp <= bv_unsigned b.

Definition JI (m1 : word -> option byte) (jk : list byte) : Prop :=
  rw_cells rsegs m1 (bv_unsigned sp + -112) (FRC jk) /\ stk rsegs m1 lo (bv_unsigned sp + -112) /\
  munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
  bytes_at rsegs m1 (bv_unsigned b) B /\ wr_at rsegs m1 (bv_unsigned v) 20 /\ bytes_at rsegs m1 132576 LT.

Lemma ju_fail : forall m1 jk (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31 : word),
  JI m1 jk -> jscalar BZ (bv_unsigned i) = None ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14b80) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & _) HJ.
  eapply ju_fail0; eassumption.
Qed.

Lemma ju_fail84 : forall m1 jk (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31 : word),
  JI m1 jk -> jscalar BZ (bv_unsigned i) = None ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14b84) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & _) HJ.
  eapply ju_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold ju_res. rewrite HJ. split; [reflexivity | exact MU].
Qed.

Lemma ju_rd : forall m1 (j : Z), bytes_at rsegs m1 (bv_unsigned b) B -> 0 <= j < bv_unsigned n ->
  ov_read_bytes rsegs m1 (wa (bv_unsigned b + j)) 1 = Some [nth (Z.to_nat j) B (Z_to_bv 8 0)].
Proof.
  intros m1 j H Hj. rewrite (bytes_at_read rsegs m1 _ B j 1 H) by lia.
  f_equal. apply ju_firstn1. lia.
Qed.

Lemma ju_jbyte : forall j, jbyte BZ j = bv_unsigned (nth (Z.to_nat j) B (Z_to_bv 8 0)).
Proof. intros j. unfold jbyte. change 0 with (bv_unsigned (Z_to_bv 8 0)). apply map_nth. Qed.

Lemma ju_jbr : forall j, 0 <= jbyte BZ j < 256.
Proof. intros j. rewrite ju_jbyte. apply ju_byte_range. Qed.

Lemma ju_jlen : jlen BZ = bv_unsigned n.
Proof. unfold jlen. rewrite length_map. exact HL. Qed.

Lemma ju_jdigits_S : forall j f, jdigits BZ j (S f) =
  if (j <? bv_unsigned n) && jdigit (jbyte BZ j) then jdigits BZ (j + 1) f else j.
Proof. intros j f. cbn [jdigits]. rewrite ju_jlen. reflexivity. Qed.

Lemma ju_jdigits_n : forall f, jdigits BZ (bv_unsigned n) f = bv_unsigned n.
Proof. intros [|f]; [reflexivity|]. rewrite ju_jdigits_S, Z.ltb_irrefl. reflexivity. Qed.

Lemma ju_jdigits_range : forall f j, j <= bv_unsigned n -> j <= jdigits BZ j f <= bv_unsigned n.
Proof.
  induction f as [|f IH]; intros j Hj; [cbn; lia|]. rewrite ju_jdigits_S.
  destruct (Z.ltb_spec j (bv_unsigned n)); cbn [andb]; [|lia].
  destruct (jdigit _); [|lia]. specialize (IH (j + 1) ltac:(lia)). lia.
Qed.

Definition jrest_exp (j2 : Z) : option jtok :=
  match jexp BZ j2 with None => None | Some j3 => Some (j3, 2, bv_unsigned i, j3 - bv_unsigned i) end.
Definition jrest_frac (j1 : Z) : option jtok :=
  match jfrac BZ j1 with None => None | Some j2 => jrest_exp j2 end.

Lemma ju_jexp_n : forall j, bv_unsigned n <= j -> jrest_exp j = Some (j, 2, bv_unsigned i, j - bv_unsigned i).
Proof.
  intros j Hj. unfold jrest_exp, jexp. rewrite ju_jlen.
  replace (j <? bv_unsigned n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ju_jfrac_n : forall j, bv_unsigned n <= j -> jrest_frac j = jrest_exp j.
Proof.
  intros j Hj. unfold jrest_frac, jfrac. rewrite ju_jlen.
  replace (j <? bv_unsigned n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ju_tok : forall m1 jk j3 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                                  x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = j3 -> bv_unsigned i <= j3 <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar BZ (bv_unsigned i) = Some (j3, 2, bv_unsigned i, j3 - bv_unsigned i) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14d24) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV & HT) H10 HJ3 H18 HJ.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word v) as Rv. pose proof (zr_word i) as Ri.
  pose proof (zr_word x10) as R10. unfold inr64 in *.
  assert (BV : 0 <= bv_unsigned v /\ bv_unsigned v + 20 <= 2^64) by (destruct HV as (? & ? & _); lia).
  apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  zstep. zstep. rewrite (ju_land7 _ HA). bf.
  zstep. zstep.
  js_hs v 0 8%nat. zstep. js_store.
  js_hs v 8 8%nat. zstep. js_store.
  js_hs v 16 4%nat. zstep. js_store.
  zstep.
  eapply ju_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold ju_res. rewrite HJ. split; [apply ju_word; exact H10|]. split; [exact MU|].
  rewrite (ju_word x18 _ H18) in HW. rewrite H10 in HW0. apply ju_rec3; assumption.
Qed.

Ltac mkJI := unfold JI; repeat match goal with |- _ /\ _ => split; [eassumption|] end; eassumption.

Ltac rng := repeat match goal with
  | x : word |- _ => lazymatch goal with _ : 0 <= bv_unsigned x < 2^64 |- _ => fail | _ => idtac end;
      let R := fresh "R" in pose proof (zr_word x) as R; unfold inr64 in R
  end.

Lemma ju_explp : forall (f : nat) m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27
                                          x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x11 = k -> bv_unsigned i <= k < bv_unsigned n -> bv_unsigned n - k <= Z.of_nat f ->
  x10 = Z_to_bv 64 (-10) -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = Some (jdigits BZ k f, 2, bv_unsigned i, jdigits BZ k f - bv_unsigned i) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14d00) fc None m1 (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
      HJI H11 Hk Hf H10 H18 H23 HJ; [lia|].
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). subst x10. rng.
  pose proof (ju_rd m1 k HB ltac:(lia)) as HR. pose proof (ju_jbr k) as Jk.
  zstep. bf.
  zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_nd by lia.
  rewrite ju_jdigits_S, (proj2 (Z.ltb_lt _ _) (proj2 Hk)) in HJ. cbn [andb] in HJ.
  destruct (jdigit (jbyte BZ k)) eqn:D; cbn [negb]; rewrite ?D in HJ; cbv beta iota in HJ.
  - zstep. zstep.
    destruct (Z.eqb_spec (bv_unsigned n) (k + 1)) as [E|E].
    + bf. zstep. zstep. zstep. replace (k + 1) with (bv_unsigned n) in HJ by lia. rewrite ju_jdigits_n in HJ.
      eapply ju_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
    + bt. eapply (IH m1 jk (k + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | lia | reflexivity
                                      | exact H18 | exact H23 | exact HJ].
  - zstep.
    eapply ju_tok; [exact HJI | exact H11 | lia | exact H18 | exact HJ].
Qed.

Definition jrest_expd (k : Z) : option jtok :=
  match (if jdig_at BZ k then Some (jdigits BZ k (length BZ)) else None) with
  | None => None | Some j3 => Some (j3, 2, bv_unsigned i, j3 - bv_unsigned i) end.

Lemma ju_expd : forall m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27
                                 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x11 = k -> bv_unsigned i <= k <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i -> bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = jrest_expd k ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14ce4) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    HJI H11 Hk H18 H23 HJ.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). rng.
  unfold jrest_expd, jdig_at in HJ. rewrite ju_jlen in HJ.
  zstep.
  destruct (Z.ltb_spec k (bv_unsigned n)) as [Kn|Kn].
  2: { bt. cbn [andb] in HJ. eapply ju_fail; [exact HJI | exact HJ]. }
  bf. zstep. bf.
  pose proof (ju_rd m1 k HB ltac:(lia)) as HR. pose proof (ju_jbr k) as Jk.
  zstep. zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_nd by lia.
  cbn [andb] in HJ.
  destruct (jdigit (jbyte BZ k)) eqn:D; cbn [negb]; rewrite ?D in HJ; cbv beta iota in HJ.
  - eapply (ju_explp (length BZ) m1 jk k); [exact HJI | exact H11 | lia | rewrite length_map; lia | reflexivity
                                           | exact H18 | exact H23 | exact HJ].
  - eapply ju_fail; [exact HJI | exact HJ].
Qed.

Lemma ju_exp : forall m1 jk j2 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27
                                 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = j2 -> bv_unsigned i <= j2 <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i -> bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = jrest_exp j2 ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14ca0) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    HJI H10 Hj H18 H23 HJ.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). rng.
  zstep.
  destruct (Z.ltb_spec j2 (bv_unsigned n)) as [Jn|Jn].
  2: { bt. rewrite ju_jexp_n in HJ by lia. eapply ju_tok; [exact HJI | exact H10 | lia | exact H18 | exact HJ]. }
  bf. zstep. bf.
  pose proof (ju_rd m1 j2 HB ltac:(lia)) as HR. pose proof (ju_jbr j2) as Jk.
  zstep. zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_ee by lia.
  unfold jrest_exp, jexp in HJ. rewrite ju_jlen, (proj2 (Z.ltb_lt _ _) Jn) in HJ. cbn [andb] in HJ.
  destruct ((jbyte BZ j2 =? 101) || (jbyte BZ j2 =? 69)) eqn:EE; cbn [negb]; rewrite ?EE in HJ; cbv beta iota zeta in HJ.
  2: { eapply ju_tok; [exact HJI | exact H10 | lia | exact H18 | exact HJ]. }
  zstep. zstep.
  destruct (Z.ltb_spec (j2 + 1) (bv_unsigned n)) as [J1|J1].
  2: { bt. try replace (j2 + 1 <? bv_unsigned n) with false in HJ by (symmetry; apply Z.ltb_ge; lia).
       cbn [andb] in HJ. cbv beta iota in HJ.
       eapply (ju_expd m1 jk (j2 + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | exact H18 | exact H23 | exact HJ]. }
  bf. try rewrite (proj2 (Z.ltb_lt _ _) J1) in HJ. cbn [andb] in HJ.
  zstep. bf.
  pose proof (ju_rd m1 (j2 + 1) HB ltac:(lia)) as HR1. pose proof (ju_jbr (j2 + 1)) as Jk1.
  zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_eqb_z by lia.
  destruct (jbyte BZ (j2 + 1) =? 45) eqn:E45; cbn [negb].
  - rewrite ?E45, ?orb_true_r in HJ. cbv beta iota in HJ.
    zstep. eapply (ju_expd m1 jk (j2 + 2)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | exact H18 | exact H23 | exact HJ].
  - zstep. zstep. rewrite ju_eqb_z by lia. rewrite ?E45, ?orb_false_r in HJ.
    destruct (jbyte BZ (j2 + 1) =? 43) eqn:E43; cbn [negb]; rewrite ?E43 in HJ; cbv beta iota in HJ.
    + zstep. eapply (ju_expd m1 jk (j2 + 2)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | exact H18 | exact H23 | exact HJ].
    + eapply (ju_expd m1 jk (j2 + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | exact H18 | exact H23 | exact HJ].
Qed.

Lemma ju_fraclp : forall (f : nat) m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27
                                           x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x11 = k -> bv_unsigned i <= k < bv_unsigned n -> bv_unsigned n - k <= Z.of_nat f ->
  x10 = Z_to_bv 64 (-10) -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = jrest_exp (jdigits BZ k f) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14c24) fc None m1 (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
      HJI H11 Hk Hf H10 H18 H23 HJ; [lia|].
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). subst x10. rng.
  pose proof (ju_rd m1 k HB ltac:(lia)) as HR. pose proof (ju_jbr k) as Jk.
  zstep. bf.
  zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_nd by lia.
  rewrite ju_jdigits_S, (proj2 (Z.ltb_lt _ _) (proj2 Hk)) in HJ. cbn [andb] in HJ.
  destruct (jdigit (jbyte BZ k)) eqn:D; cbn [negb]; rewrite ?D in HJ; cbv beta iota in HJ.
  - zstep. zstep.
    destruct (Z.eqb_spec (bv_unsigned n) (k + 1)) as [E|E].
    + bf. zstep. zstep. zstep. replace (k + 1) with (bv_unsigned n) in HJ by lia.
      rewrite ju_jdigits_n, ju_jexp_n in HJ by lia.
      eapply ju_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
    + bt. eapply (IH m1 jk (k + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | lia | reflexivity
                                      | exact H18 | exact H23 | exact HJ].
  - zstep.
    eapply ju_exp; [exact HJI | exact H11 | lia | exact H18 | exact H23 | exact HJ].
Qed.

Lemma ju_frac : forall m1 jk j1 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27
                                 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = j1 -> bv_unsigned i <= j1 <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i -> bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = jrest_frac j1 ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14bec) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    HJI H10 Hj H18 H23 HJ.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). rng.
  zstep.
  destruct (Z.ltb_spec j1 (bv_unsigned n)) as [Jn|Jn].
  2: { bt. rewrite ju_jfrac_n in HJ by lia. eapply ju_exp; [exact HJI | exact H10 | lia | exact H18 | exact H23 | exact HJ]. }
  bf. zstep. bf.
  pose proof (ju_rd m1 j1 HB ltac:(lia)) as HR. pose proof (ju_jbr j1) as Jk.
  zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_eqb_z by lia.
  unfold jrest_frac, jfrac in HJ. rewrite ju_jlen, (proj2 (Z.ltb_lt _ _) Jn) in HJ. cbn [andb] in HJ.
  destruct (jbyte BZ j1 =? 46) eqn:Ed; cbn [negb]; rewrite ?Ed in HJ; cbv beta iota in HJ.
  2: { eapply ju_exp; [exact HJI | exact H10 | lia | exact H18 | exact H23 | exact HJ]. }
  zstep. zstep.
  unfold jdig_at in HJ. rewrite ju_jlen in HJ.
  destruct (Z.ltb_spec (j1 + 1) (bv_unsigned n)) as [J1|J1].
  2: { bt. try replace (j1 + 1 <? bv_unsigned n) with false in HJ by (symmetry; apply Z.ltb_ge; lia).
       cbn [andb] in HJ. cbv beta iota in HJ. eapply ju_fail; [exact HJI | exact HJ]. }
  bf. try rewrite (proj2 (Z.ltb_lt _ _) J1) in HJ. cbn [andb] in HJ.
  zstep. bf.
  pose proof (ju_rd m1 (j1 + 1) HB ltac:(lia)) as HR1. pose proof (ju_jbr (j1 + 1)) as Jk1.
  zstep. zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_nd by lia.
  destruct (jdigit (jbyte BZ (j1 + 1))) eqn:D; cbn [negb]; rewrite ?D in HJ; cbv beta iota in HJ.
  - eapply (ju_fraclp (length BZ) m1 jk (j1 + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia
                                                  | rewrite length_map; lia | reflexivity | exact H18 | exact H23 | exact HJ].
  - eapply ju_fail; [exact HJI | exact HJ].
Qed.

Lemma ju_d1lp : forall (f : nat) m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27
                                         x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = k -> bv_unsigned i <= k < bv_unsigned n -> bv_unsigned n - k <= Z.of_nat f ->
  x11 = Z_to_bv 64 (-10) -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = jrest_frac (jdigits BZ k f) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14c78) fc None m1 (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
      HJI H10 Hk Hf H11 H18 H23 HJ; [lia|].
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). subst x11. rng.
  pose proof (ju_rd m1 k HB ltac:(lia)) as HR. pose proof (ju_jbr k) as Jk.
  zstep. bf.
  zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_nd by lia.
  rewrite ju_jdigits_S, (proj2 (Z.ltb_lt _ _) (proj2 Hk)) in HJ. cbn [andb] in HJ.
  destruct (jdigit (jbyte BZ k)) eqn:D; cbn [negb]; rewrite ?D in HJ; cbv beta iota in HJ.
  - zstep. zstep.
    destruct (Z.ltb_spec (k + 1) (bv_unsigned n)) as [E|E].
    + bt. eapply (IH m1 jk (k + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | lia | reflexivity
                                      | exact H18 | exact H23 | exact HJ].
    + bf. zstep. zstep. replace (k + 1) with (bv_unsigned n) in HJ by lia.
      rewrite ju_jdigits_n, ju_jfrac_n, ju_jexp_n in HJ by lia.
      eapply ju_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
  - eapply ju_frac; [exact HJI | exact H10 | lia | exact H18 | exact H23 | exact HJ].
Qed.

Lemma ju_num : forall m1 jk (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27
                            x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i -> bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = jnum BZ (bv_unsigned i) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v (Z_to_bv 64 (jbyte BZ (bv_unsigned i))) x10 x11 x12 x13 x14 x15 x16 x17
                          x18 n b x21 x22 x23 x24 x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14b58) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    HJI H18 H23 HJ.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). rng.
  pose proof (ju_jbr (bv_unsigned i)) as Ji.
  zstep. zstep. zstep.
  rewrite ju_minus by lia.
  replace (bv_unsigned i + Z.b2z (jbyte BZ (bv_unsigned i) =? 45))
    with (if jbyte BZ (bv_unsigned i) =? 45 then bv_unsigned i + 1 else bv_unsigned i)
    by (destruct (jbyte BZ (bv_unsigned i) =? 45); cbn [Z.b2z]; lia).
  unfold jnum in HJ. cbv zeta in HJ.
  remember (if jbyte BZ (bv_unsigned i) =? 45 then bv_unsigned i + 1 else bv_unsigned i) as j0 eqn:Hj0.
  assert (J0 : bv_unsigned i <= j0 <= bv_unsigned i + 1) by (subst j0; destruct (_ =? 45); lia).
  clear Hj0.
  unfold jdig_at in HJ. rewrite ju_jlen in HJ.
  zstep.
  destruct (Z.ltb_spec j0 (bv_unsigned n)) as [Jn|Jn].
  2: { bt. try replace (j0 <? bv_unsigned n) with false in HJ by (symmetry; apply Z.ltb_ge; lia).
       cbn [andb negb] in HJ. cbv beta iota in HJ. eapply ju_fail; [exact HJI | exact HJ]. }
  bf. try rewrite (proj2 (Z.ltb_lt _ _) Jn) in HJ. cbn [andb] in HJ.
  zstep. bf.
  pose proof (ju_rd m1 j0 HB ltac:(lia)) as HR. pose proof (ju_jbr j0) as Jk.
  zstep. zstep. zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_nd by lia.
  destruct (jdigit (jbyte BZ j0)) eqn:D; cbn [negb]; rewrite ?D in HJ; cbv beta iota in HJ.
  2: { eapply ju_fail; [exact HJI | exact HJ]. }
  zstep. zstep.
  rewrite ju_eqb_z by lia.
  destruct (jbyte BZ j0 =? 48) eqn:Z0; cbn [negb]; rewrite ?Z0 in HJ; cbv beta iota in HJ.
  - zstep. eapply (ju_frac m1 jk (j0 + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | exact H18 | exact H23 | exact HJ].
  - zstep. eapply (ju_d1lp (length BZ) m1 jk j0); [exact HJI | rewrite unsigned_lit by lia; lia | lia
                                                | rewrite length_map; lia | reflexivity | exact H18 | exact H23 | exact HJ].
Qed.

Lemma ju_send : forall m1 jk j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                                x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x27 = j - 1 -> bv_unsigned i + 1 <= j < bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar BZ (bv_unsigned i) = Some (j + 1, 1, bv_unsigned i + 1, j - bv_unsigned i - 1) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14c44) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV & HT) H27 Hj H18 HJ. rng.
  assert (BV : 0 <= bv_unsigned v /\ bv_unsigned v + 20 <= 2^64) by (destruct HV as (? & ? & _); lia).
  apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  zstep. zstep. bf.
  zstep. zstep. rewrite (ju_land7 _ HA). bf.
  zstep. zstep. zstep.
  js_hs v 0 8%nat. zstep. js_store.
  js_hs v 8 8%nat. zstep. js_store.
  js_hs v 16 4%nat. zstep. js_store.
  zstep. zstep.
  eapply ju_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold ju_res. rewrite HJ. split; [f_equal; lia|]. split; [exact MU|].
  replace (Z_to_bv 64 (bv_unsigned b + (bv_unsigned i + 1))) with (Z_to_bv 64 (bv_unsigned x18 + 1)) by (f_equal; lia).
  replace (Z_to_bv 64 (j - bv_unsigned i - 1)) with (Z_to_bv 64 (bv_unsigned x27 - bv_unsigned i)) by (f_equal; lia).
  apply ju_rec3; assumption.
Qed.

Lemma ju_lmatch : forall m1 jk len (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27
                                    x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x21 = len -> 0 <= len -> bv_unsigned i + len <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar BZ (bv_unsigned i) = Some (bv_unsigned i + len, 3, bv_unsigned i, len) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 i x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14bc0) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk len x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV & HT) H21 L0' Hl H18 HJ. rng.
  assert (BV : 0 <= bv_unsigned v /\ bv_unsigned v + 20 <= 2^64) by (destruct HV as (? & ? & _); lia).
  apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  zstep. zstep. rewrite (ju_land7 _ HA). bf.
  zstep.
  js_hs v 0 8%nat. zstep. js_store.
  js_hs v 8 8%nat. zstep. js_store.
  js_hs v 16 4%nat. zstep. js_store.
  zstep. zstep.
  eapply ju_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold ju_res. rewrite HJ. split; [f_equal; lia|]. split; [exact MU|].
  rewrite (ju_word x18 _ H18) in HW. rewrite (ju_word x21 _ H21) in HW0. apply ju_rec3; assumption.
Qed.

Hypothesis MEMCHR : memchr_contract.
Hypothesis STRLEN : strlen_contract.
Hypothesis BCMP : bcmp_contract.

Local Notation X9 := (Z_to_bv 64 (jbyte BZ (bv_unsigned i))).

Lemma ju_tab : forall m1 (x : word) k, bytes_at rsegs m1 132576 LT -> (k < 3)%nat ->
  bv_unsigned x = 132576 + 8 * Z.of_nat k ->
  ov_read_bytes rsegs m1 x 8 = Some (le8 (Z_to_bv 64 (nth k [0x103aa; 0x10298; 0x10326] 0))).
Proof.
  intros m1 x k H Hk Hx. rewrite <- (wa_of_var x _ Hx).
  rewrite (bytes_at_read rsegs m1 132576 _ (8 * Z.of_nat k) 8 H) by (try lia; rewrite !length_app, !length_le8; lia).
  f_equal. destruct k as [|[|[|k]]]; try lia; vm_compute; reflexivity.
Qed.

Lemma ju_lit1 : forall (p : Z) (str slack : list byte) (rest : list (list Z)) m1 jk
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x24 = bv_unsigned n - bv_unsigned i -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  ov_read_bytes rsegs m1 x25 8 = Some (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m1 p (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (p + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  jscalar BZ (bv_unsigned i) =
    match jlit BZ (bv_unsigned i) (map bv_unsigned str :: rest) with Some t => Some t | None => jnum BZ (bv_unsigned i) end ->
  (forall m2 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word),
     JI m2 jk ->
     jscalar BZ (bv_unsigned i) = match jlit BZ (bv_unsigned i) rest with Some t => Some t | None => jnum BZ (bv_unsigned i) end ->
     evt rsegs POST (MS (mkR y1 SP' gp tp y5 y6 y7 v X9 y10 y11 y12 y13 y14 y15 y16 y17 x18 n b y21 y22 x23 x24 x25 i x27
                             y28 y29 y30 y31) F (Z_to_bv 64 0x14b4c) fc None m2 (seg_rom rsegs))) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v X9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24 x25 i x27
                          x28 x29 x30 x31) F (Z_to_bv 64 0x14b24) fc None m1 (seg_rom rsegs)).
Proof.
  intros p str slack rest m1 jk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31
    HJI H24 H18 HR HS HZ HSL HJ K.
  destruct HJI as (FR & ST & MU & WM & MI & HB & HV & HT). rng.
  pose proof (bytes_at_bound _ _ _ _ HS) as BS. rewrite length_app in BS. cbn [length] in BS.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply STRLEN with (str := str) (slack := slack);
      [rewrite unsigned_lit by lia; exact HS | exact HZ | rewrite unsigned_lit by lia; exact HSL | exact MI]. }
  post_call rsegs m1.
  zstep.
  cbn [jlit] in HJ. rewrite length_map, ju_jlen in HJ.
  destruct (Z.ltb_spec (bv_unsigned n - bv_unsigned i) (Z.of_nat (length str))) as [Lt|Ge].
  - bt. replace (Z.of_nat (length str) <=? bv_unsigned n - bv_unsigned i) with false in HJ
          by (symmetry; apply Z.leb_gt; lia).
    cbn [andb] in HJ. eapply K; [mkJI | exact HJ].
  - bf. replace (Z.of_nat (length str) <=? bv_unsigned n - bv_unsigned i) with true in HJ
          by (symmetry; apply Z.leb_le; lia).
    cbn [andb] in HJ.
    zstep. zstep. zstep. zstep. zstep.
    pose proof (ju_sub _ _ B (Z.to_nat (bv_unsigned i)) (length str) HB ltac:(lia)) as HLS.
    rewrite Z2Nat.id in HLS by lia. rewrite <- H18 in HLS.
    pose proof (proj1 (bytes_at_app _ _ _ str (Z_to_bv 8 0 :: slack)) HS) as [HRS _].
    destruct (memcmp_model_total (firstn (length str) (skipn (Z.to_nat (bv_unsigned i)) B)) str (length str))
      as [vv HMv]; [rewrite length_firstn, length_skipn; lia | lia |].
    destruct (ju_memcmp (length str) (firstn (length str) (skipn (Z.to_nat (bv_unsigned i)) B)) str vv
                ltac:(rewrite length_firstn, length_skipn; lia) eq_refl HMv) as [RV IV].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BCMP with (ls := firstn (length str) (skipn (Z.to_nat (bv_unsigned i)) B)) (rs := str) (v := vv);
        [ exact HLS | rewrite unsigned_lit by lia; exact HRS
        | rewrite unsigned_lit by lia; rewrite Nat2Z.id; exact HMv | eassumption ]
      | post_call rsegs mm ]
    end.
    zstep.
    destruct (Z.eq_dec vv 0) as [V0|V0].
    + subst vv. bt.
      assert (EQ : firstn (length str) (skipn (Z.to_nat (bv_unsigned i)) B) = str) by (apply IV; reflexivity).
      rewrite (proj2 (ju_prefix str B (Z.to_nat (bv_unsigned i)) ltac:(lia)) EQ) in HJ. cbv beta iota in HJ.
      eapply (ju_lmatch _ jk (Z.of_nat (length str)));
        [mkJI | rewrite unsigned_lit by lia; reflexivity | lia | lia | exact H18 | exact HJ].
    + bf.
      destruct (jprefix (map bv_unsigned str) (skipn (Z.to_nat (bv_unsigned i)) BZ)) eqn:P.
      { exfalso. apply V0. apply IV. apply (ju_prefix str B (Z.to_nat (bv_unsigned i)) ltac:(lia)). exact P. }
      cbv beta iota in HJ. eapply K; [mkJI | exact HJ].
Qed.

Lemma ju_jstr_ge : forall j f, bv_unsigned n <= j -> jstr BZ (bv_unsigned i) j f = None.
Proof.
  intros j [|f] Hj; [reflexivity|]. cbn [jstr]. rewrite ju_jlen.
  replace (bv_unsigned n <=? j) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma ju_strlp : forall (f : nat) m1 jk j (x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x22 x23 x27
                                          x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x9 = j -> bv_unsigned x27 = j - 1 -> bv_unsigned i + 1 <= j < bv_unsigned n ->
  bv_unsigned n - j <= Z.of_nat f -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  bv_unsigned x23 = 2^64 - 1 - bv_unsigned b ->
  jscalar BZ (bv_unsigned i) = jstr BZ (bv_unsigned i) j f ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 (Z_to_bv 64 92) x13 x14 x15 x16 x17 x18 n b
                          (Z_to_bv 64 66297) x22 x23 (Z_to_bv 64 34) (Z_to_bv 64 32) i x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x149f4) fc None m1 (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros m1 jk j x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31
      HJI H9 H27 Hj Hf H18 H23 HJ; [lia|].
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV & HT). rng.
  cbn [jstr] in HJ. rewrite ju_jlen in HJ.
  replace (bv_unsigned n <=? j) with false in HJ by (symmetry; apply Z.leb_gt; lia). cbv beta iota in HJ.
  pose proof (ju_rd m1 j HB ltac:(lia)) as HR. pose proof (ju_jbr j) as Jj.
  zstep. bf.
  zstep. zstep. zstep.
  cbv beta; rewrite <- ju_jbyte, ju_eqb_z by lia.
  destruct (jbyte BZ j =? 34) eqn:Q1; cbn [negb]; rewrite ?Q1 in HJ; cbv beta iota in HJ.
  { eapply ju_send; [exact HJI | exact H27 | lia | exact H18 | exact HJ]. }
  zstep. rewrite ju_ltu_z by lia.
  destruct (jbyte BZ j <? 32) eqn:Q2; cbn [negb]; rewrite ?Q2 in HJ; cbv beta iota in HJ.
  { eapply ju_fail; [exact HJI | exact HJ]. }
  zstep. rewrite ju_eqb_z by lia.
  destruct (jbyte BZ j =? 92) eqn:Q3; cbn [negb]; rewrite ?Q3 in HJ; cbv beta iota in HJ.
  2: { zstep. zstep. zstep.
       destruct (Z.ltb_spec (j + 1) (bv_unsigned n)) as [N1|N1].
       - bf. zstep. eapply (IH m1 jk (j + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | lia | lia
                                               | exact H18 | exact H23 | exact HJ].
       - bt. rewrite ju_jstr_ge in HJ by lia. eapply ju_fail; [exact HJI | exact HJ]. }
  zstep. zstep.
  destruct (Z.leb_spec (bv_unsigned n) (j + 1)) as [E1|E1]; cbv beta iota in HJ.
  { bt. eapply ju_fail; [exact HJI | exact HJ]. }
  bf. zstep. bf.
  pose proof (ju_rd m1 (j + 1) HB ltac:(lia)) as HR1. pose proof (ju_jbr (j + 1)) as Jj1.
  zstep. zstep.
  cbv beta; rewrite <- ju_jbyte.
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply MEMCHR with (buf := ju_esc);
      [ rewrite unsigned_lit by lia; apply ju_ro; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity]
      | rewrite (unsigned_lit 10) by lia; apply ju_mok
      | exact MI ]. }
  post_call rsegs m1.
  try rewrite (unsigned_lit 66297) by lia. try rewrite (unsigned_lit 10) by lia.
  try rewrite (unsigned_lit (jbyte BZ (j + 1))) by lia.
  try rewrite (Z.mod_small (jbyte BZ (j + 1)) 256) by lia.
  pose proof (ju_mc _ Jj1) as MC. pose proof (ju_mcr _ Jj1) as MR.
  zstep. zstep. zstep.
  try rewrite (Z.mod_small (jbyte BZ (j + 1)) 256) by lia.
  rewrite ju_eqb_z by lia.
  destruct (memchr_res 66297 (jbyte BZ (j + 1)) 10 ju_esc =? 0) eqn:QM0; cbn [negb andb] in MC |- *.
  { rewrite <- MC in HJ. cbn [negb] in HJ. cbv beta iota in HJ. eapply ju_fail84; [mkJI | exact HJ]. }
  zstep. rewrite ju_eqb_z by lia.
  destruct (jbyte BZ (j + 1) =? 0) eqn:QZ0; cbn [negb andb] in MC |- *.
  { rewrite <- MC in HJ. cbn [negb] in HJ. cbv beta iota in HJ. eapply ju_fail84; [mkJI | exact HJ]. }
  rewrite <- MC in HJ. cbn [negb] in HJ. cbv beta iota in HJ.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (HJI2 : JI mm jk) by mkJI end.
  zstep. zstep. rewrite ju_eqb_z by lia.
  destruct (jbyte BZ (j + 1) =? 117) eqn:U; cbn [negb]; rewrite ?U in HJ; cbv beta iota in HJ.
  2: { zstep. zstep. zstep. zstep.
       destruct (Z.ltb_spec (j + 2) (bv_unsigned n)) as [N2|N2].
       - bf. zstep. eapply (IH _ jk (j + 2)); [exact HJI2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
                                              | lia | lia | exact H18 | exact H23 | exact HJ].
       - bt. rewrite ju_jstr_ge in HJ by lia. eapply ju_fail; [exact HJI2 | exact HJ]. }
  zstep. zstep. zstep.
  destruct (Z.leb_spec (bv_unsigned n - (j + 1)) 4) as [U4|U4]; cbn [orb] in HJ.
  { bt. cbv beta iota in HJ. eapply ju_fail; [exact HJI2 | exact HJ]. }
  bf.
  zstep. zstep. zstep. zstep. bf.
  pose proof (ju_rd _ (j + 2) HB ltac:(lia)) as HR2. pose proof (ju_jbr (j + 2)) as J2.
  zstep. zstep. zstep. cbv beta; rewrite <- ju_jbyte.
  eapply ju_hex2; [exact J2 | intros X2 ya yb | intros X2 ya yb].
  2: { rewrite X2 in HJ. cbn [andb negb] in HJ. cbv beta iota in HJ. eapply ju_fail; [exact HJI2 | exact HJ]. }
  rewrite X2 in HJ.
  zstep. zstep. bf.
  pose proof (ju_rd _ (j + 3) HB ltac:(lia)) as HR3. pose proof (ju_jbr (j + 3)) as J3.
  zstep. zstep. zstep. cbv beta; rewrite <- ju_jbyte.
  eapply ju_hex3; [exact J3 | intros X3 yc yd | intros X3 yc yd].
  2: { rewrite X3 in HJ. cbn [andb negb] in HJ. cbv beta iota in HJ. eapply ju_fail; [exact HJI2 | exact HJ]. }
  rewrite X3 in HJ.
  zstep. zstep. bf.
  pose proof (ju_rd _ (j + 4) HB ltac:(lia)) as HR4. pose proof (ju_jbr (j + 4)) as J4.
  zstep. zstep. zstep. cbv beta; rewrite <- ju_jbyte.
  eapply ju_hex4; [exact J4 | intros X4 ye yf | intros X4 ye yf].
  2: { rewrite X4 in HJ. cbn [andb negb] in HJ. cbv beta iota in HJ. eapply ju_fail; [exact HJI2 | exact HJ]. }
  rewrite X4 in HJ.
  zstep. zstep. bf.
  pose proof (ju_rd _ (j + 5) HB ltac:(lia)) as HR5. pose proof (ju_jbr (j + 5)) as J5.
  zstep. zstep. zstep. cbv beta; rewrite <- ju_jbyte.
  eapply ju_hex5; [exact J5 | intros X5 yg yh | intros X5 yg yh].
  2: { rewrite X5 in HJ. cbn [andb negb] in HJ. cbv beta iota in HJ. eapply ju_fail; [exact HJI2 | exact HJ]. }
  rewrite X5 in HJ. cbn [andb negb] in HJ. cbv beta iota in HJ.
  zstep. zstep. zstep.
  destruct (Z.ltb_spec (j + 6) (bv_unsigned n)) as [N6|N6].
  - bf. zstep. eapply (IH _ jk (j + 6)); [exact HJI2 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
                                         | lia | lia | exact H18 | exact H23 | exact HJ].
  - bt. rewrite ju_jstr_ge in HJ by lia. eapply ju_fail; [exact HJI2 | exact HJ].
Qed.

Lemma ju_main_lt : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m (bv_unsigned b) B -> wr_at rsegs m (bv_unsigned v) 20 -> bytes_at rsegs m 132576 LT ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 b i n v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14970) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 HB HV HT MI ST.
  pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word i) as Ri. pose proof (zr_word n) as Rn.
  pose proof (zr_word b) as Rb. pose proof (zr_word v) as Rv. unfold inr64 in *.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB.
  carve_frame 112%nat ST.
  do 14 zstep.
  zstep. bf.
  zstep. zstep. zstep.
  rewrite (zb_lxor_ones (bv_unsigned b)) by lia.
  zstep. bf.
  zstep. zstep. zstep.
  pose proof (ju_rd _ (bv_unsigned i) HB ltac:(lia)) as HR. pose proof (ju_jbr (bv_unsigned i)) as Ji.
  zstep. cbv beta; rewrite <- ju_jbyte.
  pose proof (eq_refl (jscalar BZ (bv_unsigned i))) as HJ. unfold jscalar at 2 in HJ. rewrite ju_jlen in HJ.
  replace (bv_unsigned n <=? bv_unsigned i) with false in HJ by (symmetry; apply Z.leb_gt; lia).
  cbv beta iota in HJ.
  zstep. zstep. rewrite ju_eqb_z by lia.
  destruct (jbyte BZ (bv_unsigned i) =? 34) eqn:Q; cbn [negb]; rewrite ?Q in HJ; cbv beta iota in HJ.
  - zstep. zstep.
    destruct (Z.ltb_spec (bv_unsigned i + 1) (bv_unsigned n)) as [N1|N1].
    + bf. do 6 zstep.
      eapply (ju_strlp (length BZ) _ _ (bv_unsigned i + 1));
        [mkJI | rewrite unsigned_lit by lia; reflexivity | lia | lia | rewrite length_map; lia
        | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact HJ].
    + bt. rewrite ju_jstr_ge in HJ by lia. eapply ju_fail; [mkJI | exact HJ].
  - zstep. zstep. zstep. zstep.
    replace jlit_words with (map bv_unsigned ju_true :: map bv_unsigned ju_false :: map bv_unsigned ju_null :: [])
      in HJ by (vm_compute; reflexivity).
    eapply (ju_lit1 0x103aa ju_true [Z_to_bv 8 114] [map bv_unsigned ju_false; map bv_unsigned ju_null]);
      [ mkJI | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | apply (ju_tab _ _ 0); [eassumption | lia | rewrite unsigned_lit by lia; reflexivity]
      | apply ju_ro; [eassumption | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity]
      | unfold ju_true; apply ju_nz; vm_compute; reflexivity
      | apply Z.leb_le; vm_compute; reflexivity
      | exact HJ | ].
    intros m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 HJI2 HJ2.
    pose proof HJI2 as (_ & _ & _ & _ & MI2 & _ & _ & HT2).
    zstep. zstep. zstep. bt.
    eapply (ju_lit1 0x10298 ju_false [Z_to_bv 8 114; Z_to_bv 8 111] [map bv_unsigned ju_null]);
      [ exact HJI2 | try rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | apply (ju_tab _ _ 1); [exact HT2 | lia | rewrite unsigned_lit by lia; lia]
      | apply ju_ro; [exact MI2 | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity]
      | unfold ju_false; apply ju_nz; vm_compute; reflexivity
      | apply Z.leb_le; vm_compute; reflexivity
      | exact HJ2 | ].
    intros m3 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z21 z22 z28 z29 z30 z31 HJI3 HJ3.
    pose proof HJI3 as (_ & _ & _ & _ & MI3 & _ & _ & HT3).
    zstep. zstep. zstep. bt.
    eapply (ju_lit1 0x10326 ju_null [Z_to_bv 8 32; Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 32; Z_to_bv 8 47] []);
      [ exact HJI3 | try rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | apply (ju_tab _ _ 2); [exact HT3 | lia | rewrite unsigned_lit by lia; lia]
      | apply ju_ro; [exact MI3 | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity]
      | unfold ju_null; apply ju_nz; vm_compute; reflexivity
      | apply Z.leb_le; vm_compute; reflexivity
      | exact HJ3 | ].
    intros m4 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w21 w22 w28 w29 w30 w31 HJI4 HJ4.
    zstep. zstep. zstep. bf.
    cbn [jlit] in HJ4.
    eapply ju_num; [exact HJI4 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact HJ4].
Qed.

End JS.

Theorem json_scalar_holds : memchr_contract -> strlen_contract -> bcmp_contract -> json_scalar_contract.
Proof.
  intros MEMCHR STRLEN BCMP. unfold json_scalar_contract, JSON_SCALAR, JSON_SCALAR_K, JSON_SCALAR_L.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B
    HL HBN HB HA HV DV HT DT MI ST LO.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) in * by lia.
  destruct (Z.lt_ge_cases (bv_unsigned a1) (bv_unsigned a2)) as [HI|HI].
  - destruct (HB HI) as [HB1 DB]. eapply ju_main_lt; eassumption.
  - eapply ju_main_ge; eassumption.
Qed.
