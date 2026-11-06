From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import strlen_c bcmp_c memchr_c disco_jscalar_model json_scalar_c.
Import ListNotations.
Open Scope Z_scope.

Lemma js_rec3 : forall m a (x y z : word),
  bytes_at rsegs m (a + 0) (le8 x) -> bytes_at rsegs m (a + 8) (le8 y) -> bytes_at rsegs m (a + 16) (le4 z) ->
  bytes_at rsegs m a (le8 x ++ le8 y ++ le4 z).
Proof.
  intros m a x y z H1 H2 H3. rewrite Z.add_0_r in H1.
  apply bytes_at_app. split; [exact H1|]. rewrite length_le8.
  apply bytes_at_app. split; [exact H2|]. rewrite length_le8.
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) by lia. exact H3.
Qed.

Lemma js_byte_all : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c : byte, P (bv_unsigned c) = true.
Proof.
  intros P H c. rewrite forallb_forall in H. apply H. apply in_map_iff.
  pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. change (Z.of_N 8) with 8 in R.
  exists (Z.to_nat (bv_unsigned c)). split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.

Lemma js_nd : forall c : byte, bv_ltu (Z_to_bv 64 (bv_unsigned c + -58)) (Z_to_bv 64 (-10)) = negb (jdigit (bv_unsigned c)).
Proof.
  intros c. apply Bool.eqb_prop.
  exact (js_byte_all (fun z => Bool.eqb (bv_ltu (Z_to_bv 64 (z + -58)) (Z_to_bv 64 (-10))) (negb (jdigit z)))
           ltac:(vm_compute; reflexivity) c).
Qed.

Lemma js_eqb_Z : forall x y : word, bv_eqb x y = (bv_unsigned x =? bv_unsigned y).
Proof. reflexivity. Qed.

Lemma js_byte_range : forall c : byte, 0 <= bv_unsigned c < 256.
Proof. intros c. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. change (Z.of_N 8) with 8 in R. lia. Qed.

Lemma js_e : forall c : byte, bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned c) 32)) (Z_to_bv 64 101) =
  (bv_unsigned c =? 101) || (bv_unsigned c =? 69).
Proof.
  intros c. apply Bool.eqb_prop.
  exact (js_byte_all (fun z => Bool.eqb (bv_eqb (Z_to_bv 64 (Z.lor z 32)) (Z_to_bv 64 101)) ((z =? 101) || (z =? 69)))
           ltac:(vm_compute; reflexivity) c).
Qed.

Lemma js_beq : forall z K, 0 <= z < 2^64 -> 0 <= K < 2^64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 K) = (z =? K).
Proof. intros z K Hz HK. rewrite js_eqb_Z, !unsigned_lit by lia. reflexivity. Qed.

Ltac js_lt HK HJ := first [ rewrite (proj2 (Z.ltb_lt _ _) HK) in HJ | rewrite (proj2 (Z.ltb_ge _ _) HK) in HJ | idtac ].

Lemma js_some4 : forall a b c d a' b' c' d' : Z, a = a' -> b = b' -> c = c' -> d = d' ->
  Some (a, b, c, d) = Some (a', b', c', d').
Proof. intros. subst. reflexivity. Qed.

Lemma js_hd : forall z, 0 <= z < 256 -> bv_ltu (Z_to_bv 64 (-11)) (Z_to_bv 64 (z + -58)) = jdigit z.
Proof.
  intros z Hz. apply Bool.eqb_prop.
  exact (brute256_ok (fun z => Bool.eqb (bv_ltu (Z_to_bv 64 (-11)) (Z_to_bv 64 (z + -58))) (jdigit z))
           ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma js_ha : forall z, 0 <= z < 256 -> jdigit z = false ->
  bv_ltu (Z_to_bv 64 (Z.land z 223 + -71)) (Z_to_bv 64 (-6)) = negb (jhexd z).
Proof.
  intros z Hz D. apply Bool.eqb_prop.
  pose proof (brute256_ok (fun z => jdigit z ||
                Bool.eqb (bv_ltu (Z_to_bv 64 (Z.land z 223 + -71)) (Z_to_bv 64 (-6))) (negb (jhexd z)))
           ltac:(vm_compute; reflexivity) z Hz) as H.
  cbv beta in H. rewrite D in H. exact H.
Qed.

Lemma js_dh : forall c, jdigit c = true -> jhexd c = true.
Proof. intros c H. unfold jhexd. rewrite H. reflexivity. Qed.

Lemma js_memcmp : forall k (P T : list byte) w, length P = k -> length T = k -> memcmp_model P T k = Some w ->
  -255 <= w <= 255 /\ (w = 0 <-> P = T).
Proof.
  induction k as [|k IH]; intros P T w HP HT HM.
  - destruct P, T; cbn in *; try lia. injection HM as <-. split; [lia|]. tauto.
  - destruct P as [|a P], T as [|c T]; cbn in HP, HT; try lia.
    cbn in HM. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE].
    + destruct (IH P T w ltac:(lia) ltac:(lia) HM) as [R I]. split; [exact R|].
      rewrite I. split; intro H.
      * f_equal; [apply bv_eq; exact E | exact H].
      * injection H as _ H. exact H.
    + injection HM as <-. pose proof (js_byte_range a) as RA. pose proof (js_byte_range c) as RC.
      split; [lia|]. split; intro HE; [lia|]. injection HE as HE _. subst. contradiction.
Qed.

Lemma js_prefix : forall (W R : list byte),
  jprefix (map bv_unsigned W) (map bv_unsigned R) = true <-> firstn (length W) R = W.
Proof.
  induction W as [|a W IH]; intros R; cbn [map jprefix length firstn]; [tauto|].
  destruct R as [|c R]; cbn [map jprefix firstn]; [split; intro H; discriminate|].
  rewrite andb_true_iff, IH, Z.eqb_eq. split.
  - intros [E H]. rewrite H. f_equal. apply bv_eq. symmetry. exact E.
  - intros H. injection H as E H. split; [rewrite E; reflexivity | exact H].
Qed.

Lemma js_skipn_map : forall (l : list byte) k, skipn k (map bv_unsigned l) = map bv_unsigned (skipn k l).
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma js_img : forall m A bs, mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2^64 -> bytes_at rsegs m A bs.
Proof.
  intros m A bs MI Hb HA Hl. destruct (ro_cells_image rsegs m A bs MI Hb HA Hl) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma js_notin0 : forall W : list byte, forallb (fun x => negb (bv_unsigned x =? 0)) W = true -> ~ In (Z_to_bv 8 0) W.
Proof. intros W H HI. rewrite forallb_forall in H. specialize (H _ HI). vm_compute in H. discriminate. Qed.

Lemma js_eqbs : forall x, -2^63 <= x < 2^63 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x 0) as [->|NE]; [reflexivity|]. apply Z.eqb_neq. intro E. apply NE.
  Z.div_mod_to_equations. lia.
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

Lemma js_word : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z H. subst z. symmetry. apply Z_to_bv_lit_self. Qed.

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
Hypothesis HI : bv_unsigned i < bv_unsigned n.
Hypothesis LO : lo + 112 <= bv_unsigned sp.
Hypothesis L0 : 0 <= lo.
Hypothesis DB : bv_unsigned b + bv_unsigned n <= bv_unsigned sp + -112 \/ bv_unsigned sp <= bv_unsigned b.
Hypothesis DV : bv_unsigned v + 20 <= bv_unsigned sp + -112 \/ bv_unsigned sp <= bv_unsigned v.
Hypothesis DL : 130600 + 24 <= bv_unsigned sp + -112 \/ bv_unsigned sp <= 130600.

Local Notation POST := (json_scalar_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m b i v B).
Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -112)).
Local Notation FRC jk := [CB 8 jk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition js_res (m1 : word -> option byte) (r : word) : Prop :=
  match jscalar (map bv_unsigned B) (bv_unsigned i) with
  | Some (e, k, s, l) =>
      r = Z_to_bv 64 e /\
      munch [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)] m m1 /\
      bytes_at rsegs m1 (bv_unsigned v) (le8 (Z_to_bv 64 (bv_unsigned b + s)) ++ le8 (Z_to_bv 64 l) ++ le4 (Z_to_bv 64 k))
  | None => r = Z_to_bv 64 0 /\ munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m1
  end.

Lemma js_epi : forall m1 jk (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31 : word),
  rw_cells rsegs m1 (bv_unsigned sp + -112) (FRC jk) -> stk rsegs m1 lo (bv_unsigned sp + -112) ->
  wmono rsegs m m1 -> mem_inv rsegs m1 -> js_res m1 x10 ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14984) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    FR ST WM MI RES.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold json_scalar_post, JSON_SCALAR_K.
  do 16 eexists. split; [reflexivity|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by lia.
  unfold js_res in RES. exact RES.
Qed.

Definition JI (m1 : word -> option byte) (jk : list byte) : Prop :=
  rw_cells rsegs m1 (bv_unsigned sp + -112) (FRC jk) /\ stk rsegs m1 lo (bv_unsigned sp + -112) /\
  munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
  bytes_at rsegs m1 (bv_unsigned b) B /\ wr_at rsegs m1 (bv_unsigned v) 20.

Lemma js_fail : forall m1 jk (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31 : word),
  JI m1 jk -> jscalar (map bv_unsigned B) (bv_unsigned i) = None ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14980) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV) HJ.
  zstep. eapply js_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold js_res. rewrite HJ. split; [reflexivity | exact MU].
Qed.

Lemma js_tok : forall m1 jk j3 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26
                                  x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x19 = j3 -> bv_unsigned i <= j3 <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = Some (j3, 2, bv_unsigned i, j3 - bv_unsigned i) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14ae4) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV) H19 HJ3 H18 HJ.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word v) as Rv. pose proof (zr_word i) as Ri.
  pose proof (zr_word x19) as R19. unfold inr64 in *.
  assert (BV : 0 <= bv_unsigned v /\ bv_unsigned v + 20 <= 2^64) by (destruct HV as (? & ? & _); lia).
  apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  zstep. zstep.
  js_hs v 0 8%nat. zstep.
  js_store.
  js_hs v 8 8%nat. zstep. js_store.
  js_hs v 16 4%nat. zstep. js_store.
  zstep. zstep.
  eapply js_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold js_res. rewrite HJ. split; [apply js_word; exact H19|]. split; [exact MU|].
  rewrite (js_word x18 _ H18) in HW. rewrite H19 in HW0. apply js_rec3; assumption.
Qed.

Lemma js_firstn1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma js_rd : forall m1 (j : Z), bytes_at rsegs m1 (bv_unsigned b) B -> 0 <= j < bv_unsigned n ->
  ov_read_bytes rsegs m1 (wa (bv_unsigned b + j)) 1 = Some [nth (Z.to_nat j) B (Z_to_bv 8 0)].
Proof.
  intros m1 j H Hj. rewrite (bytes_at_read rsegs m1 _ B j 1 H) by lia.
  f_equal. apply js_firstn1. lia.
Qed.

Lemma js_jbyte : forall j, jbyte (map bv_unsigned B) j = bv_unsigned (nth (Z.to_nat j) B (Z_to_bv 8 0)).
Proof. intros j. unfold jbyte. change 0 with (bv_unsigned (Z_to_bv 8 0)). apply map_nth. Qed.

Lemma js_jlen : jlen (map bv_unsigned B) = bv_unsigned n.
Proof. unfold jlen. rewrite length_map. exact HL. Qed.

Lemma js_jbyte_range : forall j, 0 <= jbyte (map bv_unsigned B) j < 256.
Proof. intros j. rewrite js_jbyte. apply js_byte_range. Qed.

Lemma js_jdigits_S : forall j f, jdigits (map bv_unsigned B) j (S f) =
  if (j <? bv_unsigned n) && jdigit (jbyte (map bv_unsigned B) j) then jdigits (map bv_unsigned B) (j + 1) f else j.
Proof. intros j f. cbn [jdigits]. rewrite js_jlen. reflexivity. Qed.

Lemma js_jdigits_n : forall f, jdigits (map bv_unsigned B) (bv_unsigned n) f = bv_unsigned n.
Proof. intros [|f]; [reflexivity|]. rewrite js_jdigits_S, Z.ltb_irrefl. reflexivity. Qed.

Lemma js_jdigits_range : forall f j, j <= bv_unsigned n -> j <= jdigits (map bv_unsigned B) j f <= bv_unsigned n.
Proof.
  induction f as [|f IH]; intros j Hj; [cbn; lia|]. rewrite js_jdigits_S.
  destruct (Z.ltb_spec j (bv_unsigned n)); cbn [andb]; [|lia].
  destruct (jdigit _); [|lia]. specialize (IH (j + 1) ltac:(lia)). lia.
Qed.

Lemma js_numC : forall (f : nat) m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                          x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x11 = k -> bv_unsigned i <= k < bv_unsigned n -> bv_unsigned n - k <= Z.of_nat f ->
  x10 = Z_to_bv 64 (-10) -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    Some (jdigits (map bv_unsigned B) k f, 2, bv_unsigned i, jdigits (map bv_unsigned B) k f - bv_unsigned i) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14aa4) fc None m1 (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      HJI H11 Hk Hf H10 H18 HJ; [lia|].
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV). subst x10.
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. unfold inr64 in *.
  pose proof (zr_word i) as Ri. unfold inr64 in Ri.
  pose proof (js_rd m1 k HB ltac:(lia)) as HR.
  zstep. zstep. zstep. zstep.
  rewrite js_nd, <- js_jbyte.
  pose proof (js_jdigits_range (S f) k ltac:(lia)) as JR.
  rewrite js_jdigits_S, (proj2 (Z.ltb_lt _ _) (proj2 Hk)) in HJ, JR. cbn [andb] in HJ, JR.
  destruct (jdigit (jbyte (map bv_unsigned B) k)) eqn:D; cbn [negb].
  - zstep. zstep.
    rewrite (js_eqb_Z n), (unsigned_lit (bv_unsigned x11 + 1)) by lia.
    destruct (Z.eqb_spec (bv_unsigned n) (bv_unsigned x11 + 1)) as [E|E]; cbn [negb].
    + zstep. replace (k + 1) with (bv_unsigned n) in HJ by lia. rewrite js_jdigits_n in HJ.
      eapply js_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
    + eapply (IH m1 jk (k + 1)); [exact HJI | rewrite unsigned_lit by lia; lia | lia | lia | reflexivity | exact H18 | exact HJ].
  - zstep. zstep.
    eapply js_tok; [exact HJI | exact H11 | lia | exact H18 | exact HJ].
Qed.

Definition js_nr (o : option Z) : option jtok :=
  match o with None => None | Some j3 => Some (j3, 2, bv_unsigned i, j3 - bv_unsigned i) end.

Lemma js_expd : forall m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x11 = k -> bv_unsigned i <= k <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    js_nr (if jdig_at (map bv_unsigned B) k then Some (jdigits (map bv_unsigned B) k (length (map bv_unsigned B))) else None) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14a8c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H11 Hk H18 HJ.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  unfold jdig_at in HJ. rewrite js_jlen, length_map in HJ.
  zstep.
  rewrite bv_ltu_Z, H11. destruct (Z.ltb_spec k (bv_unsigned n)) as [HK|HK]; cbn [negb].
  - pose proof (js_rd m1 k HB ltac:(lia)) as HR.
    zstep. zstep. zstep. zstep. zstep.
    rewrite js_nd, <- js_jbyte.
    cbn [andb] in HJ.
    destruct (jdigit (jbyte (map bv_unsigned B) k)) eqn:D; cbn [negb].
    + eapply (js_numC (length B) m1 jk k); [exact HJI | exact H11 | lia | lia | reflexivity | exact H18 | exact HJ].
    + eapply js_fail; [exact HJI | exact HJ].
  - cbn [andb] in HJ.
    eapply js_fail; [exact HJI | exact HJ].
Qed.

Lemma js_exp : forall m1 jk j2 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = j2 -> bv_unsigned i <= j2 <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = js_nr (jexp (map bv_unsigned B) j2) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14a50) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H10 Hj H18 HJ. subst j2.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  unfold jexp in HJ. rewrite js_jlen in HJ.
  zstep.
  rewrite bv_ltu_Z. destruct (Z.ltb_spec (bv_unsigned x10) (bv_unsigned n)) as [HK|HK]; cbn [negb]; js_lt HK HJ; cbn [andb] in HJ.
  2: { zstep. eapply js_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ]. }
  pose proof (js_rd m1 (bv_unsigned x10) HB ltac:(lia)) as HR.
  zstep. zstep. zstep. zstep. zstep.
  rewrite js_e, <- js_jbyte.
  destruct ((jbyte (map bv_unsigned B) (bv_unsigned x10) =? 101) || (jbyte (map bv_unsigned B) (bv_unsigned x10) =? 69)) eqn:EE;
    cbn [negb]; try rewrite EE in HJ; cbn [andb] in HJ.
  2: { zstep. eapply js_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ]. }
  zstep. zstep.
  rewrite bv_ltu_Z, (unsigned_lit (bv_unsigned x10 + 1)) by lia.
  destruct (Z.ltb_spec (bv_unsigned x10 + 1) (bv_unsigned n)) as [HK1|HK1]; cbn [negb]; js_lt HK1 HJ; cbn [andb] in HJ.
  2: { eapply js_expd; [exact HJI | apply unsigned_lit; lia | lia | exact H18 | exact HJ]. }
  pose proof (js_rd m1 (bv_unsigned x10 + 1) HB ltac:(lia)) as HR1.
  pose proof (js_jbyte_range (bv_unsigned x10 + 1)) as RB1.
  zstep. zstep. zstep. zstep.
  rewrite <- js_jbyte. rewrite js_beq by lia.
  destruct (jbyte (map bv_unsigned B) (bv_unsigned x10 + 1) =? 45) eqn:E45; cbn [negb]; try rewrite E45 in HJ.
  - rewrite orb_true_r in HJ. cbn [andb] in HJ. zstep.
    eapply js_expd; [exact HJI | apply unsigned_lit; lia | lia | exact H18 | exact HJ].
  - rewrite orb_false_r in HJ. zstep. zstep.
    rewrite js_beq by lia.
    destruct (jbyte (map bv_unsigned B) (bv_unsigned x10 + 1) =? 43) eqn:E43; cbn [negb]; try rewrite E43 in HJ;
      cbn [andb] in HJ.
    + zstep. eapply js_expd; [exact HJI | apply unsigned_lit; lia | lia | exact H18 | exact HJ].
    + eapply js_expd; [exact HJI | apply unsigned_lit; lia | lia | exact H18 | exact HJ].
Qed.

Lemma js_jexp_n : jexp (map bv_unsigned B) (bv_unsigned n) = Some (bv_unsigned n).
Proof. unfold jexp. rewrite js_jlen, Z.ltb_irrefl. reflexivity. Qed.

Lemma js_jfrac_n : jfrac (map bv_unsigned B) (bv_unsigned n) = Some (bv_unsigned n).
Proof. unfold jfrac. rewrite js_jlen, Z.ltb_irrefl. reflexivity. Qed.

Lemma js_fracL : forall (f : nat) m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                           x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = k -> bv_unsigned i <= k < bv_unsigned n -> bv_unsigned n - k <= Z.of_nat f ->
  x11 = Z_to_bv 64 (-10) -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = js_nr (jexp (map bv_unsigned B) (jdigits (map bv_unsigned B) k f)) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14a14) fc None m1 (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      HJI H10 Hk Hf H11 H18 HJ; [lia|].
  subst k x11.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  pose proof (js_rd m1 (bv_unsigned x10) HB ltac:(lia)) as HR.
  zstep. zstep. zstep. zstep.
  rewrite js_nd, <- js_jbyte.
  rewrite js_jdigits_S, (proj2 (Z.ltb_lt _ _) (proj2 Hk)) in HJ. cbn [andb] in HJ.
  destruct (jdigit (jbyte (map bv_unsigned B) (bv_unsigned x10))) eqn:D; cbn [negb].
  - zstep. zstep.
    rewrite (js_eqb_Z n), (unsigned_lit (bv_unsigned x10 + 1)) by lia.
    destruct (Z.eqb_spec (bv_unsigned n) (bv_unsigned x10 + 1)) as [E|E]; cbn [negb].
    + zstep. replace (bv_unsigned x10 + 1) with (bv_unsigned n) in HJ by lia.
      rewrite js_jdigits_n, js_jexp_n in HJ.
      eapply js_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
    + eapply (IH m1 jk (bv_unsigned x10 + 1)); [exact HJI | apply unsigned_lit; lia | lia | lia | reflexivity | exact H18 | exact HJ].
  - eapply js_exp; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
Qed.

Definition js_fe (j1 : Z) : option jtok :=
  match jfrac (map bv_unsigned B) j1 with None => None | Some j2 => js_nr (jexp (map bv_unsigned B) j2) end.

Lemma js_frac : forall m1 jk j1 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = j1 -> bv_unsigned i <= j1 <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = js_fe j1 ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x149e4) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H10 Hj H18 HJ. subst j1.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  unfold js_fe, jfrac, jdig_at in HJ. rewrite js_jlen in HJ.
  zstep.
  rewrite bv_ltu_Z. destruct (Z.ltb_spec (bv_unsigned x10) (bv_unsigned n)) as [HK|HK]; cbn [negb]; js_lt HK HJ; cbn [andb] in HJ.
  2: { eapply js_exp; [exact HJI | reflexivity | lia | exact H18 | exact HJ]. }
  pose proof (js_rd m1 (bv_unsigned x10) HB ltac:(lia)) as HR.
  pose proof (js_jbyte_range (bv_unsigned x10)) as RB.
  zstep. zstep. zstep. zstep.
  rewrite <- js_jbyte. rewrite js_beq by lia.
  destruct (jbyte (map bv_unsigned B) (bv_unsigned x10) =? 46) eqn:E46; cbn [negb]; try rewrite E46 in HJ; cbn [andb] in HJ.
  2: { eapply js_exp; [exact HJI | reflexivity | lia | exact H18 | exact HJ]. }
  zstep. zstep.
  rewrite bv_ltu_Z, (unsigned_lit (bv_unsigned x10 + 1)) by lia.
  destruct (Z.ltb_spec (bv_unsigned x10 + 1) (bv_unsigned n)) as [HK1|HK1]; cbn [negb]; js_lt HK1 HJ; cbn [andb] in HJ.
  2: { eapply js_fail; [exact HJI | exact HJ]. }
  pose proof (js_rd m1 (bv_unsigned x10 + 1) HB ltac:(lia)) as HR1.
  zstep. zstep. zstep. zstep. zstep.
  rewrite js_nd, <- js_jbyte.
  destruct (jdigit (jbyte (map bv_unsigned B) (bv_unsigned x10 + 1))) eqn:D; cbn [negb]; try rewrite D in HJ;
    cbn [andb] in HJ.
  - rewrite length_map in HJ.
    eapply (js_fracL (length B) m1 jk (bv_unsigned x10 + 1));
      [exact HJI | apply unsigned_lit; lia | lia | lia | reflexivity | exact H18 | exact HJ].
  - eapply js_fail; [exact HJI | exact HJ].
Qed.

Lemma js_intL : forall (f : nat) m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                          x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = k -> bv_unsigned i <= k < bv_unsigned n -> bv_unsigned n - k <= Z.of_nat f ->
  x11 = Z_to_bv 64 (-10) -> bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = js_fe (jdigits (map bv_unsigned B) k f) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14ac4) fc None m1 (seg_rom rsegs)).
Proof.
  induction f as [|f IH];
    intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      HJI H10 Hk Hf H11 H18 HJ; [lia|].
  subst k x11.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  pose proof (js_rd m1 (bv_unsigned x10) HB ltac:(lia)) as HR.
  zstep. zstep. zstep. zstep.
  rewrite js_nd, <- js_jbyte.
  rewrite js_jdigits_S, (proj2 (Z.ltb_lt _ _) (proj2 Hk)) in HJ. cbn [andb] in HJ.
  destruct (jdigit (jbyte (map bv_unsigned B) (bv_unsigned x10))) eqn:D; cbn [negb].
  - zstep. zstep.
    rewrite bv_ltu_Z, (unsigned_lit (bv_unsigned x10 + 1)) by lia.
    destruct (Z.ltb_spec (bv_unsigned x10 + 1) (bv_unsigned n)) as [E|E]; cbn [negb].
    + eapply (IH m1 jk (bv_unsigned x10 + 1)); [exact HJI | apply unsigned_lit; lia | lia | lia | reflexivity | exact H18 | exact HJ].
    + zstep. replace (bv_unsigned x10 + 1) with (bv_unsigned n) in HJ by lia.
      rewrite js_jdigits_n in HJ. unfold js_fe in HJ. rewrite js_jfrac_n, js_jexp_n in HJ.
      eapply js_tok; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
  - eapply js_frac; [exact HJI | reflexivity | lia | exact H18 | exact HJ].
Qed.

Lemma js_num0 : forall m1 jk j0 (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = j0 -> bv_unsigned i <= j0 <= bv_unsigned i + 1 ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    (if negb (jdig_at (map bv_unsigned B) j0) then None
     else js_fe (if jbyte (map bv_unsigned B) j0 =? 48 then j0 + 1
                 else jdigits (map bv_unsigned B) j0 (length (map bv_unsigned B)))) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14968) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk j0 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H10 Hj H18 HJ. subst j0.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  unfold jdig_at in HJ. rewrite js_jlen, length_map in HJ.
  zstep.
  rewrite bv_ltu_Z. destruct (Z.ltb_spec (bv_unsigned x10) (bv_unsigned n)) as [HK|HK]; cbn [negb]; js_lt HK HJ;
    cbn [andb negb] in HJ.
  2: { eapply js_fail; [exact HJI | exact HJ]. }
  pose proof (js_rd m1 (bv_unsigned x10) HB ltac:(lia)) as HR.
  pose proof (js_jbyte_range (bv_unsigned x10)) as RB.
  zstep. zstep. zstep. zstep. zstep.
  rewrite js_nd, <- js_jbyte.
  destruct (jdigit (jbyte (map bv_unsigned B) (bv_unsigned x10))) eqn:D; cbn [negb]; try rewrite D in HJ;
    cbn [andb negb] in HJ.
  2: { eapply js_fail; [exact HJI | exact HJ]. }
  zstep. zstep.
  rewrite js_beq by lia.
  destruct (jbyte (map bv_unsigned B) (bv_unsigned x10) =? 48) eqn:E48; cbn [negb]; try rewrite E48 in HJ.
  - zstep. eapply js_frac; [exact HJI | apply unsigned_lit; lia | lia | exact H18 | exact HJ].
  - zstep. eapply (js_intL (length B) m1 jk (bv_unsigned x10));
      [exact HJI | reflexivity | lia | lia | reflexivity | exact H18 | exact HJ].
Qed.

Lemma js_seqz : forall z, 0 <= z < 256 ->
  Z.b2z ((z + -45) mod 18446744073709551616 <? 1) = if z =? 45 then 1 else 0.
Proof.
  intros z Hz. apply Z.eqb_eq.
  exact (brute256_ok (fun z => Z.b2z ((z + -45) mod 18446744073709551616 <? 1) =? (if z =? 45 then 1 else 0))
           ltac:(vm_compute; reflexivity) z Hz).
Qed.

Lemma js_num : forall m1 jk (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                             x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x9 = jbyte (map bv_unsigned B) (bv_unsigned i) ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = jnum (map bv_unsigned B) (bv_unsigned i) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x1495c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H9 H18 HJ.
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  pose proof (js_jbyte_range (bv_unsigned i)) as RB.
  zstep. zstep. zstep.
  rewrite H9, js_seqz by lia.
  eapply (js_num0 m1 jk (if jbyte (map bv_unsigned B) (bv_unsigned i) =? 45 then bv_unsigned i + 1 else bv_unsigned i));
    [exact HJI | | | exact H18 | exact HJ].
  - destruct (jbyte (map bv_unsigned B) (bv_unsigned i) =? 45); rewrite unsigned_lit by lia; lia.
  - destruct (jbyte (map bv_unsigned B) (bv_unsigned i) =? 45); lia.
Qed.

Hypothesis STRLEN : strlen_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis MEMCHR : memchr_contract.

Definition js_Lb : list byte := le8 (Z_to_bv 64 0x103aa) ++ le8 (Z_to_bv 64 0x10298) ++ le8 (Z_to_bv 64 0x10326).

Lemma js_sub : forall m1 (j : Z) (k : nat), bytes_at rsegs m1 (bv_unsigned b) B -> 0 <= j ->
  (Z.to_nat j + k <= length B)%nat -> bytes_at rsegs m1 (bv_unsigned b + j) (firstn k (skipn (Z.to_nat j) B)).
Proof.
  intros m1 j k H Hj Hk.
  rewrite <- (firstn_skipn (Z.to_nat j) B) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn k (skipn (Z.to_nat j) B)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma js_tok3 : forall m1 jk len (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                  x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x21 = len -> 0 <= len -> bv_unsigned i + len <= bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = Some (bv_unsigned i + len, 3, bv_unsigned i, len) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x149c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk len x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV) H21 HL1 HL2 H18 HJ.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word v) as Rv. pose proof (zr_word i) as Ri.
  pose proof (zr_word x21) as R21. pose proof (zr_word n) as Rn. unfold inr64 in *.
  assert (BV : 0 <= bv_unsigned v /\ bv_unsigned v + 20 <= 2^64) by (destruct HV as (? & ? & _); lia).
  apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  zstep.
  js_hs v 0 8%nat. zstep. js_store.
  js_hs v 8 8%nat. zstep. js_store.
  js_hs v 16 4%nat. zstep. js_store.
  zstep. zstep.
  eapply js_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold js_res. rewrite HJ. split; [apply js_word; rewrite unsigned_lit by lia; lia|]. split; [exact MU|].
  rewrite (js_word x18 _ H18) in HW. rewrite (js_word x21 _ H21) in HW0. apply js_rec3; assumption.
Qed.

Ltac js_ji jk := match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  let H := fresh "HJI" in assert (H : JI mm jk) by (unfold JI; repeat (split; [assumption|]); assumption) end.

Lemma js_lit1 : forall m1 jk (A : Z) (w : list Z) (W slack : list byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  JI m1 jk -> bytes_at rsegs m1 JSON_SCALAR_L js_Lb ->
  ov_read_bytes rsegs m1 x24 8 = Some (le8 (Z_to_bv 64 A)) ->
  0 <= A < 2^64 ->
  (forall mm, mem_inv rsegs mm -> bytes_at rsegs mm A (W ++ Z_to_bv 8 0 :: slack)) ->
  ~ In (Z_to_bv 8 0) W ->
  (- (A + Z.of_nat (length W) + 1)) mod 8 <= Z.of_nat (length slack) ->
  map bv_unsigned W = w -> (length W <= 8)%nat ->
  bv_unsigned x23 = bv_unsigned n - bv_unsigned i ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  ((Z.of_nat (length w) <=? bv_unsigned n - bv_unsigned i) &&
     jprefix w (skipn (Z.to_nat (bv_unsigned i)) (map bv_unsigned B)) = true ->
   jscalar (map bv_unsigned B) (bv_unsigned i) =
     Some (bv_unsigned i + Z.of_nat (length w), 3, bv_unsigned i, Z.of_nat (length w))) ->
  (forall m2 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 : word),
     JI m2 jk -> bytes_at rsegs m2 JSON_SCALAR_L js_Lb ->
     (Z.of_nat (length w) <=? bv_unsigned n - bv_unsigned i) &&
       jprefix w (skipn (Z.to_nat (bv_unsigned i)) (map bv_unsigned B)) = false ->
     evt rsegs POST (MS (mkR y1 SP' gp tp y5 y6 y7 v x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 n b y21 y22 x23 x24
                             x25 x26 i y28 y29 y30 y31) F (Z_to_bv 64 0x14950) fc None m2 (seg_rom rsegs))) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14928) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk A w W slack x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI HL0 HR HA HIMG HNZ HPAD HW HWl H23 H18 HT HK.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV). clear HJI.
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  pose proof (HIMG m1 MI) as HS.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply STRLEN with (str := W) (slack := slack);
      [rewrite unsigned_lit by lia; exact HS | exact HNZ | rewrite unsigned_lit by lia; exact HPAD | exact MI]. }
  post_call rsegs m1.
  subst w. rewrite length_map in HT, HK.
  js_ji jk.
  zstep.
  rewrite bv_ltu_Z, H23, (unsigned_lit (Z.of_nat (length W))) by lia.
  destruct (Z.ltb_spec (bv_unsigned n - bv_unsigned i) (Z.of_nat (length W))) as [HC|HC]; cbn [negb].
  - eapply HK; [eassumption | eassumption |].
    rewrite (proj2 (Z.leb_gt _ _) HC). reflexivity.
  - match goal with H : bytes_at rsegs _ A (W ++ _) |- _ => apply bytes_at_app in H; destruct H as [HSW _] end.
    destruct (memcmp_model_total (firstn (length W) (skipn (Z.to_nat (bv_unsigned i)) B)) W (length W)
      ltac:(rewrite length_firstn, length_skipn; lia) ltac:(lia)) as [vv HM].
    destruct (js_memcmp (length W) (firstn (length W) (skipn (Z.to_nat (bv_unsigned i)) B)) W vv
      ltac:(rewrite length_firstn, length_skipn; lia) eq_refl HM) as [RV IV].
    zstep. zstep. zstep. zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BCMP with (ls := firstn (length W) (skipn (Z.to_nat (bv_unsigned i)) B)) (rs := W) (v := vv);
        [ rewrite H18; apply js_sub; [assumption | lia | lia]
        | rewrite unsigned_lit by lia; exact HSW
        | rewrite unsigned_lit by lia; rewrite Nat2Z.id; exact HM
        | assumption ]
      | post_call rsegs mm ]
    end.
    js_ji jk.
    zstep.
    rewrite js_eqbs by lia.
    destruct (Z.eqb_spec vv 0) as [V0|V0]; cbn [negb].
    + eapply (js_tok3 _ jk (Z.of_nat (length W))); [eassumption | apply unsigned_lit; lia | lia | lia | exact H18 |].
      apply HT. apply andb_true_intro. split; [apply Z.leb_le; lia|].
      rewrite js_skipn_map. apply js_prefix. apply IV. exact V0.
    + eapply HK; [eassumption | eassumption |].
      apply andb_false_intro2. rewrite js_skipn_map.
      destruct (jprefix (map bv_unsigned W) (map bv_unsigned (skipn (Z.to_nat (bv_unsigned i)) B))) eqn:P;
        [|reflexivity].
      apply js_prefix in P. apply IV in P. contradiction.
Qed.

Lemma js_LLb : length js_Lb = 24%nat.
Proof. reflexivity. Qed.

Ltac js_dec := vm_compute; first [reflexivity | let H := fresh in intro H; discriminate H].

Ltac js_lit_app mm jk A w sl HL0 k H18 HJ :=
  eapply (js_lit1 mm jk A w (map (Z_to_bv 8) w) (map (Z_to_bv 8) sl));
  [ eassumption | exact HL0
  | exact (bytes_at_read rsegs mm 130600 js_Lb k 8 HL0 ltac:(lia) ltac:(rewrite js_LLb; lia))
  | lia
  | let mm' := fresh "mm" in let MM := fresh "MM" in
    intros mm' MM; apply js_img; [exact MM | vm_compute; reflexivity | lia | cbn; lia]
  | apply js_notin0; vm_compute; reflexivity
  | js_dec
  | vm_compute; reflexivity
  | cbn; lia
  | apply unsigned_lit; lia
  | exact H18
  | let Hc := fresh "Hc" in intros Hc; rewrite HJ, Hc; reflexivity
  | ].

Lemma js_litp : forall m1 jk (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                              x28 x29 x30 x31 : word),
  JI m1 jk -> bytes_at rsegs m1 JSON_SCALAR_L js_Lb ->
  bv_unsigned x9 = jbyte (map bv_unsigned B) (bv_unsigned i) ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    match jlit (map bv_unsigned B) (bv_unsigned i) jlit_words with
    | Some t => Some t
    | None => jnum (map bv_unsigned B) (bv_unsigned i)
    end ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14918) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI HL0 H9 H18 HJ.
  pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  unfold jlit_words in HJ. cbn [jlit] in HJ. rewrite js_jlen in HJ.
  zstep. zstep. zstep. zstep.
  js_lit_app m1 jk 0x103aa [116; 114; 117; 101] [114] HL0 0 H18 HJ.
  intros m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y21 y22 y28 y29 y30 y31 HJI2 HL2 Hc1.
  rewrite Hc1 in HJ.
  zstep. zstep. zstep. if_true.
  js_lit_app m2 jk 0x10298 [102; 97; 108; 115; 101] [114; 111] HL2 8 H18 HJ.
  intros m3 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z21 z22 z28 z29 z30 z31 HJI3 HL3 Hc2.
  rewrite Hc2 in HJ.
  zstep. zstep. zstep. if_true.
  js_lit_app m3 jk 0x10326 [110; 117; 108; 108] [32; 105; 110; 32; 47] HL3 16 H18 HJ.
  intros m4 u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u21 u22 u28 u29 u30 u31 HJI4 HL4 Hc3.
  rewrite Hc3 in HJ.
  zstep. zstep. zstep. if_false.
  eapply js_num; [exact HJI4 | exact H9 | exact H18 | exact HJ].
Qed.

Lemma js_fail0 : forall m1 jk (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                               x28 x29 x30 x31 : word),
  JI m1 jk -> jscalar (map bv_unsigned B) (bv_unsigned i) = None ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14984) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV) HJ.
  eapply js_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold js_res. rewrite HJ. split; [reflexivity | exact MU].
Qed.

Lemma js_tok1 : forall m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26
                                x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x26 = k -> bv_unsigned i <= k -> k + 1 < bv_unsigned n ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = Some (k + 2, 1, bv_unsigned i + 1, k - bv_unsigned i) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14a30) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    (FR & ST & MU & WM & MI & HB & HV) H26 Hk1 Hk2 H18 HJ.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word v) as Rv. pose proof (zr_word i) as Ri.
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word x26) as R26. unfold inr64 in *.
  assert (BV : 0 <= bv_unsigned v /\ bv_unsigned v + 20 <= 2^64) by (destruct HV as (? & ? & _); lia).
  apply (munch_weaken _ [(bv_unsigned sp + -112, bv_unsigned sp); (bv_unsigned v, bv_unsigned v + 20)]) in MU;
    [|unfold sub_fp; cbn [outside]; intros; tauto].
  zstep. zstep. zstep.
  js_hs v 0 8%nat. zstep. js_store.
  js_hs v 8 8%nat. zstep. js_store.
  js_hs v 16 4%nat. zstep. js_store.
  zstep. zstep.
  eapply js_epi; [exact FR | exact ST | exact WM | exact MI |].
  unfold js_res. rewrite HJ. split; [apply js_word; rewrite unsigned_lit by lia; lia|]. split; [exact MU|].
  rewrite H18 in HW. rewrite H26 in HW0.
  replace (bv_unsigned b + (bv_unsigned i + 1)) with (bv_unsigned b + bv_unsigned i + 1) by lia.
  apply js_rec3; assumption.
Qed.

Definition js_LH (f : nat) : Prop :=
  forall m1 jk j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x9 = j -> bv_unsigned x26 = j - 1 -> bv_unsigned i + 1 <= j < bv_unsigned n ->
  bv_unsigned n - j <= Z.of_nat f ->
  x21 = Z_to_bv 64 0x102f9 -> x23 = Z_to_bv 64 34 -> x24 = Z_to_bv 64 32 -> x25 = Z_to_bv 64 92 ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = jstr (map bv_unsigned B) (bv_unsigned i) j f ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14828) fc None m1 (seg_rom rsegs)).

Lemma js_jstr_end : forall j f, bv_unsigned n <= j -> jstr (map bv_unsigned B) (bv_unsigned i) j f = None.
Proof. intros j [|f] Hj; [reflexivity|]. cbn [jstr]. rewrite js_jlen, (proj2 (Z.leb_le _ _) Hj). reflexivity. Qed.

Lemma js_snext : forall f, js_LH f ->
  forall m1 jk k (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x9 = k -> bv_unsigned i <= k < bv_unsigned n -> bv_unsigned n - (k + 1) <= Z.of_nat f ->
  x21 = Z_to_bv 64 0x102f9 -> x23 = Z_to_bv 64 34 -> x24 = Z_to_bv 64 32 -> x25 = Z_to_bv 64 92 ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) = jstr (map bv_unsigned B) (bv_unsigned i) (k + 1) f ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14900) fc None m1 (seg_rom rsegs)).
Proof.
  intros f LH m1 jk k x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H9 Hk Hf H21 H23 H24 H25 H18 HJ.
  pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  zstep. zstep. zstep.
  rewrite bv_ltu_Z, H9, (unsigned_lit (k + 1)) by lia.
  destruct (Z.ltb_spec (k + 1) (bv_unsigned n)) as [HK|HK]; cbn [negb].
  - zstep. eapply (LH m1 jk (k + 1)); [exact HJI | apply unsigned_lit; lia | lia | lia | lia
      | exact H21 | exact H23 | exact H24 | exact H25 | exact H18 | exact HJ].
  - eapply js_fail; [exact HJI|]. rewrite HJ. apply js_jstr_end. lia.
Qed.

Definition js_E : list byte := map (Z_to_bv 8) [34; 92; 47; 98; 102; 110; 114; 116; 117; 0].

Lemma js_esc : forall c, 0 <= c < 256 ->
  bv_eqb (Z_to_bv 64 (memchr_res 66297 c 10 js_E)) (Z_to_bv 64 0) = negb (jesc c || (c =? 0)).
Proof.
  intros c Hc. apply Bool.eqb_prop.
  exact (brute256_ok (fun c => Bool.eqb (bv_eqb (Z_to_bv 64 (memchr_res 66297 c 10 js_E)) (Z_to_bv 64 0))
                                        (negb (jesc c || (c =? 0)))) ltac:(vm_compute; reflexivity) c Hc).
Qed.

Lemma js_hx5 : forall f, js_LH f ->
  forall m1 jk j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x9 = j + 5 -> bv_unsigned i + 1 <= j -> j + 6 <= bv_unsigned n ->
  bv_unsigned n - (j + 6) <= Z.of_nat f -> x13 = Z_to_bv 64 (-11) ->
  x21 = Z_to_bv 64 0x102f9 -> x23 = Z_to_bv 64 34 -> x24 = Z_to_bv 64 32 -> x25 = Z_to_bv 64 92 ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    (if negb (jhexd (jbyte (map bv_unsigned B) (j + 5))) then None
     else jstr (map bv_unsigned B) (bv_unsigned i) (j + 6) f) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x148e0) fc None m1 (seg_rom rsegs)).
Proof.
  intros f LH m1 jk j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H9 Hj1 Hj2 Hf H13 H21 H23 H24 H25 H18 HJ. subst x13.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  pose proof (js_rd m1 (j + 5) HB ltac:(lia)) as HR.
  pose proof (js_jbyte_range (j + 5)) as RB.
  zstep. zstep. zstep. zstep.
  rewrite <- js_jbyte, js_hd by lia.
  destruct (jdigit (jbyte (map bv_unsigned B) (j + 5))) eqn:D; cbn [negb].
  { rewrite (js_dh _ D) in HJ. cbn [negb] in HJ.
    eapply (js_snext f LH m1 jk (j + 5)); [exact HJI | exact H9 | lia | lia | exact H21 | exact H23 | exact H24
      | exact H25 | exact H18 | rewrite HJ; f_equal; lia]. }
  zstep. zstep. zstep. zstep.
  rewrite js_ha by first [lia | exact D].
  destruct (jhexd (jbyte (map bv_unsigned B) (j + 5))) eqn:HX; cbn [negb]; try rewrite HX in HJ; cbn [negb] in HJ.
  - eapply (js_snext f LH m1 jk (j + 5)); [exact HJI | exact H9 | lia | lia | exact H21 | exact H23 | exact H24
      | exact H25 | exact H18 | rewrite HJ; f_equal; lia].
  - eapply js_fail; [exact HJI | exact HJ].
Qed.

Lemma js_hx3 : forall f, js_LH f ->
  forall m1 jk j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = bv_unsigned b + j - 1 -> bv_unsigned x26 = j - 1 ->
  bv_unsigned i + 1 <= j -> j + 6 <= bv_unsigned n ->
  bv_unsigned n - (j + 6) <= Z.of_nat f -> x13 = Z_to_bv 64 (-11) ->
  x21 = Z_to_bv 64 0x102f9 -> x23 = Z_to_bv 64 34 -> x24 = Z_to_bv 64 32 -> x25 = Z_to_bv 64 92 ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    (if negb (jhexd (jbyte (map bv_unsigned B) (j + 4)) && jhexd (jbyte (map bv_unsigned B) (j + 5))) then None
     else jstr (map bv_unsigned B) (bv_unsigned i) (j + 6) f) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x148c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros f LH m1 jk j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H10 H26 Hj1 Hj2 Hf H13 H21 H23 H24 H25 H18 HJ. subst x13.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  pose proof (js_rd m1 (j + 4) HB ltac:(lia)) as HR.
  pose proof (js_jbyte_range (j + 4)) as RB.
  zstep. zstep. zstep.
  rewrite <- js_jbyte, js_hd by lia.
  destruct (jdigit (jbyte (map bv_unsigned B) (j + 4))) eqn:D; cbn [negb].
  { rewrite (js_dh _ D) in HJ. cbn [andb] in HJ. zstep.
    eapply (js_hx5 f LH _ jk j); [eassumption | rewrite unsigned_lit by lia; lia | lia | lia | lia | reflexivity
      | exact H21 | exact H23 | exact H24 | exact H25 | exact H18 | exact HJ]. }
  zstep. zstep. zstep. zstep.
  rewrite js_ha by first [lia | exact D].
  destruct (jhexd (jbyte (map bv_unsigned B) (j + 4))) eqn:HX; cbn [negb]; try rewrite HX in HJ; cbn [andb negb] in HJ.
  - zstep. eapply (js_hx5 f LH _ jk j); [eassumption | rewrite unsigned_lit by lia; lia | lia | lia | lia | reflexivity
      | exact H21 | exact H23 | exact H24 | exact H25 | exact H18 | exact HJ].
  - eapply js_fail; [exact HJI | exact HJ].
Qed.

Lemma js_hx2 : forall f, js_LH f ->
  forall m1 jk j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x10 = bv_unsigned b + j - 1 -> bv_unsigned x26 = j - 1 ->
  bv_unsigned i + 1 <= j -> j + 6 <= bv_unsigned n ->
  bv_unsigned n - (j + 6) <= Z.of_nat f -> x13 = Z_to_bv 64 (-11) ->
  x21 = Z_to_bv 64 0x102f9 -> x23 = Z_to_bv 64 34 -> x24 = Z_to_bv 64 32 -> x25 = Z_to_bv 64 92 ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    (if negb (jhexd (jbyte (map bv_unsigned B) (j + 3)) && jhexd (jbyte (map bv_unsigned B) (j + 4)) &&
              jhexd (jbyte (map bv_unsigned B) (j + 5))) then None
     else jstr (map bv_unsigned B) (bv_unsigned i) (j + 6) f) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x148a4) fc None m1 (seg_rom rsegs)).
Proof.
  intros f LH m1 jk j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H10 H26 Hj1 Hj2 Hf H13 H21 H23 H24 H25 H18 HJ. subst x13.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  pose proof (js_rd m1 (j + 3) HB ltac:(lia)) as HR.
  pose proof (js_jbyte_range (j + 3)) as RB.
  zstep. zstep. zstep.
  rewrite <- js_jbyte, js_hd by lia.
  destruct (jdigit (jbyte (map bv_unsigned B) (j + 3))) eqn:D; cbn [negb].
  { rewrite (js_dh _ D) in HJ. cbn [andb] in HJ.
    eapply (js_hx3 f LH _ jk j); [eassumption | exact H10 | exact H26 | lia | lia | lia | reflexivity
      | exact H21 | exact H23 | exact H24 | exact H25 | exact H18 | exact HJ]. }
  zstep. zstep. zstep. zstep.
  rewrite js_ha by first [lia | exact D].
  destruct (jhexd (jbyte (map bv_unsigned B) (j + 3))) eqn:HX; cbn [negb]; try rewrite HX in HJ; cbn [andb negb] in HJ.
  - eapply (js_hx3 f LH _ jk j); [eassumption | exact H10 | exact H26 | lia | lia | lia | reflexivity
      | exact H21 | exact H23 | exact H24 | exact H25 | exact H18 | exact HJ].
  - eapply js_fail; [exact HJI | exact HJ].
Qed.

Lemma js_hexs : forall f, js_LH f ->
  forall m1 jk j (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  JI m1 jk -> bv_unsigned x9 = j + 1 -> bv_unsigned x26 = j - 1 ->
  bv_unsigned i + 1 <= j -> j + 1 < bv_unsigned n ->
  bv_unsigned n - (j + 6) <= Z.of_nat f ->
  x21 = Z_to_bv 64 0x102f9 -> x23 = Z_to_bv 64 34 -> x24 = Z_to_bv 64 32 -> x25 = Z_to_bv 64 92 ->
  bv_unsigned x18 = bv_unsigned b + bv_unsigned i ->
  jscalar (map bv_unsigned B) (bv_unsigned i) =
    (if (bv_unsigned n - (j + 1) <=? 4) ||
        negb (jhexd (jbyte (map bv_unsigned B) (j + 2)) && jhexd (jbyte (map bv_unsigned B) (j + 3)) &&
              jhexd (jbyte (map bv_unsigned B) (j + 4)) && jhexd (jbyte (map bv_unsigned B) (j + 5))) then None
     else jstr (map bv_unsigned B) (bv_unsigned i) (j + 6) f) ->
  evt rsegs POST (MS (mkR x1 SP' gp tp x5 x6 x7 v x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 n b x21 x22 x23 x24
                          x25 x26 i x28 x29 x30 x31) F (Z_to_bv 64 0x14874) fc None m1 (seg_rom rsegs)).
Proof.
  intros f LH m1 jk j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H9 H26 Hj1 Hj2 Hf H21 H23 H24 H25 H18 HJ.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri. unfold inr64 in *.
  zstep. zstep. zstep.
  rewrite bv_ltu_Z, H9, !unsigned_lit by lia.
  destruct (Z.ltb_spec (bv_unsigned n - (j + 1)) 5) as [HC|HC]; cbn [negb].
  { eapply js_fail; [exact HJI|]. rewrite HJ, (proj2 (Z.leb_le (bv_unsigned n - (j + 1)) 4) ltac:(lia)). reflexivity. }
  rewrite (proj2 (Z.leb_gt (bv_unsigned n - (j + 1)) 4) ltac:(lia)) in HJ. cbn [orb] in HJ.
  pose proof (js_rd m1 (j + 2) HB ltac:(lia)) as HR.
  pose proof (js_jbyte_range (j + 2)) as RB.
  zstep. zstep. zstep. zstep. zstep.
  rewrite <- js_jbyte, js_hd by lia.
  destruct (jdigit (jbyte (map bv_unsigned B) (j + 2))) eqn:D; cbn [negb].
  { rewrite (js_dh _ D) in HJ. cbn [andb] in HJ.
    eapply (js_hx2 f LH _ jk j); [eassumption | rewrite unsigned_lit by lia; lia | exact H26 | lia | lia | lia
      | reflexivity | exact H21 | exact H23 | exact H24 | exact H25 | exact H18 | exact HJ]. }
  zstep. zstep. zstep. zstep.
  rewrite js_ha by first [lia | exact D].
  destruct (jhexd (jbyte (map bv_unsigned B) (j + 2))) eqn:HX; cbn [negb]; try rewrite HX in HJ; cbn [andb negb] in HJ.
  - eapply (js_hx2 f LH _ jk j); [eassumption | rewrite unsigned_lit by lia; lia | exact H26 | lia | lia | lia
      | reflexivity | exact H21 | exact H23 | exact H24 | exact H25 | exact H18 | exact HJ].
  - eapply js_fail; [exact HJI | exact HJ].
Qed.

Lemma js_sstep : forall f, js_LH f -> js_LH (S f).
Proof.
  intros f IH m1 jk j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
    HJI H9 H26 Hj Hf H21 H23 H24 H25 H18 HJ.
  subst j x21 x23 x24 x25.
  pose proof HJI as (FR & ST & MU & WM & MI & HB & HV).
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri.
  pose proof (zr_word x9) as R9. unfold inr64 in *.
  pose proof (js_rd m1 (bv_unsigned x9) HB ltac:(lia)) as HR.
  pose proof (js_jbyte_range (bv_unsigned x9)) as RB.
  cbn [jstr] in HJ. rewrite js_jlen, (proj2 (Z.leb_gt _ _) (proj2 Hj)) in HJ.
  zstep. zstep. zstep.
  rewrite <- js_jbyte. rewrite js_beq by lia.
  destruct (jbyte (map bv_unsigned B) (bv_unsigned x9) =? 34) eqn:E34; cbn [negb]; try rewrite E34 in HJ.
  { eapply (js_tok1 m1 jk (bv_unsigned x9 - 1)); [exact HJI | exact H26 | lia | lia | exact H18 |].
    rewrite HJ. cbv iota. apply js_some4; lia. }
  zstep.
  rewrite bv_ltu_Z, !unsigned_lit by lia.
  destruct (jbyte (map bv_unsigned B) (bv_unsigned x9) <? 32) eqn:E32; cbn [negb]; try rewrite E32 in HJ.
  { eapply js_fail; [exact HJI | rewrite HJ; reflexivity]. }
  zstep.
  rewrite js_beq by lia.
  destruct (jbyte (map bv_unsigned B) (bv_unsigned x9) =? 92) eqn:E92; cbn [negb]; try rewrite E92 in HJ.
  2: { eapply (js_snext f IH m1 jk (bv_unsigned x9));
         [exact HJI | reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact H18 |].
       rewrite HJ. reflexivity. }
  zstep. zstep.
  rewrite bv_ltu_Z, H26.
  replace (bv_unsigned x9 - 1 + 2) with (bv_unsigned x9 + 1) by lia.
  rewrite (unsigned_lit (bv_unsigned x9 + 1)) by lia.
  destruct (Z.ltb_spec (bv_unsigned x9 + 1) (bv_unsigned n)) as [HK1|HK1]; cbn [negb].
  2: { eapply js_fail; [exact HJI|]. rewrite HJ. cbv iota. rewrite (proj2 (Z.leb_le _ _) HK1). reflexivity. }
  rewrite (proj2 (Z.leb_gt _ _) HK1) in HJ. cbv iota in HJ.
  pose proof (js_rd m1 (bv_unsigned x9 + 1) HB ltac:(lia)) as HR1.
  pose proof (js_jbyte_range (bv_unsigned x9 + 1)) as RB1.
  zstep. zstep. zstep. zstep. zstep. zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MEMCHR with (buf := js_E);
      [ rewrite unsigned_lit by lia; apply js_img; [exact MI | vm_compute; reflexivity | lia | cbn; lia]
      | unfold memchr_ok; destruct (find_byte _ _); [left|]; rewrite unsigned_lit by lia; cbn; lia
      | exact MI ]
    | post_call rsegs mm ]
  end.
  js_ji jk.
  zstep. zstep. zstep.
  rewrite <- js_jbyte, (Z.mod_small (jbyte (map bv_unsigned B) (bv_unsigned x9 + 1)) 256) by lia.
  rewrite js_esc by lia.
  destruct (jesc (jbyte (map bv_unsigned B) (bv_unsigned x9 + 1))) eqn:EJ; cbn [orb negb]; try rewrite EJ in HJ;
    cbn [negb] in HJ.
  - assert (NZ : (jbyte (map bv_unsigned B) (bv_unsigned x9 + 1) =? 0) = false).
    { apply Z.eqb_neq. intro E0. rewrite E0 in EJ. discriminate EJ. }
    zstep. rewrite js_beq by lia. rewrite NZ. cbn [negb].
    zstep. zstep. rewrite js_beq by lia.
    destruct (jbyte (map bv_unsigned B) (bv_unsigned x9 + 1) =? 117) eqn:E117; cbn [negb]; try rewrite E117 in HJ;
      cbv iota in HJ.
    + eapply (js_hexs f IH _ jk (bv_unsigned x9)); [eassumption | apply unsigned_lit; lia | exact H26 | lia | lia | lia
        | reflexivity | reflexivity | reflexivity | reflexivity | exact H18 | exact HJ].
    + eapply (js_snext f IH _ jk (bv_unsigned x9 + 1)); [eassumption | apply unsigned_lit; lia | lia | lia
        | reflexivity | reflexivity | reflexivity | reflexivity | exact H18 | rewrite HJ; f_equal; lia].
  - destruct (jbyte (map bv_unsigned B) (bv_unsigned x9 + 1) =? 0) eqn:E0; cbn [negb].
    + zstep. rewrite js_beq by lia. rewrite E0. cbn [negb]. eapply js_fail0; [eassumption | exact HJ].
    + eapply js_fail0; [eassumption | exact HJ].
Qed.

Lemma js_sloop : forall f, js_LH f.
Proof.
  induction f as [|f IH].
  - intros m1 jk j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31
      HJI H9 H26 Hj Hf. exfalso. lia.
  - apply js_sstep. exact IH.
Qed.

Lemma js_body : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bytes_at rsegs m (bv_unsigned b) B -> wr_at rsegs m (bv_unsigned v) 20 ->
  bytes_at rsegs m JSON_SCALAR_L js_Lb -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 b i n v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x147b0) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 HB HV HL0 MI ST.
  pose proof (zr_word b) as Rb. pose proof (zr_word n) as Rn. pose proof (zr_word i) as Ri.
  pose proof (zr_word sp) as Rsp. unfold inr64 in *.
  pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold JSON_SCALAR_L, js_Lb in HL0.
  carve_frame 112%nat ST.
  do 14 zstep.
  fold js_Lb in HL0.
  match goal with FR : rw_cells _ _ _ (CB 8 ?jk :: _) |- _ => js_ji jk end.
  assert (HJ0 : jscalar (map bv_unsigned B) (bv_unsigned i) =
    if jbyte (map bv_unsigned B) (bv_unsigned i) =? 34
    then jstr (map bv_unsigned B) (bv_unsigned i) (bv_unsigned i + 1) (length (map bv_unsigned B))
    else match jlit (map bv_unsigned B) (bv_unsigned i) jlit_words with
         | Some t => Some t
         | None => jnum (map bv_unsigned B) (bv_unsigned i)
         end).
  { unfold jscalar. rewrite js_jlen, (proj2 (Z.leb_gt _ _) HI). reflexivity. }
  pose proof (js_rd _ (bv_unsigned i) ltac:(eassumption) ltac:(lia)) as HR.
  pose proof (js_jbyte_range (bv_unsigned i)) as RB.
  do 8 zstep.
  rewrite <- js_jbyte. rewrite js_beq by lia.
  destruct (jbyte (map bv_unsigned B) (bv_unsigned i) =? 34) eqn:E34; cbn [negb]; try rewrite E34 in HJ0.
  2: { eapply js_litp; [eassumption | eassumption | rewrite unsigned_lit by lia; reflexivity
         | rewrite unsigned_lit by lia; reflexivity | exact HJ0]. }
  zstep. zstep.
  rewrite bv_ltu_Z, (unsigned_lit (bv_unsigned i + 1)) by lia.
  destruct (Z.ltb_spec (bv_unsigned i + 1) (bv_unsigned n)) as [HK|HK]; cbn [negb].
  2: { eapply js_fail; [eassumption|]. rewrite HJ0. apply js_jstr_end. exact HK. }
  do 6 zstep.
  rewrite length_map in HJ0.
  eapply (js_sloop (length B) _ _ (bv_unsigned i + 1)); [eassumption | apply unsigned_lit; lia | lia | lia | lia
    | reflexivity | reflexivity | reflexivity | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact HJ0].
Qed.

End JS.

Theorem json_scalar_holds : memchr_contract -> strlen_contract -> bcmp_contract -> json_scalar_contract.
Proof.
  intros MEMCHR STRLEN BCMP. unfold json_scalar_contract, JSON_SCALAR, JSON_SCALAR_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B
    HL HBN HB HV DV HLt DL MI ST LO.
  pose proof (zr_word a1) as R1. pose proof (zr_word a2) as R2. unfold inr64 in *.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  unfold JSON_SCALAR_L in DL.
  zstep.
  rewrite bv_ltu_Z. destruct (Z.ltb_spec (bv_unsigned a1) (bv_unsigned a2)) as [HI|HI]; cbn [negb].
  - destruct (HB HI) as [HBB DB].
    eapply js_body; try eassumption; try lia.
  - zstep. zstep. apply evt_done. unfold json_scalar_post.
    exists t0, t1, t2, (Z_to_bv 64 0), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m.
    split; [reflexivity|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
    replace (jscalar (map bv_unsigned B) (bv_unsigned a1)) with (@None jtok).
    + split; [reflexivity | apply munch_refl].
    + unfold jscalar, jlen. rewrite length_map, HL, (proj2 (Z.leb_le _ _) HI). reflexivity.
Qed.
