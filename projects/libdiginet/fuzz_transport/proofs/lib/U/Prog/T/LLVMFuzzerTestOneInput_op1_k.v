(* Helpers of the walk of case 1 of LLVMFuzzerTestOneInput (U/Prog/T/LLVMFuzzerTestOneInput_op1.v): op_frame
   (fuzz_transport.c:1035-1050, TModel/TOps.v op_frame_m) inlined at 0x13b38 .. 0x13dac, ubsan image.
   - a finite check over an interval of Z (o1_zall), for the facts about one byte or one 16-bit value the
     compiler's arithmetic needs (the w % 1485 multiply sequence, the table indices, the sign test of sel);
   - the model: the eight cursor reads of op_frame as bytes of the cursor (o1_byt) and the op_m equation of op 1;
   - the tables: the DST / SRC pointer tables in .data.rel.ro (0x21f58, 0x21f38; relro_img), the CMD bytes in
     .rodata (0x10485; mem_inv) and the six-byte MACs the pointers reach (lh_mac_at). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- a finite check over [lo, lo + p) *)

Fixpoint o1_zall (f : Z -> bool) (lo : Z) (p : positive) {struct p} : bool :=
  match p with
  | xH => f lo
  | xO q => o1_zall f lo q && o1_zall f (lo + Zpos q) q
  | xI q => f lo && o1_zall f (lo + 1) q && o1_zall f (lo + 1 + Zpos q) q
  end.

Lemma o1_zall_ok : forall p f lo, o1_zall f lo p = true -> forall x, lo <= x < lo + Zpos p -> f x = true.
Proof.
  induction p as [q IH|q IH|]; intros f lo H x Hx; cbn [o1_zall] in H.
  - apply andb_prop in H. destruct H as [H H2]. apply andb_prop in H. destruct H as [H0 H1].
    rewrite Pos2Z.inj_xI in Hx.
    destruct (Z.eq_dec x lo) as [->|Hne]; [exact H0|].
    destruct (Z_lt_le_dec x (lo + 1 + Zpos q)) as [Hl|Hl].
    + apply (IH f (lo + 1) H1). lia.
    + apply (IH f (lo + 1 + Zpos q) H2). lia.
  - apply andb_prop in H. destruct H as [H1 H2]. rewrite Pos2Z.inj_xO in Hx.
    destruct (Z_lt_le_dec x (lo + Zpos q)) as [Hl|Hl].
    + apply (IH f lo H1). lia.
    + apply (IH f (lo + Zpos q) H2). lia.
  - assert (E : x = lo) by lia. subst x. exact H.
Qed.

Lemma o1_zall2 : forall p q (f : Z -> Z -> bool),
  o1_zall (fun x => o1_zall (fun y => f x y) 0 q) 0 p = true ->
  forall x y, 0 <= x < Zpos p -> 0 <= y < Zpos q -> f x y = true.
Proof.
  intros p q f H x y Hx Hy.
  pose proof (o1_zall_ok p _ 0 H x ltac:(lia)) as H1. cbv beta in H1.
  exact (o1_zall_ok q (fun y => f x y) 0 H1 y ltac:(lia)).
Qed.

(* A goal [e = true] whose only free variable is x, with 0 <= x < Zpos p in the context: checked for every x.
   e must be closed but for x (vm_compute runs on [o1_zall F 0 p], a closed term): F is checked for a free
   variable first, which fails loudly (vm_compute of an open term normalises bitvector proofs without bound). *)
Ltac o1_closed t :=
  tryif (match t with context [?y] => is_var y end) then fail 100 "o1_bf: an open term" t else idtac.

Ltac o1_bf x p :=
  lazymatch goal with |- ?e = true =>
    let e' := eval pattern x in e in
    lazymatch e' with ?F x =>
      o1_closed F;
      refine (o1_zall_ok p F 0 _ x _); [vm_compute; reflexivity | lia]
    end
  end.

(* the same for a branch condition c = true / c = false on bitvectors that are closed but for x *)
Ltac o1_bfc x p :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu;
  rewrite ?unsigned_lit_wrap;
  lazymatch goal with
  | |- _ = true => o1_bf x p
  | |- _ = false => apply Bool.negb_true_iff; o1_bf x p
  end.

(* a word equation Z_to_bv 64 e1 = Z_to_bv 64 e2 whose only free variable is x *)
Ltac o1_bfw x p :=
  apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; apply Z.eqb_eq; o1_bf x p.

(* a branch condition decided by lia (the operands' bounds in the context) *)
Ltac o1c :=
  rewrite ?bv_lts_zero_r, ?bv_lts_zero_l;
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu;
  rewrite ?unsigned_lit_wrap;
  repeat match goal with
  | |- negb _ = true => apply Bool.negb_true_iff
  | |- negb _ = false => apply Bool.negb_false_iff
  end;
  first [ apply Z.eqb_eq; Z.div_mod_to_equations; lia
        | apply Z.eqb_neq; Z.div_mod_to_equations; lia
        | apply Z.ltb_lt; Z.div_mod_to_equations; lia
        | apply Z.ltb_ge; Z.div_mod_to_equations; lia
        | apply Z.leb_le; Z.div_mod_to_equations; lia
        | apply Z.leb_gt; Z.div_mod_to_equations; lia ].

(* a conditional branch whose condition lia decides *)
Ltac o1_br :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    first [ replace c with false by (symmetry; o1c); cbv iota
          | replace c with true by (symmetry; o1c); cbv iota ]
  end.

Ltac o1_brf tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; tac] end.
Ltac o1_brt tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; tac] end.

(* ---------------------------------------------------------------- small arithmetic facts *)

Lemma o1_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma o1_lor8 : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor lo (Z.shiftl hi 8) mod 2 ^ 16 = lo + hi * 256.
Proof.
  intros lo hi Hl Hh. apply Z.eqb_eq.
  exact (o1_zall2 256 256 (fun lo hi => Z.lor lo (Z.shiftl hi 8) mod 2 ^ 16 =? lo + hi * 256)
           ltac:(vm_compute; reflexivity) lo hi Hl Hh).
Qed.

Lemma o1_lor_mul : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor (hi * 256) lo = lo + hi * 256.
Proof.
  intros lo hi Hl Hh. apply Z.eqb_eq.
  exact (o1_zall2 256 256 (fun lo hi => Z.lor (hi * 256) lo =? lo + hi * 256)
           ltac:(vm_compute; reflexivity) lo hi Hl Hh).
Qed.

Lemma o1_land128 : forall b, 0 <= b < 256 -> (Z.land b 128 =? 0) = (b <? 128).
Proof.
  intros b Hb. apply Bool.eqb_true_iff.
  o1_bf b 256%positive.
Qed.

Lemma o1_swrap32 : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2 ^ 31) by reflexivity. rewrite E. lia.
Qed.

(* lw of g_last_counter: the sign-extended word's low 32 bits are the field *)
Lemma o1_s32 : forall B, bv_unsigned (Z_to_bv 64 (s32_at B 64976)) mod 2 ^ 32 = g_last_counter B.
Proof.
  intros B. rewrite unsigned_lit_wrap. unfold g_last_counter, OFF_g_last_counter, s32_at.
  pose proof (u_at_range B 64976 4) as R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
  revert R. generalize (u_at B 64976 4). intros u R.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma o1_zxb_b8 : forall v, 0 <= v < 256 -> zxb (b8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb, b8. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hv.
Qed.

(* ---------------------------------------------------------------- the model: the cursor reads of op_frame *)

(* the byte i of the cursor c (0 past its end), and c advanced by k bytes (at most its n) *)
Definition o1_byt (D : list byte) (c : fuzz_in) (i : Z) : Z :=
  if i <? fi_n c then at8 D (Z.to_nat (fi_off c + i)) else 0.
Definition o1_adv (c : fuzz_in) (k : Z) : fuzz_in :=
  FuzzIn (fi_off c + Z.min k (fi_n c)) (fi_n c - Z.min k (fi_n c)).

Lemma o1_byt_in : forall D c i, 0 <= i < fi_n c -> o1_byt D c i = bv_unsigned (nth (Z.to_nat (fi_off c + i)) D (b8 0)).
Proof. intros D c i H. unfold o1_byt, at8, bz. destruct (Z.ltb_spec i (fi_n c)); [reflexivity | lia]. Qed.

Lemma o1_byt_out : forall D c i, fi_n c <= i -> o1_byt D c i = 0.
Proof. intros D c i H. unfold o1_byt. destruct (Z.ltb_spec i (fi_n c)); [lia | reflexivity]. Qed.

Lemma o1_byt_rng : forall D c i, 0 <= o1_byt D c i < 256.
Proof.
  intros D c i. unfold o1_byt, at8, bz. destruct (i <? fi_n c); [apply o1_byte_rng | lia].
Qed.

Lemma o1_adv0 : forall c, 0 <= fi_n c -> o1_adv c 0 = c.
Proof.
  intros [o n] H. unfold o1_adv. cbn [fi_off fi_n] in *. replace (Z.min 0 n) with 0 by lia.
  f_equal; lia.
Qed.

Lemma o1_u8 : forall D c k k', 0 <= fi_n c -> 0 <= k -> k' = k + 1 ->
  fuzz_u8_m D (o1_adv c k) = (o1_adv c k', o1_byt D c k).
Proof.
  intros D [o n] k k' Hn Hk ->. unfold fuzz_u8_m, o1_adv, o1_byt. cbn [fi_off fi_n] in *.
  destruct (Z.ltb_spec k n) as [L|L].
  - replace (Z.min k n) with k by lia. replace (Z.min (k + 1) n) with (k + 1) by lia.
    destruct (Z.eqb_spec (n - k) 0) as [E|E]; [lia|].
    replace (o + (k + 1)) with (o + k + 1) by lia. replace (n - (k + 1)) with (n - k - 1) by lia.
    reflexivity.
  - replace (Z.min k n) with n by lia. replace (Z.min (k + 1) n) with n by lia.
    destruct (Z.eqb_spec (n - n) 0) as [E|E]; [reflexivity | lia].
Qed.

Lemma o1_u8_0 : forall D c, 0 <= fi_n c -> fuzz_u8_m D c = (o1_adv c 1, o1_byt D c 0).
Proof.
  intros D c H. rewrite <- (o1_adv0 c H) at 1. apply o1_u8; lia.
Qed.

Lemma o1_u16 : forall D c k k', 0 <= fi_n c -> 0 <= k -> k' = k + 2 ->
  fuzz_u16_m D (o1_adv c k) = (o1_adv c k', o1_byt D c k + o1_byt D c (k + 1) * 256).
Proof.
  intros D c k k' Hn Hk ->. unfold fuzz_u16_m.
  rewrite (o1_u8 D c k (k + 1)) by lia. cbv beta iota.
  rewrite (o1_u8 D c (k + 1) (k + 2)) by lia. cbv beta iota.
  rewrite o1_lor8 by apply o1_byt_rng. reflexivity.
Qed.

(* op_frame's values, from the bytes of the cursor after the op byte *)
Definition o1_c1 (off n : Z) : fuzz_in := FuzzIn (off + 1) (n - 1).
Definition o1b (D : list byte) (off n i : Z) : Z := o1_byt D (o1_c1 off n) i.
Definition o1_c5 (off n : Z) : fuzz_in := o1_adv (o1_c1 off n) 8.
Definition o1_w (D : list byte) (off n : Z) : Z := o1b D off n 6 + o1b D off n 7 * 256.
Definition o1_len (w n5 : Z) : Z := if w mod 1485 <? n5 then w mod 1485 else n5.
Definition o1_di (b0 : Z) : Z := Z.land (Z.shiftr b0 5) 3.
Definition o1_si (b0 : Z) : Z := Z.land (Z.shiftr b0 3) 3.
Definition o1_ci (b0 : Z) : Z := Z.land b0 7 mod 7.
Definition o1_dst (b0 : Z) : list byte := nth (Z.to_nat (o1_di b0)) op_frame_DST [].
Definition o1_src (b0 : Z) : list byte := nth (Z.to_nat (o1_si b0)) op_frame_SRC [].
Definition o1_cmd (b0 : Z) : Z := nth (Z.to_nat (o1_ci b0)) op_frame_CMD 0.
Definition o1_ack (B : list byte) (b0 b3 b4 : Z) : Z := if Z.land b0 128 =? 0 then b3 + b4 * 256 else g_last_counter B.

Lemma o1_len_rng : forall w n5, 0 <= w -> 0 <= n5 -> 0 <= o1_len w n5 <= n5.
Proof.
  intros w n5 Hw Hn. unfold o1_len. pose proof (Z.mod_pos_bound w 1485 ltac:(lia)).
  destruct (Z.ltb_spec (w mod 1485) n5); lia.
Qed.

Lemma o1_match : forall (x y : option (list byte * unit)) (c6 : fuzz_in) (k : nat), x = y ->
  match match x with Some (B1, _) => Some (B1, c6) | None => None end with
  | Some (B1, c2) => Some (B1, (c2, S k))
  | None => None
  end =
  match y with Some (B1, _) => Some (B1, (c6, S k)) | None => None end.
Proof. intros x y c6 k ->. destruct y as [[B1 u]|]; reflexivity. Qed.

(* op 1 of the model as one build_and_receive_m (fuzz_transport.c:1175-1177, 1035-1050) *)
Lemma o1_model : forall I B A D off n k, 0 <= off -> 1 <= n ->
  snd (fuzz_u8_m D (FuzzIn off n)) mod 9 = 1 ->
  LLVMFuzzerTestOneInput_op_m I B A D (FuzzIn off n) k =
  match build_and_receive_m I B (A k) (o1_dst (o1b D off n 0)) (o1_src (o1b D off n 0))
          (o1b D off n 1 + o1b D off n 2 * 256) (o1_ack B (o1b D off n 0) (o1b D off n 3) (o1b D off n 4))
          (Z.land (o1b D off n 5) 3) (o1_cmd (o1b D off n 0))
          (sub D (fi_off (o1_c5 off n)) (Z.to_nat (o1_len (o1_w D off n) (fi_n (o1_c5 off n))))) with
  | Some (B1, _) =>
      Some (B1, (FuzzIn (fi_off (o1_c5 off n) + o1_len (o1_w D off n) (fi_n (o1_c5 off n)))
                        (fi_n (o1_c5 off n) - o1_len (o1_w D off n) (fi_n (o1_c5 off n))), S k))
  | None => None
  end.
Proof.
  intros I B A D off n k Ho Hn Hop.
  assert (E0 : fuzz_u8_m D (FuzzIn off n) = (FuzzIn (off + 1) (n - 1), at8 D (Z.to_nat off))).
  { unfold fuzz_u8_m. cbn [fi_off fi_n]. destruct (Z.eqb_spec n 0) as [E|E]; [lia | reflexivity]. }
  rewrite E0 in Hop. cbn [snd] in Hop.
  unfold LLVMFuzzerTestOneInput_op_m. rewrite E0. cbv beta iota zeta. rewrite Hop.
  change (1 =? 0) with false. change (1 =? 1) with true. cbv beta iota.
  unfold op_frame_m.
  assert (Hc1 : 0 <= fi_n (FuzzIn (off + 1) (n - 1))) by (cbn [fi_n]; lia).
  rewrite (o1_u8_0 D (FuzzIn (off + 1) (n - 1)) Hc1). cbv beta iota.
  rewrite (o1_u16 D (FuzzIn (off + 1) (n - 1)) 1 3 Hc1) by lia. cbv beta iota.
  rewrite (o1_u16 D (FuzzIn (off + 1) (n - 1)) 3 5 Hc1) by lia. cbv beta iota zeta.
  rewrite (o1_u8 D (FuzzIn (off + 1) (n - 1)) 5 6 Hc1) by lia. cbv beta iota.
  rewrite (o1_u16 D (FuzzIn (off + 1) (n - 1)) 6 8 Hc1) by lia. cbv beta iota.
  unfold fuzz_take_m. cbv beta iota zeta.
  apply o1_match. reflexivity.
Qed.

(* ---------------------------------------------------------------- memory: the input buffer *)

Lemma o1_sub1 : forall (D : list byte) k, (k < length D)%nat -> firstn 1 (skipn k D) = [nth k D (b8 0)].
Proof.
  induction D as [|d D IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma o1_rd1 : forall m data D k A, bytes_at rsegs m data D -> 0 <= k -> k < Z.of_nat (length D) ->
  A = data + k -> ov_read_bytes rsegs m (Z_to_bv 64 A) 1 = Some [nth (Z.to_nat k) D (b8 0)].
Proof.
  intros m data D k A HD Hk HkD ->.
  rewrite <- (o1_sub1 D (Z.to_nat k)) by lia.
  exact (bytes_at_read rsegs m data D k 1 HD Hk ltac:(lia)).
Qed.

Lemma o1_bsub : forall m a bs (k : Z) q addr, bytes_at rsegs m a bs -> 0 <= k -> (Z.to_nat k + q <= length bs)%nat ->
  addr = a + k -> bytes_at rsegs m addr (sub bs k q).
Proof.
  intros m a bs k q addr (Ha & Hl & Hb) Hk Hn ->.
  assert (LS : length (sub bs k q) = q) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi. rewrite ne_sub by lia.
  replace (i <? q)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (a + k + Z.of_nat i) with (a + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

(* ---------------------------------------------------------------- memory: the tables *)

(* the pointers of DST[4] (0x21f58) and SRC[4] (0x21f38), .data.rel.ro: HOST, SPEC_BCAST, OTHER, HOST and
   DESK, DESK2, HOST, NOTDD (0x10470 HOST, 0x10476 DESK, 0x1047c SPEC_BCAST, 0x1048c DESK2, 0x10492 NOTDD,
   0x10498 OTHER in .rodata) *)
Definition o1_dptr (di : Z) : Z :=
  if di =? 0 then 66672 else if di =? 1 then 66684 else if di =? 2 then 66712 else 66672.
Definition o1_sptr (si : Z) : Z :=
  if si =? 0 then 66678 else if si =? 1 then 66700 else if si =? 2 then 66672 else 66706.

Lemma o1_img_nth : forall n a bs i, image_bytes rsegs a n = Some bs -> (i < n)%nat ->
  seg_rom rsegs (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs i H Hi; cbn [image_bytes] in H; [lia|].
  destruct (seg_rom rsegs (wa a)) as [b|] eqn:E1; [|discriminate].
  destruct (image_bytes rsegs (a + 1) n) as [bs'|] eqn:E2; [|discriminate].
  injection H as <-. destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E1.
  - rewrite <- (IH (a + 1) bs' i E2 ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma o1_relro_rd : forall m a n bs bs', relro_img m ->
  RELRO_BASE <= a -> a + Z.of_nat n <= RELRO_BASE + RELRO_LEN ->
  image_bytes rsegs a n = Some bs -> map bv_unsigned bs = map bv_unsigned bs' ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) n = Some bs'.
Proof.
  intros m a n bs bs' RE H1 H2 HI HZ.
  apply bytes_eq_of_zs in HZ. subst bs'.
  pose proof (image_bytes_length rsegs n a bs HI) as LB.
  assert (HB : bytes_at rsegs m a bs).
  { unfold RELRO_BASE, RELRO_LEN in H1, H2. split; [lia|]. split; [rewrite LB; lia|].
    intros i Hi. rewrite <- (o1_img_nth n a bs i HI ltac:(lia)).
    replace (a + Z.of_nat i) with (RELRO_BASE + (a + Z.of_nat i - RELRO_BASE)) by (unfold RELRO_BASE; lia).
    apply RE. unfold RELRO_BASE, RELRO_LEN. lia. }
  pose proof (bytes_at_read rsegs m a bs 0 n HB ltac:(lia) ltac:(rewrite LB; lia)) as R.
  rewrite Z.add_0_r in R. change (Z.to_nat 0) with O in R. change (skipn O bs) with bs in R.
  replace (firstn n bs) with bs in R by (rewrite <- LB; symmetry; apply firstn_all). exact R.
Qed.

Ltac o1_relro RE a n :=
  let v := eval vm_compute in (image_bytes rsegs a n) in
  lazymatch v with
  | Some ?bs =>
      apply (o1_relro_rd _ a n bs _ RE);
      [ apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity ]
  end.

Lemma o1_di_rng : forall b0, 0 <= o1_di b0 < 4.
Proof.
  intros b0. unfold o1_di. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma o1_si_rng : forall b0, 0 <= o1_si b0 < 4.
Proof.
  intros b0. unfold o1_si. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma o1_ci_rng : forall b0, 0 <= o1_ci b0 < 7.
Proof. intros b0. unfold o1_ci. apply Z.mod_pos_bound. lia. Qed.

Lemma o1_dst_rd : forall m b0, relro_img m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (139096 + 8 * o1_di b0)) 8 = Some (le8 (Z_to_bv 64 (o1_dptr (o1_di b0)))).
Proof.
  intros m b0 RE. pose proof (o1_di_rng b0) as R. revert R. generalize (o1_di b0). intros di R.
  assert (Hc : di = 0 \/ di = 1 \/ di = 2 \/ di = 3) by lia.
  destruct Hc as [->|[->|[->| ->]]].
  - o1_relro RE (139096 + 8 * 0) 8%nat.
  - o1_relro RE (139096 + 8 * 1) 8%nat.
  - o1_relro RE (139096 + 8 * 2) 8%nat.
  - o1_relro RE (139096 + 8 * 3) 8%nat.
Qed.

Lemma o1_src_rd : forall m b0, relro_img m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (139064 + 8 * o1_si b0)) 8 = Some (le8 (Z_to_bv 64 (o1_sptr (o1_si b0)))).
Proof.
  intros m b0 RE. pose proof (o1_si_rng b0) as R. revert R. generalize (o1_si b0). intros si R.
  assert (Hc : si = 0 \/ si = 1 \/ si = 2 \/ si = 3) by lia.
  destruct Hc as [->|[->|[->| ->]]].
  - o1_relro RE (139064 + 8 * 0) 8%nat.
  - o1_relro RE (139064 + 8 * 1) 8%nat.
  - o1_relro RE (139064 + 8 * 2) 8%nat.
  - o1_relro RE (139064 + 8 * 3) 8%nat.
Qed.

Lemma o1_ro_rd : forall m a bs, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_bytes_b rsegs a bs = true -> ov_read_bytes rsegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m a bs MI H1 H2 HR.
  pose proof (ro_bytes_at rsegs m a bs MI H1 H2 (ro_bytes_b_sound rsegs bs a HR)) as HB.
  pose proof (bytes_at_read rsegs m a bs 0 (length bs) HB ltac:(lia) ltac:(lia)) as R.
  rewrite Z.add_0_r in R. change (Z.to_nat 0) with O in R. change (skipn O bs) with bs in R.
  rewrite firstn_all in R. exact R.
Qed.

Lemma o1_cmd_rd : forall m b0, mem_inv rsegs m ->
  ov_read_bytes rsegs m (Z_to_bv 64 (66693 + o1_ci b0)) 1 = Some [b8 (o1_cmd b0)].
Proof.
  intros m b0 MI. unfold o1_cmd. pose proof (o1_ci_rng b0) as R. revert R. generalize (o1_ci b0). intros ci R.
  assert (Hc : ci = 0 \/ ci = 1 \/ ci = 2 \/ ci = 3 \/ ci = 4 \/ ci = 5 \/ ci = 6) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]];
    (apply (o1_ro_rd m _ [_]);
     [exact MI | apply Z.leb_le; vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity
     | vm_compute; reflexivity]).
Qed.

Lemma o1_cmd_rng : forall b0, 0 <= o1_cmd b0 < 256.
Proof.
  intros b0. unfold o1_cmd. pose proof (o1_ci_rng b0) as R. revert R. generalize (o1_ci b0). intros ci R.
  assert (Hc : ci = 0 \/ ci = 1 \/ ci = 2 \/ ci = 3 \/ ci = 4 \/ ci = 5 \/ ci = 6) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]];
    (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
Qed.

Lemma o1_mac : forall m p mac, mem_inv rsegs m -> length mac = 6%nat -> 0 <= p -> p + 6 <= 2 ^ 64 ->
  ro_bytes_b rsegs p mac = true -> lh_mac_at m p mac.
Proof.
  intros m p mac MI L H1 H2 HR. unfold lh_mac_at.
  pose proof (ro_bytes_b_sound rsegs mac p HR) as RB.
  split; [exact L|]. split; [exact H1|]. split; [exact H2|]. split.
  - apply ro_bytes_at; [exact MI | exact H1 | rewrite L; change (Z.of_nat 6) with 6; lia | exact RB].
  - intros i Hi. destruct (nth_error mac (Z.to_nat i)) as [b|] eqn:E.
    + destruct (ro_bytes_nth rsegs mac p (Z.to_nat i) b RB E) as [_ R].
      rewrite Z2Nat.id in R by lia. exact R.
    + apply nth_error_None in E. rewrite L in E. lia.
Qed.

Lemma o1_dst_mac : forall m b0, mem_inv rsegs m -> lh_mac_at m (o1_dptr (o1_di b0)) (o1_dst b0).
Proof.
  intros m b0 MI. unfold o1_dst. pose proof (o1_di_rng b0) as R. revert R. generalize (o1_di b0). intros di R.
  assert (Hc : di = 0 \/ di = 1 \/ di = 2 \/ di = 3) by lia.
  destruct Hc as [->|[->|[->| ->]]];
    (apply o1_mac; [exact MI | reflexivity | apply Z.leb_le; vm_compute; reflexivity
                   | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity]).
Qed.

Lemma o1_src_mac : forall m b0, mem_inv rsegs m -> lh_mac_at m (o1_sptr (o1_si b0)) (o1_src b0).
Proof.
  intros m b0 MI. unfold o1_src. pose proof (o1_si_rng b0) as R. revert R. generalize (o1_si b0). intros si R.
  assert (Hc : si = 0 \/ si = 1 \/ si = 2 \/ si = 3) by lia.
  destruct Hc as [->|[->|[->| ->]]];
    (apply o1_mac; [exact MI | reflexivity | apply Z.leb_le; vm_compute; reflexivity
                   | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity]).
Qed.

(* ---------------------------------------------------------------- the state at build_and_receive's entry *)

(* op_frame's arguments from its bytes b0 .. b5, w = the u16 of b6, b7, and the cursor (off5, n5) after the eight
   reads (U/Prog/T/LLVMFuzzerTestOneInput_lh.v llvm_at_bar, rret = 0x13db0) *)
Definition o1_post (data : Z) (D : list byte) (regs0 : bvmap 5 word) (m0 : word -> option byte) (Sp lo ops : Z)
    (B : list byte) (off b0 b1 b2 b3 b4 b5 w off5 n5 : Z) (F : bvmap 5 word) (fc : bv 32)
    (ms : machine_state) : Prop :=
  llvm_at_bar data D regs0 m0 Sp lo ops B LH_RET_BAR1
    (Z_to_bv 64 (data + off5 + o1_len w n5)) (Z_to_bv 64 0x39) (Z_to_bv 64 (data + off5)) (Z_to_bv 64 7)
    (Z_to_bv 64 (data + off)) (Z_to_bv 64 (n5 - o1_len w n5)) (Z_to_bv 64 n5)
    (o1_dptr (o1_di b0)) (o1_sptr (o1_si b0)) (data + off5)
    (o1_dst b0) (o1_src b0) (sub D off5 (Z.to_nat (o1_len w n5)))
    (b1 + b2 * 256) (o1_ack B b0 b3 b4) (Z.land b5 3) (o1_cmd b0) F fc ms.

Section CTX.
Context (data : Z) (D : list byte) (regs0 : bvmap 5 word).

(* what every segment of the walk keeps *)
Definition o1_ctx (m0 : word -> option byte) (Sp lo ops : Z) (B : list byte) (m : word -> option byte)
    (j10 jio j60 : list byte) (b0 b1 b2 b3 b4 b5 off5 n5 : Z) : Prop :=
  0 <= ops < OPS_MAX /\ 0 <= off5 /\ 0 <= n5 /\ off5 + n5 <= Z.of_nat (length D) /\
  0 <= b0 < 256 /\ 0 <= b1 < 256 /\ 0 <= b2 < 256 /\ 0 <= b3 < 256 /\ 0 <= b4 < 256 /\ 0 <= b5 < 256 /\
  llvm_mem data D regs0 m0 Sp lo B m j10 jio j60.

End CTX.
