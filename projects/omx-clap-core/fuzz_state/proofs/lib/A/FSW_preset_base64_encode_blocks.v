(* preset_base64_encode 0x84390 (preset_file.c:577-608), the MODEL half of the walk: what the instructions compute,
   as plain arithmetic over Z and over fs's released model lib/Prog/WriterSpec.v (b64c, b64_enc, b64_table). No image,
   no ASan kit: every lemma here is a fact about the numbers the walk's symbolic values denote, so the walk file
   (lib/A/FSW_preset_base64_encode.v) only has to bring the engine's output into these shapes.

   The instruction words behind each lemma (fs.asan, capstone):
     0x843bc..0x843d0  addi a2,s0,2; mulhu a0,a2,a1; slli a0,a0,1; andi a0,a0,-4; addi a0,a0,1   -> enc_size len
                       (a1 = the .rodata word 0x10320 = 0xaaaaaaaaaaaaaaab = ENC_MAGIC)
     0x84440           srli a3,t0,2                                                              -> b0 / 4
     0x84470..0x84484  slli t0,t0,0x10; slli t1,t1,8; or a3,t1,t0; slli a3,a3,0x2e; srli a2,a3,0x3a
                                                                                                 -> (b0 mod 4) * 16 + b1 / 16
     0x844b4..0x844c0  or a3,t1,a7; slli a3,a3,0x34; srli a2,a3,0x3a                             -> (b1 mod 16) * 4 + b2 / 64
     0x844f4           andi a2,a7,0x3f                                                           -> b2 mod 64
     0x84624..0x84630  slli a3,a3,0x10; srli a7,a3,0x12                                          -> bA / 4  (tail)
     0x846a0..0x846a4  srli a5,a5,6; andi a2,a5,0x3c                                             -> (bB mod 16) * 4 (tail)
   The four values of a round are exactly WriterSpec.b64_enc's four indices (WriterSpec.v:64-72).

   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0, read from a file, not a pipe):
   preset_base64_encode has RELEASED proofs for fs's PLAIN and UBSAN builds only (lib/Prog, lib/U/Prog,
   ossv/recipes@566eb6ffa5, release/pau-projects-recipes@b6a0088adc), none for an ASan build; the plain contract
   lib/Prog/preset_base64_encode_c.v:35 is the template for the functional content, not a drop-in. Lemma names
   (git grep -w over the four released refs, under proofs/): enc_mulhu, enc_ix1, enc_ix2, enc_ix3, b64_enc_app,
   b64_enc_len, b64_list_nth: no hit. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the .rodata word at 0x10320, the compiler's reciprocal of 3 *)
Definition ENC_MAGIC : Z := 12297829382473034411.

(* ---- brute force over one and two bytes: every lemma below about single bytes is a statement about at most
   256 * 256 cases, and the engine's shapes (Z.shiftl / Z.shiftr / Z.lor / Z.land under the 64-bit wrap) are
   decided by computation, not by bit reasoning ---- *)
Definition zseq256 : list Z := map Z.of_nat (seq 0 256).
Lemma in_zseq256 : forall x, 0 <= x < 256 -> In x zseq256.
Proof.
intros x Hx. unfold zseq256. apply in_map_iff. exists (Z.to_nat x).
split; [lia|]. apply in_seq. lia.
Qed.
Lemma brute1_lemma : forall (f g : Z -> Z),
  forallb (fun x => f x =? g x) zseq256 = true -> forall x, 0 <= x < 256 -> f x = g x.
Proof.
intros f g H x Hx. apply Z.eqb_eq.
exact (proj1 (forallb_forall _ _) H x (in_zseq256 x Hx)).
Qed.
Lemma brute2_lemma : forall (f g : Z -> Z -> Z),
  forallb (fun x => forallb (fun y => f x y =? g x y) zseq256) zseq256 = true ->
  forall x y, 0 <= x < 256 -> 0 <= y < 256 -> f x y = g x y.
Proof.
intros f g H x y Hx Hy. apply Z.eqb_eq.
exact (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) H x (in_zseq256 x Hx)) y (in_zseq256 y Hy)).
Qed.
Ltac brute1 x :=
  lazymatch goal with |- ?L = ?R =>
    let f := eval pattern x in L in
    let g := eval pattern x in R in
    lazymatch f with ?F _ => lazymatch g with ?G _ =>
      exact (brute1_lemma F G ltac:(vm_compute; reflexivity) x ltac:(lia)) end end end.
Ltac brute2 x y :=
  lazymatch goal with |- ?L = ?R =>
    let f := eval pattern x, y in L in
    let g := eval pattern x, y in R in
    lazymatch f with ?F _ _ => lazymatch g with ?G _ _ =>
      exact (brute2_lemma F G ltac:(vm_compute; reflexivity) x y ltac:(lia) ltac:(lia)) end end end.

(* ---- the size: mulhu by ENC_MAGIC, doubled, with the low two bits cleared, plus one ---- *)
Lemma land_m4 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 4) = 4 * (x / 4).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 4 = Z.ldiff (Z.ones 64) (Z.ones 2)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia.
Qed.

Lemma enc_mulhu : forall x, 0 <= x <= 2 ^ 28 -> Z.shiftr (x * ENC_MAGIC) 64 = 2 * x / 3.
Proof.
intros x Hx. rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.div_mod x 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 3 ltac:(lia)) as Hmb.
assert (Hk : 0 <= x / 3 <= 2 ^ 28) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
set (k := x / 3) in *.
assert (HR : x mod 3 = 0 \/ x mod 3 = 1 \/ x mod 3 = 2) by lia.
unfold ENC_MAGIC.
destruct HR as [E0 | [E1 | E2]].
- replace x with (3 * k) by lia.
  replace (2 * (3 * k)) with (2 * k * 3) by lia. rewrite Z.div_mul by lia.
  replace (3 * k * 12297829382473034411) with (2 * k * 2 ^ 64 + k) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small k) by lia. lia.
- replace x with (3 * k + 1) by lia.
  replace (2 * (3 * k + 1)) with (2 * k * 3 + 2) by lia. rewrite Z.div_add_l by lia.
  replace ((3 * k + 1) * 12297829382473034411) with (2 * k * 2 ^ 64 + (k + 12297829382473034411)) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (k + 12297829382473034411)) by lia.
  replace (2 / 3) with 0 by reflexivity. lia.
- replace x with (3 * k + 2) by lia.
  replace (2 * (3 * k + 2)) with ((2 * k + 1) * 3 + 1) by lia. rewrite Z.div_add_l by lia.
  replace ((3 * k + 2) * 12297829382473034411)
    with ((2 * k + 1) * 2 ^ 64 + (k + 6148914691236517206)) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (k + 6148914691236517206)) by lia.
  replace (1 / 3) with 0 by reflexivity. lia.
Qed.

(* the doubled quotient with its low two bits cleared, divided by four, is (len + 2) / 3: the step from the
   machine's `slli a0,a0,1; andi a0,a0,-4` to enc_size *)
Lemma enc_q4 : forall len, 0 <= len -> 2 * (len + 2) / 3 * 2 / 4 = (len + 2) / 3.
Proof.
intros len Hlen.
pose proof (Z.div_mod (len + 2) 3 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (len + 2) 3 ltac:(lia)) as M.
set (q := (len + 2) / 3) in *. set (r := (len + 2) mod 3) in *.
assert (HA : 2 * (len + 2) / 3 = 2 * q + 2 * r / 3).
{ replace (2 * (len + 2)) with (2 * q * 3 + 2 * r) by lia. rewrite Z.div_add_l by lia. reflexivity. }
rewrite HA.
assert (Hr2 : 2 * r / 3 = 0 \/ 2 * r / 3 = 1)
  by (assert (r = 0 \/ r = 1 \/ r = 2) as [-> | [-> | ->]] by lia; cbn; auto).
destruct Hr2 as [-> | ->].
- replace ((2 * q + 0) * 2) with (q * 4 + 0) by lia. rewrite Z.div_add_l by lia.
  replace (0 / 4) with 0 by reflexivity. lia.
- replace ((2 * q + 1) * 2) with (q * 4 + 2) by lia. rewrite Z.div_add_l by lia.
  replace (2 / 4) with 0 by reflexivity. lia.
Qed.

(* enc_size len = (len + 2) / 3 * 4 + 1 is what the five instructions leave in a0 *)
Lemma enc_machine : forall len, 0 <= len <= 2 ^ 27 ->
  Z.land (Z.shiftl (Z.shiftr ((len + 2) * ENC_MAGIC) 64) 1 mod 2 ^ 64) (2 ^ 64 - 4) + 1
  = (len + 2) / 3 * 4 + 1.
Proof.
intros len Hlen.
rewrite (enc_mulhu (len + 2) ltac:(lia)).
assert (Hq : 0 <= 2 * (len + 2) / 3 <= 2 ^ 28) by
  (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (Z.mod_small (2 * (len + 2) / 3 * 2)) by lia.
rewrite land_m4 by lia. rewrite (enc_q4 len ltac:(lia)). lia.
Qed.

(* ---- the four six-bit indices of one 3-byte round ---- *)
Lemma enc_ix0 : forall b0, 0 <= b0 < 256 -> Z.shiftr b0 2 = b0 / 4.
Proof. intros b0 Hb. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma enc_or1 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.lor (Z.shiftl b1 8 mod 2 ^ 64) (Z.shiftl b0 16 mod 2 ^ 64) = b0 * 65536 + b1 * 256.
Proof. intros b0 b1 H0 H1. brute2 b0 b1. Qed.

Lemma enc_ix1 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.shiftr (Z.shiftl (b0 * 65536 + b1 * 256) 46 mod 2 ^ 64) 58 = (b0 mod 4) * 16 + b1 / 16.
Proof. intros b0 b1 H0 H1. brute2 b0 b1. Qed.

Lemma enc_or2 : forall b1 b2, 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Z.lor (Z.shiftl b1 8 mod 2 ^ 64) b2 = b1 * 256 + b2.
Proof. intros b1 b2 H1 H2. brute2 b1 b2. Qed.

Lemma enc_ix2 : forall b1 b2, 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  Z.shiftr (Z.shiftl (b1 * 256 + b2) 52 mod 2 ^ 64) 58 = (b1 mod 16) * 4 + b2 / 64.
Proof. intros b1 b2 H1 H2. brute2 b1 b2. Qed.

Lemma enc_ix3 : forall b2, 0 <= b2 < 256 -> Z.land b2 63 = b2 mod 64.
Proof. intros b2 H2. brute1 b2. Qed.

(* ---- the tail's two indices ---- *)
Lemma enc_t0 : forall b, 0 <= b < 256 -> Z.shiftr (Z.shiftl b 16 mod 2 ^ 64) 18 = b / 4.
Proof. intros b Hb. brute1 b. Qed.

Lemma enc_t2 : forall b, 0 <= b < 256 ->
  Z.land (Z.shiftr (Z.shiftl b 8 mod 2 ^ 64) 6) 60 = (b mod 16) * 4.
Proof. intros b Hb. brute1 b. Qed.

(* the tail's second index with one byte only: b1 = 0 gives (b0 mod 4) * 16 *)
Lemma enc_t1_one : forall b, 0 <= b < 256 ->
  Z.shiftr (Z.shiftl (b * 65536) 46 mod 2 ^ 64) 58 = (b mod 4) * 16.
Proof. intros b Hb. brute1 b. Qed.

(* ---- the six-bit indices are in range, and the table byte of each ---- *)
Lemma enc_ix_range : forall b0 b1 b2, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  0 <= b0 / 4 < 64 /\ 0 <= (b0 mod 4) * 16 + b1 / 16 < 64 /\
  0 <= (b1 mod 16) * 4 + b2 / 64 < 64 /\ 0 <= b2 mod 64 < 64.
Proof.
intros b0 b1 b2 H0 H1 H2.
pose proof (Z.mod_pos_bound b0 4 ltac:(lia)). pose proof (Z.mod_pos_bound b1 16 ltac:(lia)).
pose proof (Z.mod_pos_bound b2 64 ltac:(lia)).
assert (0 <= b0 / 4 < 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (0 <= b1 / 16 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (0 <= b2 / 64 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
lia.
Qed.

Lemma b64c_range : forall v, 0 <= v < 64 -> 0 <= WriterSpec.b64c v < 256.
Proof.
intros v Hv. unfold WriterSpec.b64c.
destruct (v <? 26) eqn:E1; [apply Z.ltb_lt in E1; lia|apply Z.ltb_ge in E1].
destruct (v <? 52) eqn:E2; [apply Z.ltb_lt in E2; lia|apply Z.ltb_ge in E2].
destruct (v <? 62) eqn:E3; [apply Z.ltb_lt in E3; lia|apply Z.ltb_ge in E3].
destruct (v =? 62) eqn:E4; [lia|]. lia.
Qed.

(* the 64 letters as FSH_Rt.FS_RO_STRS lists them at G_B64 (0x21060): the image byte at G_B64 + v is b64c v *)
Lemma b64_list_nth : forall v, 0 <= v < 64 ->
  nth (Z.to_nat v) (map WriterSpec.b64c (map Z.of_nat (seq 0 64))) 0 = WriterSpec.b64c v.
Proof.
intros v Hv.
assert (C : forallb (fun i => nth i (map WriterSpec.b64c (map Z.of_nat (seq 0 64))) 0
                              =? WriterSpec.b64c (Z.of_nat i)) (seq 0 64) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) C (Z.to_nat v) (proj2 (in_seq 64 0 (Z.to_nat v)) ltac:(lia))) as H.
apply Z.eqb_eq in H. rewrite H. f_equal. lia.
Qed.
Lemma b64_list_length : length (map WriterSpec.b64c (map Z.of_nat (seq 0 64))) = 64%nat.
Proof. reflexivity. Qed.

(* ---- b64_enc: one round appends four letters, and the encoding of a prefix is a prefix ---- *)
Lemma b64_enc_3 : forall b0 b1 b2 rest,
  WriterSpec.b64_enc (b0 :: b1 :: b2 :: rest)
  = [WriterSpec.b64c (b0 / 4); WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16);
     WriterSpec.b64c ((b1 mod 16) * 4 + b2 / 64); WriterSpec.b64c (b2 mod 64)]
    ++ WriterSpec.b64_enc rest.
Proof. intros. reflexivity. Qed.

Lemma b64_enc_app : forall n l1 l2, length l1 = (3 * n)%nat ->
  WriterSpec.b64_enc (l1 ++ l2) = WriterSpec.b64_enc l1 ++ WriterSpec.b64_enc l2.
Proof.
induction n as [|n IH]; intros l1 l2 H.
- destruct l1; [reflexivity | cbn in H; lia].
- destruct l1 as [|b0 [|b1 [|b2 r]]]; cbn in H; try lia.
  cbn [app]. rewrite !b64_enc_3. rewrite (IH r l2 ltac:(cbn in H; lia)).
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma b64_enc_len : forall l,
  Z.of_nat (length (WriterSpec.b64_enc l)) = 4 * ((Z.of_nat (length l) + 2) / 3).
Proof.
assert (G : forall n l, (length l <= n)%nat ->
  Z.of_nat (length (WriterSpec.b64_enc l)) = 4 * ((Z.of_nat (length l) + 2) / 3)).
{ induction n as [|n IH]; intros l H.
  - destruct l; [reflexivity | cbn in H; lia].
  - destruct l as [|b0 [|b1 [|b2 r]]]; cbn in H.
    + reflexivity.
    + cbn; reflexivity.
    + cbn; reflexivity.
    + rewrite b64_enc_3, length_app, Nat2Z.inj_add, (IH r ltac:(cbn in H; lia)).
      replace (Z.of_nat (length (b0 :: b1 :: b2 :: r)) + 2) with (Z.of_nat (length r) + 2 + 1 * 3)
        by (cbn [length]; lia).
      rewrite Z.div_add by lia. cbn [length]. lia. }
intros l. exact (G (length l) l ltac:(lia)).
Qed.

(* every byte b64_enc writes is a byte *)
Lemma b64_enc_bytes : forall l, WriterSpec.bytes_ok l -> WriterSpec.bytes_ok (WriterSpec.b64_enc l).
Proof.
assert (G : forall n l, (length l <= n)%nat -> WriterSpec.bytes_ok l ->
  WriterSpec.bytes_ok (WriterSpec.b64_enc l)).
{ induction n as [|n IH]; intros l Hn Hok.
  - destruct l; [constructor | cbn in Hn; lia].
  - destruct l as [|b0 [|b1 [|b2 r]]]; cbn in Hn.
    + constructor.
    + inversion Hok as [|? ? Hb0 _]; subst.
      pose proof (Z.mod_pos_bound b0 4 ltac:(lia)).
      assert (0 <= b0 / 4 < 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      cbn [WriterSpec.b64_enc]. repeat constructor;
        try (apply b64c_range; lia); lia.
    + inversion Hok as [|? ? Hb0 Hr]; subst. inversion Hr as [|? ? Hb1 _]; subst.
      pose proof (Z.mod_pos_bound b0 4 ltac:(lia)). pose proof (Z.mod_pos_bound b1 16 ltac:(lia)).
      assert (0 <= b0 / 4 < 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      assert (0 <= b1 / 16 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      cbn [WriterSpec.b64_enc]. repeat constructor; try (apply b64c_range; lia); lia.
    + inversion Hok as [|? ? Hb0 Hr]; subst. inversion Hr as [|? ? Hb1 Hr2]; subst.
      inversion Hr2 as [|? ? Hb2 Hr3]; subst.
      destruct (enc_ix_range b0 b1 b2 Hb0 Hb1 Hb2) as (R0 & R1 & R2 & R3).
      rewrite b64_enc_3. apply Forall_app. split.
      * repeat constructor; apply b64c_range; lia.
      * exact (IH r ltac:(cbn in Hn; lia) Hr3). }
intros l Hok. exact (G (length l) l ltac:(lia) Hok).
Qed.
