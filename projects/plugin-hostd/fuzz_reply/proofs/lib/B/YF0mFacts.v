(* YF0mFacts.v - three start-up facts about plugin-hostd/fuzz_reply's asan-ubsan instance, each decided by vm_compute against
   the generated tables of lib/B/YF0m.v (TFIB_ERRNO, Tfib_owned_static, Tfib_const_abs) and the image's segments
   (lib/B/YB1h.v TSEGS). Each is stated for every B with TfibSyms B, the form the walk lanes take as a hypothesis.
   (1) tfib_errno_not_owned_static : the errno word is outside Tfib_owned_static - exactly W5's Section hypothesis HEO
       (A/W_relay_add.v), which its errno_not_aowned consumes.
   (2) tfib_errno_align4 : the errno word is 4-aligned - the ALIGN4 traps on the errno pointer (a Theorem Labs lane's HERRAL).
   (3) tfib_rom_owned_pinned : every byte of Tfib_owned_static that lies in a read-only segment of the image is pinned
       by a Tfib_const_abs cell whose literal byte equals the image byte there (408 bytes: tfib_rom_owned_counts).
   (4) tfib_wake1_in_img / (5) tfib_wake1_not_owned_static : g_wake[1] is an image byte off the owned statics -
       W5's HWKI / HWKO (A/W_relay_add.v).
   (6) tfib_lit_end5_in_rom / (7) tfib_lit_end5_not_owned_static : the literal " end\0" (.str.4) is read-only image
       bytes off the owned statics - a Theorem Labs lane / W4Gesture-2. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m YB1h.
Import ListNotations.
Open Scope Z_scope.

(** (1) errno is not owned-static. *)
Definition tfib_owned_b (x : Z) : bool :=
  existsb (fun r : Z * Z => ((fst r <=? x) && (x <? fst r + snd r))%bool) Tfib_owned_static.
Lemma tfib_errno_owned_b : forallb (fun i => negb (tfib_owned_b (TFIB_ERRNO + i))) [0; 1; 2; 3] = true.
Proof. vm_compute. reflexivity. Qed.
Theorem tfib_errno_not_owned_static : forall B : asyms, TfibSyms B ->
  forall i, 0 <= i < 4 -> ~ Exists (in_zr (as_errno B + i)) (as_owned_static B).
Proof.
intros B HB i Hi. rewrite (ts_errno B HB), (ts_owned B HB). intros HE.
apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (Hl : In i [0; 1; 2; 3]).
{ assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia. destruct Hc as [E|[E|[E|E]]]; subst i; cbn; tauto. }
pose proof (proj1 (forallb_forall _ _) tfib_errno_owned_b i Hl) as Hf. cbn beta in Hf.
apply negb_true_iff in Hf. unfold tfib_owned_b in Hf.
assert (Ht : existsb (fun r : Z * Z => ((fst r <=? TFIB_ERRNO + i) && (TFIB_ERRNO + i <? fst r + snd r))%bool)
               Tfib_owned_static = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.

(** (2) errno is 4-aligned. *)
Theorem tfib_errno_align4 : forall B : asyms, TfibSyms B -> as_errno B mod 4 = 0.
Proof. intros B HB. rewrite (ts_errno B HB). vm_compute. reflexivity. Qed.

(** (3) the owned read-only bytes are pinned by const cells equal to the image bytes. *)
(* the literal (address, width, value) of a cell written z1/z2/z4/z8 (ANum a) v *)
Definition tfib_cell_lit (c : acell) : option (Z * Z * Z) :=
  match c_at c, c_val c with
  | ANum a, AV (ANum v) => Some (a, Z.of_nat (c_w c), v)
  | _, _ => None
  end.
(* the little-endian byte a literal cell states at address x, if it covers x *)
Definition tfib_cell_byte (c : acell) (x : Z) : option Z :=
  match tfib_cell_lit c with
  | Some (a, w, v) => if ((a <=? x) && (x <? a + w))%bool then Some (Z.land (Z.shiftr v (8 * (x - a))) 255) else None
  | None => None
  end.
(* the image byte, exactly rom_view's right-hand side *)
Definition tfib_img_byte (x : Z) : option Z := option_map (fun b : byte => bv_unsigned b) (seg_rom TSEGS (Z_to_bv 64 x)).
Definition tfib_pinned_b (x : Z) : bool :=
  existsb (fun c => match tfib_cell_byte c x, tfib_img_byte x with Some u, Some v => Z.eqb u v | _, _ => false end)
    Tfib_const_abs.
(* the read-only segments of the image, as (base, size) *)
Definition tfib_ro_bounds : list (Z * Z) :=
  map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_size sg))) (List.filter (fun sg => negb (seg_writable sg)) TSEGS).
Definition tfib_zclip (r b : Z * Z) : Z * Z :=
  (Z.max (fst r) (fst b), Z.min (fst r + snd r) (fst b + snd b) - Z.max (fst r) (fst b)).
Definition tfib_zseq (r : Z * Z) : list Z := map (fun k => fst r + Z.of_nat k) (seq 0 (Z.to_nat (snd r))).
Definition tfib_rom_owned_bytes : list Z :=
  flat_map (fun r => flat_map (fun b => tfib_zseq (tfib_zclip r b)) tfib_ro_bounds) Tfib_owned_static.
Lemma tfib_rom_pin_check : forallb tfib_pinned_b tfib_rom_owned_bytes = true.
Proof. vm_compute. reflexivity. Qed.
(* the counts the header of YF0m.v states: 19 owned ranges inside the read-only segments, 408 bytes *)
Example tfib_rom_owned_counts :
  (length (List.filter (fun r => existsb (fun b => 0 <? snd (tfib_zclip r b)) tfib_ro_bounds) Tfib_owned_static),
   length tfib_rom_owned_bytes) = (19%nat, 408%nat).
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_in_zseq : forall r x, fst r <= x < fst r + snd r -> In x (tfib_zseq r).
Proof.
intros r x Hx. unfold tfib_zseq. apply in_map_iff. exists (Z.to_nat (x - fst r)). split.
- rewrite Z2Nat.id by lia. lia.
- apply in_seq. split; [lia|]. apply Nat.lt_le_trans with (m := Z.to_nat (snd r)); [apply Z2Nat.inj_lt; lia | lia].
Qed.
Theorem tfib_rom_owned_pinned : forall a, in_rom TSEGS a -> Exists (in_zr a) Tfib_owned_static ->
  exists c, In c Tfib_const_abs /\ tfib_cell_byte c a <> None /\ tfib_cell_byte c a = tfib_img_byte a.
Proof.
intros a (sg & Hsg & Hw & Ha) Hown. apply Exists_exists in Hown as (r & Hr & Hz). unfold in_zr in Hz.
set (b := (Z.of_N (seg_base sg), Z.of_N (seg_size sg))).
assert (Hb : In b tfib_ro_bounds).
{ unfold tfib_ro_bounds. apply in_map_iff. exists sg. split; [reflexivity|]. apply List.filter_In. split; [exact Hsg|]. rewrite Hw. reflexivity. }
assert (Hin : In a tfib_rom_owned_bytes).
{ unfold tfib_rom_owned_bytes. apply in_flat_map. exists r. split; [exact Hr|]. apply in_flat_map. exists b. split; [exact Hb|].
  apply tfib_in_zseq. unfold tfib_zclip, b. cbn [fst snd]. lia. }
pose proof (proj1 (forallb_forall _ _) tfib_rom_pin_check a Hin) as Hp. unfold tfib_pinned_b in Hp.
apply existsb_exists in Hp as (c & Hc & Hm). exists c. split; [exact Hc|].
destruct (tfib_cell_byte c a) as [u|] eqn:Eu; [|discriminate]. destruct (tfib_img_byte a) as [v|] eqn:Ev; [|discriminate].
apply Z.eqb_eq in Hm. subst v. split; [discriminate | reflexivity].
Qed.

(** (4)-(5) g_wake[1] (bytes g_wake + 4 .. + 7) is an image byte off the owned statics - W5's HWKI / HWKO
    (A/W_relay_add.v), for relay_add's read across the fake-frame seat. g_wake is read from THIS image's own
    asan_globals descriptor cell in Tfib_const_abs (tfib_g_wake_in_table), never by offset from the other image. *)
Definition tfib_g_wake : Z := 0xa2520.
Example tfib_g_wake_in_table :
  existsb (fun c => match tfib_cell_lit c with
                    | Some (a, w, v) => ((a =? 0xa2a60) && (w =? 8) && (v =? tfib_g_wake))%bool
                    | None => false end) Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.
Definition tfib_in_img_b (x : Z) : bool :=
  existsb (fun sg => ((Z.of_N (seg_base sg) <=? x) && (x <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) TSEGS.
Lemma tfib_wake1_b :
  forallb (fun i => (tfib_in_img_b (tfib_g_wake + 4 + i) && negb (tfib_owned_b (tfib_g_wake + 4 + i)))%bool) [0; 1; 2; 3] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_wake1_i : forall i, 0 <= i < 4 ->
  tfib_in_img_b (tfib_g_wake + 4 + i) = true /\ tfib_owned_b (tfib_g_wake + 4 + i) = false.
Proof.
intros i Hi. assert (Hl : In i [0; 1; 2; 3]).
{ assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia. destruct Hc as [E|[E|[E|E]]]; subst i; cbn; tauto. }
pose proof (proj1 (forallb_forall _ _) tfib_wake1_b i Hl) as H. cbn beta in H.
apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H2. split; assumption.
Qed.
Theorem tfib_wake1_in_img : forall w, w = tfib_g_wake -> forall i, 0 <= i < 4 -> in_img TSEGS (w + 4 + i).
Proof.
intros w -> i Hi. destruct (tfib_wake1_i i Hi) as [H _]. unfold tfib_in_img_b in H.
apply existsb_exists in H as (sg & Hsg & Hb). apply andb_true_iff in Hb as [H1 H2].
exists sg. split; [exact Hsg|]. split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.
Theorem tfib_wake1_not_owned_static : forall B : asyms, TfibSyms B ->
  forall w, w = tfib_g_wake -> forall i, 0 <= i < 4 -> ~ Exists (in_zr (w + 4 + i)) (as_owned_static B).
Proof.
intros B HB w -> i Hi. rewrite (ts_owned B HB). intros HE. destruct (tfib_wake1_i i Hi) as [_ Hf].
apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz. unfold tfib_owned_b in Hf.
assert (Ht : existsb (fun r : Z * Z => ((fst r <=? tfib_g_wake + 4 + i) && (tfib_g_wake + 4 + i <? fst r + snd r))%bool)
               Tfib_owned_static = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.

(** (6)-(7) the literal " end\0" (A_OBJ 28 on this image B - A_OBJ 31 is image A's index - .str.4) is a read-only image range off the owned statics - a Theorem Labs lane /
    W4Gesture-2. Its own redzone at +5 IS an owned static and the owned range before it ends exactly at its start, so
    this is checked, not assumed. The address is read from THIS image's own asan_globals descriptor
    (tfib_lit_end5_in_table: beg cell and size cell = 5). *)
Definition tfib_lit_end5 : Z := 0x20f00.
Example tfib_lit_end5_in_table :
  (existsb (fun c => match tfib_cell_lit c with
                     | Some (a, w, v) => ((a =? 0xa2920) && (w =? 8) && (v =? tfib_lit_end5))%bool
                     | None => false end) Tfib_const_abs &&
   existsb (fun c => match tfib_cell_lit c with
                     | Some (a, w, v) => ((a =? 0xa2920 + 8) && (w =? 8) && (v =? 5))%bool
                     | None => false end) Tfib_const_abs)%bool = true.
Proof. vm_compute. reflexivity. Qed.
Definition tfib_in_rom_b (x : Z) : bool :=
  existsb (fun sg => (negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? x) && (x <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) TSEGS.
Lemma tfib_lit_end5_b :
  forallb (fun k => (tfib_in_rom_b (tfib_lit_end5 + k) && negb (tfib_owned_b (tfib_lit_end5 + k)))%bool) [0; 1; 2; 3; 4] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_lit_end5_k : forall a, tfib_lit_end5 <= a < tfib_lit_end5 + 5 ->
  tfib_in_rom_b a = true /\ tfib_owned_b a = false.
Proof.
intros a Ha. assert (Hl : In (a - tfib_lit_end5) [0; 1; 2; 3; 4]).
{ assert (Hc : a - tfib_lit_end5 = 0 \/ a - tfib_lit_end5 = 1 \/ a - tfib_lit_end5 = 2 \/ a - tfib_lit_end5 = 3 \/ a - tfib_lit_end5 = 4) by lia.
  destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; cbn; tauto. }
pose proof (proj1 (forallb_forall _ _) tfib_lit_end5_b _ Hl) as H. cbn beta in H.
replace (tfib_lit_end5 + (a - tfib_lit_end5)) with a in H by lia.
apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H2. split; assumption.
Qed.
Theorem tfib_lit_end5_in_rom : forall w, w = tfib_lit_end5 -> forall a, w <= a < w + 5 -> in_rom TSEGS a.
Proof.
intros w -> a Ha. destruct (tfib_lit_end5_k a Ha) as [H _]. unfold tfib_in_rom_b in H.
apply existsb_exists in H as (sg & Hsg & Hb). apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [Hw H1].
apply negb_true_iff in Hw. exists sg. split; [exact Hsg|]. split; [exact Hw|]. split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2].
Qed.
(* DO NOT WIDEN: the clause holds for EXACTLY [0x20f00, 0x20f05). Tfib_owned_static's row (0x20ee1, 0x1f) ENDS at
   0x20f00 and its row (0x20f05, 0x1b) STARTS at 0x20f05 - the redzones on either side of this registered literal - so
   a range one byte wider in either direction, or rounded to 8 bytes or to an aligned word, IS owned_static and the
   clause becomes FALSE. tfib_lit_end5_tight checks both neighbours. *)
Example tfib_lit_end5_tight : tfib_owned_b (tfib_lit_end5 - 1) = true /\ tfib_owned_b (tfib_lit_end5 + 5) = true.
Proof. vm_compute. split; reflexivity. Qed.
Theorem tfib_lit_end5_not_owned_static : forall B : asyms, TfibSyms B ->
  forall w, w = tfib_lit_end5 -> forall a, w <= a < w + 5 -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros B HB w -> a Ha. rewrite (ts_owned B HB). intros HE. destruct (tfib_lit_end5_k a Ha) as [_ Hf].
apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz. unfold tfib_owned_b in Hf.
assert (Ht : existsb (fun r : Z * Z => ((fst r <=? a) && (a <? fst r + snd r))%bool) Tfib_owned_static = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.
