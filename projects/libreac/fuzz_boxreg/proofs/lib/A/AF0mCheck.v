(* Image facts and the image gates for libreac/fuzz_boxreg's ASan build (fuzz_boxreg.asan, sha256 eacfa20547ad7dc0...),
   over lib/A/AF0m.v (a Theorem Labs lane's file, a Theorem Labs lane's af0m.py) and lib/A/AF0mRoPins.v (ro_pins.py's file). Rule 24: no
   function is proved here. Form: libreac/fuzz_grant's lib/A/AF0mCheck.v (a working branch ac3f475adac) and cgif's
   lib/A/AE2y.v rodata_chk / const_chk_sound (origin/ossv/recipes c8557374ad2).
   - Which check a cell gets depends on its ELF section (a Theorem Labs lane, 2026-10-29 00:37Z). box_file_sections and
     box_nobits_sections are the image's allocated sections (readelf -S of the pinned image), split by whether the file
     carries their bytes. file_backed a w: [a, a + w) lies in one section of box_file_sections; nobits a w: in one of
     box_nobits_sections (.tbss, .relro_padding, .bss). box_abs_split: each row of Tfib_const_abs is exactly one of the
     two (255 rows: 143 file-backed, 112 in .bss).
   - Gate 2, file-backed cells: abs_image_chk / abs_image_chk_sound. box_abs_image: every file-backed row of
     Tfib_const_abs states the image's file bytes; box_pins_image: so does every row of Tfib_ro_pins.
   - Cells in a NOBITS section (box_bss_rows, the 112 .bss rows) are NOT compared with file bytes: the file carries none
     (the loader zero-fills them), so such a comparison proves nothing. Their values are what the runtime's start-up
     stores, and the start-up certificate checks them: cgif's AD1g tfib_holes_if (its if_chk holds
     forallb (xcell ch0) TFIB_CONST, TFIB_CONST = Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow, for every
     hand-off state ch0 of HS_tfib_list, lib/A/AB01.v), a core file of boxreg's relocation that reads the same states.
     AB01.v and AD1g.v are not on this branch yet, so that gate cannot run here. Measured instead (2026-10-29,
     a Theorem Labs lane's boxpa/tools/cells_check.py on the generated AB01.v, sha256 341e8017...): all 110
     .bss rows and all 60 Tfib_const_shadow cells hold the stated value in all 50 hand-off states at main 0x7faac
     (asyms-cells.tsv, one row per cell, with its section).
   - The read-only gate (a Theorem Labs lane's row 37; a Theorem Labs lane's ruling 23:56Z): every owned byte inside a segment without write
     permission (box_ro_ranges) is pinned to its image byte by a row of the const table. ro_pinned_chk /
     ro_pinned_chk_sound make it one vm_compute; box_ro_pinned proves it for Tfib_const_abs, and box_ro_gate states it.
     af0m.py emits the pins itself since the 01:59Z re-run (26 cells over the 144 bytes of the right redzones of the 5
     read-only globals ZERO 0x20cc0, .str 0x20ce0, read_mac.base 0x20d00, .str 0x20d40, .str.1 0x20d60), appended at the
     table's end (rows 230..255 of 255). The cross-check against this lane's own ro_pins.py pins found all 26 as rows
     with the same address, width and value, so that file left the branch (2026-10-29 02:5xZ). box_abs_owned: every
     file-backed row lies in Tfib_owned_static (cgif's AD1g xowned_all needs it). *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.libreac.fuzz_boxreg.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YG0f YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AF0m.
Import ListNotations.
Local Open Scope Z_scope.
Definition box_segs : list Segment := OSSVerify.libreac.fuzz_boxreg.images.Asan.M.loaded_segments.
(* The bytes the image carries at a, little-endian, as a value; None when it carries none. *)
Fixpoint img_word (a : Z) (w : nat) : option Z :=
match w with
| O => Some 0
| S w' =>
  match seg_rom box_segs (Z_to_bv 64 a), img_word (a + 1) w' with
  | Some b, Some v => Some (bv_unsigned b + 256 * v)
  | _, _ => None
  end
end.
(* The image's allocated sections (readelf -S of the pinned image, (sh_addr, sh_size)), split by whether the file carries
   their bytes. *)
Definition box_file_sections : list (Z * Z) :=
[(0x102a8, 0x24) (* .note.gnu.build-id *); (0x102e0, 0x123ac) (* .rodata *); (0x2268c, 0x2074) (* .eh_frame_hdr *);
(0x24700, 0xa858) (* .eh_frame *); (0x2ff58, 0x679c4) (* .text *); (0x98920, 0x20) (* .init_array *);
(0x98940, 0x10) (* .fini_array *); (0x98950, 0x8) (* .preinit_array *); (0x98958, 0x500) (* .data.rel.ro *);
(0x98e58, 0xd58) (* .got *); (0x9abb0, 0x2bc0) (* .data *); (0x9d770, 0x140) (* asan_globals *)].
Definition box_nobits_sections : list (Z * Z) :=
[(0x97920, 0x14) (* .tbss *); (0x99bb0, 0x450) (* .relro_padding *); (0x9d8c0, 0x557f30) (* .bss *)].
(* (p_vaddr, p_filesz) of the image's two PT_LOAD headers without write permission (readelf -l). *)
Definition box_ro_ranges : list (Z * Z) := [(IMG_LO, 0x1ef58); (0x2ff58, 0x679c4)].
Definition in_secs (l : list (Z * Z)) (a : Z) (w : nat) : bool :=
existsb (fun r => (fst r <=? a) && (a + Z.of_nat w <=? fst r + snd r))%bool l.
Definition file_backed (a : Z) (w : nat) : bool := in_secs box_file_sections a w.
Definition nobits (a : Z) (w : nat) : bool := in_secs box_nobits_sections a w.
Definition abs_image_chk (l : list acell) : bool :=
forallb (fun c => match c_at c, c_val c with
  | ANum a, AV (ANum v) => negb (file_backed a (c_w c)) || match img_word a (c_w c) with Some x => Z.eqb x v | None => false end
  | _, _ => true
  end) l.
Lemma abs_image_chk_sound : forall l, abs_image_chk l = true ->
Forall (fun c => forall a v, c_at c = ANum a -> c_val c = AV (ANum v) -> file_backed a (c_w c) = true ->
  img_word a (c_w c) = Some v) l.
Proof.
intros l H. apply Forall_forall. intros [e w av] Hc a v Ha Hv Hf. cbn [c_at c_val c_w] in Ha, Hv, Hf |- *. subst e av.
pose proof (proj1 (forallb_forall _ _) H _ Hc) as H1. cbv beta in H1. cbn [c_at c_val c_w] in H1.
rewrite Hf in H1. cbn [negb orb] in H1.
destruct (img_word a w) as [x|]; [apply Z.eqb_eq in H1; subst x; reflexivity | discriminate].
Qed.
Definition pinb (c : acell) (a : Z) : bool :=
match c_at c, c_val c with
| ANum a', AV (ANum v) => (a' <=? a) && (a <? a' + Z.of_nat (c_w c)) && match img_word a' (c_w c) with Some x => Z.eqb x v | None => false end
| _, _ => false
end.
Lemma pinb_sound : forall c a, pinb c a = true ->
exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\ img_word a' (c_w c) = Some v.
Proof.
intros [e w av] a H. unfold pinb in H. cbn [c_at c_val c_w] in H |- *.
destruct e as [a'| | | | | | | | | | | | | | | | | |]; try (cbn in H; discriminate).
destruct av as [e'|]; [|cbn in H; discriminate]. destruct e' as [v| | | | | | | | | | | | | | | | | |]; try (cbn in H; discriminate).
destruct (img_word a' w) as [x|] eqn:Ei; [|rewrite Bool.andb_false_r in H; discriminate].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. subst x.
exists a', v. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exact Ei].
Qed.
Definition zbytes (lo n : Z) : list Z := map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat n)).
Lemma in_zbytes : forall lo n a, lo <= a < lo + n -> In a (zbytes lo n).
Proof.
intros lo n a H. unfold zbytes. apply in_map_iff. exists (Z.to_nat (a - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Definition ro_pinned_chk (owned : list (Z * Z)) (l : list acell) : bool :=
forallb (fun r => forallb (fun s =>
  let lo := Z.max (fst r) (fst s) in let hi := Z.min (fst r + snd r) (fst s + snd s) in
  forallb (fun a => existsb (fun c => pinb c a) l) (zbytes lo (hi - lo))) box_ro_ranges) owned.
Lemma ro_pinned_chk_sound : forall owned l, ro_pinned_chk owned l = true ->
forall a, Exists (fun s => fst s <= a < fst s + snd s) box_ro_ranges -> Exists (fun r => fst r <= a < fst r + snd r) owned ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  img_word a' (c_w c) = Some v) l.
Proof.
intros owned l H a Hs Hr. unfold ro_pinned_chk in H.
apply Exists_exists in Hs as (s & Hs & Ls). apply Exists_exists in Hr as (r & Hr & Lr).
pose proof (proj1 (forallb_forall _ _) H r Hr) as H1. cbv beta in H1.
pose proof (proj1 (forallb_forall _ _) H1 s Hs) as H2. cbv beta zeta in H2.
assert (Ha : In a (zbytes (Z.max (fst r) (fst s)) (Z.min (fst r + snd r) (fst s + snd s) - Z.max (fst r) (fst s))))
by (apply in_zbytes; lia).
pose proof (proj1 (forallb_forall _ _) H2 a Ha) as H3. cbv beta in H3.
apply existsb_exists in H3 as (c & Hc & Hp). apply Exists_exists. exists c. split; [exact Hc | exact (pinb_sound c a Hp)].
Qed.
Definition owned_cells_chk (owned : list (Z * Z)) (l : list acell) : bool :=
forallb (fun c => match c_at c with
  | ANum a => existsb (fun r => (fst r <=? a) && (a + Z.of_nat (c_w c) <=? fst r + snd r)) owned
  | _ => false end)%bool l.
(* The section split of Tfib_const_abs: each row lies in a file-backed section or in a NOBITS section, never both,
   never neither. *)
Definition cell_file (c : acell) : bool := match c_at c with ANum a => file_backed a (c_w c) | _ => false end.
Definition cell_nobits (c : acell) : bool := match c_at c with ANum a => nobits a (c_w c) | _ => false end.
Theorem box_abs_split :
forallb (fun c => xorb (cell_file c) (cell_nobits c)) Tfib_const_abs = true /\
length (filter cell_file Tfib_const_abs) = 143%nat /\ length (filter cell_nobits Tfib_const_abs) = 112%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* The rows whose value only the start-up certificate can check (see the header): its gate's input. *)
Definition box_bss_rows : list acell := filter cell_nobits Tfib_const_abs.
Theorem box_abs_image : abs_image_chk Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.
Theorem box_abs_owned : owned_cells_chk Tfib_owned_static (filter cell_file Tfib_const_abs) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem box_ro_pinned : ro_pinned_chk Tfib_owned_static Tfib_const_abs = true.
Proof. vm_compute. reflexivity. Qed.
Definition box_ro_gate : Prop :=
forall a, Exists (fun s => fst s <= a < fst s + snd s) box_ro_ranges -> Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static ->
Exists (fun c => exists a' v, c_at c = ANum a' /\ c_val c = AV (ANum v) /\ a' <= a < a' + Z.of_nat (c_w c) /\
  img_word a' (c_w c) = Some v) Tfib_const_abs.
Lemma box_ro_gate_holds : box_ro_gate.
Proof. exact (ro_pinned_chk_sound Tfib_owned_static Tfib_const_abs box_ro_pinned). Qed.
