(* fuzz_preset, the crt102 walk, slice Crt102Top: THE A' BINDING OF B (the family lead's standing item). Every crt / rtt
   lane takes `PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B` (or a field of it) as a generic Section hypothesis
   over a free `B : asyms`. This file decides, by vm_compute on closed terms, whether those facts HOLD for every B with
   AF0m.TfibSyms B (lib/A/AF0m.v:1789, the record class of the A' asan image), with the #102 AF0l on the lane base.

   VERDICT: they hold. crt102_palibcore_A (PALibCore, YC1fP.v:322, all seven fields), crt102_palib_A (PALib, YC1fP.v:331,
   PALibCore plus the two use-after-return fields), and Crt102Entry's three narrower stand-ins: crt102_tfib_uar_img_A
   (pal_uar_img), crt102_tfib_stack_malloc3_A (pal_stack_malloc3), crt102_tfib_pst_static_A (pal_pst_static). Under the
   base AF0l eb3d91d8c440 the four code fields were FALSE (pc_wrap_free / pc_wrap_malloc / pc_free_ra0 /
   pc_malloc_ra0 each 0x94 low); under dfca6bb1a8d7 they are the listing's own values (the Eval lines below print them).

   ROLE ON THE LANE. The witness the composition CITES for PAL is PALibA.palib_A (lib/A/PALibA.v
   88c72c8175cf, B := AD2l.TfibB). This file is the INDEPENDENT CONTROL of it, at every B with TfibSyms B rather than
   at the one record, derived from the record's cells and not from TfibB's field values; and it supplies what PALibA
   does not state: crt102_tfib_pst_static_A (Crt102Top's pal_pst_static at TfibB) and crt102_tfib_uar_img_A.
   The core's PALibA 9191751aea39 (the core port at commit 16aec65c367b) is the OLD-PIN INSTANCE, not a
   generic one: palib_A at the one concrete record AD2l.TfibB of that tree, whose AF0l is the base eb3d91d8c440 and
   AF0m 1d01cd9b0fcd, header pin d83eb25dbf0d (the old A pin).

   HOW THE THREE ADDRESS FIELDS ARE PINNED. TfibSyms does not name as_shadow_cell / as_got_shadow / as_uar_cell /
   as_got_uar. It pins as_const B ly = Tfib_const ly (ts_const), and asyms_ok (ts_ok) puts four cells in as_const
   (aso_const_law, YG0f.v:188-190): the shadow cell holding SHADOW_OFF, the uar cell holding the 4-byte 1, and the two
   GOT words holding those cells' addresses. crt_cells_at lists every ANum cell of a given width and value; its
   soundness lemma turns each membership into membership in a computed list, and the computed lists are SINGLETONS
   (crt102_cells_shadow_A, crt102_cells_got_shadow_A, crt102_cells_uar_A, crt102_cells_uar_one_A), so each field is
   determined and the derivation is not vacuous in the record's cells. TfibSyms itself is inhabited at #102:
   AD2l.TfibB_syms (lib/A/AD2l.v eb321db7a357), at which crt102_palibcore_TfibB / crt102_palib_TfibB instantiate the
   two theorems.

   INPUTS OF RECORD (by path):
   - base commit b3beee08c347 (the file was first written on 42fde5231414; unchanged in
     substance since 1b8c4b046f8).
   - lib/A/AF0l.v dfca6bb1a8d7 (the #102 A' record, by path from the #102 integration, commit 987a6556ad7e),
     lib/A/AF0m.v 97f423adf6eb (generated for the A' asan twin bff8519bbe3ea0e4), lib/Reusable/YC1fP.v 5a3e259a9c67,
     lib/A/PRH_Img.v 934516a622e8, lib/A/PRH_Base.v ee2f5cd7ed35 (prh_pst unchanged), lib/Reusable/YImgTop.v d2a97d3111ce.
   - listing v3 (commit 74dcda1eda12): lib/A/Listing_prog.v, lib/A/PAImg_prog.v.
   - the image-free checkers in_img_b / pst_allb of lib/A/Prog/S1ImgA.v (on the lane base).
   - build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1,
     PAU pau-preset-102.
   - pins: A' asan 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4.

   NUMERALS. ADDRESS: none typed (every address is pa_val / pa_sigma of the listing, a TFIB_* / Tfib_* name of AF0m /
   AF0l, prh_pst of PRH_Img, or IMG_LO / IMG_TOP). LENGTH: 8 and 4 (the cells' widths, a word and the uar flag), 4
   (errno). WORD: 1 (the uar flag's value), 3 (frame class 3), 0 (the fields of crt_ly_any, which Tfib_const does not
   read). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YM05 YG00 YG01 YG0f YG0n YG0d YCbq YP0b YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog AF0l AF0m PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* ---- image-free: the ANum cells of a list by width and value ---- *)
(* a layout to instantiate the `forall ly` of ts_const / aso_const_law at; Tfib_const does not read it *)
Definition crt_ly_any : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).

Definition crt_cell_hit (w : nat) (v : Z) (c : acell) : list Z :=
  match c with
  | ACell (ANum a) w' (AV (ANum v')) => if Nat.eqb w w' && Z.eqb v v' then [a] else []
  | _ => []
  end.
Definition crt_cells_at (l : list acell) (w : nat) (v : Z) : list Z := flat_map (crt_cell_hit w v) l.

Lemma crt_cells_at_sound : forall l w v a, In (ACell (ANum a) w (AV (ANum v))) l -> In a (crt_cells_at l w v).
Proof.
intros l w v a H. unfold crt_cells_at. apply in_flat_map. exists (ACell (ANum a) w (AV (ANum v))).
split; [exact H|]. cbv beta iota delta [crt_cell_hit]. rewrite Nat.eqb_refl, Z.eqb_refl. simpl. left. reflexivity.
Qed.

Lemma crt_in_one : forall (l : list Z) x a, In a l -> l = [x] -> a = x.
Proof. intros l x a H E. subst l. destruct H as [H | []]. symmetry. exact H. Qed.

(* every byte a is outside the ranges l and outside [lo, lo + w) *)
Definition crt_out_b (l : list (Z * Z)) (lo w a : Z) : bool :=
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l) && negb ((lo <=? a) && (a <? lo + w)).

Lemma crt_out_b_sound : forall l lo w a, crt_out_b l lo w a = true -> ~ Exists (in_zr a) l /\ ~ (lo <= a < lo + w).
Proof.
intros l lo w a H. unfold crt_out_b in H. apply andb_prop in H as [H1 H2].
apply negb_true_iff in H1. apply negb_true_iff in H2. split.
- intros HE. apply Exists_exists in HE as (r & Hr & Hin). unfold in_zr in Hin.
  assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
  { apply existsb_exists. exists r. split; [exact Hr|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in H1. discriminate H1.
- intros Hr. assert (E : (lo <=? a) && (a <? lo + w) = true).
  { apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in H2. discriminate H2.
Qed.

(* ---- image A', the whole-program listing ---- *)
Section c. Context {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation TCA := (Tfib_const crt_ly_any).

(* the record's cells, by computation: each list is ONE address, the listing's *)
Lemma crt102_cells_shadow_A : crt_cells_at TCA 8%nat SHADOW_OFF = [VAL (A_OBJ 12)].
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_cells_got_shadow_A : crt_cells_at TCA 8%nat (VAL (A_OBJ 12)) = [VAL (A_OBJ 0)].
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_cells_uar_one_A : length (crt_cells_at TCA 4%nat 1) = 1%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_cells_uar_A : flat_map (crt_cells_at TCA 8%nat) (crt_cells_at TCA 4%nat 1) = [VAL (A_OBJ 1)].
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_cells_uar_img_A : forallb (fun z => (IMG_LO <=? z) && (z + 4 <=? IMG_TOP)) (crt_cells_at TCA 4%nat 1) = true.
Proof. vm_compute. reflexivity. Qed.
(* errno's four bytes are image bytes; no statics byte is a runtime-owned static or errno *)
Lemma crt102_errno_cells_A : pst_allb (in_img_b SEGS) [(TFIB_ERRNO, 4)] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crt102_pst_out_A : pst_allb (crt_out_b Tfib_owned_static TFIB_ERRNO 4) PST = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- the fields, at every B with TfibSyms B (named projections of TfibSyms / asyms_ok only) ---- *)
Lemma crt102_tfib_cell_A : forall B, TfibSyms B -> as_shadow_cell B = VAL (A_OBJ 12).
Proof.
intros B HT. destruct (aso_const_law B (AF0m.ts_ok B HT) crt_ly_any) as (H & _ & _ & _).
rewrite (AF0m.ts_const B HT crt_ly_any) in H. unfold z8, c8 in H.
exact (crt_in_one _ _ _ (crt_cells_at_sound _ _ _ _ H) crt102_cells_shadow_A).
Qed.

Lemma crt102_tfib_got_shadow_A : forall B, TfibSyms B -> as_got_shadow B = VAL (A_OBJ 0).
Proof.
intros B HT. destruct (aso_const_law B (AF0m.ts_ok B HT) crt_ly_any) as (_ & _ & H & _).
rewrite (AF0m.ts_const B HT crt_ly_any), (crt102_tfib_cell_A B HT) in H. unfold z8, c8 in H.
exact (crt_in_one _ _ _ (crt_cells_at_sound _ _ _ _ H) crt102_cells_got_shadow_A).
Qed.

Lemma crt102_tfib_uar_in_A : forall B, TfibSyms B -> In (as_uar_cell B) (crt_cells_at TCA 4%nat 1).
Proof.
intros B HT. destruct (aso_const_law B (AF0m.ts_ok B HT) crt_ly_any) as (_ & H & _ & _).
rewrite (AF0m.ts_const B HT crt_ly_any) in H. unfold z4, c4 in H. exact (crt_cells_at_sound _ _ _ _ H).
Qed.

Lemma crt102_tfib_got_uar_A : forall B, TfibSyms B -> as_got_uar B = VAL (A_OBJ 1).
Proof.
intros B HT. destruct (aso_const_law B (AF0m.ts_ok B HT) crt_ly_any) as (_ & _ & _ & H).
rewrite (AF0m.ts_const B HT crt_ly_any) in H. unfold z8, c8 in H.
apply (crt_in_one (flat_map (crt_cells_at TCA 8%nat) (crt_cells_at TCA 4%nat 1))); [| exact crt102_cells_uar_A].
apply in_flat_map. exists (as_uar_cell B). split; [exact (crt102_tfib_uar_in_A B HT) | exact (crt_cells_at_sound _ _ _ _ H)].
Qed.

Lemma crt102_tfib_env_A : forall B, TfibSyms B -> api_env SEGS B.
Proof.
intros B HT. unfold api_env. rewrite (AF0m.ts_errno B HT), (AF0m.ts_code B HT).
split; [split; apply Z.leb_le; vm_compute; reflexivity|]. split.
- intros a Ha. apply in_img_b_sound. apply (pst_allb_sound _ _ a crt102_errno_cells_A).
  apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha.
- split; apply (AF0m.ts_universe_drv B HT); apply YCej.memZL_In; vm_compute; reflexivity.
Qed.

(* ---- THE BINDING: PALibCore, then PALib ---- *)
Theorem crt102_palibcore_A : forall B, AF0m.TfibSyms B -> PALibCore (L := A_prog_listing) (PI := PI_prog_A) B.
Proof.
intros B HT. split.
- exact (crt102_tfib_got_shadow_A B HT).
- exact (crt102_tfib_cell_A B HT).
- left. apply Z.leb_le. vm_compute. reflexivity.
- exact (crt102_tfib_env_A B HT).
- rewrite (AF0m.ts_code B HT). vm_compute. reflexivity.
- rewrite (AF0m.ts_code B HT). vm_compute. reflexivity.
- rewrite (AF0m.ts_code B HT). split; apply Z.ltb_lt; vm_compute; reflexivity.
Qed.

Theorem crt102_palib_A : forall B, AF0m.TfibSyms B -> PALib (L := A_prog_listing) (PI := PI_prog_A) B.
Proof.
intros B HT. split.
- exact (crt102_tfib_got_shadow_A B HT).
- exact (crt102_tfib_cell_A B HT).
- left. apply Z.leb_le. vm_compute. reflexivity.
- exact (crt102_tfib_env_A B HT).
- rewrite (AF0m.ts_code B HT). vm_compute. reflexivity.
- rewrite (AF0m.ts_code B HT). vm_compute. reflexivity.
- rewrite (AF0m.ts_code B HT). split; apply Z.ltb_lt; vm_compute; reflexivity.
- exact (crt102_tfib_got_uar_A B HT).
- exact A_prog_got_uar_disj.
Qed.

(* ---- not vacuous: the two theorems at the #102 A' record AD2l.TfibB, whose TfibSyms is AD2l.TfibB_syms ---- *)
Lemma crt102_palibcore_TfibB : PALibCore (L := A_prog_listing) (PI := PI_prog_A) AD2l.TfibB.
Proof. exact (crt102_palibcore_A AD2l.TfibB AD2l.TfibB_syms). Qed.
Lemma crt102_palib_TfibB : PALib (L := A_prog_listing) (PI := PI_prog_A) AD2l.TfibB.
Proof. exact (crt102_palib_A AD2l.TfibB AD2l.TfibB_syms). Qed.

(* ---- Crt102Entry's three narrower stand-ins (pal_uar_img, pal_stack_malloc3, pal_pst_static), same B ---- *)
Lemma crt102_tfib_uar_img_A : forall B, AF0m.TfibSyms B -> IMG_LO <= as_uar_cell B /\ as_uar_cell B + 4 <= IMG_TOP.
Proof.
intros B HT. pose proof crt102_cells_uar_img_A as Hf. rewrite forallb_forall in Hf.
specialize (Hf _ (crt102_tfib_uar_in_A B HT)). apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption.
Qed.

Lemma crt102_tfib_stack_malloc3_A : forall B, AF0m.TfibSyms B ->
  SIGMA AS___asan_stack_malloc_3 = pc_stack_malloc (as_code B) 3.
Proof. intros B HT. rewrite (AF0m.ts_code B HT). vm_compute. reflexivity. Qed.

Lemma crt102_tfib_pst_static_A : forall B, AF0m.TfibSyms B -> forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B HT a Ha. rewrite (AF0m.ts_owned B HT), (AF0m.ts_errno B HT).
exact (crt_out_b_sound _ _ _ _ (pst_allb_sound _ _ a crt102_pst_out_A Ha)).
Qed.

(* the numbers, so the log shows them: each listing value beside the AF0l / AF0m value it is checked against, then
   the three cells as the record's cell lists give them *)
Eval vm_compute in ((SIGMA AS___wrap_free, pc_wrap_free Tfib_code), (SIGMA AS___wrap_malloc, pc_wrap_malloc Tfib_code),
  (BASE, pc_free_ra0 Tfib_code, pc_malloc_ra0 Tfib_code), (SIGMA AS___asan_stack_malloc_3, pc_stack_malloc Tfib_code 3)).
Eval vm_compute in ((VAL (A_OBJ 0), VAL (A_OBJ 12), VAL (A_OBJ 1)),
  (crt_cells_at TCA 8%nat SHADOW_OFF, crt_cells_at TCA 8%nat (VAL (A_OBJ 12)), crt_cells_at TCA 4%nat 1,
   flat_map (crt_cells_at TCA 8%nat) (crt_cells_at TCA 4%nat 1))).
End c.

Print Assumptions crt102_palibcore_A.
Print Assumptions crt102_palib_A.
