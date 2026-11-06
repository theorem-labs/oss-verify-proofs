(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image A' (#102 pin asan 1be0f53d, unstripped twin bff8519b), lane S7b (WalkS7bR,
   a Theorem Labs lane): the INSTANCE WITNESSES of the LITERAL image premises of the writer walks (unit ruling a Theorem Labs lane
   16:45Z: an image premise counts only beside a lemma closed by vm_compute at the real instance). Proves nothing about
   the program, and no walk Requires this file. The premises, each witnessed by ONE lemma stated as the premise's text
   at PA := PI_prog_A, B := AD2l.TfibB, for EVERY allocator relation ARx with AR_laws_x at TfibB:
     pj_write HLIT      (PRW_pj_write.v:214-217)                                     : s7bl_pjw_hlit
     put_string HLIT17  (PRW_put_string_base.v:943-946; the same text in _a.v:117-120, _l.v:119-122,
                         _t.v:150-153, PRW_put_string.v:94-97)                       : s7bl_ps_hlit17
     put_string HLIT85 / 87 / 91 / 93 / 89 (`ps_lit_fact B ARx k l`, PRW_put_string_base.v:937-940; _a.v:123-127,
                         _e.v:127-131, PRW_put_string.v:98-102)                      : s7bl_ps_hlit85 / 87 / 91 / 93 / 89
     write_value HLIT   (PRW_write_value.v:1244-1249, all ten wv_lits)              : s7bl_wv_hlit
   THE INSTANCE (the kit's cut 7cdbb61b5fa0): PAImg_prog.v 505a51ff7d08 (PI_prog_A),
   Listing_prog.v 7ed1529926bd, AD2l.v eb321db7a357 (TfibB), AF0m.v 97f423adf6eb (Tfib_owned_static,
   Tfib_zero_shadow, Tfib_const_shadow, TFIB_ERRNO), PRH_Base.v ef7c8ca98529 (src_rd / kept_at / kept_img, route (a)),
   YImgShadowCover.v c773dcbec9bc, PresetRodata.v 4eb7e95e7e93. The segments are the FULLY QUALIFIED A' image
   (RSEGS_A; s7bl_segs_A is the guard that PI_prog_A's pa_segs is it).
   METHOD (WalkS7aR's): its generic step s7w_lit_rd (kept_img + the ROM bytes + one img_shadow_cover check give src_rd
   and kept_at at any ARx state with arodata_okP) is used, not copied, from its function-free home S7a_litrd.v
   (WalkS7aR, a working branch; moved there out of S7a_indent_wit.v so that no walk of another
   function enters this file's closure). Its
   per-literal static facts are here ONE closed boolean per literal, s7bl_lit_b: the bounds pa_lo + 64 <= p and
   p + n + 64 <= pa_hi, then for every byte p + j of the literal: a non-writable segment holds it, it is not an owned
   static, not errno, its granule is a whole zero-shadow granule or has a const-shadow cell z1 (shadow_addr a) v with
   v = 0 or a mod 8 < v < 8 (kept_img's ro_shadow_ok), and its ROM byte is the literal's byte j; then the hull cover
   img_shadow_cover zs cs (p / 8 / 8 * 64) ((p + n - 1) / 8 / 8 * 64 + 64). One soundness lemma (s7bl_kept_img_b) turns
   the boolean into kept_img, and s7bl_lit feeds s7w_lit_rd. The REDZONE CHECK (the pal_lit lesson) is a second closed
   boolean per literal, s7bl_rz_b p bytes (bytes WITH the NUL): the byte before p is owned static (the previous
   global's redzone), every byte of the literal and its NUL is not owned static and is the image's byte, the byte after
   the NUL is owned static (the literal's own redzone), and the last byte is 0. So each literal is exactly one global.
   pj_write's HLIT (.str.3, the same global as indent's newline) goes through the same checker (s7bl_c_pjw).
   NO ADDRESS IS TYPED: each literal is read from the listing (s7bl_ps k / s7bl_wv k are the premises' ps_str k /
   WV_STR k without the class, equal by conversion), every derived value (shadow cell, hull, neighbours) is computed
   inside the closed vm_compute. MEASURED at A' (not in git: a parse of Listing_prog.v / AF0m.v and the ELF's
   PT_LOAD bytes; put_string's six also in the internal file zf-fuzz-preset-06fa7260d2.build-20261029T200731Z.log), one 32-byte global
   each, every one in the read-only segment [0x10000, 0x30374), none in a zero-shadow range, its granule's shadow
   cell = its length with the NUL:
     put_string: 65 """" 0x215c0 (cell 02), 93 "\\%c" 0x215e0 (04), 87 "\\n" 0x21600 (03), 85 "\\t" 0x21620 (03),
       91 "\\r" 0x21640 (03), 89 "\\u%04x" 0x21660 (07);
     write_value: 103 "true" 0x21460 (05), 126 "false" 0x21480 (06), 122 "null" 0x214a0 (05), 42 "{" 0x214e0 (02),
       39 "[" 0x21500 (02), 151 "," 0x21520 (02), 59 ": " 0x21540 (03), 130 ":" 0x21560 (02), 219 "}" 0x21580 (02),
       216 "]" 0x215a0 (02);
     pj_write: 18 "\n" 0x21440 (02) = indent's slot 9.
   No finding: every literal's granule is its own (partial, const-shadow cell), and every redzone check holds.
   Numerals: the slots 18 / 65 / 85 / 87 / 89 / 91 / 93 / 103 / 122 / 126 / 39 / 42 / 59 / 130 / 151 / 216 / 219 and the
   byte lists are the premises' own; 0 (the NUL); 1 (the byte before a literal); 4 (errno's width); 8, 64 (LENGTH: a
   granule, a shadow granule's span); 4096 (LENGTH: page 0, in s7bl_lit). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YImgShadowCover.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S7a_litrd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_pj_write PRW_put_string_base PRW_write_value.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* the A' segments, FULLY QUALIFIED (never the short name Img0.rsegs) *)
#[local] Abbreviation RSEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
Open Scope Z_scope.

(* ---- THE CHECKER: kept_img's static part, the ROM bytes and the hull cover of one literal, as one closed boolean ---- *)

(* the whole granule [g, g + 8) lies in one zero-shadow range *)
Definition s7bl_zs_b (zs : list (Z * Z)) (g : Z) : bool :=
  existsb (fun r => (fst r <=? g) && (g + 8 <=? fst r + snd r)) zs.
Lemma s7bl_zs_b_sound : forall zs g, s7bl_zs_b zs g = true -> exists q m, In (q, m) zs /\ q <= g /\ g + 8 <= q + m.
Proof.
intros zs g H. apply existsb_exists in H as ([q m] & Hin & H). cbn [fst snd] in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists q, m. split; [exact Hin|]. split; [exact H1 | exact H2].
Qed.

(* a const-shadow cell of a's granule: z1 (shadow_addr a) v with v = 0 or a inside the granule's addressable prefix *)
Definition s7bl_cell_b (a : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum y) (S O) (AV (ANum w)) => (y =? shadow_addr a) && ((w =? 0) || ((a mod 8 <? w) && (w <? 8)))
  | _ => false
  end.
Lemma s7bl_cell_b_sound : forall a c, s7bl_cell_b a c = true ->
  exists w, c = z1 (ANum (shadow_addr a)) w /\ (w = 0 \/ a mod 8 < w < 8).
Proof.
intros a [ca cw cv] H. unfold s7bl_cell_b in H.
destruct ca; try discriminate H. destruct cw as [|[|cw]]; try discriminate H.
destruct cv as [e|m x]; try discriminate H. destruct e; try discriminate H.
cbv beta iota in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst.
eexists. split; [reflexivity|].
apply orb_true_iff in H2 as [H2 | H2].
- left. apply Z.eqb_eq in H2. exact H2.
- right. apply andb_prop in H2 as [H3 H4]. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4. exact (conj H3 H4).
Qed.

(* the image's ROM byte at a is v *)
Definition s7bl_rom_b (segs : list Segment) (a v : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.
Lemma s7bl_rom_b_sound : forall segs a v, s7bl_rom_b segs a v = true ->
  option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) = Some v.
Proof.
intros segs a v H. unfold s7bl_rom_b in H.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [|discriminate H].
apply Z.eqb_eq in H. cbn [option_map]. rewrite H. reflexivity.
Qed.

(* one byte a of a literal, with its value v: read-only segment, not owned static, not errno, shadow, ROM byte *)
Definition s7bl_byte_b (segs : list Segment) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z)) (cs : list acell)
  (a v : Z) : bool :=
  s7w_ro_b segs a && negb (s7w_zr_b own a) && negb ((errno <=? a) && (a <? errno + 4)) &&
  (s7bl_zs_b zs (a - a mod 8) || existsb (s7bl_cell_b a) cs) && s7bl_rom_b segs a v.
Fixpoint s7bl_bytes_b (segs : list Segment) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z)) (cs : list acell)
  (p : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | v :: l' => s7bl_byte_b segs own errno zs cs p v && s7bl_bytes_b segs own errno zs cs (p + 1) l'
  end.
Lemma s7bl_bytes_b_nth : forall segs own errno zs cs l p, s7bl_bytes_b segs own errno zs cs p l = true ->
  forall j, (j < length l)%nat -> s7bl_byte_b segs own errno zs cs (p + Z.of_nat j) (nth j l 0) = true.
Proof.
intros segs own errno zs cs l. induction l as [|v l IH]; intros p H j Hj; cbn [length] in Hj; [lia|].
cbn [s7bl_bytes_b] in H. apply andb_prop in H as [H1 H2].
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. exact H1.
- cbn [nth]. replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. apply IH; [exact H2 | lia].
Qed.

(* THE CHECKER: a literal l (its bytes as the premise states them) at p *)
Definition s7bl_lit_b (lo hi : Z) (segs : list Segment) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z))
  (cs : list acell) (p : Z) (l : list Z) : bool :=
  (lo + 64 <=? p) && (p + Z.of_nat (length l) + 64 <=? hi) && s7bl_bytes_b segs own errno zs cs p l &&
  img_shadow_cover zs cs (p / 8 / 8 * 64) ((p + Z.of_nat (length l) - 1) / 8 / 8 * 64 + 64).

(* the literal's bytes are image bytes (write_value's third conjunct): a read-only segment holds each *)
Lemma s7bl_lit_img : forall lo hi segs own errno zs cs p l, s7bl_lit_b lo hi segs own errno zs cs p l = true ->
  forall i, 0 <= i < Z.of_nat (length l) -> in_img segs (p + i).
Proof.
intros lo hi segs own errno zs cs p l H i Hi. unfold s7bl_lit_b in H.
apply andb_prop in H as [H _]. apply andb_prop in H as [_ Hb].
pose proof (s7bl_bytes_b_nth _ _ _ _ _ l p Hb (Z.to_nat i) ltac:(lia)) as Hy.
rewrite (Z2Nat.id i ltac:(lia)) in Hy. unfold s7bl_byte_b in Hy.
apply andb_prop in Hy as [Hy _]. apply andb_prop in Hy as [Hy _]. apply andb_prop in Hy as [Hy _].
apply andb_prop in Hy as [Hro _].
destruct (s7w_ro_b_sound _ _ Hro) as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
Qed.

(* THE REDZONE CHECK of a literal whose bytes WITH the NUL are l: the byte before is owned static, each byte of l is
   not owned static and is the image's, the byte after l is owned static, and l ends in the NUL *)
Definition s7bl_rz_b (segs : list Segment) (own : list (Z * Z)) (p : Z) (l : list Z) : bool :=
  s7w_zr_b own (p - 1) &&
  forallb (fun j => negb (s7w_zr_b own (p + Z.of_nat j)) && s7bl_rom_b segs (p + Z.of_nat j) (nth j l 0))
    (seq 0 (length l)) &&
  s7w_zr_b own (p + Z.of_nat (length l)) && (last l 1 =? 0).

(* ---- THE GENERIC STEP: a literal whose boolean holds is kept_img, and (through s7w_lit_rd) a readable, kept
   source at any ARx state with arodata_okP ---- *)
(* the instance's projections are written with the Section's PA EXPLICITLY: a bare pa_lo could resolve to the global
   instance PI_prog_A *)
Section g. Context {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := (@pa_segs rc L PA).
#[local] Abbreviation PLO := (@pa_lo rc L PA).
#[local] Abbreviation PHI := (@pa_hi rc L PA).
Variable B : asyms.

Lemma s7bl_kept_img_b : forall cs p l, (forall ly, incl cs (as_const B ly)) ->
  s7bl_lit_b PLO PHI segs (as_owned_static B) (as_errno B) (as_zero_shadow B) cs p l = true ->
  kept_img (PA := PA) B p (Z.of_nat (length l)).
Proof.
intros cs p l IC H. unfold s7bl_lit_b in H.
apply andb_prop in H as [H _]. apply andb_prop in H as [H Hb]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold kept_img. split; [exact H1|]. split; [exact H2|].
intros a Ha.
pose proof (s7bl_bytes_b_nth _ _ _ _ _ l p Hb (Z.to_nat (a - p)) ltac:(lia)) as Hy.
rewrite (Z2Nat.id (a - p) ltac:(lia)) in Hy. replace (p + (a - p)) with a in Hy by lia.
unfold s7bl_byte_b in Hy.
apply andb_prop in Hy as [Hy _]. apply andb_prop in Hy as [Hy Hsh]. apply andb_prop in Hy as [Hy Her].
apply andb_prop in Hy as [Hro Hown]. apply negb_true_iff in Hown. apply negb_true_iff in Her.
split; [left; exact (s7w_ro_b_sound _ _ Hro)|].
split; [exact (s7w_zr_b_sound _ _ Hown)|].
split.
- intros [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite E1, E2 in Her. cbn in Her. discriminate Her.
- unfold ro_shadow_ok, in_zs. apply orb_true_iff in Hsh as [Hz | Hc].
  + left. exact (s7bl_zs_b_sound _ _ Hz).
  + right. apply existsb_exists in Hc as (c & Hcin & Hc).
    destruct (s7bl_cell_b_sound a c Hc) as (w & Ec & Hw). subst c.
    exists w. split; [intros ly; exact (IC ly _ Hcin) | exact Hw].
Qed.

Lemma s7bl_lit : forall (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x segs B ARx HL ->
  forall cs p l, (forall ly, incl cs (as_const B ly)) ->
  4096 <= PLO -> PHI <= kLowMemEnd ->
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B) -> (0 < length l)%nat ->
  s7bl_lit_b PLO PHI segs (as_owned_static B) (as_errno B) (as_zero_shadow B) cs p l = true ->
  forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (aview segs (w_H W) mem) ->
  src_rd (PA := PA) W mem p l /\ kept_at (PA := PA) B [] p (Z.of_nat (length l)).
Proof.
intros ARx HL LAWS cs p l IC HPL HPH ZA Hn H ly S Hp W mem md HAR HRO.
pose proof H as H'. unfold s7bl_lit_b in H'. apply andb_prop in H' as [H' Hcv]. apply andb_prop in H' as [_ Hb].
refine (s7w_lit_rd B ARx LAWS (as_zero_shadow B) cs _ _ ly S Hp W mem md p l HPL HPH ZA Hcv (incl_refl _) IC
  (Z.le_refl _) (Z.le_refl _) HAR HRO (s7bl_kept_img_b cs p l IC H) Hn _).
intros j Hj. pose proof (s7bl_bytes_b_nth _ _ _ _ _ l p Hb j Hj) as Hy.
unfold s7bl_byte_b in Hy. apply andb_prop in Hy as [_ Hr]. exact (s7bl_rom_b_sound _ _ _ Hr).
Qed.
End g.

(* ---- THE CLOSED INSTANCE FACTS (vm_compute on closed goals) ---- *)

(* the literals, read from the listing: put_string's ps_str k and write_value's WV_STR k without the class *)
Definition s7bl_ps (k : nat) : Z := A_prog_val (A_OBJ 2) + PRW_put_string_base.ps_lit k.
Definition s7bl_wv (k : nat) : Z := A_prog_val (PRW_write_value.wv_addhi_atom k) + PRW_write_value.wv_addhi_off k.
Definition s7bl_pjw : Z := A_prog_val (PRW_pj_write.pjw_addhi_atom 18) + PRW_pj_write.pjw_addhi_off 18.

(* the instance's bounds and the zero-shadow ranges' alignment (closed facts, s7bl_lit's premises) *)
Lemma s7bl_bounds_c : 4096 <= IMG_LO /\ IMG_TOP <= 0x7fff8000.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma s7bl_zs_aligned_c : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) AF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s7bl_zs_aligned_A : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow AD2l.TfibB).
Proof.
apply Forall_forall. intros r Hr. pose proof s7bl_zs_aligned_c as H. rewrite forallb_forall in H.
specialize (H r Hr). apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
split; [exact H1 | exact H2].
Qed.

(* the image's const-shadow cells are TfibB's const cells at every layout *)
Lemma s7bl_ic_A : forall ly, incl AF0m.Tfib_const_shadow (as_const AD2l.TfibB ly).
Proof.
intros ly c Hc. cbn [as_const AD2l.TfibB]. unfold AF0m.Tfib_const.
apply in_app_iff. right. apply in_app_iff. right. exact Hc.
Qed.

#[local] Abbreviation LIT_OK p l := (s7bl_lit_b IMG_LO IMG_TOP RSEGS_A AF0m.Tfib_owned_static AF0m.TFIB_ERRNO
  AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow p l = true).
#[local] Abbreviation RZ_OK p l := (s7bl_rz_b RSEGS_A AF0m.Tfib_owned_static p l = true).

(* put_string's six literals (HLIT17's [34] has no NUL; HLIT85 .. 93's lists carry it) *)
Lemma s7bl_c_ps65 : LIT_OK (s7bl_ps 65) [34] /\ RZ_OK (s7bl_ps 65) ([34] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_ps85 : LIT_OK (s7bl_ps 85) [92; 116; 0] /\ RZ_OK (s7bl_ps 85) [92; 116; 0].
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_ps87 : LIT_OK (s7bl_ps 87) [92; 110; 0] /\ RZ_OK (s7bl_ps 87) [92; 110; 0].
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_ps91 : LIT_OK (s7bl_ps 91) [92; 114; 0] /\ RZ_OK (s7bl_ps 91) [92; 114; 0].
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_ps93 : LIT_OK (s7bl_ps 93) [92; 37; 99; 0] /\ RZ_OK (s7bl_ps 93) [92; 37; 99; 0].
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_ps89 : LIT_OK (s7bl_ps 89) [92; 117; 37; 48; 52; 120; 0] /\
  RZ_OK (s7bl_ps 89) [92; 117; 37; 48; 52; 120; 0].
Proof. split; vm_compute; reflexivity. Qed.

(* write_value's ten literals (wv_lits carries no NUL; the redzone check appends it) *)
Lemma s7bl_c_wv122 : LIT_OK (s7bl_wv 122) [110; 117; 108; 108] /\ RZ_OK (s7bl_wv 122) ([110; 117; 108; 108] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv126 : LIT_OK (s7bl_wv 126) [102; 97; 108; 115; 101] /\
  RZ_OK (s7bl_wv 126) ([102; 97; 108; 115; 101] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv103 : LIT_OK (s7bl_wv 103) [116; 114; 117; 101] /\ RZ_OK (s7bl_wv 103) ([116; 114; 117; 101] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv39 : LIT_OK (s7bl_wv 39) [91] /\ RZ_OK (s7bl_wv 39) ([91] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv42 : LIT_OK (s7bl_wv 42) [123] /\ RZ_OK (s7bl_wv 42) ([123] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv59 : LIT_OK (s7bl_wv 59) [58; 32] /\ RZ_OK (s7bl_wv 59) ([58; 32] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv130 : LIT_OK (s7bl_wv 130) [58] /\ RZ_OK (s7bl_wv 130) ([58] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv151 : LIT_OK (s7bl_wv 151) [44] /\ RZ_OK (s7bl_wv 151) ([44] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv216 : LIT_OK (s7bl_wv 216) [93] /\ RZ_OK (s7bl_wv 216) ([93] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.
Lemma s7bl_c_wv219 : LIT_OK (s7bl_wv 219) [125] /\ RZ_OK (s7bl_wv 219) ([125] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.

(* pj_write's newline (.str.3) *)
Lemma s7bl_c_pjw : LIT_OK s7bl_pjw [10] /\ RZ_OK s7bl_pjw ([10] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.

(* ---- THE WITNESSES at the instance ---- *)
Section w. Context {rc : YM05.RunCeil}.
#[local] Existing Instance prh_img_A.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation RLO := (@pa_relro_lo rc A_prog_listing PA).
#[local] Abbreviation RHI := (@pa_relro_hi rc A_prog_listing PA).

(* THE GUARD: the segments every closed fact above is stated over are the walk's own (PI_prog_A's pa_segs) *)
Lemma s7bl_segs_A : SEGS = RSEGS_A.
Proof. reflexivity. Qed.
(* the premises' literal names are the listing's, by conversion *)
Lemma s7bl_pjw_nl : PRW_pj_write.PJW_NL (rc := rc) (PA := PA) = s7bl_pjw.
Proof. reflexivity. Qed.
Lemma s7bl_ps_str : forall k, PRW_put_string_base.ps_str (rc := rc) (PA := PA) k = s7bl_ps k.
Proof. intros k. reflexivity. Qed.
Lemma s7bl_wv_str : forall k, PRW_write_value.WV_STR (rc := rc) (PA := PA) k = s7bl_wv k.
Proof. intros k. reflexivity. Qed.

(* kept_img (route (a)) at each literal, exactly [p, p + n) with n the premise's length *)
Lemma s7bl_kept_img_ps65 : kept_img (PA := PA) TA (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 65) 1.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_ps 65) [34] s7bl_ic_A (proj1 s7bl_c_ps65)). Qed.
Lemma s7bl_kept_img_ps85 : kept_img (PA := PA) TA (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 85) 3.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_ps 85) [92; 116; 0] s7bl_ic_A (proj1 s7bl_c_ps85)). Qed.
Lemma s7bl_kept_img_ps87 : kept_img (PA := PA) TA (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 87) 3.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_ps 87) [92; 110; 0] s7bl_ic_A (proj1 s7bl_c_ps87)). Qed.
Lemma s7bl_kept_img_ps91 : kept_img (PA := PA) TA (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 91) 3.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_ps 91) [92; 114; 0] s7bl_ic_A (proj1 s7bl_c_ps91)). Qed.
Lemma s7bl_kept_img_ps93 : kept_img (PA := PA) TA (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 93) 4.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_ps 93) [92; 37; 99; 0] s7bl_ic_A (proj1 s7bl_c_ps93)). Qed.
Lemma s7bl_kept_img_ps89 : kept_img (PA := PA) TA (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 89) 7.
Proof.
exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_ps 89) [92; 117; 37; 48; 52; 120; 0] s7bl_ic_A (proj1 s7bl_c_ps89)).
Qed.
Lemma s7bl_kept_img_wv122 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 122) 4.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 122) [110; 117; 108; 108] s7bl_ic_A (proj1 s7bl_c_wv122)). Qed.
Lemma s7bl_kept_img_wv126 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 126) 5.
Proof.
exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 126) [102; 97; 108; 115; 101] s7bl_ic_A (proj1 s7bl_c_wv126)).
Qed.
Lemma s7bl_kept_img_wv103 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 103) 4.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 103) [116; 114; 117; 101] s7bl_ic_A (proj1 s7bl_c_wv103)). Qed.
Lemma s7bl_kept_img_wv39 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 39) 1.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 39) [91] s7bl_ic_A (proj1 s7bl_c_wv39)). Qed.
Lemma s7bl_kept_img_wv42 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 42) 1.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 42) [123] s7bl_ic_A (proj1 s7bl_c_wv42)). Qed.
Lemma s7bl_kept_img_wv59 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 59) 2.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 59) [58; 32] s7bl_ic_A (proj1 s7bl_c_wv59)). Qed.
Lemma s7bl_kept_img_wv130 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 130) 1.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 130) [58] s7bl_ic_A (proj1 s7bl_c_wv130)). Qed.
Lemma s7bl_kept_img_wv151 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 151) 1.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 151) [44] s7bl_ic_A (proj1 s7bl_c_wv151)). Qed.
Lemma s7bl_kept_img_wv216 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 216) 1.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 216) [93] s7bl_ic_A (proj1 s7bl_c_wv216)). Qed.
Lemma s7bl_kept_img_wv219 : kept_img (PA := PA) TA (PRW_write_value.WV_STR (rc := rc) (PA := PA) 219) 1.
Proof. exact (s7bl_kept_img_b (PA := PA) TA _ (s7bl_wv 219) [125] s7bl_ic_A (proj1 s7bl_c_wv219)). Qed.

(* the generic step at the instance *)
Lemma s7bl_lit_A : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  forall p l, (0 < length l)%nat -> LIT_OK p l ->
  forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS RLO RHI TA (aview SEGS (w_H W') m') ->
  src_rd (PA := PA) W' m' p l /\ kept_at (PA := PA) TA [] p (Z.of_nat (length l)).
Proof.
intros ARx HL LAWS p l Hn C. destruct s7bl_bounds_c as (HPL & HPH).
exact (s7bl_lit (PA := PA) TA ARx HL LAWS AF0m.Tfib_const_shadow p l s7bl_ic_A HPL HPH s7bl_zs_aligned_A Hn C).
Qed.

(* pj_write's HLIT (PRW_pj_write.v:208-211) *)
Lemma s7bl_pjw_hlit : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS RLO RHI TA (aview SEGS (w_H W') m') ->
  src_rd (PA := PA) W' m' (PRW_pj_write.PJW_NL (rc := rc) (PA := PA)) [10] /\
  kept_at (PA := PA) TA [] (PRW_pj_write.PJW_NL (rc := rc) (PA := PA)) 1.
Proof.
intros ARx HL LAWS. rewrite s7bl_pjw_nl.
exact (s7bl_lit_A ARx HL LAWS s7bl_pjw [10] ltac:(cbn [length]; lia) (proj1 s7bl_c_pjw)).
Qed.

(* put_string's HLIT17 (PRW_put_string_base.v:935-938; _a / _l / _t repeat it) *)
Lemma s7bl_ps_hlit17 : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS RLO RHI TA (aview SEGS (w_H W') m') ->
  src_rd (PA := PA) W' m' (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 65) [34] /\
  kept_at (PA := PA) TA [] (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 65) 1.
Proof.
intros ARx HL LAWS.
exact (s7bl_lit_A ARx HL LAWS (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 65) [34] ltac:(cbn [length]; lia)
  (proj1 s7bl_c_ps65)).
Qed.

(* put_string's HLIT85 / 87 / 91 / 93 / 89 (PRW_put_string_a.v:124-128, PRW_put_string_e.v:128-132) *)
Lemma s7bl_ps_hlit85 : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  PRW_put_string_base.ps_lit_fact (PA := PA) TA ARx 85 [92; 116; 0].
Proof.
intros ARx HL LAWS. unfold PRW_put_string_base.ps_lit_fact.
exact (s7bl_lit_A ARx HL LAWS (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 85) [92; 116; 0]
  ltac:(cbn [length]; lia) (proj1 s7bl_c_ps85)).
Qed.
Lemma s7bl_ps_hlit87 : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  PRW_put_string_base.ps_lit_fact (PA := PA) TA ARx 87 [92; 110; 0].
Proof.
intros ARx HL LAWS. unfold PRW_put_string_base.ps_lit_fact.
exact (s7bl_lit_A ARx HL LAWS (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 87) [92; 110; 0]
  ltac:(cbn [length]; lia) (proj1 s7bl_c_ps87)).
Qed.
Lemma s7bl_ps_hlit91 : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  PRW_put_string_base.ps_lit_fact (PA := PA) TA ARx 91 [92; 114; 0].
Proof.
intros ARx HL LAWS. unfold PRW_put_string_base.ps_lit_fact.
exact (s7bl_lit_A ARx HL LAWS (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 91) [92; 114; 0]
  ltac:(cbn [length]; lia) (proj1 s7bl_c_ps91)).
Qed.
Lemma s7bl_ps_hlit93 : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  PRW_put_string_base.ps_lit_fact (PA := PA) TA ARx 93 [92; 37; 99; 0].
Proof.
intros ARx HL LAWS. unfold PRW_put_string_base.ps_lit_fact.
exact (s7bl_lit_A ARx HL LAWS (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 93) [92; 37; 99; 0]
  ltac:(cbn [length]; lia) (proj1 s7bl_c_ps93)).
Qed.
Lemma s7bl_ps_hlit89 : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  PRW_put_string_base.ps_lit_fact (PA := PA) TA ARx 89 [92; 117; 37; 48; 52; 120; 0].
Proof.
intros ARx HL LAWS. unfold PRW_put_string_base.ps_lit_fact.
exact (s7bl_lit_A ARx HL LAWS (PRW_put_string_base.ps_str (rc := rc) (PA := PA) 89) [92; 117; 37; 48; 52; 120; 0]
  ltac:(cbn [length]; lia) (proj1 s7bl_c_ps89)).
Qed.

(* write_value's HLIT (PRW_write_value.v:1233-1238), all ten wv_lits *)
Lemma s7bl_wv_hlit : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TA ARx HL ->
  forall (k : nat) (bs : list Z) ly' S' Hp' (W' : world SEGS) m' md',
  In (k, bs) PRW_write_value.wv_lits ->
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS RLO RHI TA (aview SEGS (w_H W') m') ->
  src_rd (PA := PA) W' m' (PRW_write_value.WV_STR (rc := rc) (PA := PA) k) bs /\
  kept_at (PA := PA) TA [] (PRW_write_value.WV_STR (rc := rc) (PA := PA) k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (PRW_write_value.WV_STR (rc := rc) (PA := PA) k + i)).
Proof.
intros ARx HL LAWS k bs ly' S' Hp' W' m' md' Hin HAR HRO.
assert (C : (0 < length bs)%nat /\ LIT_OK (s7bl_wv k) bs).
{ unfold PRW_write_value.wv_lits in Hin. cbn [In] in Hin.
  destruct Hin as [E | [E | [E | [E | [E | [E | [E | [E | [E | [E | []]]]]]]]]]];
    injection E as Ek Eb; subst k bs; (split; [cbn [length]; lia|]).
  - exact (proj1 s7bl_c_wv122).
  - exact (proj1 s7bl_c_wv126).
  - exact (proj1 s7bl_c_wv103).
  - exact (proj1 s7bl_c_wv39).
  - exact (proj1 s7bl_c_wv42).
  - exact (proj1 s7bl_c_wv59).
  - exact (proj1 s7bl_c_wv130).
  - exact (proj1 s7bl_c_wv151).
  - exact (proj1 s7bl_c_wv216).
  - exact (proj1 s7bl_c_wv219). }
destruct C as (Hn & C).
destruct (s7bl_lit_A ARx HL LAWS (PRW_write_value.WV_STR (rc := rc) (PA := PA) k) bs Hn C ly' S' Hp' W' m' md' HAR HRO)
  as (H1 & H2).
split; [exact H1|]. split; [exact H2|].
exact (s7bl_lit_img _ _ _ _ _ _ _ _ bs C).
Qed.
End w.

About s7bl_pjw_hlit.
About s7bl_ps_hlit17.
About s7bl_ps_hlit85.
About s7bl_wv_hlit.
Print Assumptions s7bl_pjw_hlit.
Print Assumptions s7bl_ps_hlit17.
Print Assumptions s7bl_ps_hlit85.
Print Assumptions s7bl_ps_hlit87.
Print Assumptions s7bl_ps_hlit91.
Print Assumptions s7bl_ps_hlit93.
Print Assumptions s7bl_ps_hlit89.
Print Assumptions s7bl_wv_hlit.
(* which modules the short image names resolve to in this file's context (CrcBp's wrong-image trap) *)
Locate Img0.rsegs.
Locate AF0m.Tfib_const_shadow.
Locate AD2l.TfibB.
Locate A_prog_listing.
