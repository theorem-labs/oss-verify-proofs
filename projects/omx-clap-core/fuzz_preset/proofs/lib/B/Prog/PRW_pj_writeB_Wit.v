(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f48, unstripped twin c90d4fa54d43), lane
   PjwBPort of a Theorem Labs lane: the INSTANCE WITNESSES of the STATIC image premises of PRW_pj_writeB.v's Section h, each
   stated as the premise's text at the B' instance PA := PI_prog_B (the cut's lib/B/PAImg_prog.v 15fab93fe702, listing
   lib/B/Listing_prog.v c97cc46b3e13), B := YD2l.TfibB (lib/Reusable/YD2l.v, image B''s generated asyms record over
   YF0m's tables), and closed by vm_compute on a closed term (unit ruling a Theorem Labs lane 16:45Z). The segments are named
   FULLY QUALIFIED (RSEGS_B), never by a short name a plain image could capture; pjwbw_segs_B is the guard that the
   walk's pa_segs PI_prog_B is lib/B/Img0.rsegs. Proves nothing about the program.
   ported from the A' witnesses of the same premises (a working branch f75b9f6e6fa6:
   lib/A/Prog/PRW_S7bWit.v s7bw_pjw_ent / s7bw_pjw_ret / s7bw_pjw_nl_img / s7bw_pst_ok_pjw / s7bw_pstro_A /
   s7bw_memset_pc, lib/A/Prog/PRW_S7bLitWit.v s7bl_pjw_hlit with its checker, the s7bl_ lemmas): how - the same statements and
   proofs at the B' names (PI_prog_B, prh_img_B, YD2l.TfibB, YF0m's tables, IMG_LO_B / IMG_TOP_B, B_prog_relro_lo /
   _hi); the image-generic checkers come from lib/A/Prog/S1ImgCheck.v (in_img_b / pst_allb, no image file Required)
   and WalkS7aR's function-free lib/A/Prog/S7a_litrd.v (s7w_lit_rd, s7w_ro_b, s7w_zr_b, s7w_pst_clear_b); the literal
   checker of PRW_S7bLitWit.v (an A' file: it Requires image A) is copied here as pjwbl_*, unchanged but for its names.
   The premises (PRW_pj_writeB.v Section h) and their witnesses:
     segs_low  : the class field pa_segs_low of PI_prog_B (cited in PRW_pj_writeB_Inst.v);
     Hent      : pjwbw_ent        (pj_write's entry is 4 * its generated slot; B_entry_pj_write: 0x872cc, slot 5888);
     AMS       : pjwbw_ams        (a Theorem Labs lane's lib/AU/PRowSet.v prow_asan_memset_xm_B at pc_asan_memset (as_code B),
                                   glued to pa_sigma AS___asan_memset by pjwbw_memset_pc);
     HRET      : pjwbw_ret        (prh_img_B's pi_ret_sites F_pj_write RT_fuzz_free = [pj_write + 4 * 25]);
     HPSTRO    : pjwbw_pstro      (no alloc.c static in the read-only band);
     PST_ok    : pjwbw_pst_ok     (alloc.c's statics are image bytes, none owned by the runtime);
     HLIT      : pjwbw_hlit       (.str.3 "\n", read from the listing's PAddHi at pj_write's slot 18: src_rd and kept_at
                                   at any ARx with AR_laws_x, by s7w_lit_rd; the closed checks pjwbl_c_pjw);
     HIMGNL    : pjwbw_nl_img;
     S9_CF     : by projection, in PRW_pj_writeB_Inst.v.
   NO ADDRESS IS TYPED: every value is read from the listing / the instance and decided inside the closed vm_compute.
   Numerals: 25 / 18 / 4 (the premises' own slots and the instruction size), 10 (the newline byte), 0 (the NUL),
   1 (the byte before a literal), 4 (errno's width), 8, 64 (LENGTH: a granule, a shadow granule's span), 4096 (LENGTH:
   page 0), 0x7fff8000 (kLowMemEnd, the bound s7w_lit_rd asks). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowSet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgCheck S7a_litrd.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PRW_pj_writeB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* the B' segments, FULLY QUALIFIED (never the short name Img0.rsegs) *)
#[local] Abbreviation RSEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
Open Scope Z_scope.

(* ---- THE CHECKER (PRW_S7bLitWit.v's s7bl_*, copied): kept_img's static part, the ROM bytes and the hull cover of one
   literal, as one closed boolean ---- *)

(* the whole granule [g, g + 8) lies in one zero-shadow range *)
Definition pjwbl_zs_b (zs : list (Z * Z)) (g : Z) : bool :=
  existsb (fun r => (fst r <=? g) && (g + 8 <=? fst r + snd r)) zs.
Lemma pjwbl_zs_b_sound : forall zs g, pjwbl_zs_b zs g = true -> exists q m, In (q, m) zs /\ q <= g /\ g + 8 <= q + m.
Proof.
intros zs g H. apply existsb_exists in H as ([q m] & Hin & H). cbn [fst snd] in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists q, m. split; [exact Hin|]. split; [exact H1 | exact H2].
Qed.

(* a const-shadow cell of a's granule: z1 (shadow_addr a) v with v = 0 or a inside the granule's addressable prefix *)
Definition pjwbl_cell_b (a : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum y) (S O) (AV (ANum w)) => (y =? shadow_addr a) && ((w =? 0) || ((a mod 8 <? w) && (w <? 8)))
  | _ => false
  end.
Lemma pjwbl_cell_b_sound : forall a c, pjwbl_cell_b a c = true ->
  exists w, c = z1 (ANum (shadow_addr a)) w /\ (w = 0 \/ a mod 8 < w < 8).
Proof.
intros a [ca cw cv] H. unfold pjwbl_cell_b in H.
destruct ca; try discriminate H. destruct cw as [|[|cw]]; try discriminate H.
destruct cv as [e|m x]; try discriminate H. destruct e; try discriminate H.
cbv beta iota in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst.
eexists. split; [reflexivity|].
apply orb_true_iff in H2 as [H2 | H2].
- left. apply Z.eqb_eq in H2. exact H2.
- right. apply andb_prop in H2 as [H3 H4]. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4. exact (conj H3 H4).
Qed.

(* the image's ROM byte at a is v *)
Definition pjwbl_rom_b (segs : list Segment) (a v : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 a) with Some b => bv_unsigned b =? v | None => false end.
Lemma pjwbl_rom_b_sound : forall segs a v, pjwbl_rom_b segs a v = true ->
  option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) = Some v.
Proof.
intros segs a v H. unfold pjwbl_rom_b in H.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [|discriminate H].
apply Z.eqb_eq in H. cbn [option_map]. rewrite H. reflexivity.
Qed.

(* one byte a of a literal, with its value v: read-only segment, not owned static, not errno, shadow, ROM byte *)
Definition pjwbl_byte_b (segs : list Segment) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z)) (cs : list acell)
  (a v : Z) : bool :=
  s7w_ro_b segs a && negb (s7w_zr_b own a) && negb ((errno <=? a) && (a <? errno + 4)) &&
  (pjwbl_zs_b zs (a - a mod 8) || existsb (pjwbl_cell_b a) cs) && pjwbl_rom_b segs a v.
Fixpoint pjwbl_bytes_b (segs : list Segment) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z)) (cs : list acell)
  (p : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | v :: l' => pjwbl_byte_b segs own errno zs cs p v && pjwbl_bytes_b segs own errno zs cs (p + 1) l'
  end.
Lemma pjwbl_bytes_b_nth : forall segs own errno zs cs l p, pjwbl_bytes_b segs own errno zs cs p l = true ->
  forall j, (j < length l)%nat -> pjwbl_byte_b segs own errno zs cs (p + Z.of_nat j) (nth j l 0) = true.
Proof.
intros segs own errno zs cs l. induction l as [|v l IH]; intros p H j Hj; cbn [length] in Hj; [lia|].
cbn [pjwbl_bytes_b] in H. apply andb_prop in H as [H1 H2].
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. exact H1.
- cbn [nth]. replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. apply IH; [exact H2 | lia].
Qed.

(* THE CHECKER: a literal l (its bytes as the premise states them) at p *)
Definition pjwbl_lit_b (lo hi : Z) (segs : list Segment) (own : list (Z * Z)) (errno : Z) (zs : list (Z * Z))
  (cs : list acell) (p : Z) (l : list Z) : bool :=
  (lo + 64 <=? p) && (p + Z.of_nat (length l) + 64 <=? hi) && pjwbl_bytes_b segs own errno zs cs p l &&
  img_shadow_cover zs cs (p / 8 / 8 * 64) ((p + Z.of_nat (length l) - 1) / 8 / 8 * 64 + 64).

(* THE REDZONE CHECK of a literal whose bytes WITH the NUL are l: the byte before is owned static, each byte of l is
   not owned static and is the image's, the byte after l is owned static, and l ends in the NUL *)
Definition pjwbl_rz_b (segs : list Segment) (own : list (Z * Z)) (p : Z) (l : list Z) : bool :=
  s7w_zr_b own (p - 1) &&
  forallb (fun j => negb (s7w_zr_b own (p + Z.of_nat j)) && pjwbl_rom_b segs (p + Z.of_nat j) (nth j l 0))
    (seq 0 (length l)) &&
  s7w_zr_b own (p + Z.of_nat (length l)) && (last l 1 =? 0).

(* ---- THE GENERIC STEP: a literal whose boolean holds is kept_img, and (through s7w_lit_rd) a readable, kept
   source at any ARx state with arodata_okP ---- *)
(* the instance's projections are written with the Section's PA EXPLICITLY *)
Section g. Context {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := (@pa_segs rc L PA).
#[local] Abbreviation PLO := (@pa_lo rc L PA).
#[local] Abbreviation PHI := (@pa_hi rc L PA).
Variable B : asyms.

Lemma pjwbl_kept_img_b : forall cs p l, (forall ly, incl cs (as_const B ly)) ->
  pjwbl_lit_b PLO PHI segs (as_owned_static B) (as_errno B) (as_zero_shadow B) cs p l = true ->
  kept_img (PA := PA) B p (Z.of_nat (length l)).
Proof.
intros cs p l IC H. unfold pjwbl_lit_b in H.
apply andb_prop in H as [H _]. apply andb_prop in H as [H Hb]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold kept_img. split; [exact H1|]. split; [exact H2|].
intros a Ha.
pose proof (pjwbl_bytes_b_nth _ _ _ _ _ l p Hb (Z.to_nat (a - p)) ltac:(lia)) as Hy.
rewrite (Z2Nat.id (a - p) ltac:(lia)) in Hy. replace (p + (a - p)) with a in Hy by lia.
unfold pjwbl_byte_b in Hy.
apply andb_prop in Hy as [Hy _]. apply andb_prop in Hy as [Hy Hsh]. apply andb_prop in Hy as [Hy Her].
apply andb_prop in Hy as [Hro Hown]. apply negb_true_iff in Hown. apply negb_true_iff in Her.
split; [left; exact (s7w_ro_b_sound _ _ Hro)|].
split; [exact (s7w_zr_b_sound _ _ Hown)|].
split.
- intros [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite E1, E2 in Her. cbn in Her. discriminate Her.
- unfold ro_shadow_ok, in_zs. apply orb_true_iff in Hsh as [Hz | Hc].
  + left. exact (pjwbl_zs_b_sound _ _ Hz).
  + right. apply existsb_exists in Hc as (c & Hcin & Hc).
    destruct (pjwbl_cell_b_sound a c Hc) as (w & Ec & Hw). subst c.
    exists w. split; [intros ly; exact (IC ly _ Hcin) | exact Hw].
Qed.

Lemma pjwbl_lit : forall (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x segs B ARx HL ->
  forall cs p l, (forall ly, incl cs (as_const B ly)) ->
  4096 <= PLO -> PHI <= kLowMemEnd ->
  Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B) -> (0 < length l)%nat ->
  pjwbl_lit_b PLO PHI segs (as_owned_static B) (as_errno B) (as_zero_shadow B) cs p l = true ->
  forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (aview segs (w_H W) mem) ->
  src_rd (PA := PA) W mem p l /\ kept_at (PA := PA) B [] p (Z.of_nat (length l)).
Proof.
intros ARx HL LAWS cs p l IC HPL HPH ZA Hn H ly S Hp W mem md HAR HRO.
pose proof H as H'. unfold pjwbl_lit_b in H'. apply andb_prop in H' as [H' Hcv]. apply andb_prop in H' as [_ Hb].
refine (s7w_lit_rd B ARx LAWS (as_zero_shadow B) cs _ _ ly S Hp W mem md p l HPL HPH ZA Hcv (incl_refl _) IC
  (Z.le_refl _) (Z.le_refl _) HAR HRO (pjwbl_kept_img_b cs p l IC H) Hn _).
intros j Hj. pose proof (pjwbl_bytes_b_nth _ _ _ _ _ l p Hb j Hj) as Hy.
unfold pjwbl_byte_b in Hy. apply andb_prop in Hy as [_ Hr]. exact (pjwbl_rom_b_sound _ _ _ Hr).
Qed.
End g.

(* ---- THE CLOSED INSTANCE FACTS (vm_compute on closed goals) ---- *)

(* pj_write's newline (.str.3), read from the listing: the atom and the addend of the PAddHi at pj_write's slot 18 *)
Definition pjwbl_pjw : Z := B_prog_val (PRW_pj_writeB.pjw_addhi_atom 18) + PRW_pj_writeB.pjw_addhi_off 18.

(* the instance's bounds and the zero-shadow ranges' alignment (closed facts, pjwbl_lit's premises) *)
Lemma pjwbl_bounds_c : 4096 <= IMG_LO_B /\ IMG_TOP_B <= 0x7fff8000.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma pjwbl_zs_aligned_c : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) YF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pjwbl_zs_aligned_B : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow YD2l.TfibB).
Proof.
apply Forall_forall. intros r Hr. pose proof pjwbl_zs_aligned_c as H. rewrite forallb_forall in H.
specialize (H r Hr). apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
split; [exact H1 | exact H2].
Qed.

(* the image's const-shadow cells are TfibB's const cells at every layout *)
Lemma pjwbl_ic_B : forall ly, incl YF0m.Tfib_const_shadow (as_const YD2l.TfibB ly).
Proof.
intros ly c Hc. cbn [as_const YD2l.TfibB]. unfold YF0m.Tfib_const.
apply in_app_iff. right. apply in_app_iff. right. exact Hc.
Qed.

#[local] Abbreviation LIT_OK p l := (pjwbl_lit_b IMG_LO_B IMG_TOP_B RSEGS_B YF0m.Tfib_owned_static YF0m.TFIB_ERRNO
  YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow p l = true).
#[local] Abbreviation RZ_OK p l := (pjwbl_rz_b RSEGS_B YF0m.Tfib_owned_static p l = true).

(* pj_write's newline: the checker, and the redzone check (the literal is exactly one global) *)
Lemma pjwbl_c_pjw : LIT_OK pjwbl_pjw [10] /\ RZ_OK pjwbl_pjw ([10] ++ [0]).
Proof. split; vm_compute; reflexivity. Qed.

(* ---- THE WITNESSES at the instance ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val rc B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Abbreviation RLO := (@pa_relro_lo rc B_prog_listing PA).
#[local] Abbreviation RHI := (@pa_relro_hi rc B_prog_listing PA).
#[local] Abbreviation TB := YD2l.TfibB.

(* THE GUARD: the segments every closed fact here is stated over are the walk's own (PI_prog_B's pa_segs) *)
Lemma pjwbw_segs_B : SEGS = RSEGS_B.
Proof. reflexivity. Qed.

(* Hent : SIGMA AS_pj_write = BASE + AF_pj_write *)
Lemma pjwbw_ent : SIGMA AS_pj_write = BASE + PRW_pj_writeB.AF_pj_write.
Proof. cbn [pa_sigma pa_val PI_prog_B]. vm_compute. reflexivity. Qed.

(* HRET : nth 0 (pi_ret_sites F_pj_write RT_fuzz_free) 0 = BASE + AF_pj_write + 4 * 25 *)
Lemma pjwbw_ret : nth 0 (pi_ret_sites F_pj_write RT_fuzz_free) 0 = BASE + PRW_pj_writeB.AF_pj_write + 4 * 25.
Proof. cbn [pa_val PI_prog_B]. vm_compute. reflexivity. Qed.

(* HIMGNL : in_img SEGS PJW_NL *)
Lemma pjwbw_nl_img : in_img SEGS (PRW_pj_writeB.PJW_NL (rc := rc) (PA := PA)).
Proof.
unfold PRW_pj_writeB.PJW_NL. cbn [pa_val pa_segs PI_prog_B].
apply in_img_b_sound. vm_compute. reflexivity.
Qed.

(* PST_ok : alloc.c's statics are image bytes the runtime does not own *)
Lemma pjwbw_pst_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TB).
Proof.
intros a Ha. cbn [pa_segs PI_prog_B].
assert (C0 : pst_allb (in_img_b RSEGS_B) (@prh_pst prh_img_B) = true) by (vm_compute; reflexivity).
assert (C1 : pst_allb (fun x => negb (s7w_zr_b (as_owned_static TB) x)) (@prh_pst prh_img_B) = true)
  by (vm_compute; reflexivity).
split.
- apply in_img_b_sound. exact (pst_allb_sound _ _ a C0 Ha).
- apply s7w_zr_b_sound. pose proof (pst_allb_sound _ _ a C1 Ha) as H. cbv beta in H.
  apply negb_true_iff in H. exact H.
Qed.

(* HPSTRO : no static of alloc.c lies in the read-only band; one closed check over prh_pst *)
Lemma pjwbw_pst_clear_c : s7w_pst_clear_b RSEGS_B B_prog_relro_lo B_prog_relro_hi (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pjwbw_pstro : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).
Proof. intros a. exact (s7w_pst_clear_sound RSEGS_B B_prog_relro_lo B_prog_relro_hi _ pjwbw_pst_clear_c a). Qed.

(* AMS : the memset row's entry is the listing's symbol (the record's code pointer), and the row itself *)
Lemma pjwbw_memset_pc : SIGMA AS___asan_memset = pc_asan_memset (as_code TB).
Proof. cbn [pa_sigma PI_prog_B]. vm_compute. reflexivity. Qed.
Lemma pjwbw_ams : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (hl : Z), AR_laws_x SEGS TB ARx hl ->
  YGcallMxmn.aintrin_realizes_xm SEGS TB ARx OSet (SIGMA AS___asan_memset).
Proof.
intros ARx hl LAWS. rewrite pjwbw_memset_pc.
exact (PRowSet.prow_asan_memset_xm_B (fx := fx) (rc := rc) TB ARx hl LAWS YD2l.TfibB_syms).
Qed.

(* the premise's literal name is the listing's, by conversion *)
Lemma pjwbl_pjw_nl : PRW_pj_writeB.PJW_NL (rc := rc) (PA := PA) = pjwbl_pjw.
Proof. reflexivity. Qed.

(* the generic step at the instance *)
Lemma pjwbl_lit_B : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TB ARx HL ->
  forall p l, (0 < length l)%nat -> LIT_OK p l ->
  forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS RLO RHI TB (aview SEGS (w_H W') m') ->
  src_rd (PA := PA) W' m' p l /\ kept_at (PA := PA) TB [] p (Z.of_nat (length l)).
Proof.
intros ARx HL LAWS p l Hn C. destruct pjwbl_bounds_c as (HPL & HPH).
exact (pjwbl_lit (PA := PA) TB ARx HL LAWS YF0m.Tfib_const_shadow p l pjwbl_ic_B HPL HPH pjwbl_zs_aligned_B Hn C).
Qed.

(* HLIT : pj_write's newline, src_rd and kept_at at any ARx state with arodata_okP *)
Lemma pjwbw_hlit : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z), AR_laws_x SEGS TB ARx HL ->
  forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS RLO RHI TB (aview SEGS (w_H W') m') ->
  src_rd (PA := PA) W' m' (PRW_pj_writeB.PJW_NL (rc := rc) (PA := PA)) [10] /\
  kept_at (PA := PA) TB [] (PRW_pj_writeB.PJW_NL (rc := rc) (PA := PA)) 1.
Proof.
intros ARx HL LAWS. rewrite pjwbl_pjw_nl.
exact (pjwbl_lit_B ARx HL LAWS pjwbl_pjw [10] ltac:(cbn [length]; lia) (proj1 pjwbl_c_pjw)).
Qed.
End w.

About pjwbw_ent.
About pjwbw_ret.
About pjwbw_ams.
About pjwbw_hlit.
Print Assumptions pjwbw_ent.
Print Assumptions pjwbw_ret.
Print Assumptions pjwbw_nl_img.
Print Assumptions pjwbw_pst_ok.
Print Assumptions pjwbw_pstro.
Print Assumptions pjwbw_ams.
Print Assumptions pjwbw_hlit.
(* which modules the short image names resolve to in this file's context (CrcBp's wrong-image trap) *)
Locate Img0.rsegs.
Locate B_prog_listing.
Locate PI_prog_B.
Locate prh_img_B.
Locate YD2l.TfibB.
