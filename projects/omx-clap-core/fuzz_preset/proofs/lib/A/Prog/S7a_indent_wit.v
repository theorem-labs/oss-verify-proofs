(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the INSTANCE WITNESSES of indent's image premises at image A' (the #102 asan pin 1be0f53d,
   unstripped twin bff8519bbe3e; unit ruling c-omx-hpreset 16:45Z: an image premise counts only beside a lemma closed
   by vm_compute at the instance). The instance, all of it from the kit's cut 7cdbb61b5fa0: B := AD2l.TfibB (blob
   eb321db7a357), PA := PAImg_prog.PI_prog_A (h-verbs-1's A' listing v3: PAImg_prog.v 505a51ff7d08, Listing_prog.v
   7ed1529926bd), PI := PRH_Img.prh_img_A (blob 934516a622e8, the SEVEN-cell table of the #102 kit), the const-shadow
   cells AF0m.Tfib_const_shadow (blob 97f423adf6eb), the segments lib/A/Img0.rsegs (the facts' A' image), named FULLY
   QUALIFIED here (RSEGS_A; the short name Img0.rsegs can resolve to the PLAIN image's lib/Img0.v in a closure that
   loads both, CrcBp's measurement) and tied to the walk's segments by s7w_segs_A (reflexivity).
   NO ADDRESS IS TYPED IN THIS FILE: the two literals are read from the listing (s7w_nl / s7w_sp are indent's slots 9 and
   15, exactly S7a_indent's IND_NL / IND_SP), and every value derived from them (the shadow cell, the hull's granule
   range, the redzone neighbours) is computed at its use site by vm_compute on a closed goal, so a re-pin cannot leave
   a derived value stale.
   - Hent (S7a_indent.v :149; indent_holds): its witness is the listing's own vm_compute fact A_entry_indent
     (PAImg_prog.v; A': sigma 0x886e0, slot 7232). s7w_ent_A only rewrites it into Hent's spelling.
   - HLIT (S7a_indent.v :173-175; indent_holds): s7w_hlit_A, for EVERY allocator relation ARx with AR_laws_x at TfibB.
     MEASURED at A' (scratch, never pushed, build the internal file zf-fuzz-preset-3add01d1fe.build-20261029T184147Z.log): IND_NL =
     0x21440 ("\n", .str.3, bytes 10 0), IND_SP = 0x21680 ("  ", .str.23, bytes 32 32 0). THE REDZONE CHECK (the pal_lit
     lesson), proved here by vm_compute (s7w_redzone_nl / _sp): the byte before each literal is owned static (the
     previous global's redzone; measured (0x21421, 31) and (0x21667, 25)), the literal's bytes [p, p + n) and its NUL at
     p + n are NOT owned static, and its own redzone starts at p + n + 1 (measured (0x21442, 30) and (0x21683, 29)).
     The shadow: each literal's granule is PARTIAL, its const-shadow cell (at shadow_addr p) holds 02 / 03, and it lies in
     no as_zero_shadow range, so ro_shadow_ok's const-cell case carries it, kept by AR_laws_x field 16
     (alx_const_cells). The shadow hulls are covered by the const cells and the zero-shadow ranges (s7w_cover_c).
   - HPSTRO (S7a_indent.v :178; indent_holds): s7w_pstro_A. The SEVEN statics of prh_img_A (s7w_pst_A; PrhImg's
     pi_g_live / peak / count / fail / ran_out / most / own_ran_out, PRH_Base.v :173-179 @ef7c8ca98529) lie in rsegs'
     writable segments, outside both read-only segments and outside the relro range [0xa19f0, 0xa3000)
     (s7w_pst_clear_c, by vm_compute).
   THE GENERIC STEP s7w_lit_rd and the closed-check helpers (s7w_ro_b, s7w_zr_b, s7w_is_z1 / s7w_cell_in,
   s7w_pst_clear_b) live in the function-free lib/A/Prog/S7a_litrd.v (the ONE copy; the writer row's literal witnesses
   cite it too). The instance discharges its zero-shadow alignment premise by vm_compute (s7w_zs_aligned_A).
   Every vm_compute here is on a CLOSED goal (RSEGS_A, TfibB's lists, the A_prog_* tables, the listing).
   Numerals: 9 / 15 (indent's slots that form the two literals), 10, 32 (the literals' bytes), 2, 3 (the cells'
   values, checked by vm_compute), 1, 2 (LENGTH: the literals), 0x5dd560, 0x5dd580, 0x5dd5a0, 0xa65c0, 0x5dd5c0,
   0xa65e0, 0x5dd540 (ADDRESS: the seven statics, = prh_pst prh_img_A by s7w_pst_A, reflexivity), 8, 1 (LENGTH: their
   widths), 8, 64 (LENGTH: a granule, a shadow granule's span), 4096 (LENGTH: page 0). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S7a_litrd S7a_indent.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* the A' segments, FULLY QUALIFIED (never the short name Img0.rsegs) *)
#[local] Notation RSEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
Open Scope Z_scope.

(* ---- the two literals, read from the listing (S7a_indent's IND_NL / IND_SP without the class) ---- *)
Definition s7w_nl : Z := A_prog_val (ind_addhi_atom 9) + ind_addhi_off 9.
Definition s7w_sp : Z := A_prog_val (ind_addhi_atom 15) + ind_addhi_off 15.

(* ---- the closed instance facts (vm_compute on closed goals) ---- *)
(* Hent from the listing's own fact A_entry_indent *)
Lemma s7w_ent_c : A_prog_sigma AS_indent = A_prog_val A_TEXT + AF_indent.
Proof.
destruct A_entry_indent as (E1 & E2). unfold AF_indent, IND_SLOT. rewrite E1, E2. vm_compute. reflexivity.
Qed.
(* the literals' bytes in the image *)
Definition s7w_rom (a : Z) : option Z := option_map (fun b : byte => bv_unsigned b) (seg_rom RSEGS_A (Z_to_bv 64 a)).
Lemma s7w_rom_c : s7w_rom s7w_nl = Some 10 /\ s7w_rom (s7w_nl + 1) = Some 0 /\
  s7w_rom s7w_sp = Some 32 /\ s7w_rom (s7w_sp + 1) = Some 32 /\ s7w_rom (s7w_sp + 2) = Some 0.
Proof. split; [|split; [|split; [|split]]]; vm_compute; reflexivity. Qed.

(* the bytes HLIT reads are read-only and not owned static *)
Lemma s7w_bytes_c : forall a, a = s7w_nl \/ a = s7w_sp \/ a = s7w_sp + 1 ->
  s7w_ro_b RSEGS_A a = true /\ s7w_zr_b AF0m.Tfib_owned_static a = false.
Proof. intros a [-> | [-> | ->]]; split; vm_compute; reflexivity. Qed.
(* THE REDZONE CHECK: the byte before each literal is owned (the previous global's redzone), the literal and its NUL
   are not, and its own redzone starts right after the NUL *)
Lemma s7w_redzone_nl : s7w_zr_b AF0m.Tfib_owned_static (s7w_nl - 1) = true /\
  s7w_zr_b AF0m.Tfib_owned_static s7w_nl = false /\ s7w_zr_b AF0m.Tfib_owned_static (s7w_nl + 1) = false /\
  s7w_zr_b AF0m.Tfib_owned_static (s7w_nl + 2) = true.
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma s7w_redzone_sp : s7w_zr_b AF0m.Tfib_owned_static (s7w_sp - 1) = true /\
  s7w_zr_b AF0m.Tfib_owned_static s7w_sp = false /\ s7w_zr_b AF0m.Tfib_owned_static (s7w_sp + 1) = false /\
  s7w_zr_b AF0m.Tfib_owned_static (s7w_sp + 2) = false /\ s7w_zr_b AF0m.Tfib_owned_static (s7w_sp + 3) = true.
Proof. split; [|split; [|split; [|split]]]; vm_compute; reflexivity. Qed.

(* the literals' const-shadow cells, at shadow_addr of the literal (computed) *)
Lemma s7w_cell_nl_c : existsb (s7w_is_z1 (shadow_addr s7w_nl) 2) AF0m.Tfib_const_shadow = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s7w_cell_sp_c : existsb (s7w_is_z1 (shadow_addr s7w_sp) 3) AF0m.Tfib_const_shadow = true /\
  shadow_addr (s7w_sp + 1) = shadow_addr s7w_sp.
Proof. split; vm_compute; reflexivity. Qed.
(* the shadow hulls (the granule range of each literal's hull, computed): every granule's shadow byte is a const cell or
   in a zero-shadow range *)
Lemma s7w_cover_c :
  img_shadow_cover AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow (s7w_nl / 8 / 8 * 64) ((s7w_nl + 1 - 1) / 8 / 8 * 64 + 64)
    = true /\
  img_shadow_cover AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow (s7w_sp / 8 / 8 * 64) ((s7w_sp + 2 - 1) / 8 / 8 * 64 + 64)
    = true.
Proof. split; vm_compute; reflexivity. Qed.
(* the image's zero-shadow ranges are granule-aligned *)
Lemma s7w_zs_aligned_c : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) AF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s7w_zs_aligned_A : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow AD2l.TfibB).
Proof.
apply Forall_forall. intros r Hr. pose proof s7w_zs_aligned_c as H. rewrite forallb_forall in H.
specialize (H r Hr). apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
split; [exact H1 | exact H2].
Qed.
(* the image bounds kept_img states over (pa_lo / pa_hi of PI_prog_A are IMG_LO / IMG_TOP) *)
Lemma s7w_bounds_c : 4096 <= IMG_LO /\ IMG_TOP <= 0x7fff8000 /\
  IMG_LO + 64 <= s7w_nl /\ s7w_nl + 1 + 64 <= IMG_TOP /\ IMG_LO + 64 <= s7w_sp /\ s7w_sp + 2 + 64 <= IMG_TOP /\
  ~ (AF0m.TFIB_ERRNO <= s7w_nl < AF0m.TFIB_ERRNO + 4) /\ ~ (AF0m.TFIB_ERRNO <= s7w_sp + 1 < AF0m.TFIB_ERRNO + 4) /\
  ~ (AF0m.TFIB_ERRNO <= s7w_sp < AF0m.TFIB_ERRNO + 4).
Proof.
assert (L : forall x y, (x <=? y) = true -> x <= y) by (intros x y H; apply Z.leb_le; exact H).
assert (N : forall x e, (x <? e) = true -> ~ (e <= x < e + 4)) by (intros x e H [H1 _]; apply Z.ltb_lt in H; lia).
split; [apply L; vm_compute; reflexivity|]. split; [apply L; vm_compute; reflexivity|].
split; [apply L; vm_compute; reflexivity|]. split; [apply L; vm_compute; reflexivity|].
split; [apply L; vm_compute; reflexivity|]. split; [apply L; vm_compute; reflexivity|].
split; [apply N; vm_compute; reflexivity|]. split; [apply N; vm_compute; reflexivity|].
apply N; vm_compute; reflexivity.
Qed.

(* the seven statics of the #102 table, by conversion *)
Lemma s7w_pst_A : @prh_pst prh_img_A =
  [(0x5dd560, 8); (0x5dd580, 8); (0x5dd5a0, 8); (0xa65c0, 8); (0x5dd5c0, 1); (0xa65e0, 8); (0x5dd540, 1)].
Proof. reflexivity. Qed.
Lemma s7w_pst_clear_c : s7w_pst_clear_b RSEGS_A A_prog_relro_lo A_prog_relro_hi
  [(0x5dd560, 8); (0x5dd580, 8); (0x5dd5a0, 8); (0xa65c0, 8); (0x5dd5c0, 1); (0xa65e0, 8); (0x5dd540, 1)] = true.
Proof. vm_compute. reflexivity. Qed.


(* ---- THE WITNESSES at the instance ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation TA := AD2l.TfibB.

(* THE GUARD: the segments every closed fact above is stated over are the walk's own (PI_prog_A's pa_segs) *)
Lemma s7w_segs_A : @pa_segs rc A_prog_listing PA = RSEGS_A.
Proof. reflexivity. Qed.
(* S7a_indent's literals are the listing's, by conversion *)
Lemma s7w_ind_nl : IND_NL (rc := rc) (PA := PA) = s7w_nl.
Proof. reflexivity. Qed.
Lemma s7w_ind_sp : IND_SP (rc := rc) (PA := PA) = s7w_sp.
Proof. reflexivity. Qed.

(* Hent *)
Lemma s7w_ent_A : @pa_sigma rc A_prog_listing PA AS_indent = @pa_val rc A_prog_listing PA A_TEXT + AF_indent.
Proof. exact s7w_ent_c. Qed.

(* kept_img (route (a)) at the two literals: exactly [p, p + n) *)
Lemma s7w_kept_img_nl : kept_img (rc := rc) (PA := PA) TA s7w_nl 1.
Proof.
destruct s7w_bounds_c as (_ & _ & B1 & B2 & _ & _ & BE1 & _).
unfold kept_img. split; [exact B1|]. split; [exact B2|].
intros a Ha. assert (E : a = s7w_nl) by lia. subst a.
destruct (s7w_bytes_c s7w_nl ltac:(left; reflexivity)) as (Hr & Ho).
split; [left; exact (s7w_ro_b_sound _ _ Hr)|].
split; [exact (s7w_zr_b_sound _ _ Ho)|].
split; [exact BE1|].
right. exists 2. split.
- intros ly. cbn [as_const AD2l.TfibB]. unfold AF0m.Tfib_const.
  apply in_app_iff. right. apply in_app_iff. right. exact (s7w_cell_in _ _ _ s7w_cell_nl_c).
- right. split; apply Z.ltb_lt; vm_compute; reflexivity.
Qed.
Lemma s7w_kept_img_sp : kept_img (rc := rc) (PA := PA) TA s7w_sp 2.
Proof.
destruct s7w_bounds_c as (_ & _ & _ & _ & B1 & B2 & _ & BE2 & BE3).
destruct s7w_cell_sp_c as (C1 & C2).
unfold kept_img. split; [exact B1|]. split; [exact B2|].
intros a Ha. assert (E : a = s7w_sp \/ a = s7w_sp + 1) by lia.
destruct (s7w_bytes_c a ltac:(right; exact E)) as (Hr & Ho).
split; [left; exact (s7w_ro_b_sound _ _ Hr)|].
split; [exact (s7w_zr_b_sound _ _ Ho)|].
split; [destruct E as [-> | ->]; [exact BE3 | exact BE2]|].
right. exists 3. split.
- intros ly. cbn [as_const AD2l.TfibB]. unfold AF0m.Tfib_const.
  apply in_app_iff. right. apply in_app_iff. right.
  destruct E as [-> | ->]; [|rewrite C2]; exact (s7w_cell_in _ _ _ C1).
- right. destruct E as [-> | ->]; split; apply Z.ltb_lt; vm_compute; reflexivity.
Qed.

(* HLIT *)
Lemma s7w_hlit_A : forall (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
    (HL : Z),
  AR_laws_x SEGS TA ARx HL ->
  forall ly S Hp (W : world SEGS) mem md,
  ARx ly S Hp W mem md ->
  arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) TA (aview SEGS (w_H W) mem) ->
  (src_rd (PA := PA) W mem (IND_NL (rc := rc) (PA := PA)) [10] /\
   kept_at (PA := PA) TA [] (IND_NL (rc := rc) (PA := PA)) 1) /\
  (src_rd (PA := PA) W mem (IND_SP (rc := rc) (PA := PA)) [32; 32] /\
   kept_at (PA := PA) TA [] (IND_SP (rc := rc) (PA := PA)) 2).
Proof.
intros ARx HL LAWS ly S Hp W mem md HAR HRO.
rewrite s7w_ind_nl, s7w_ind_sp.
destruct s7w_bounds_c as (HPL & HPH & _).
destruct s7w_cover_c as (CV1 & CV2).
destruct s7w_rom_c as (R1 & _ & R2 & R3 & _).
assert (IC : forall ly, incl AF0m.Tfib_const_shadow (as_const TA ly)).
{ intros ly' c Hc. cbn [as_const AD2l.TfibB]. unfold AF0m.Tfib_const.
  apply in_app_iff. right. apply in_app_iff. right. exact Hc. }
assert (IZ : incl AF0m.Tfib_zero_shadow (as_zero_shadow TA)) by (intros r Hr; exact Hr).
assert (RN : forall j, (j < length [10])%nat ->
  option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (s7w_nl + Z.of_nat j))) = Some (nth j [10] 0)).
{ intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth Z.of_nat]. rewrite Z.add_0_r.
  exact R1. }
assert (RS : forall j, (j < length [32; 32])%nat ->
  option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (s7w_sp + Z.of_nat j))) =
    Some (nth j [32; 32] 0)).
{ intros j Hj. cbn [length] in Hj. destruct j as [|[|j]].
  - cbn [nth Z.of_nat]. rewrite Z.add_0_r. exact R2.
  - cbn [nth]. exact R3.
  - lia. }
split.
- exact (s7w_lit_rd TA ARx LAWS AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow _ _ ly S Hp W mem md s7w_nl [10]
    HPL HPH s7w_zs_aligned_A CV1 IZ IC (Z.le_refl _) (Z.le_refl _) HAR HRO s7w_kept_img_nl
    ltac:(cbn [length]; lia) RN).
- exact (s7w_lit_rd TA ARx LAWS AF0m.Tfib_zero_shadow AF0m.Tfib_const_shadow _ _ ly S Hp W mem md s7w_sp [32; 32]
    HPL HPH s7w_zs_aligned_A CV2 IZ IC (Z.le_refl _) (Z.le_refl _) HAR HRO s7w_kept_img_sp
    ltac:(cbn [length]; lia) RS).
Qed.

(* HPSTRO *)
Lemma s7w_pstro_A : forall a,
  in_roP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) a ->
  ~ Exists (in_zr a) (@prh_pst prh_img_A).
Proof.
intros a. rewrite s7w_pst_A. exact (s7w_pst_clear_sound RSEGS_A A_prog_relro_lo A_prog_relro_hi _ s7w_pst_clear_c a).
Qed.

(* the TYPE CHECK: the three witnesses are exactly indent_holds's premises Hent, HLIT and HPSTRO at the instance
   (a Check, not a lemma: indent_holds is not restated here) *)
Check (fun (RL : PrhRoomLive) (SK : YI16.sink_head)
           (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop) (HL : Z)
           (LAWS : AR_laws_x SEGS TA ARx HL) (TL : PALib TA) (CTX0 : list (list Z)) HPUT =>
  indent_holds (RL := RL) (SK := SK) (PA := PA) TA ARx HL LAWS TL s7w_ent_A CTX0 HPUT
    (s7w_hlit_A ARx HL LAWS) s7w_pstro_A).
End w.

Print Assumptions s7w_ent_A.
Print Assumptions s7w_hlit_A.
Print Assumptions s7w_pstro_A.
Print Assumptions S7a_indent.indent_holds.
(* which modules the short image names resolve to in this file's context (CrcBp's wrong-image trap) *)
Locate Img0.rsegs.
Locate rsegs.
Locate AF0m.Tfib_const_shadow.
Locate AD2l.TfibB.
Locate A_prog_listing.
(* indent's top: its premises and the image it is stated at (rule 7's check: every PA / L / PI argument names image A) *)
Set Printing Implicit.
Unset Printing Notations.
About S7a_indent.indent_holds.
Set Printing Notations.
Unset Printing Implicit.
