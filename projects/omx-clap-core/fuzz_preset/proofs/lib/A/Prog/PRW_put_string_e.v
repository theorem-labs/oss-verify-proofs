(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ex_ws_x.v, with its module paths and module names changed; 1951 of its 2020 lines of code are new or changed and 807 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PRW_put_string_base.v; 1189 of its 1333 lines of code are new or changed and 1876 lines of the source are left out. *)
(* fuzz_preset image A, slice S7b (WalkS7b.S7bPutString.PsEsc; #102 re-fit WalkS7bR.PutStringF.PsEscF): put_string's
   walk, the ESCAPE stretch, over PRW_put_string_base.v: from the escape join ps_esc (A 0x88518, the return of the run
   put) through the escape's write into u = F + 32 (__asan_memcpy of .str.20 / .str.19 / .str.21 for c = 9 / 10 / 13,
   else __wrap_snprintf with "\\%c" (c = 34 / 92) or "\\u%04x"), __wrap_strlen (u), put (o, u, len) (A 0x885b0) and
   `mv s10, s4`, to the re-poison join ps_next (A 0x885b8).
   KIT: the kit's cut 7cdbb61b5fa0. The snprintf call is the engine's
   ROW YGcallSnp.asnprintf_realizes_xrom (owner a Theorem Labs lane) at its instance, through YGcallSnpCk.snp_esc_of_xrom: the
   row returns at SOME float state fx' (f10 / fcsr free, fs0-fs11 kept, frm = 0), so everything after it (strlen, put,
   the re-poison join) runs at fx' (the internal file REFIT-WRITER.md's float-threading design): those stretches live in Section fl,
   CLOSED before the escape's own Section fl2, so they are generic in the float state; the callee texts they read
   (put's tput_specX, __wrap_strlen's astrlen_realizes_xrom) are Section hypotheses quantified over the float state.
   The memcpy arms keep the float state.
   THE ROW'S INSTANCE (WalkS7bR.SnpInstR, 2026-10-29): SNP is stated at the parameters that a Theorem Labs lane's row
   instance snprintf_xrom_A (lib/A/PSnpSnpRoot.v:140, blob 4edc9be9a050 at the cut; first read at int102 19612fe2ec90) provides: the format family FF_esc IMG_LO
   gcan (its FF_preset_x lo got at lo := IMG_LO, got := gcan; the two families have the same body), the window
   STK_RT_PRINTF (>= its 8160), the canary cells gcan -> can, the image range [IMG_LO, IMG_TOP) and the read-only
   ranges ps_snp_cr (its PSnpPcom.PCM_CR, PSnpPcom.v:83-84: the same body over SEGS). SNPI is STATIC (ps_snp_img: image
   facts about SEGS, B and the listing, no state; witness PRW_S7bWit.v s7bw_ps_snp_img). The facts the row asks of the
   CALL STATE are derived here from the laws: the canary cells (pe_canary, AR_laws_x field 16 alx_const_cells), the
   read-only ranges' view (pe_consts_view, ps_commonR's arodata_okP and field 16), the frame above the image range
   (pe_frame_top, fields 17 alx_img and 18 alx_layout_ok).
   No address literal: entries, return sites and literals are by name (A_prog_slot, the listing's PAddHi addends).
   THE RE-HIDING MOVE: the whole escape runs after the opening-quote put, and put reallocs when it grows (a crossing
   call), so the escape's joins are ps_commonR at wle' SEGS RZ_cf, its journals are at that relation, its runs and
   branches are the R forms there, and it concludes SRr' SEGS RZ_cf. The three runtime calls keep the world: the
   strlen and memcpy rules (aj_strlen_at_xromR, aj_intrin_at_xmR) and the snprintf row lift by SRr_SRr'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the step relation over a world relation and the re-hiding relation (SRrG, wle', SRr' with its bind / mono,
   paj_branchR) and the fixed zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_S7bKit PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S7a_WriterRet S7a_WriterLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_put_string_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0b YO0c FMsnprintfShared YGcallSnp YGcallSnpCk.
(* the cell-to-bytes helper (ImgBase.cell_holds_val_mem, image-free) for the canary cell B's constant cells keep *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia must see the division equations: the realignment is a mod 32 (never rely on an inherited flag) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's generated numbers (PRH_Img.v) are the PrhImg the texts read *)
#[local] Existing Instance prh_img_A.

(* the row's float clause gives fregs_kept_x (YCbqG.v:26): it keeps every f register but f10 *)
Lemma pe_fk_of_row : forall f f' : YK11.FPState,
  (forall k : bv 5, bv_unsigned k <> 10 ->
     LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs f') k =
     LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs f) k) ->
  fregs_kept_x f f'.
Proof.
intros f f' H r Hr. apply H.
assert (Hc : r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
  r = 26 \/ r = 27) by (clear - Hr; lia).
repeat (destruct Hc as [-> | Hc]; [intros Hx; vm_compute in Hx; discriminate Hx |]).
subst r. intros Hx. vm_compute in Hx. discriminate Hx.
Qed.

Section d. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
(* The kit's non-primary room invariant (PRH_Base.v PrhRoomLive, owner a Theorem Labs lane) *)
Context {RL : PrhRoomLive}.
Section f.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v), at this Section's run ceiling *)
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

Section h.
(* this file's Section hypotheses are the ones its lemmas read (the shared put_string header's others are unused here) *)
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the engine's / instance's side condition (YGcallSx.v Section x, owner a Theorem Labs lane) *)
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, discharged by a8's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
(* every live fake frame's shadow hull is visible (PRW_HShadow.v ARx_frame_hull_vis, owner a8 YGcfFsVis.v) *)
Hypothesis HFHULL : ARx_frame_hull_vis SEGS ARx.
(* image fact, discharged at PI_prog_A by reflexivity (PAImg_prog.v:408 pa_lo := IMG_LO; pa_hi := IMG_TOP): the
   instance's image band is image A's (kept_at's image arms are per instance since 2026-10-29; WalkS7bR's ruling) *)
Hypothesis HPAB : pa_lo = IMG_LO /\ pa_hi = IMG_TOP.
(* alloc.c's six statics and fuzz_preset.c's g_own_ran_out (the ledger's globals, prh_pst, PRH_Base.v:752-755) are image bytes the runtime does not own, apart from errno, and none
   lies in the read-only band (YC1fPx's PST_ok; the S7b walk's pj_write takes the same texts; image facts) *)
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).
(* the generic memory invariant (h-hpreset-7's 12:18Z ruling) and its laws; the walk crosses calls *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
Local Notation AJR R := (ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R).
Variable CTX0 : list (list Z).
(* put's text (tput_specX after the re-hiding move: SRr' SEGS RZ_cf, its post at wle' SEGS RZ_cf; its
   premise length rp_os <= 4, the bound PresetDrvHeadroomA.v's drv_cf_headroom_at_call_A takes, comes from ps_pre
   through ps_put_step), at EVERY float state: the escape's put runs after the snprintf row, at the float state the
   row returns (the internal file REFIT-WRITER.md's float-threading design, point 4) *)
Hypothesis PUT : forall fx0 : YK11.FPState, tput_specX (fx := fx0) (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
(* __wrap_strlen's text, the read-only (arodata) form with the keep (YGcallMxmn.v astrlen_realizes_xrom; owner R2 /
   a Theorem Labs lane), at its entry, at EVERY float state (it runs after the snprintf row, point 4 as PUT) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  astrlen_realizes_xrom (fx := fx0) SEGS B ARx pa_relro_lo pa_relro_hi (SIGMA AS___wrap_strlen).
(* image facts, discharged at PI_prog_A (HLIT17's form, the base's ps_lit_fact): the escape literals put_string copies
   with __asan_memcpy (.str.20 "\\t", .str.19 "\\n", .str.21 "\\r", with the NUL) and its two snprintf formats
   (.str.18 "\\%c", .str.22 "\\u%04x", with the NUL): their bytes are the image's and their home is read-only, at
   every state *)
Local Notation ps_lit_fact := (ps_lit_fact B ARx).
Hypothesis HLIT85 : ps_lit_fact 85 [92; 116; 0].
Hypothesis HLIT87 : ps_lit_fact 87 [92; 110; 0].
Hypothesis HLIT91 : ps_lit_fact 91 [92; 114; 0].
Hypothesis HLIT93 : ps_lit_fact 93 [92; 37; 99; 0].
Hypothesis HLIT89 : ps_lit_fact 89 [92; 117; 37; 48; 52; 120; 0].
(* the base file's definitions and lemmas at this section's variables and hypotheses (each reads the float state of
   the Section it is used in; at another float state the walk writes the base name with (fx := ..)) *)
Local Notation ps_pre := (ps_pre B ARx CTX0).
Local Notation ps_commonR := (ps_commonR B ARx Pm).
Local Notation ps_Qfin := (ps_Qfin B ARx Pm).
Local Notation ps_esc := (ps_esc B ARx Pm).
Local Notation ps_next := (ps_next B ARx Pm).
Local Notation ps_common_frameR := (ps_common_frameR B ARx LAWS segs_low HW PST_ok Pm CTX0).
Local Notation ps_common_runR := (ps_common_runR B ARx LAWS HW PST_ok Pm).

(* ---- the escape's own symbolic states (no float state) ---- *)
(* the realigned slots R + 24 .. R + 64 (the five literal addresses), as atoms 32 .. 36 of the seat's env *)
Definition pe_rreg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 64 24 24
    [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0));
     YP09.mkChunk 48 (CVal 8 (SOff 35 0)); YP09.mkChunk 56 (CVal 8 (SOff 36 0))].
Definition pe_extra : list word :=
  [Z_to_bv 64 (ps_str 91); Z_to_bv 64 (ps_str 89); Z_to_bv 64 (ps_str 87); Z_to_bv 64 (ps_str 85); Z_to_bv 64 (ps_str 93)].
Definition pe_E (regs : bvmap 5 word) : env := Eimg (Ereg regs pe_extra).
Definition pe_ss428 : sstate := mkSS (AF_put_string + 428) sr_atoms [pe_rreg] None (mkFacts [] [] []).
Definition pe_ss0 (k : Z) : sstate := mkSS (AF_put_string + k) sr_atoms [] None (mkFacts [] [] []).
(* the callee-saved registers 2, 3, 4, 8, 9, 18 .. 27 *)
Definition pe_csl : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
(* the escape buffer's bytes: the escape of byte i and its NUL at u = F + 32 *)
Definition pe_u (X : psx) (pos : Z) (i : nat) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall j, (j < length (WriterSpec.esc (nth i (x_bs X) 0%Z) ++ [0%Z]))%nat ->
    aview SEGS (w_H Wc) memc (x_F X pos + 32 + Z.of_nat j) = Some (nth j (WriterSpec.esc (nth i (x_bs X) 0) ++ [0]) 0).
(* ---- the snprintf row's instance (a Theorem Labs lane's snprintf_xrom_A, lib/A/PSnpSnpRoot.v:140, blob 4edc9be9a050 at the cut) ----
   the row's read-only ranges: each non-writable segment of the image as (base, size). This is the body of the
   instance's PSnpPcom.PCM_CR (PSnpPcom.v:83-84 there) over SEGS, so at PA := PI_prog_A it is that list. *)
Definition ps_snp_cr : list (Z * Z) :=
  map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (List.filter (fun s => negb (seg_writable s)) SEGS).
(* the STATIC image facts of the instance at the canary cells gcan -> can (no state: facts about SEGS, B's records and
   the listing; witness at PI_prog_A / AD2l.TfibB: PRW_S7bWit.v s7bw_ps_snp_img):
   - the two snprintf formats (.str.18 "\\%c", .str.22 "\\u%04x", each with its NUL) end below the GOT cell gcan, the
     format family's upper bound (FF_esc IMG_LO gcan);
   - the two cells are image bytes, and each byte of the canary cell has an image byte (so it reads at every state);
   - the GOT cell is one of B's constant cells, holding can;
   - every read-only range is nonempty and apart from errno;
   - a byte of a read-only range that is an owned static is pinned to its image byte by one of B's constant cells;
   - the image's last segment ends in IMG_TOP's page (so the layout's page-aligned image extent reaches IMG_TOP). *)
Definition ps_snp_img (gcan can : Z) : Prop :=
  ps_str 93 + Z.of_nat (length YGcallSnpCk.snp_esc_fmt_c) + 1 <= gcan /\
  ps_str 89 + Z.of_nat (length YGcallSnpCk.snp_esc_fmt_x) + 1 <= gcan /\
  (forall j, 0 <= j < 8 ->
     in_img SEGS (gcan + j) /\ in_img SEGS (can + j) /\ seg_rom SEGS (Z_to_bv 64 (can + j)) <> None) /\
  (forall ly, In (z8 (ANum gcan) can) (as_const B ly)) /\
  Forall (fun r => 0 < snd r /\ zdisjoint r (as_errno B, 4)) ps_snp_cr /\
  (forall ly a, Exists (in_zr a) ps_snp_cr -> Exists (in_zr a) (as_owned_static B) ->
     exists p (w : nat) v, In (ACell (ANum p) w (AV (ANum v))) (as_const B ly) /\ p <= a < p + Z.of_nat w /\
       option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a)) =
       Some (YG0f.le_byte v w (Z.to_nat (a - p)))) /\
  (exists sg, In sg SEGS /\ IMG_TOP - 4096 < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).

(* a byte of a read-only range is a byte of a non-writable segment *)
Lemma pe_cr_seg : forall a, Exists (in_zr a) ps_snp_cr ->
  exists s, In s SEGS /\ seg_writable s = false /\
    Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold ps_snp_cr in Hr.
apply in_map_iff in Hr as (s & <- & Hs). apply filter_In in Hs as (Hs & Hw).
exists s. split; [exact Hs|]. split; [exact (proj1 (Bool.negb_true_iff _) Hw) | exact Ha].
Qed.
Lemma pe_cr_img : forall r, In r ps_snp_cr -> forall a, fst r <= a < fst r + snd r -> in_img SEGS a.
Proof.
intros r Hr a Ha.
assert (He : Exists (in_zr a) ps_snp_cr) by (apply Exists_exists; exists r; split; [exact Hr | exact Ha]).
destruct (pe_cr_seg a He) as (s & Hs & _ & Hsa). exists s. split; [exact Hs | exact Hsa].
Qed.
(* the canary cells at every ARx state: the GOT cell holds can (B's constant cell, kept by AR_laws_x field 16
   alx_const_cells), and the canary cell's eight bytes read (image bytes) *)
Lemma pe_canary : forall gcan can ly S Hp (W : world SEGS) mem md, ps_snp_img gcan can -> ARx ly S Hp W mem md ->
  exists cval, val_mem SEGS (mrestrict (w_H W) mem) gcan 8 can /\ val_mem SEGS (mrestrict (w_H W) mem) can 8 cval.
Proof.
intros gcan can ly S Hp W mem md (_ & _ & Hcimg & Hgc & _) HAR.
assert (Hv : forall i, 0 <= i < 8 -> aview SEGS (w_H W) mem (can + i) <> None).
{ intros i Hi. destruct (Hcimg i Hi) as (_ & _ & Hr). unfold aview, mbyte.
  destruct (mrestrict (w_H W) mem (Z_to_bv 64 (can + i))); [cbn [option_map]; discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 (can + i))); [cbn [option_map]; discriminate | exfalso; exact (Hr eq_refl)]. }
destruct (PRW_put_string_base.rdword_some_of (aview SEGS (w_H W) mem) can Hv) as (cval & Hcv).
exists cval. split.
- pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARx LAWS ly S Hp W mem md HAR) _ (Hgc ly)) as Hc.
  exact (ImgBase.cell_holds_val_mem SEGS B ly (w_H W) mem (ANum gcan) 8 (ANum can) Hc).
- exact (val_mem_of_rdword SEGS (w_H W) mem can cval Hcv).
Qed.
(* the read-only ranges read as the image at every ARx state with the read-only view: a byte off the owned statics by
   the view (fpre's arodata_okP, which ps_commonR carries), an owned static's byte by B's constant cells (field 16) *)
Lemma pe_consts_view : forall gcan can ly S Hp (W : world SEGS) mem md, ps_snp_img gcan can -> ARx ly S Hp W mem md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  FMsnprintfShared.consts_view SEGS W mem ps_snp_cr.
Proof.
intros gcan can ly S Hp W mem md (_ & _ & _ & _ & Hcr & Hpin & _) HAR Hro a Ha.
assert (Hdec : forall r, {in_zr a r} + {~ in_zr a r}).
{ intros r. unfold in_zr. destruct (Z_le_dec (fst r) a) as [H1 | H1].
  - destruct (Z_lt_dec a (fst r + snd r)) as [H2 | H2]; [left; split; assumption | right; intros (_ & H); contradiction].
  - right. intros (H & _). contradiction. }
destruct (@Exists_dec _ (in_zr a) (as_owned_static B) Hdec) as [Hown | Hnown].
- destruct (Hpin ly a Ha Hown) as (p & w & v & Hin & Hpa & Hrom).
  pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARx LAWS ly S Hp W mem md HAR) _ Hin) as Hc.
  cbn [cell_holds c_at c_val c_w aeval] in Hc.
  specialize (Hc (Z.to_nat (a - p)) ltac:(clear - Hpa; lia)).
  rewrite Z2Nat.id in Hc by (clear - Hpa; lia). replace (p + (a - p)) with a in Hc by lia.
  rewrite Hc, Hrom. reflexivity.
- apply Hro.
  + left. destruct (pe_cr_seg a Ha) as (s & Hs & Hw & Hsa). exists s. split; [exact Hs|]. split; [exact Hw | exact Hsa].
  + exact Hnown.
  + intros He. apply Exists_exists in Ha as (r & Hr & Har). rewrite Forall_forall in Hcr.
    destruct (Hcr r Hr) as (_ & Hd). unfold zdisjoint, in_zr in *. cbn [fst snd] in *. clear - Hd Har He. lia.
Qed.
(* a live fake frame lies at or above IMG_TOP: at or above the end of the layout's image extent (AR_laws_x field 17
   alx_img), which is page-aligned (field 18 alx_layout_ok, layout_ok's lo_img) and past the image's last segment,
   which ends in IMG_TOP's page *)
Lemma pe_frame_top : forall gcan can ly S Hp (W : world SEGS) mem md cid pos, ps_snp_img gcan can ->
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> IMG_TOP <= frame_addr ly cid pos.
Proof.
intros gcan can ly S Hp W mem md cid pos (_ & _ & _ & _ & _ & _ & (sg & Hsg & Htop)) HAR Hin.
destruct (alx_img SEGS B ARx LAWS ly S Hp W mem md HAR) as (Hcov & Hfr).
pose proof (Hfr cid pos Hin) as Hf. pose proof (Hcov sg Hsg) as (_ & Hs).
pose proof (lo_img _ (alx_layout_ok SEGS B ARx LAWS ly S Hp W mem md HAR)) as (Hl0 & _ & _ & Hpa).
unfold page_aligned in Hpa. rewrite Hl0 in Hf, Hs. rewrite IMG_TOP_val in Htop |- *. unfold kImgLo in *.
clear - Hf Hs Htop Hpa. lia.
Qed.

(* ==================== Section fl: the stretches GENERIC in the float state (closed below) ====================
   Everything the escape applies at the float state the snprintf row returns lives here: after `End fl` the joins
   (pe_s, pe_K) and the stretches (pe_tail, pe_strlen, pe_put, the moves) take the float state as their implicit
   argument fx. *)
Section fl.
Context {fx : YK11.FPState}.
(* the tokenless runner at the re-hiding relation: every stretch of this file runs after the opening-quote put *)
Let NTRUNTOI := SRr_run_to_pi_AJx_invR B ARx LAWS Pm PLAW (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
(* put's call step: its join premise, its continuation's join and its conclusion SRr' are at wle' SEGS RZ_cf *)
Local Notation ps_put_step := (ps_put_step B ARx LAWS segs_low HPAB HPSTRO Pm PCALL CTX0 (PUT fx)).

(* the seat at a stretch that reads no memory: registers only *)
Lemma pe_seat0 : forall k (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (pe_ss0 k)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_put_string + k))) mem (seg_rom SEGS))).
Proof.
intros k W regs mem. rewrite restrict_mkst_fx. unfold pe_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- first [ exact (conj I (conj I I)) | split; [exact I | split; [exact I | exact I]]
        | match goal with |- ?g => idtac "FACTSGOAL" g end; fail 1 ].
Qed.

(* the seat at A 0x88518 (the escape join): registers as atoms, the five literal words at R + 24 .. R + 56 *)
Lemma pe_seat428 : forall X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_pre X ch -> ps_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  st_ok_pi SEGS VAL (pe_E regsc) pe_ss428
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 428))) memc (seg_rom SEGS))).
Proof.
intros X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc Hpre Hesc.
destruct Hesc as (_ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & SH4 &
  W8 & W16 & W24 & W32 & W40 & W48 & W56).
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
pose proof asan_consts as (C1 & _).
assert (HRr : 0 <= x_R X /\ x_R X + 64 < 2 ^ 64) by (unfold x_R, x_sp in *; lia).
assert (B9 : base_val (pe_E regsc) (Some 9%nat) = x_R X).
{ cbn [base_val]. unfold pe_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (pe_E regsc) 32 = Z_to_bv 64 (ps_str 91))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew (pe_E regsc) 33 = Z_to_bv 64 (ps_str 89))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew (pe_E regsc) 34 = Z_to_bv 64 (ps_str 87))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew (pe_E regsc) 35 = Z_to_bv 64 (ps_str 85))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E36 : ew (pe_E regsc) 36 = Z_to_bv 64 (ps_str 93))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 4)).
pose proof (rdword_range_ps _ _ _ _ W24) as V24. pose proof (rdword_range_ps _ _ _ _ W32) as V32.
pose proof (rdword_range_ps _ _ _ _ W40) as V40. pose proof (rdword_range_ps _ _ _ _ W48) as V48.
pose proof (rdword_range_ps _ _ _ _ W56) as V56.
rewrite restrict_mkst_fx. unfold pe_ss428. apply pa_entry_st_ok_full.
- unfold pe_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, pe_rreg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
  split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 24 8 (SOff 32 0) (ps_str 91));
       [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | first [zside | lia | (cbv; discriminate)]
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W24)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 32 8 (SOff 33 0) (ps_str 89));
       [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | first [zside | lia | (cbv; discriminate)]
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W32)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 40 8 (SOff 34 0) (ps_str 87));
       [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | first [zside | lia | (cbv; discriminate)]
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W40)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 48 8 (SOff 35 0) (ps_str 85));
       [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | first [zside | lia | (cbv; discriminate)]
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W48)] |].
  apply Forall_cons;
    [apply (chunk_ok_val SEGS (pe_E regsc) _ (x_R X) 56 8 (SOff 36 0) (ps_str 93));
       [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | first [zside | lia | (cbv; discriminate)]
       | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W56)] |].
  apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- first [ exact (conj I (conj I I)) | split; [exact I | split; [exact I | exact I]] ].
Qed.

(* ---- registers read back from a listing state ---- *)
Lemma pe_agree : forall regs extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma pe_reg_sv : forall (H : word -> bool) E ss ms (r : bv 5) e,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros H E ss ms r e HS He. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), He. reflexivity. Qed.
Lemma pe_reg_sv_pi : forall (H : word -> bool) E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros H E ss ms r e HS He. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), He. reflexivity. Qed.
Lemma pe_atom_reg : forall E regs0 extra (q : bv 5), env_agree 32 (Ereg regs0 extra) E ->
  sv_denot E (SOff (Z.to_nat (bv_unsigned q)) 0) = getr regs0 q.
Proof.
intros E regs0 extra q HA. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
destruct HA as [HA _]. rewrite HA by (pose proof (u5_range q); lia). apply ew_Ereg_reg.
Qed.
Lemma pe_atom_val : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity. Qed.
Lemma pe_reg_of : forall (H : word -> bool) E ss ms regs0 extra (r q : bv 5),
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned q)) 0 -> getr (ms_regs ms) r = getr regs0 q.
Proof.
intros H E ss ms regs0 extra r q HS HA Hr. rewrite (pe_reg_sv H E ss ms r _ HS Hr). exact (pe_atom_reg E regs0 extra q HA).
Qed.
Lemma pe_reg_of_pi : forall (H : word -> bool) E ss ms regs0 extra (r q : bv 5),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned q)) 0 -> getr (ms_regs ms) r = getr regs0 q.
Proof.
intros H E ss ms regs0 extra r q HS HA Hr. rewrite (pe_reg_sv_pi H E ss ms r _ HS Hr). exact (pe_atom_reg E regs0 extra q HA).
Qed.
Lemma pe_ra : forall (H : word -> bool) E ss ms k, st_ok SEGS E ss (restrict H ms) -> img_env VAL A_LIM E ->
  sr_get (ss_regs ss) 1%bv = SOff A_TEXT k -> getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + k).
Proof. intros H E ss ms k HS HE Hr. rewrite (pe_reg_sv H E ss ms 1%bv _ HS Hr). exact (codeptr_val E k HE). Qed.
Lemma pe_csl_in : forall r, acallee_saved r -> In (Z_to_bv 5 r) pe_csl.
Proof.
intros r Hr. unfold acallee_saved in Hr. unfold pe_csl.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [-> | Hc]; [cbn [In]; repeat first [left; apply bv_eq; reflexivity | right] |]).
subst r. cbn [In]. repeat first [left; apply bv_eq; reflexivity | right].
Qed.
Lemma pe_pres : forall (H : word -> bool) E ss ms regs0 extra,
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) pe_csl = true ->
  aregs_preserved regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 extra HS HA Hl r Hr.
exact (regs_kept_of_st_ok SEGS E ss (restrict H ms) regs0 extra pe_csl HS HA Hl _ (pe_csl_in r Hr)).
Qed.
Lemma pe_pres_at : forall regs regs', aregs_preserved regs regs' ->
  forall (r : Z) (b : bv 5), acallee_saved r -> bv_unsigned b = r -> getr regs' b = getr regs b.
Proof. intros regs regs' HP r b Hr Hb. pose proof (HP r Hr) as H. rewrite <- Hb, !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pe_pres_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.
(* a stretch whose regions have no write window keeps every byte *)
Lemma pe_keep_nowin : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hn a Ha. apply (kept_of_frame E rs H m m' (fun x => x = a) Hf); [|reflexivity].
intros x ->. split; [exact Ha | apply Hn].
Qed.

(* ---- the string byte, its escape, and the literals ---- *)
Lemma pe_c_range : forall X ch i, ps_pre X ch -> (i < length (x_bs X))%nat -> 0 <= nth i (x_bs X) 0 < 256.
Proof.
intros X ch i Hpre Hi.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcstr0 & _).
destruct Hcstr0 as ((Hg & _) & _). destruct (Hg i ltac:(rewrite length_app; cbn [length]; lia)) as (_ & Hr).
rewrite app_nth1 in Hr by lia. exact Hr.
Qed.
Lemma pe_esc_facts : forall c, 0 <= c < 256 ->
  (length (WriterSpec.esc c) = 2 \/ length (WriterSpec.esc c) = 6)%nat /\ Forall (fun x => 0 < x < 256) (WriterSpec.esc c).
Proof.
intros c Hc. unfold WriterSpec.esc.
destruct (c =? 34) eqn:E1; [split; [left; reflexivity | repeat (apply Forall_cons; [lia|]); apply Forall_nil]|].
destruct (c =? 92) eqn:E2; [split; [left; reflexivity | repeat (apply Forall_cons; [lia|]); apply Forall_nil]|].
destruct (c =? 10) eqn:E3; [split; [left; reflexivity | repeat (apply Forall_cons; [lia|]); apply Forall_nil]|].
destruct (c =? 9) eqn:E4; [split; [left; reflexivity | repeat (apply Forall_cons; [lia|]); apply Forall_nil]|].
destruct (c =? 13) eqn:E5; [split; [left; reflexivity | repeat (apply Forall_cons; [lia|]); apply Forall_nil]|].
split; [right; reflexivity|].
repeat (apply Forall_cons;
  [first [lia | unfold WriterSpec.hexd; match goal with |- context [?x <? 10] => destruct (x <? 10) end; lia] |]).
apply Forall_nil.
Qed.
(* the escape's state between the escape join and the put of the escape: the join invariant (after the opening-quote
   put: at wle' SEGS RZ_cf), the plan, the registers the stretch and ps_next read (all callee-saved), u's shadow granule
   unpoisoned, the realigned slots *)
Definition pe_s (X : psx) (pos : Z) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc /\
  (i < length (x_bs X))%nat /\ WriterSpec.special (nth i (x_bs X) 0) = true /\
  [34] :: WriterSpec.spieces_run [] (x_bs X) =
    P ++ WriterSpec.esc (nth i (x_bs X) 0) :: WriterSpec.spieces_run [] (skipn (S i) (x_bs X)) /\
  getr regsc 2 = w64 (x_R X) /\ getr regsc 3 = getr (x_regs X) 3 /\ getr regsc 4 = getr (x_regs X) 4 /\
  getr regsc 8 = w64 (x_sp X) /\ getr regsc 9 = w64 (x_R X) /\
  getr regsc 19 = w64 (x_o X) /\ getr regsc 20 = w64 (x_s X + Z.of_nat i + 1) /\
  getr regsc 21 = w64 (x_F X pos + 32) /\ getr regsc 22 = w64 (x_SHF X pos) /\ getr regsc 23 = w64 PS_SB /\
  getr regsc 24 = w64 (x_s X + Z.of_nat i) /\ getr regsc 25 = w64 34 /\
  aview SEGS (w_H Wc) memc (x_SHF X pos + 4) = Some 0 /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 8) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 16) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 24) = Some (ps_str 91) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 32) = Some (ps_str 89) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 40) = Some (ps_str 87) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 48) = Some (ps_str 85) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 56) = Some (ps_str 93).
Lemma pe_s_of_esc : forall X pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  ps_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc.
Proof.
intros X pos i P lyc Sc Hpc Wc regsc memc mdc kc
  (Hcom & Hi & Hsp & Hplan & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R27 & SH4 &
   W8 & W16 & W24 & W32 & W40 & W48 & W56).
repeat (split; [eassumption|]). exact W56.
Qed.

(* ---- where the walk's bytes lie ---- *)
Lemma pe_geo : forall X ch pos lyc Sc Hpc Wc memc mdc kc,
  ps_pre X ch ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc mdc kc ->
  In (0, pos) (frames Sc) /\ frame_addr lyc 0 pos = x_F X pos /\
  4096 <= x_F X pos /\ x_F X pos + 64 <= YM05.alloc_ceiling /\ x_F X pos mod 32 = 0 /\
  (x_F X pos + 64 <= kLowShadowBeg \/ kHighMemBeg <= x_F X pos) /\
  (forall a, x_F X pos <= a < x_F X pos + 64 -> apresent (w_H Wc) memc a) /\
  x_sp X mod 16 = 0 /\ x_d X mod 16 = 0 /\ 0 <= x_d X /\
  x_sp X - 208 <= x_R X <= x_sp X - 192 /\ x_R X mod 32 = 0 /\
  YM05.alloc_ceiling + STK_RT_PRINTF + 208 <= x_sp X /\ x_sp X + x_d X <= 2 ^ 47 /\
  ly_stk_lo lyc + STK_put_string <= x_sp X /\
  (forall a, x_sp X - STK_put_string <= a < x_sp X + x_d X -> apresent (w_H Wc) memc a).
Proof.
intros X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof STK_ps_facts as (_ & _ & _ & SK4 & _).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & HR32).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLLE. pose proof (ajxR_frs HJ) as HFRS.
pose proof (ajxR_pres HJ) as Hpres.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _ & _ & _ & Eslo & _).
assert (HinF : In (0, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HARc HinF) as (HF32 & (HFa0 & HFa1) & HFpres & _).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HARc HinF) as (HF4096 & HFceil & _).
assert (EF : frame_addr lyc 0 pos = x_F X pos) by (unfold x_F, frame_addr; rewrite HlyF; reflexivity).
rewrite EF in HF32, HFa0, HFa1, HFpres, HF4096, HFceil. change (fs_frame_bytes 0) with 64 in HFa1, HFpres, HFceil.
unfold x_R, x_sp in *.
split; [exact HinF|]. split; [exact EF|]. split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HF32|].
split; [destruct HFa1 as [Hx | (Hx & _)]; [left | right]; exact Hx|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [exact Hal16|]. split; [exact Hd16|]. split; [exact Hd0|]. split; [exact HR|]. split; [exact HR32|].
split; [unfold STK_RT_PRINTF, ESTACK in *; lia|]. split; [lia|].
split; [rewrite Eslo; lia|].
intros a Ha. apply Hpres. lia.
Qed.

(* image bytes lie apart from a live fake frame's bytes *)
Lemma pe_img_frame : forall ly S Hp (W : world SEGS) mem md cid pos p n q m,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> (forall a, p <= a < p + n -> in_img SEGS a) ->
  0 < n -> 0 < m ->
  frame_addr ly cid pos <= q -> q + m <= frame_addr ly cid pos + fs_frame_bytes cid ->
  p + n <= q \/ q + m <= p.
Proof.
intros ly S Hp W mem md cid pos p n q m HAR Hin Himg Hn Hm Hq1 Hq2.
destruct (Z_le_gt_dec (p + n) q) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec (q + m) p) as [H2 | H2]; [right; exact H2|]. exfalso.
destruct (Z_le_gt_dec p q) as [Hpq | Hpq].
- apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos q HAR Hin); [clear - Hq1 Hq2 Hm; lia|].
  apply Himg. clear - Hpq H1. lia.
- apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos p HAR Hin); [clear - Hq1 Hq2 Hpq H2; lia|].
  apply Himg. clear - Hn. lia.
Qed.
(* u's granule (its shadow byte SHF + 4 is 0) is addressable *)
Lemma pe_radd : forall X pos (Wc : world SEGS) memc n, x_F X pos mod 32 = 0 -> 0 <= n <= 8 ->
  aview SEGS (w_H Wc) memc (x_SHF X pos + 4) = Some 0 ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (x_F X pos + 32) n.
Proof.
intros X pos Wc memc n HF Hn H0 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (x_SHF X pos + 4); [exact H0|].
unfold x_SHF, PS_SB. lia.
Qed.

(* the join invariant across a runtime call that writes at most its window below R (STK_RT_PRINTF bytes) and the
   escape buffer u .. u + 8 *)
Lemma pe_common_call : forall X ch pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc',
  ps_pre X ch -> ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - STK_RT_PRINTF <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc' mdc' kc'.
Proof.
intros X ch pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hpre Hcom HJ' HPm' KK.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ho1 & Ho2 & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc' mdc' kc' Hpre HJ') as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof (ajxR_ar HJ') as HARc.
pose proof Hcom as (_ & Hsav & HF56 & _).
unfold STK_RT_PRINTF, ESTACK in *.
set (F := x_F X pos) in *. set (R := x_R X) in *. set (sp := x_sp X) in *.
apply (ps_common_runR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hcom).
- exact Ho1.
- unfold sp in *. clear - Ho2 Hd0 H47. lia.
- exact HJ'.
- exact HPm'.
- unfold ps_saved_ok in Hsav |- *. fold sp in Hsav |- *. rewrite Forall_forall in Hsav |- *.
  intros pz Hpin. rewrite <- (Hsav pz Hpin). apply rdword_eq_of. intros j Hj.
  assert (Hrg : -104 <= fst pz <= -8).
  { unfold ps_saved_list in Hpin. cbn [In] in Hpin. repeat (destruct Hpin as [<- | Hpin]; [cbn [fst]; lia|]). destruct Hpin. }
  apply KK; clear - Hrg Hj HR HSPc HFceil HC H47 Hd0; lia.
- rewrite <- HF56. apply rdword_eq_of. intros j Hj. fold F. apply KK; clear - Hj HF4096 HFceil HC HSPc HR; lia.
- intros a Ha. destruct Ha as [Ha | [Hi | (b & m & HB & Hb)]].
  + apply KK; clear - Ha HR HSPc HFceil HC; lia.
  + pose proof (segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
    apply KK; [clear - Hl; lia | clear - Hl HR HSPc HC; lia |].
    intros Hx. apply (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ 0 pos a HARc HinF); [|exact Hi].
    rewrite EF. change (fs_frame_bytes 0) with 64. fold F. clear - Hx. lia.
  + destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARc HB) as (_ & Hb4096 & Hbceil & _).
    pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HARc HB HinF) as Hzd.
    unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite EF in Hzd. change (fs_frame_bytes 0) with 64 in Hzd. fold F in Hzd.
    unfold ASAN_CEIL in *.
    apply KK; [clear - Hb Hb4096 Hbceil HC; lia | clear - Hb Hbceil HC HR HSPc; lia | clear - Hb Hzd; lia].
Qed.

(* the escape's state across a runtime call (registers callee-saved, bytes outside the call's window and u kept) *)
Lemma pe_s_move : forall X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs' memc' mdc' kc',
  ps_pre X ch -> pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> aregs_preserved regsc regs' ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - STK_RT_PRINTF <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  pe_s X pos i P lyc Sc Hpc Wc regs' memc' mdc' kc'.
Proof.
intros X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs' memc' mdc' kc' Hpre Hs HP HJ' HPm' KK.
destruct Hs as (Hcom & Hi & Hsp & Hplan & R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & SH4 &
  W8 & W16 & W24 & W32 & W40 & W48 & W56).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc' mdc' kc' Hpre HJ') as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (KR : forall a, x_R X <= a < x_R X + 64 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply KK; unfold STK_RT_PRINTF, ESTACK in *; clear - Ha HR HSPc HFceil HC H47 Hd0; lia. }
assert (KS : aview SEGS (w_H Wc) memc' (x_SHF X pos + 4) = aview SEGS (w_H Wc) memc (x_SHF X pos + 4)).
{ apply KK; unfold x_SHF, PS_SB, SHADOW_OFF, STK_RT_PRINTF, ESTACK, kLowShadowBeg, kHighMemBeg in *;
    clear - HR HSPc HFceil HC H47 HFapp HF4096; lia. }
split; [exact (pe_common_call X ch pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hpre Hcom HJ' HPm' KK)|].
split; [exact Hi|]. split; [exact Hsp|]. split; [exact Hplan|].
split; [rewrite (pe_pres_at _ _ HP 2 2%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R2|].
split; [rewrite (pe_pres_at _ _ HP 3 3%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R3|].
split; [rewrite (pe_pres_at _ _ HP 4 4%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R4|].
split; [rewrite (pe_pres_at _ _ HP 8 8%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R8|].
split; [rewrite (pe_pres_at _ _ HP 9 9%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R9|].
split; [rewrite (pe_pres_at _ _ HP 19 19%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R19|].
split; [rewrite (pe_pres_at _ _ HP 20 20%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R20|].
split; [rewrite (pe_pres_at _ _ HP 21 21%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R21|].
split; [rewrite (pe_pres_at _ _ HP 22 22%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R22|].
split; [rewrite (pe_pres_at _ _ HP 23 23%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R23|].
split; [rewrite (pe_pres_at _ _ HP 24 24%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R24|].
split; [rewrite (pe_pres_at _ _ HP 25 25%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R25|].
split; [rewrite KS; exact SH4|].
split; [rewrite <- W8; apply rdword_eq_of; intros j Hj; apply KR; lia|].
split; [rewrite <- W16; apply rdword_eq_of; intros j Hj; apply KR; lia|].
split; [rewrite <- W24; apply rdword_eq_of; intros j Hj; apply KR; lia|].
split; [rewrite <- W32; apply rdword_eq_of; intros j Hj; apply KR; lia|].
split; [rewrite <- W40; apply rdword_eq_of; intros j Hj; apply KR; lia|].
split; [rewrite <- W48; apply rdword_eq_of; intros j Hj; apply KR; lia|].
rewrite <- W56; apply rdword_eq_of; intros j Hj; apply KR; lia.
Qed.
Lemma pe_u_move : forall X pos i (Wc : world SEGS) memc memc', pe_u X pos i Wc memc ->
  (forall a, x_F X pos + 32 <= a < x_F X pos + 40 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  0 <= nth i (x_bs X) 0 < 256 -> pe_u X pos i Wc memc'.
Proof.
intros X pos i Wc memc memc' Hu K Hc j Hj. destruct (pe_esc_facts _ Hc) as (Hl & _).
rewrite length_app in Hj. cbn [length] in Hj. rewrite K by lia. apply Hu. rewrite length_app. cbn [length]. lia.
Qed.

(* the escape's continuation shape: the re-poison join with the escape put *)
Definition pe_K (X : psx) (pos : Z) (i : nat) (P : list (list Z)) : Prop :=
  forall lyn Sn Hpn Wn regsn memn mdn kn,
    ps_next X pos i (S i) (P ++ [WriterSpec.esc (nth i (x_bs X) 0)]) lyn Sn Hpn Wn regsn memn mdn kn ->
    SRr' SEGS RZ_cf Wn (mkCfg (mkst regsn (Z_to_bv 64 (BASE + (AF_put_string + 588))) memn (seg_rom SEGS)) mdn)
      (ps_Qfin X).

(* ---- the put of the escape (A 0x885b0) and `mv s10, s4` (A 0x885b4), to the re-poison join (A 0x885b8) ---- *)
Lemma pe_put : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> pe_u X pos i Wc memc ->
  getr regsc 10 = w64 (x_o X) -> getr regsc 11 = w64 (x_F X pos + 32) ->
  getr regsc 12 = w64 (Z.of_nat (length (WriterSpec.esc (nth i (x_bs X) 0)))) ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 584)) ->
  pe_K X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc) (ps_Qfin X).
Proof.
intros X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc Hs Hu H10 H11 H12 H1 K.
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hs as (Hcom & Hi & Hsp & Hplan & R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & SH4 &
  W8 & W16 & W24 & W32 & W40 & W48 & W56).
pose proof Hcom as (HJ & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HARc.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
destruct (pe_esc_facts _ Hc) as (Hlen & Hnz).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AF_ps_ret_k 584 ltac:(lia) ltac:(reflexivity)) as (H584 & H584b).
pose proof (pa_B_ok (L := A_prog_listing) (PAImg := PA)) as (HB0 & HB1 & _).
unfold pe_u in Hu.
set (c := nth i (x_bs X) 0) in *. set (b := WriterSpec.esc c) in *.
assert (Hlb : (2 <= length b <= 6)%nat) by (destruct Hlen; lia).
apply (ps_put_step X ch pos P b (WriterSpec.spieces_run [] (skipn (S i) (x_bs X)) ++ [[34]]) lyc Sc Hpc Wc regsc memc mdc kc
  (Z_to_bv 64 (BASE + (AF_put_string + 584))) (x_F X pos + 32)).
- exact Hpre.
- exact HS0.
- exact Hcom.
- unfold WriterSpec.spieces.
  change ([34] :: WriterSpec.spieces_run [] (x_bs X) ++ [[34]]) with (([34] :: WriterSpec.spieces_run [] (x_bs X)) ++ [[34]]).
  rewrite Hplan, <- app_assoc. reflexivity.
- unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold STK_RT_PRINTF, ESTACK in *. lia.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- exact H1.
- apply ret_ok_codeptr_v; [exact (proj1 H584) | exact (proj2 H584)].
- rewrite unsigned_lit_small by lia. exact H584b.
- rewrite unsigned_lit_small by lia. apply ps_ret_lt_ceil. cbn [In]. tauto.
- unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. unfold STK_RT_PRINTF, ESTACK in *. lia.
- exact H10.
- exact H11.
- exact H12.
- (* the escape's bytes at u: read, in the fake frame, addressable *)
  split; [|split; [lia|split; [lia|split; [|split]]]].
  + apply (YGcallSnpCk.snp_garr8_of_aview SEGS (w_H Wc) memc (x_F X pos + 32) b). intros j Hj.
    pose proof (Hu j ltac:(rewrite length_app; cbn [length]; fold b; lia)) as Hx. fold b in Hx.
    rewrite app_nth1 in Hx by lia. exact Hx.
  + unfold amem_range. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  + apply (pe_radd X pos Wc memc); [exact HF32 | lia | exact SH4].
  + intros _. apply (hull_sub _ (x_F X pos) 64); [|lia|lia].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HARc HinF) as Hh. rewrite EF in Hh. exact Hh.
- (* the home: the fake frame, apart from the buffer block *)
  intros Lamc bufc capc Hk Hd Hin Hblks. split.
  + right. exists 0, pos. split; [exact HinF|]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  + destruct (Z.eq_dec capc 0) as [Hz | Hnz0]; [left; exact Hz | right].
    pose proof (Hblks _ _ (Hin Hnz0)) as HinB.
    pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HARc HinB HinF) as Hzd.
    unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite EF in Hzd. change (fs_frame_bytes 0) with 64 in Hzd.
    pose proof (@cf_head_nonneg cp) as Hch.
    destruct (Z_le_gt_dec (x_F X pos + 32 + Z.of_nat (length b)) bufc) as [Hl | Hl]; [left; exact Hl|].
    destruct (Z_le_gt_dec (bufc + capc) (x_F X pos + 32)) as [Hr | Hr]; [right; exact Hr|]. exfalso.
    revert Hzd. unfold req_size. destruct (Z.eqb_spec (capc + cf_head) 0); intros Hzd; lia.
- (* after put: A 0x885b4 `mv s10, s4`, to the re-poison join (A 0x885b8) *)
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HCOM2 HP2 KW KPR KF.
  pose proof HCOM2 as (HJ2 & _ & _ & _ & HPM2 & _).
  pose proof (pe_seat0 584 W2 regs2 mem2) as HS.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  unfold SRr'.
  pnt_run_to_inv NTRUNTOI HS HJ2 HPM2 (AF_put_string + 588).
  { intros a (r & Hin & Ha). cbn [In ss_mem pe_ss0] in Hin. destruct Hin. }
  idtac "PUT-POST-RUN".
  lazymatch goal with HF' : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (pe_keep_nowin _ _ _ _ _ HF' ltac:(intros a (r & Hin & _); destruct Hin)) as KM;
    pose proof (ps_common_frameR (wle' SEGS RZ_cf) X ch pos (P ++ [b]) ly2 S2 Hp2 W2 mem2 md2 (kc + k1) _ _ _ _ _ Hpre
      HCOM2 HJ2 HPM2 HF' ltac:(intros a (r & Hin & _); destruct Hin)) as HCOM3
  end.
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?k)) _ _) _) _ =>
    replace k with (AF_put_string + 588) by (unfold AF_put_string; rewrite (proj2 A_entry_put_string); vm_compute; reflexivity)
  end.
  unfold pe_K, SRr' in K. eapply K.
  assert (RP : forall (r : Z) (q : bv 5), acallee_saved r -> bv_unsigned q = r -> getr regs2 q = getr regsc q)
    by (intros r q Hr Hq; exact (pe_pres_at _ _ HP2 r q Hr Hq)).
  assert (KMW : forall a, x_R X <= a < x_R X + 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
  { intros a Ha. rewrite KM by (unfold STK_RT_PRINTF, ESTACK in *; lia). apply KW. lia. }
  split; [exact HCOM3|].
  split; [lia|]. split; [exact Hi|].
  split; [rewrite Nat.sub_diag; cbn [firstn]; rewrite <- app_assoc; exact Hplan|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 2%bv 2%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 2 2%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R2|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 3%bv 3%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 3 3%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R3|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 4%bv 4%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 4 4%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R4|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 8%bv 8%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 8 8%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R8|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 9%bv 9%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 9 9%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R9|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 19%bv 19%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 19 19%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R19|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 20%bv 20%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 20 20%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R20|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 21%bv 21%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 21 21%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R21|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 22%bv 22%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 22 22%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R22|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 23%bv 23%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 23 23%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R23|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 24%bv 24%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 24 24%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R24|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 25%bv 25%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 25 25%bv ltac:(unfold acallee_saved; lia) eq_refl); exact R25|].
  split; [rewrite (pe_reg_of_pi _ _ _ _ _ _ 26%bv 20%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)),
          (RP 20 20%bv ltac:(unfold acallee_saved; lia) eq_refl), R20; f_equal; lia|].
  split; [rewrite <- W8; apply rdword_eq_of; intros j Hj; apply KMW; lia|].
  split; [rewrite <- W16; apply rdword_eq_of; intros j Hj; apply KMW; lia|].
  split; [rewrite <- W24; apply rdword_eq_of; intros j Hj; apply KMW; lia|].
  split; [rewrite <- W32; apply rdword_eq_of; intros j Hj; apply KMW; lia|].
  split; [rewrite <- W40; apply rdword_eq_of; intros j Hj; apply KMW; lia|].
  split; [rewrite <- W48; apply rdword_eq_of; intros j Hj; apply KMW; lia|].
  rewrite <- W56; apply rdword_eq_of; intros j Hj; apply KMW; lia.
Qed.

(* ---- __wrap_strlen (u) (A 0x885a0), then the put's arguments (A 0x885a4 .. 0x885ac) ---- *)
Lemma pe_strlen : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> pe_u X pos i Wc memc ->
  getr regsc 10 = w64 (x_F X pos + 32) -> getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 568)) ->
  pe_K X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS___wrap_strlen)) memc (seg_rom SEGS)) mdc) (ps_Qfin X).
Proof.
intros X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc Hs Hu H10 H1 K.
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hs as (Hcom & Hi & Hsp & Hplan & R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & SH4 & _).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _ & _ & Hro & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HARc.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
destruct (pe_esc_facts _ Hc) as (Hlen & Hnz).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof (AF_ps_ret_k 568 ltac:(lia) ltac:(reflexivity)) as (H568 & H568b).
pose proof STK_ps_facts as (_ & _ & _ & SK4 & SK5 & _).
unfold pe_u in Hu.
set (c := nth i (x_bs X) 0) in *. set (b := WriterSpec.esc c) in *.
assert (Hlb : (2 <= length b <= 6)%nat) by (destruct Hlen; lia).
unfold STK_RT_PRINTF, STK_RT_STR, ESTACK in *.
(* the strlen rule keeps the world (W2 = Wc): its SRr lifts to SRr' *)
eapply (SRr'_bind SEGS RZ_cf).
{ apply SRr_SRr'.
  apply (aj_strlen_at_xromR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx pa_relro_lo pa_relro_hi LAWS segs_low
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) _ (ASTRLEN fx)
    Wc regsc memc (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X)
    (x_md X) [(0, pos)] lyc Sc Hpc mdc kc (x_F X pos + 32) (Z.of_nat (length b)) (x_R X - (x_sp X + x_d X))
    (Z_to_bv 64 (BASE + (AF_put_string + 568)))).
  - exact HJ.
  - exact H10.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Zplus_mod, Hal16, Hd16. assert (H16 : x_R X mod 16 = 0) by lia. rewrite H16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact H1.
  - apply ret_ok_codeptr_v; [exact (proj1 H568) | exact (proj2 H568)].
  - (* the escape's first NUL is at u + |b| *)
    split; [lia|]. split.
    + intros j Hj. exists (nth (Z.to_nat j) b 0). split.
      * pose proof (Hu (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; fold b; lia)) as Hx. fold b in Hx.
        rewrite Z2Nat.id in Hx by lia. rewrite app_nth1 in Hx by lia. exact Hx.
      * rewrite Forall_forall in Hnz. fold b in Hnz.
        assert (Hin : In (nth (Z.to_nat j) b 0) b) by (apply nth_In; lia).
        pose proof (Hnz _ Hin) as Hx. lia.
    + intros _. pose proof (Hu (length b) ltac:(rewrite length_app; cbn [length]; fold b; lia)) as Hx. fold b in Hx.
      rewrite app_nth2, Nat.sub_diag in Hx by lia. exact Hx.
  - intros a Ha. split.
    + replace a with (x_F X pos + 32 + Z.of_nat (Z.to_nat (a - (x_F X pos + 32)))) by lia.
      rewrite Hu by (rewrite length_app; cbn [length]; fold b; lia). discriminate.
    + unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. clear - Ha Hlb HFceil HSPc HR. lia.
  - first [unfold amem_range8 | unfold YGcallMx.amem_range8 | unfold YGcfStr.amem_range8].
    unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  - apply (pe_radd X pos Wc memc); [exact HF32 | lia | exact SH4].
  - apply (hull_sub _ (x_F X pos) 64); [|lia|lia].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HARc HinF) as Hh. rewrite EF in Hh. exact Hh.
  - intros a Ha. apply (aview_some_of_apresent SEGS). apply HFpres. lia.
  - exact Hro. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Hfr & Hpres2 & Hmn).
pose proof (PCALL _ _ Hmn HPM) as HPM2.
assert (KK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - 4 * 4096 <= a < x_R X) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hw. apply Hfr; [exact Ha|]. unfold ESTACK. lia. }
pose proof (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs2 mem2 md2 kc Hpre Hs HP2 HJ2 HPM2
  (fun a Ha Hw _ => KK0 a Ha Hw)) as Hs2.
pose proof (pe_u_move X pos i Wc memc mem2 Hu ltac:(intros a Ha; apply KK0; lia) Hc) as Hu2.
clear KK0.
pose proof Hs2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R19' & _ & R21' & _).
(* A 0x885a4: mv a2, a0; mv a0, s3; mv a1, s5; jal put *)
pose proof (pe_seat0 568 Wc regs2 mem2) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
unfold SRr'.
pnt_run_to_inv NTRUNTOI HS HJ2 HPM2 (AF_put_string + 584).
{ intros a (r & Hin & Ha). cbn [In ss_mem pe_ss0] in Hin. destruct Hin. }
idtac "STRLEN-POST-RUN".
lazymatch goal with HF' : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?msx)) |- _ =>
  pose proof (pe_keep_nowin _ _ _ _ _ HF' ltac:(intros a (r & Hin & _); destruct Hin)) as KM
end.
cbv beta iota in HS. pmkst HS.
pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as HP3.
pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 19%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as A0.
pose proof (pe_reg_of _ _ _ _ _ _ 11%bv 21%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as A1.
pose proof (pe_reg_of _ _ _ _ _ _ 12%bv 10%bv HS (pe_agree regs2 []) ltac:(vm_compute; reflexivity)) as A2.
pose proof (pe_ra _ _ _ _ (AF_put_string + 584) HS HEI ltac:(vm_compute; reflexivity)) as RA.
apply (pe_put X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ kc).
- apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regs2 mem2 md2 kc (ms_regs ms) (ms_mem ms) _ kc Hpre Hs2 HP3 HJ2 HPM2).
  intros a Ha _ _. exact (KM a Ha).
- apply (pe_u_move X pos i Wc mem2 (ms_mem ms) Hu2); [intros a Ha; apply KM; lia | exact Hc].
- rewrite A0. exact R19'.
- rewrite A1. exact R21'.
- rewrite A2. exact Ha0.
- exact RA.
- exact K.
Qed.

(* ---- after the escape's write (A 0x88584 after __asan_memcpy, A 0x8859c after __wrap_snprintf), to strlen ---- *)
Lemma pe_tail : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall k pos i P lyc Sc Hpc Wc regsc memc mdc kc, (k = 536 \/ k = 560) ->
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> pe_u X pos i Wc memc ->
  pe_K X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + k))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin X).
Proof.
intros X ch Hpre HS0 k pos i P lyc Sc Hpc Wc regsc memc mdc kc Hk Hs Hu K.
unfold SRr'.
pose proof Hs as (Hcom & Hi & _ & _ & _ & _ & _ & _ & _ & _ & _ & R21 & _).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _).
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as (_ & _ & HF4096 & HFceil & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
destruct Hk as [-> | ->].
- pose proof (pe_seat0 536 Wc regsc memc) as HS.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
  pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 584).
  { intros a (r & Hin & Ha). cbn [In ss_mem pe_ss0] in Hin. destruct Hin. }
  idtac "TAIL536-POST-RUN".
  lazymatch goal with HF' : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (pe_keep_nowin _ _ _ _ _ HF' ltac:(intros a (r & Hin & _); destruct Hin)) as KM
  end.
  cbv beta iota in HS. pmkst HS.
  pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regsc []) ltac:(vm_compute; reflexivity)) as HP3.
  pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 21%bv HS (pe_agree regsc []) ltac:(vm_compute; reflexivity)) as A0.
  pose proof (pe_ra _ _ _ _ (AF_put_string + 568) HS HEI ltac:(vm_compute; reflexivity)) as RA.
  apply (pe_strlen X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ kc).
  + apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc (ms_regs ms) (ms_mem ms) _ kc Hpre Hs HP3 HJ HPM).
    intros a Ha _ _. exact (KM a Ha).
  + apply (pe_u_move X pos i Wc memc (ms_mem ms) Hu); [intros a Ha; apply KM; clear - Ha HF4096 HFceil HC; lia | exact Hc].
  + rewrite A0. exact R21.
  + exact RA.
  + exact K.
- pose proof (pe_seat0 560 Wc regsc memc) as HS.
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regsc []))) by apply Eimg_env.
  pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 584).
  { intros a (r & Hin & Ha). cbn [In ss_mem pe_ss0] in Hin. destruct Hin. }
  idtac "TAIL560-POST-RUN".
  lazymatch goal with HF' : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (pe_keep_nowin _ _ _ _ _ HF' ltac:(intros a (r & Hin & _); destruct Hin)) as KM
  end.
  cbv beta iota in HS. pmkst HS.
  pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regsc []) ltac:(vm_compute; reflexivity)) as HP3.
  pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 21%bv HS (pe_agree regsc []) ltac:(vm_compute; reflexivity)) as A0.
  pose proof (pe_ra _ _ _ _ (AF_put_string + 568) HS HEI ltac:(vm_compute; reflexivity)) as RA.
  apply (pe_strlen X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ kc).
  + apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc (ms_regs ms) (ms_mem ms) _ kc Hpre Hs HP3 HJ HPM).
    intros a Ha _ _. exact (KM a Ha).
  + apply (pe_u_move X pos i Wc memc (ms_mem ms) Hu); [intros a Ha; apply KM; clear - Ha HF4096 HFceil HC; lia | exact Hc].
  + rewrite A0. exact R21.
  + exact RA.
  + exact K.
Qed.
End fl.
(* ======================= end of Section fl: pe_s, pe_K, pe_put, pe_strlen, pe_tail take {fx} ======================= *)

(* the escape state moves to the float state a float-changing call returns at (the base's ps_common_refxR at
   wle' SEGS RZ_cf on the join; every other conjunct reads no float state) *)
Lemma pe_s_refx : forall (f f' : YK11.FPState) X pos i P lyc Sc Hpc Wc regsc memc mdc kc,
  pe_s (fx := f) X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  YK0o.frm_zero (@YK11.fp_csr f') -> fregs_kept_x (x_fx X) f' ->
  pe_s (fx := f') X pos i P lyc Sc Hpc Wc regsc memc mdc kc.
Proof.
intros f f' X pos i P lyc Sc Hpc Wc regsc memc mdc kc (Hcom & Hrest) Hz Hk. split; [|exact Hrest].
exact (ps_common_refxR B ARx Pm (wle' SEGS RZ_cf) f f' X pos P lyc Sc Hpc Wc memc mdc kc Hcom Hz Hk).
Qed.
(* the escape's continuation at every float state the walk may reach (ps_esc_run's continuation premise) *)
Definition pe_KF (X : psx) (pos : Z) (i : nat) (P : list (list Z)) : Prop :=
  forall fx' : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x (x_fx X) fx' -> pe_K (fx := fx') X pos i P.

(* the rendered escape is put_string's escape *)
Lemma pe_render_c : forall c, c = 34 \/ c = 92 ->
  YGcallSnpCk.snp_esc_render YGcallSnpCk.snp_esc_fmt_c c = WriterSpec.esc c.
Proof. intros c [-> | ->]; reflexivity. Qed.
Lemma pe_render_x : forall c, c <> 34 -> c <> 92 -> c <> 10 -> c <> 9 -> c <> 13 ->
  YGcallSnpCk.snp_esc_render YGcallSnpCk.snp_esc_fmt_x c = WriterSpec.esc c.
Proof.
intros c H1 H2 H3 H4 H5. unfold YGcallSnpCk.snp_esc_render, WriterSpec.esc.
destruct (list_eq_dec Z.eq_dec YGcallSnpCk.snp_esc_fmt_x YGcallSnpCk.snp_esc_fmt_c) as [He | _]; [discriminate He|].
rewrite (proj2 (Z.eqb_neq c 34) H1), (proj2 (Z.eqb_neq c 92) H2), (proj2 (Z.eqb_neq c 10) H3),
  (proj2 (Z.eqb_neq c 9) H4), (proj2 (Z.eqb_neq c 13) H5). reflexivity.
Qed.
Lemma pe_br_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (YO0b.s64 (U E a) <? YO0b.s64 (U E b)).
Proof. intros E a b. rewrite YO0c.branch_ge. reflexivity. Qed.

(* ==================== Section fl2: the escape at the CURRENT float state fx ==================== *)
Section fl2.
Context {fx : YK11.FPState}.
(* the tokenless runner and the branch at the re-hiding relation (the escape runs after the opening-quote put) *)
Let NTRUNTOI := SRr_run_to_pi_AJx_invR B ARx LAWS Pm PLAW (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Let BR := paj_branchR (PI := PA) (wle' SEGS RZ_cf).
(* __asan_memcpy's text in the m-form at its entry (YGcallMxmn.v aintrin_realizes_xm OCpy; owner R2 / a Theorem Labs lane), at
   the CURRENT float state (the memcpy arms keep it) *)
Hypothesis AMCPY : aintrin_realizes_xm SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
(* the snprintf row's canary cells: the stack-protector GOT cell gcan and the canary cell can it holds (at the
   instance: AE2p.A_GOT_canary = 0xa2c98 and AE2p.A_canary = 0x5fdf30, the values of record of snprintf_xrom_A) *)
Variables gcan can : Z.
(* STATIC IMAGE FACTS of the row's instance (ps_snp_img above; witness at PI_prog_A / AD2l.TfibB with gcan / can :=
   AImgCells.A_GOT_STACK_CHK_GUARD / A_STACK_CHK_GUARD: PRW_S7bWit.v s7bw_ps_snp_img) *)
Hypothesis SNPI : ps_snp_img gcan can.
(* the engine's snprintf ROW (YGcallSnp.v :94 asnprintf_realizes_xrom, owner a Theorem Labs lane) at __wrap_snprintf's entry,
   at the CURRENT float state, at the parameters a Theorem Labs lane's snprintf_xrom_A (lib/A/PSnpSnpRoot.v:140, blob
   4edc9be9a050 at the cut) provides: rlo / rhi := pa_relro_lo / pa_relro_hi, FF_esc IMG_LO gcan (its FF_preset_x lo got at
   lo := IMG_LO, got := gcan; 0x10000 <= lo and got <= A_GOT_canary hold at the instance), K := STK_RT_PRINTF
   (8160 <= K), the canary cells gcan can, the image range [IMG_LO, IMG_TOP) (img_lo <= 65536, 0x600000 <= img_hi),
   cr := ps_snp_cr (its PSnpPcom.PCM_CR), pc := SIGMA AS___wrap_snprintf (its PSnpI.PC_snprintf); the closed side
   conditions at the instance: PRW_S7bWit.v s7bw_snp_row_side *)
Hypothesis SNP : YGcallSnp.asnprintf_realizes_xrom SEGS B ARx pa_relro_lo pa_relro_hi (YGcallSnpCk.FF_esc IMG_LO gcan)
  STK_RT_PRINTF gcan can IMG_LO IMG_TOP ps_snp_cr (SIGMA AS___wrap_snprintf).

(* ---- the escape by copy: __asan_memcpy (u, lit, 3) (A 0x88580), lit = .str.20 / .str.19 / .str.21 ---- *)
Lemma pe_cpy : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc lit,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  (nth i (x_bs X) 0 = 9 /\ lit = ps_str 85 \/ nth i (x_bs X) 0 = 10 /\ lit = ps_str 87 \/
   nth i (x_bs X) 0 = 13 /\ lit = ps_str 91) ->
  getr regsc 10 = w64 (x_F X pos + 32) -> getr regsc 11 = w64 lit -> getr regsc 12 = w64 3 ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 536)) ->
  pe_K X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS___asan_memcpy)) memc (seg_rom SEGS)) mdc) (ps_Qfin X).
Proof.
intros X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc lit Hs Hcase H10 H11 H12 H1 K.
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hs as (Hcom & Hi & Hsp & Hplan & R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & SH4 & _).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _ & _ & Hro & _).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HARc.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof (AF_ps_ret_k 536 ltac:(lia) ltac:(reflexivity)) as (H536 & H536b).
(* the literal: ESC, the letter, NUL; read-only image bytes *)
assert (HL : exists x, WriterSpec.esc (nth i (x_bs X) 0) = [92; x] /\ src_rd Wc memc lit [92; x; 0] /\ kept_at B [] lit 3).
{ destruct Hcase as [(Hcx & ->) | [(Hcx & ->) | (Hcx & ->)]]; rewrite Hcx.
  - exists 116. split; [reflexivity|]. exact (HLIT85 _ _ _ _ _ _ HARc Hro).
  - exists 110. split; [reflexivity|]. exact (HLIT87 _ _ _ _ _ _ HARc Hro).
  - exists 114. split; [reflexivity|]. exact (HLIT91 _ _ _ _ _ _ HARc Hro). }
destruct HL as (x & Hesc & Hsrc & Hkept).
pose proof Hsrc as (Hbytes & Hl4096 & Hlceil & Hlam & Hlrad & Hlhull). cbn [length] in Hlceil, Hlam, Hlrad, Hlhull.
change (Z.of_nat 3) with 3 in Hlceil, Hlam, Hlrad, Hlhull.
assert (Hlimg : forall a, lit <= a < lit + 3 -> in_img SEGS a).
{ intros a Ha. destruct Hkept as [(b0 & m & Hin & _) | [(_ & _ & _ & Hall) | (_ & _ & Hall)]];
    [destruct Hin | exact (in_roP_img _ (proj1 (Hall a Ha))) | exact (in_roP_img _ (proj1 (Hall a Ha)))]. }
assert (Hdl : lit + 3 <= x_F X pos + 32 \/ x_F X pos + 32 + 3 <= lit).
{ apply (pe_img_frame _ _ _ _ _ _ 0 pos lit 3 (x_F X pos + 32) 3 HARc HinF Hlimg ltac:(lia) ltac:(lia));
    rewrite EF; [lia | change (fs_frame_bytes 0) with 64; lia]. }
unfold STK_RT_PRINTF, ESTACK in *.
(* the memcpy rule keeps the world (W2 = Wc): its SRr lifts to SRr' *)
eapply (SRr'_bind SEGS RZ_cf).
{ apply SRr_SRr'.
  apply (aj_intrin_at_xmR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS segs_low (wle' SEGS RZ_cf) OCpy _ AMCPY
    Wc regsc memc (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X)
    (x_md X) [(0, pos)] lyc Sc Hpc mdc kc (x_F X pos + 32) lit 3 (x_R X - (x_sp X + x_d X))
    (Z_to_bv 64 (BASE + (AF_put_string + 536)))).
  - exact HJ.
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Zplus_mod, Hal16, Hd16. assert (H16 : x_R X mod 16 = 0) by lia. rewrite H16. reflexivity.
  - lia.
  - unfold ESTACK. pose proof STK_ps_facts as (SK1 & _). unfold ESTACK in SK1. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact H1.
  - apply ret_ok_codeptr_v; [exact (proj1 H536) | exact (proj2 H536)].
  - intros a Ha. split.
    + unfold awr_byte. right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
    + unfold ESTACK. lia.
  - unfold amem_range. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  - apply (pe_radd X pos Wc memc); [exact HF32 | lia | exact SH4].
  - intros _. apply (hull_sub _ (x_F X pos) 64); [|lia|lia].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HARc HinF) as Hh. rewrite EF in Hh. exact Hh.
  - split; [lia|]. split; [lia|]. split.
    + intros a Ha. split.
      * replace a with (lit + Z.of_nat (Z.to_nat (a - lit))) by lia.
        rewrite (YGcallSnpCk.snp_aview_of_garr8 SEGS (w_H Wc) memc lit [92; x; 0] (Z.to_nat (a - lit)) Hbytes
          ltac:(cbn [length]; lia)). discriminate.
      * unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
    + split; [lia|]. split; [exact Hlam|]. split; [exact Hlrad|]. intros _. apply Hlhull. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2 & Hmn).
pose proof (PCALL _ _ Hmn HPM) as HPM2.
assert (KK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - 4 * 4096 <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hw Hu. apply Hfr; [exact Ha | lia | unfold ESTACK; lia]. }
pose proof (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs2 mem2 md2 kc Hpre Hs HP2 HJ2 HPM2 KK0) as Hs2.
assert (Hu2 : pe_u X pos i Wc mem2).
{ unfold pe_u. rewrite Hesc. intros j Hj. cbn [length app] in Hj.
  pose proof (Heff (Z.of_nat j) ltac:(lia)) as He. cbn iota in He. rewrite He.
  exact (YGcallSnpCk.snp_aview_of_garr8 SEGS (w_H Wc) memc lit [92; x; 0] j Hbytes ltac:(cbn [length]; lia)). }
exact (pe_tail X ch Hpre HS0 536 pos i P lyc Sc Hpc Wc regs2 mem2 md2 kc (or_introl eq_refl) Hs2 Hu2 K).
Qed.

(* ---- the escape by format: __wrap_snprintf (u, 8, fmt, c) (A 0x88598), the engine's row ----
   The row returns at SOME float state fx' (frm = 0, every f register but f10 kept): the post gives fx', its two float
   facts, and the escape state at the CALLER's fx (its float clause is about fx, which the call does not change); the
   caller moves it to fx' (pe_s_refx). *)
Lemma pe_snp_call : forall X ch, ps_pre X ch ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc f fmt,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  (f = ps_str 93 /\ fmt = YGcallSnpCk.snp_esc_fmt_c \/ f = ps_str 89 /\ fmt = YGcallSnpCk.snp_esc_fmt_x) ->
  getr regsc 10 = w64 (x_F X pos + 32) -> getr regsc 11 = w64 8 -> getr regsc 12 = w64 f ->
  getr regsc 13 = w64 (nth i (x_bs X) 0) -> getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 560)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS___wrap_snprintf)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = Wc /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + (AF_put_string + 560))) mem2 (seg_rom SEGS)) md2 /\
       YK0o.frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       pe_s (fx := fx) X pos i P lyc Sc Hpc Wc regs2 mem2 md2 kc /\
       (forall j, (j < length (YGcallSnpCk.snp_esc_render fmt (nth i (x_bs X) 0%Z) ++ [0%Z]))%nat ->
          aview SEGS (w_H Wc) mem2 (x_F X pos + 32 + Z.of_nat j) =
          Some (nth j (YGcallSnpCk.snp_esc_render fmt (nth i (x_bs X) 0) ++ [0]) 0))).
Proof.
intros X ch Hpre pos i P lyc Sc Hpc Wc regsc memc mdc kc f fmt Hs Hfmt H10 H11 H12 H13 H1.
pose proof SNPI as (Hf93 & Hf89 & Hcimg & _ & Hcr & _ & _).
assert (HKp : ESTACK <= STK_RT_PRINTF) by (unfold STK_RT_PRINTF, ESTACK; lia).
pose proof (YGcallSnpCk.snp_esc_of_xrom SEGS B ARx pa_relro_lo pa_relro_hi IMG_LO gcan STK_RT_PRINTF STK_RT_PRINTF gcan can
  IMG_LO IMG_TOP ps_snp_cr (SIGMA AS___wrap_snprintf) (Z.le_refl _) HKp SNP) as SNPX.
pose proof HPAB as (EPL & EPH).
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof Hs as (Hcom & Hi & Hsp & Hplan & R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & SH4 & _).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _ & _ & Hro & _ & (Hfz & _)).
pose proof (pe_geo X ch pos lyc Sc Hpc Wc memc mdc kc Hpre HJ) as
  (HinF & EF & HF4096 & HFceil & HF32 & HFapp & HFpres & Hal16 & Hd16 & Hd0 & HR & HR32 & HSPc & H47 & Hlo & Hpw).
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_qt HJ) as HQT.
pose proof (pe_c_range X ch i Hpre Hi) as Hc.
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
pose proof STK_ps_facts as (_ & _ & _ & SK4 & _).
pose proof (AF_ps_ret_k 560 ltac:(lia) ltac:(reflexivity)) as (H560 & H560b).
(* the row's state facts at the call state, derived from the laws (pe_canary / pe_consts_view / pe_frame_top) *)
pose proof (pe_canary gcan can lyc Sc Hpc Wc memc mdc SNPI HAR) as Hcan.
pose proof (pe_consts_view gcan can lyc Sc Hpc Wc memc mdc SNPI HAR Hro) as Hcv.
pose proof (pe_frame_top gcan can lyc Sc Hpc Wc memc mdc 0 pos SNPI HAR HinF) as Hftop.
(* the format ends below the GOT cell (ps_snp_img's first two facts) *)
assert (Hfg : f + Z.of_nat (length fmt) + 1 <= gcan) by (destruct Hfmt as [(-> & ->) | (-> & ->)]; assumption).
set (u := x_F X pos + 32) in *. set (c := nth i (x_bs X) 0) in *.
assert (Hsp' : spZ regsc = x_R X) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold STK_RT_PRINTF, ESTACK in *; lia).
(* the format: its bytes with the NUL, read-only image bytes *)
assert (HF : src_rd Wc memc f (fmt ++ [0]) /\ kept_at B [] f (Z.of_nat (length fmt) + 1)).
{ destruct Hfmt as [(-> & ->) | (-> & ->)].
  - exact (HLIT93 _ _ _ _ _ _ HAR Hro).
  - exact (HLIT89 _ _ _ _ _ _ HAR Hro). }
destruct HF as (Hfsrc & Hfkept).
assert (Hfl : (Z.of_nat (length fmt) = 3 \/ Z.of_nat (length fmt) = 6)) by (destruct Hfmt as [(_ & ->) | (_ & ->)]; cbn; lia).
assert (Hfimg : forall a, f <= a < f + (Z.of_nat (length fmt) + 1) -> in_img SEGS a).
{ intros a Ha. destruct Hfkept as [(b0 & m & Hin & _) | [(_ & _ & _ & Hall) | (_ & _ & Hall)]];
    [destruct Hin | exact (in_roP_img _ (proj1 (Hall a Ha))) | exact (in_roP_img _ (proj1 (Hall a Ha)))]. }
(* kept_at's image arms read the instance's band pa_lo / pa_hi (HPAB: image A's) *)
assert (Hfb : IMG_LO + 64 <= f /\ f + (Z.of_nat (length fmt) + 1) + 64 <= IMG_TOP).
{ destruct Hfkept as [(b0 & m & Hin & _) | [(_ & H1x & H2x & _) | (H1x & H2x & _)]]; [destruct Hin | |];
    rewrite EPL in H1x; rewrite EPH in H2x; split; assumption. }
(* image ranges lie below the window and apart from the escape buffer *)
assert (IW : forall p n, 0 < n -> (forall a, p <= a < p + n -> in_img SEGS a) ->
  Forall (zdisjoint (p, n)) (FMsnprintfShared.snp_out STK_RT_PRINTF (spZ regsc) u 8)).
{ intros p n Hn Hall. apply YGcallSnpCk.snp_out_Forall. split.
  - unfold zdisjoint. cbn [fst snd]. left. pose proof (segs_low _ (Hall (p + n - 1) ltac:(lia))) as Hl.
    rewrite Hsp'. unfold kLowMemEnd, STK_RT_PRINTF, ESTACK in *. lia.
  - unfold zdisjoint. cbn [fst snd].
    apply (pe_img_frame _ _ _ _ _ _ 0 pos p n u 8 HAR HinF Hall Hn ltac:(lia)); rewrite EF; unfold u; [lia | change (fs_frame_bytes 0) with 64; lia]. }
assert (Hgimg : forall j, 0 <= j < 8 -> in_img SEGS (gcan + j)) by (intros j Hj; exact (proj1 (Hcimg j Hj))).
assert (Hcimg2 : forall j, 0 <= j < 8 -> in_img SEGS (can + j)) by (intros j Hj; exact (proj1 (proj2 (Hcimg j Hj)))).
pose proof (segs_low _ (Hgimg 0 ltac:(lia))) as Lg0. pose proof (segs_low _ (Hgimg 7 ltac:(lia))) as Lg7.
pose proof (segs_low _ (Hcimg2 0 ltac:(lia))) as Lc0. pose proof (segs_low _ (Hcimg2 7 ltac:(lia))) as Lc7.
rewrite Z.add_0_r in Lg0, Lc0.
(* the call's entry state *)
assert (HPRE2 : ecall_pre_x SEGS B ARx lyc Sc Hpc Wc regsc memc mdc).
{ split; [exact HAR|]. split; [rewrite H1; apply ret_ok_codeptr_v; [exact (proj1 H560) | exact (proj2 H560)]|].
  split; [rewrite Hsp'; lia|]. split; [rewrite Hsp'; unfold STK_RT_PRINTF, ESTACK in *; lia|].
  split; [rewrite Hsp'; pose proof Hstatic as (_ & _ & _ & _ & Hshi & _); pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _); rewrite Eshi; unfold x_sp in *; lia|].
  split; [intros a Ha; apply Hpw; rewrite Hsp' in Ha; unfold ESTACK in *; lia|].
  split; [rewrite R3; exact Hgp | rewrite R4; exact Htp]. }
(* the row keeps the world (W2 = Wc): its SRr lifts to SRr' *)
eapply (SRr'_mono SEGS RZ_cf).
{ apply SRr_SRr'.
  apply (SNPX lyc Sc Hpc Wc regsc memc mdc u f fmt c HPRE2).
  - rewrite Hsp'. unfold STK_RT_PRINTF, ESTACK in *. lia.
  - intros a Ha. apply Hpw. rewrite Hsp' in Ha. unfold STK_RT_PRINTF, ESTACK in *. lia.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - destruct Hfmt as [(_ & ->) | (_ & ->)]; [left | right]; reflexivity.
  - exact Hc.
  - intros k _. pose proof Hfsrc as (Hfby & Hf4096 & Hfc & Hfam & Hfrad & Hfhull).
    rewrite length_app in Hfc, Hfam, Hfrad, Hfhull. cbn [length] in Hfc, Hfam, Hfrad, Hfhull.
    rewrite Nat2Z.inj_add in Hfc, Hfam, Hfrad, Hfhull. cbn [Z.of_nat Pos.of_succ_nat] in Hfc, Hfam, Hfrad, Hfhull.
    split; [exact Hfby|]. split; [lia|]. split; [lia|]. split; [exact Hfam|]. split; [exact Hfrad|]. apply Hfhull. lia.
  - exact Hcan.
  - unfold u. lia.
  - unfold u. lia.
  - unfold amem_range, u. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  - intros a Ha.
    assert (Haw : awr_byte (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (ablocks B (x_ly X) (x_S X))
      (ablocks B lyc Sc) lyc [(0, pos)] a).
    { unfold awr_byte. right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. unfold u in Ha. lia. }
    destruct (awr_byte_present_xR SEGS B (@prh_pst prh_img_A) ARx LAWS (wle' SEGS RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Haw)
      as (Hpa & Hno).
    split; [apply (apresent_writable SEGS); exact Hpa|]. split; [exact Hno|].
    rewrite Hsp'. unfold u in Ha. unfold STK_RT_PRINTF, ESTACK in *. clear - Ha HKp HFceil HSPc HR. lia.
  - apply (pe_radd X pos Wc memc); [exact HF32 | lia | exact SH4].
  - apply (hull_sub _ (x_F X pos) 64); [|unfold u; lia|unfold u; lia].
    pose proof (HFHULL _ _ _ _ _ _ 0 pos HAR HinF) as Hh. rewrite EF in Hh. exact Hh.
  - exact Hro.
  - exact Hcv.
  - rewrite Forall_forall in Hcr |- *. intros [p n] Hin. destruct (Hcr _ Hin) as (Hn & _).
    pose proof (pe_cr_img _ Hin) as Hall. cbn [fst snd] in *.
    pose proof (segs_low _ (Hall p ltac:(lia))) as L0. pose proof (segs_low _ (Hall (p + n - 1) ltac:(lia))) as L1.
    unfold kLowMemEnd in *. lia.
  - rewrite Forall_forall in Hcr |- *. intros [p n] Hin. destruct (Hcr _ Hin) as (Hn & _).
    exact (IW p n Hn (pe_cr_img _ Hin)).
  - lia.
  - unfold kLowMemEnd in *. lia.
  - lia.
  - unfold kLowMemEnd in *. lia.
  - apply IW; [lia | intros a Ha; replace a with (gcan + (a - gcan)) by lia; apply Hgimg; lia].
  - apply IW; [lia | intros a Ha; replace a with (can + (a - can)) by lia; apply Hcimg2; lia].
  - apply IW; [lia | exact Hfimg].
  - clear - Hfb. lia.
  - exact Hfg.
  - rewrite Hsp'. unfold x_sp in *. unfold STK_RT_PRINTF, ESTACK in *. lia.
  - unfold amem_range, u. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  - rewrite EF in Hftop. unfold zdisjoint, u; cbn [fst snd]. clear - Hftop. lia.
  - (* the row's entry rounding mode: the CURRENT float state's frm = 0 (ps_commonR's ps_float) *)
    exact Hfz. }
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & Hc2 & Hfk' & Hfrm' & HAR2 & HP2 & Hsame & Hres & Hgar & Hfr &
  Hpres2 & Hmn).
pose proof (PCALL _ _ Hmn HPM) as HPM2.
set (T := YGcallSnpCk.snp_esc_render fmt c) in *.
assert (HTl : (length T <= 6)%nat).
{ unfold T, YGcallSnpCk.snp_esc_render. destruct (list_eq_dec Z.eq_dec fmt YGcallSnpCk.snp_esc_fmt_c); cbn [length]; lia. }
assert (HJ2 : AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X)
  (x_W X) (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc mem2 md2 kc).
{ apply (ajournal_x_after_writeR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS segs_low (wle' SEGS RZ_cf)
    (STK_put_string + x_d X)
    (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc memc mdc kc
    mem2 md2 (fun a => (u <= a < u + Z.of_nat (length T) + 1) \/ (spZ regsc - STK_RT_PRINTF <= a < spZ regsc)) Sc Hpc
    [(0, pos)] HJ).
  - intros a Ha Hna. apply Hfr; [exact Ha | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left.
    + unfold awr_byte. right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. unfold u in Ha. lia.
    + unfold awr_byte. left. rewrite Hsp' in Ha. unfold STK_RT_PRINTF, ESTACK in *. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT.
  - (* the cut's ajournal_x_after_write (YCbqG.v 219748197d6b :734): the wild depot is kept *)
    reflexivity. }
assert (KK0 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_R X - STK_RT_PRINTF <= a < x_R X) -> ~ (x_F X pos + 32 <= a < x_F X pos + 40) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hw Hu. apply Hfr; [exact Ha | unfold u in *; lia | rewrite Hsp'; unfold STK_RT_PRINTF, ESTACK in *; lia]. }
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [rewrite Hc2; unfold cfg_at, raZ; rewrite H1; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact Hfrm'|].
split; [exact (pe_fk_of_row fx fx' Hfk')|].
split; [exact (pe_s_move (fx := fx) X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc regs2 mem2 md2 kc Hpre Hs HP2 HJ2 HPM2 KK0)|].
intros j Hj. exact (YGcallSnpCk.snp_aview_of_garr8 SEGS (w_H Wc) mem2 u (T ++ [0]) j Hgar Hj).
Qed.

(* the escape by format, to the re-poison join: the row, the move of the escape state to the row's float state fx',
   then the tail stretch at fx' (Section fl's pe_tail, generic in the float state) *)
Lemma pe_snp : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc f fmt,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  ((nth i (x_bs X) 0 = 34 \/ nth i (x_bs X) 0 = 92) /\ f = ps_str 93 /\ fmt = YGcallSnpCk.snp_esc_fmt_c \/
   (nth i (x_bs X) 0 <> 34 /\ nth i (x_bs X) 0 <> 92 /\ nth i (x_bs X) 0 <> 10 /\ nth i (x_bs X) 0 <> 9 /\
    nth i (x_bs X) 0 <> 13) /\ f = ps_str 89 /\ fmt = YGcallSnpCk.snp_esc_fmt_x) ->
  getr regsc 10 = w64 (x_F X pos + 32) -> getr regsc 11 = w64 8 -> getr regsc 12 = w64 f ->
  getr regsc 13 = w64 (nth i (x_bs X) 0) -> getr regsc 1 = Z_to_bv 64 (BASE + (AF_put_string + 560)) ->
  pe_KF X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS___wrap_snprintf)) memc (seg_rom SEGS)) mdc) (ps_Qfin X).
Proof.
intros X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc f fmt Hs Hcase H10 H11 H12 H13 H1 K.
assert (Hfmt : f = ps_str 93 /\ fmt = YGcallSnpCk.snp_esc_fmt_c \/ f = ps_str 89 /\ fmt = YGcallSnpCk.snp_esc_fmt_x)
  by (destruct Hcase as [(_ & Hf & Hm) | (_ & Hf & Hm)]; [left | right]; split; assumption).
assert (Hrend : YGcallSnpCk.snp_esc_render fmt (nth i (x_bs X) 0) = WriterSpec.esc (nth i (x_bs X) 0)).
{ destruct Hcase as [(Hc & _ & ->) | ((H34 & H92 & H10' & H9 & H13') & _ & ->)].
  - exact (pe_render_c _ Hc).
  - exact (pe_render_x _ H34 H92 H10' H9 H13'). }
pose proof Hs as (Hcom & _). pose proof Hcom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hfk)).
eapply (SRr'_bind SEGS RZ_cf);
  [exact (pe_snp_call X ch Hpre pos i P lyc Sc Hpc Wc regsc memc mdc kc f fmt Hs Hfmt H10 H11 H12 H13 H1)|].
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & Hz' & Hk' & Hs2 & Hr2).
rewrite Hrend in Hr2.
pose proof (ps_fk_trans (x_fx X) fx fx' Hfk Hk') as Hk2.
exact (pe_tail (fx := fx') X ch Hpre HS0 560 pos i P lyc Sc Hpc Wc regs2 mem2 md2 kc (or_intror eq_refl)
  (pe_s_refx fx fx' X pos i P lyc Sc Hpc Wc regs2 mem2 md2 kc Hs2 Hz' Hk2) Hr2 (K fx' Hz' Hk2)).
Qed.

(* ---- the two kinds of call state at the end of the escape's branches (A 0x88580 / 0x88598) ---- *)
Lemma pe_leaf_cpy : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc (ss : sstate) ms mdx n lit,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  st_ok SEGS (pe_E regsc) (setpc ss (SIGMA AS___asan_memcpy)) (restrict (w_H Wc) ms) -> ss_resv ss = None ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) pe_csl = true ->
  sr_get (ss_regs ss) 10%bv = SOff 21 0 -> sr_get (ss_regs ss) 11%bv = SOff n 0 -> sr_get (ss_regs ss) 12%bv = SLit 3 ->
  sr_get (ss_regs ss) 1%bv = SOff A_TEXT (AF_put_string + 536) ->
  ew (pe_E regsc) n = Z_to_bv 64 lit -> 0 <= lit < 2 ^ 64 ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc (ms_mem ms) mdx kc -> Pm (ms_mem ms) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a) ->
  (nth i (x_bs X) 0 = 9 /\ lit = ps_str 85 \/ nth i (x_bs X) 0 = 10 /\ lit = ps_str 87 \/
   nth i (x_bs X) 0 = 13 /\ lit = ps_str 91) ->
  pe_K X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg ms mdx) (ps_Qfin X).
Proof.
intros X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc ss ms mdx n lit Hs HS Hrv Hcs H10 H11 H12 H1 En Hl HJ HPM KM
  Hcase K.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS Hrv). cbn [ss_pc setpc].
pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regsc pe_extra) Hcs) as HP.
pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 21%bv HS (pe_agree regsc pe_extra) H10) as A0.
pose proof (pe_reg_sv _ _ _ _ 11%bv _ HS H11) as A1.
pose proof (pe_reg_sv _ _ _ _ 12%bv _ HS H12) as A2.
pose proof (pe_ra _ _ _ _ _ HS (Eimg_env _) H1) as RA.
pose proof Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R21 & _).
apply (pe_cpy X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdx kc lit).
- apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc (ms_regs ms) (ms_mem ms) mdx kc Hpre Hs HP HJ HPM).
  intros a Ha _ _. exact (KM a Ha).
- exact Hcase.
- rewrite A0. exact R21.
- rewrite A1. exact (pe_atom_val _ n lit En Hl).
- rewrite A2. reflexivity.
- exact RA.
- exact K.
Qed.
Lemma pe_leaf_snp : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc (ss : sstate) ms mdx n f fmt,
  pe_s X pos i P lyc Sc Hpc Wc regsc memc mdc kc -> getr regsc 27 = w64 (nth i (x_bs X) 0) ->
  st_ok SEGS (pe_E regsc) (setpc ss (SIGMA AS___wrap_snprintf)) (restrict (w_H Wc) ms) -> ss_resv ss = None ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) pe_csl = true ->
  sr_get (ss_regs ss) 10%bv = SOff 21 0 -> sr_get (ss_regs ss) 11%bv = SLit 8 -> sr_get (ss_regs ss) 12%bv = SOff n 0 ->
  sr_get (ss_regs ss) 13%bv = SOff 27 0 -> sr_get (ss_regs ss) 1%bv = SOff A_TEXT (AF_put_string + 560) ->
  ew (pe_E regsc) n = Z_to_bv 64 f -> 0 <= f < 2 ^ 64 ->
  AJR (wle' SEGS RZ_cf) (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X)
     (x_mem X) (x_md X) [(0, pos)] lyc Sc Hpc Wc (ms_mem ms) mdx kc -> Pm (ms_mem ms) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a) ->
  ((nth i (x_bs X) 0 = 34 \/ nth i (x_bs X) 0 = 92) /\ f = ps_str 93 /\ fmt = YGcallSnpCk.snp_esc_fmt_c \/
   (nth i (x_bs X) 0 <> 34 /\ nth i (x_bs X) 0 <> 92 /\ nth i (x_bs X) 0 <> 10 /\ nth i (x_bs X) 0 <> 9 /\
    nth i (x_bs X) 0 <> 13) /\ f = ps_str 89 /\ fmt = YGcallSnpCk.snp_esc_fmt_x) ->
  pe_KF X pos i P ->
  SRr' SEGS RZ_cf Wc (mkCfg ms mdx) (ps_Qfin X).
Proof.
intros X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc ss ms mdx n f fmt Hs R27 HS Hrv Hcs H10 H11 H12 H13 H1
  En Hl HJ HPM KM Hcase K.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS Hrv). cbn [ss_pc setpc].
pose proof (pe_pres _ _ _ _ _ _ HS (pe_agree regsc pe_extra) Hcs) as HP.
pose proof (pe_reg_of _ _ _ _ _ _ 10%bv 21%bv HS (pe_agree regsc pe_extra) H10) as A0.
pose proof (pe_reg_sv _ _ _ _ 11%bv _ HS H11) as A1.
pose proof (pe_reg_sv _ _ _ _ 12%bv _ HS H12) as A2.
pose proof (pe_reg_of _ _ _ _ _ _ 13%bv 27%bv HS (pe_agree regsc pe_extra) H13) as A3.
pose proof (pe_ra _ _ _ _ _ HS (Eimg_env _) H1) as RA.
pose proof Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R21 & _).
apply (pe_snp X ch Hpre HS0 pos i P lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdx kc f fmt).
- apply (pe_s_move X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc (ms_regs ms) (ms_mem ms) mdx kc Hpre Hs HP HJ HPM).
  intros a Ha _ _. exact (KM a Ha).
- exact Hcase.
- rewrite A0. exact R21.
- rewrite A1. reflexivity.
- rewrite A2. exact (pe_atom_val _ n f En Hl).
- rewrite A3. exact R27.
- exact RA.
- exact K.
Qed.

(* ---- the stretch's own code: the seat at A 0x88518, the escape's dispatch on c, to the calls ----
   A 0x88518 li a0,12; bge a0,s2 (c <= 12 -> 0x88544) | li a0,13; beq s2,a0 (c = 13 -> memcpy .str.21) | li a0,92;
   beq s2,a0 (c = 92 -> snprintf "\\%c") | bne s2,s9 (c <> 34 -> snprintf "\\u%04x"; c = 34 -> snprintf "\\%c");
   A 0x88544 li a0,9; beq s2,a0 (c = 9 -> memcpy .str.20) | li a0,10; bne s2,a0 (c <> 10 -> snprintf "\\u%04x";
   c = 10 -> memcpy .str.19). *)
Ltac pe_bool H := first
  [ apply Z.eqb_eq in H | apply Z.eqb_neq in H
  | apply negb_true_iff in H; first [apply Z.eqb_neq in H | apply Z.ltb_ge in H]
  | apply negb_false_iff in H; first [apply Z.eqb_eq in H | apply Z.ltb_lt in H] ].
(* the branch condition on c (atom 18) against a literal or s9 (atom 25, = 34), as a fact named Hb *)
Ltac pe_hc E18 E25 Hcr Hc256 Hb :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite ?branch_eq_U, ?branch_ne_U, ?pe_br_ge in Hc;
    rewrite ?(U_atom _ 18 _ E18 Hcr), ?(U_atom _ 25 34 E25 ltac:(clear - Hc256; lia)) in Hc;
    rewrite ?U_lit in Hc by (clear - Hc256; lia);
    rewrite ?YO0b.s64_small in Hc by (clear - Hc256; lia);
    pe_bool Hc;
    rename Hc into Hb
  end.
Ltac pe_nowin := let a' := fresh "a" in let r' := fresh "r" in let Hin' := fresh "Hin" in let Ha' := fresh "Ha" in
  intros a' (r' & Hin' & Ha'); vm_compute in Hin'; destruct Hin' as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha'; lia.
Ltac pe_km KMc :=
  lazymatch type of KMc with forall a, _ -> aview _ (w_H ?W) ?m1 a = _ =>
    lazymatch goal with HF' : frame_of _ _ (mrestrict (w_H W) m1) (mrestrict (w_H W) ?m2) |- _ =>
      let KN := fresh "KMn" in
      pose proof (fun a Ha => eq_trans (pe_keep_nowin _ _ _ _ _ HF' ltac:(pe_nowin) a Ha) (KMc a Ha)) as KN;
      clear HF' KMc; rename KN into KMc
    end
  end.
Ltac pe_run HS HJ HPM KMc :=
  pnt_run_to_inv NTRUNTOI HS HJ HPM (AF_put_string + 560);
  [ let a' := fresh "a" in let Hw := fresh "Hw" in intros a' Hw; exfalso; revert a' Hw; pe_nowin | pe_km KMc ].

Lemma ps_esc_run : forall X ch, ps_pre X ch -> ps_s0 X ->
  forall pos i P lyc Sc Hpc Wc regsc memc mdc kc, ps_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc ->
  (forall fx' : YK11.FPState, YK0o.frm_zero (@YK11.fp_csr fx') -> fregs_kept_x (x_fx X) fx' ->
   forall lyn Sn Hpn Wn regsn memn mdn kn,
     PRW_put_string_base.ps_next (fx := fx') B ARx Pm X pos i (S i) (P ++ [WriterSpec.esc (nth i (x_bs X) 0)])
       lyn Sn Hpn Wn regsn memn mdn kn ->
     SRr' SEGS RZ_cf Wn (mkCfg (@mkst fx' regsn (Z_to_bv 64 (BASE + (AF_put_string + 588))) memn (seg_rom SEGS)) mdn)
       (ps_Qfin X)) ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_put_string + 428))) memc (seg_rom SEGS)) mdc)
    (ps_Qfin X).
Proof.
intros X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc Hesc K.
unfold SRr'.
change (pe_KF X pos i P) in K.
pose proof (pe_s_of_esc X pos i P lyc Sc Hpc Wc regsc memc mdc kc Hesc) as Hs0.
pose proof Hesc as (Hcom & Hi & Hsp & _ & _ & _ & _ & _ & _ & R18 & _ & _ & _ & _ & _ & _ & R25 & R27 & _ &
  _ & _ & W24 & W32 & W40 & W48 & W56).
pose proof Hcom as (HJ & _ & _ & _ & HPM & _ & _ & _ & _ & (HZ & HFK)).
(* the memcpy arms keep the float state: their continuation is K at fx' := fx *)
pose proof (K fx HZ HFK) as Kx.
pose proof (pe_c_range X ch i Hpre Hi) as Hc256.
pose proof (pe_seat428 X ch pos i P lyc Sc Hpc Wc regsc memc mdc kc Hpre Hesc) as HS.
assert (HEI : img_env VAL A_LIM (pe_E regsc)) by (unfold pe_E; apply Eimg_env).
assert (E18 : ew (pe_E regsc) 18 = Z_to_bv 64 (nth i (x_bs X) 0))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact R18).
assert (E25 : ew (pe_E regsc) 25 = Z_to_bv 64 34)
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew (pe_E regsc) 32 = Z_to_bv 64 (ps_str 91))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew (pe_E regsc) 33 = Z_to_bv 64 (ps_str 89))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew (pe_E regsc) 34 = Z_to_bv 64 (ps_str 87))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew (pe_E regsc) 35 = Z_to_bv 64 (ps_str 85))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E36 : ew (pe_E regsc) 36 = Z_to_bv 64 (ps_str 93))
  by (unfold pe_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 4)).
pose proof (rdword_range_ps _ _ _ _ W24) as V91. pose proof (rdword_range_ps _ _ _ _ W32) as V89.
pose proof (rdword_range_ps _ _ _ _ W40) as V87. pose proof (rdword_range_ps _ _ _ _ W48) as V85.
pose proof (rdword_range_ps _ _ _ _ W56) as V93.
assert (Hcr : 0 <= nth i (x_bs X) 0 < 2 ^ 64) by (clear - Hc256; lia).
assert (KMc : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a)
  by (intros a _; reflexivity).
clear Hesc Hcom W24 W32 W40 W48 W56.
pe_run HS HJ HPM KMc.
pnt_branch BR HS.
- (* 12 >= c *)
  pe_hc E18 E25 Hcr Hc256 Hb1. pe_run HS HJ HPM KMc. pnt_branch BR HS.
  + (* c = 9: __asan_memcpy (u, .str.20, 3) *)
    pe_hc E18 E25 Hcr Hc256 Hb2. pe_run HS HJ HPM KMc.
    apply (pe_leaf_cpy X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 35 (ps_str 85) Hs0 HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | exact E35 | exact V85 | exact HJ | exact HPM | exact KMc
      | left; split; [clear - Hb2; lia | reflexivity]
      | exact Kx ].
  + pe_hc E18 E25 Hcr Hc256 Hb2. pe_run HS HJ HPM KMc. pnt_branch BR HS.
    * (* c <> 9, c <> 10, c <= 12: __wrap_snprintf (u, 8, "\\u%04x", c) *)
      pe_hc E18 E25 Hcr Hc256 Hb3. pe_run HS HJ HPM KMc.
      apply (pe_leaf_snp X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 33 (ps_str 89)
        YGcallSnpCk.snp_esc_fmt_x Hs0 R27 HS);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | exact E33 | exact V89 | exact HJ | exact HPM | exact KMc
        | right; split; [clear - Hb1 Hb2 Hb3; repeat split; lia | split; reflexivity]
        | exact K ].
    * (* c = 10: __asan_memcpy (u, .str.19, 3) *)
      pe_hc E18 E25 Hcr Hc256 Hb3. pe_run HS HJ HPM KMc.
      apply (pe_leaf_cpy X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 34 (ps_str 87) Hs0 HS);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity
        | exact E34 | exact V87 | exact HJ | exact HPM | exact KMc
        | right; left; split; [clear - Hb3; lia | reflexivity]
        | exact Kx ].
- (* c > 12 *)
  pe_hc E18 E25 Hcr Hc256 Hb1. pe_run HS HJ HPM KMc. pnt_branch BR HS.
  + (* c = 13: __asan_memcpy (u, .str.21, 3) *)
    pe_hc E18 E25 Hcr Hc256 Hb2. pe_run HS HJ HPM KMc.
    apply (pe_leaf_cpy X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 32 (ps_str 91) Hs0 HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | exact E32 | exact V91 | exact HJ | exact HPM | exact KMc
      | right; right; split; [clear - Hb2; lia | reflexivity]
      | exact Kx ].
  + pe_hc E18 E25 Hcr Hc256 Hb2. pe_run HS HJ HPM KMc. pnt_branch BR HS.
    * (* c = 92: __wrap_snprintf (u, 8, "\\%c", c) *)
      pe_hc E18 E25 Hcr Hc256 Hb3. pe_run HS HJ HPM KMc.
      apply (pe_leaf_snp X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 36 (ps_str 93)
        YGcallSnpCk.snp_esc_fmt_c Hs0 R27 HS);
        [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
        | exact E36 | exact V93 | exact HJ | exact HPM | exact KMc
        | left; split; [right; clear - Hb3; lia | split; reflexivity]
        | exact K ].
    * pe_hc E18 E25 Hcr Hc256 Hb3. pe_run HS HJ HPM KMc. pnt_branch BR HS.
      -- (* c <> 34, c <> 92, c <> 13, c > 12: __wrap_snprintf (u, 8, "\\u%04x", c) *)
         pe_hc E18 E25 Hcr Hc256 Hb4. pe_run HS HJ HPM KMc.
         apply (pe_leaf_snp X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 33 (ps_str 89)
           YGcallSnpCk.snp_esc_fmt_x Hs0 R27 HS);
           [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
           | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
           | exact E33 | exact V89 | exact HJ | exact HPM | exact KMc
           | right; split; [clear - Hb1 Hb2 Hb3 Hb4; repeat split; lia | split; reflexivity]
           | exact K ].
      -- (* c = 34: __wrap_snprintf (u, 8, "\\%c", c) *)
         pe_hc E18 E25 Hcr Hc256 Hb4. pe_run HS HJ HPM KMc.
         apply (pe_leaf_snp X ch Hpre HS0 pos i P lyc Sc Hpc Wc regsc memc mdc kc _ _ _ 36 (ps_str 93)
           YGcallSnpCk.snp_esc_fmt_c Hs0 R27 HS);
           [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
           | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
           | exact E36 | exact V93 | exact HJ | exact HPM | exact KMc
           | left; split; [left; clear - Hb4; lia | split; reflexivity]
           | exact K ].
Qed.
End fl2.
End h.
End f.
End d.

Print Assumptions ps_esc_run.
About ps_esc_run.
Set Printing All. Check ps_esc_run. Unset Printing All.
