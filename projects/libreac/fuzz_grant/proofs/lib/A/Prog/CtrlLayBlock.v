(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* ctrl_lay_block (0x82ffc) on fuzz_grant's ASan build, for the one call the
   program makes: reac_ctrl_stamp_headamp passes the static control-frame row
   CTRL_FRAMES[CTRL_HEADAMP] (A_OBJ 18 = 0x9c670, byte +2 = 2 = BLOCK_TMPL) and
   a null model pointer, so the jump table at A_OBJ 24 = 0x20ff4 sends the walk
   to the template case (entry 2 = 0x831d8) and the call of reac_box_model_block
   at 0x8322c is not reached.

   The call writes the caller's 32 bytes [p+18, p+50), so the contract is in
   cgif's caller-journal form (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365):
   the premise is the caller's journal, the right to write those bytes is a
   premise the caller supplies per byte, and the post extends the same journal.
   The three definitions tcj_kept, twr_ok and tsrc_ok are shared with
   CtrlStampHeadamp.v and CtrlBuildGrantSweep.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YN3g YI0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase
YC4b YC81 YC88 YCbw YCkd YC1g YC1h YC45 YC85 GrantFrame GrantRo CtrlFinish CtrlLayBlockSpec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1i ACj1 ACbf GrantACjr GrantACja PaJr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
(* proof speed: zone_lia as ACbf.v's own proofs run it (ACbf.v zone_lia_nd); Local, so it reaches no importer *)
Local Ltac zone_lia ::= zone_lia_nd.
(* Proof speed only (an internal proof-speed note): rs_hide_all hides the context's disjunctions and mod facts from
   lia; `unfold rs_hold in *` gives them back.  Used around add_flag_region below, whose flag_disj_cheap and fallback
   branches call lia once per region with the whole context in scope. *)
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
Context {RO : GrantBase.ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* A_JT, ROW_BYTES, TLAY_STK and EV_LAY are CtrlLayBlockSpec.v's, with the
   contract; A_ROW is CtrlFinish.v's, SB is YC81.v's. *)
Notation SB := YC81.SB.
(* the walk's symbolic entry state *)
Definition Bx_LAY : sv := SOff 32 0.
Definition Bspan_LAY : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lay_regions : smem :=
[ stack_region 128; got_regionP; bcell_regionP 32; uar_got_regionP 274; uar_cell_regionP 274 ].
Definition lay_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_lay : sstate := mkSS AF_ctrl_lay_block sr_atoms lay_regions None lay_facts.
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
(* ---- what the image holds -------------------------------------------------
   TM is the template pointer the row carries (0x21180 in fuzz_grant.asan); JE
   is the jump table's entry for the template case (0x621e4, so the `jr` at
   0x8315c goes to VAL (A_OBJ 24) + JE = BASE + AF_ctrl_lay_block + 0x1dc).
   Each hypothesis is a fact of the image alone; each is discharged in GrantClose.v, at
   GrantImg.v's instance PI_grant, by computation over the image's read-only bytes. *)
Variable TM : Z.
Variable JE : Z.
Hypothesis HTM_rng : IMG_LO + 64 <= TM /\ TM + 32 + 64 <= IMG_HI.
Hypothesis HROW_rng : IMG_LO + 64 <= VAL (A_OBJ A_ROW) /\ VAL (A_OBJ A_ROW) + ROW_BYTES + 64 <= IMG_HI.
Hypothesis HJT_rng : IMG_LO + 64 <= VAL (A_OBJ A_JT) /\ VAL (A_OBJ A_JT) + 40 + 64 <= IMG_HI.
Hypothesis HJT_eq : VAL (A_OBJ A_JT) + JE = BASE + AF_ctrl_lay_block + 0x1dc.
(* The entry is a positive 31-bit offset: the `lw` at 0x83150 sign-extends it. *)
Hypothesis HJE_rng : 0 <= JE < 2 ^ 31.
(* The row and the table are two read-only regions the walk declares at once. *)
Hypothesis HROW_JT : VAL (A_OBJ A_ROW) + ROW_BYTES <= VAL (A_OBJ A_JT) \/ VAL (A_OBJ A_JT) + 40 <= VAL (A_OBJ A_ROW).
Hypothesis HROW_k : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_ROW) + 2) 1 2.
Hypothesis HROW_tm : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_ROW) + 8) 8 TM.
Hypothesis HROW_ao : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_ROW) + 16) 1 18.
Hypothesis HROW_al : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_ROW) + 17) 1 3.
Hypothesis HJT_e : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ A_JT) + 8) 4 JE.
Hypothesis HTMPL : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
garr8 SEGS (mrestrict H mem) TM T32z.
(* The bytes of the image's constants are marked usable, and the shadow of the
   image's read range is mapped: GrantRo.v proves both from these, and the
   composition discharges them from the runtime's own symbols. *)
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HZS_ROW : in_zs B (VAL (A_OBJ A_ROW)) ROW_BYTES.
Hypothesis HZS_TM : in_zs B TM 32.
Hypothesis HZS_JT : in_zs B (VAL (A_OBJ A_JT)) 40.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Definition lay_extra : list word := map (Z_to_bv 64) [SB; TM; JE].
Lemma denot_atom_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v H H1 H2 H3. rewrite denot_lit_U, (U_atom_off E n v c H ltac:(lia) ltac:(lia)). reflexivity. Qed.
Lemma denot_lit0 : forall E k, 0 <= k < 2 ^ 64 -> sv_denot E (SLit k) = Z_to_bv 64 k.
Proof. intros E k Hk. rewrite denot_lit_U, U_SLit, zcanon_id by (rewrite M64_val; lia). reflexivity. Qed.
Lemma ra_of_kept : forall (rd rd' : Z -> option Z) off a n (P : Z -> Prop),
(forall s, P s -> rd' s = rd s) -> (forall x, a <= x < a + n -> P (shadow_of_addr off x)) ->
range_addressable rd off a n -> range_addressable rd' off a n.
Proof.
intros rd rd' off a n P HK HP HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s.
split; [rewrite (HK _ (HP x Hx)); exact Hs | exact Hok].
Qed.
Lemma sfs_set_fs : forall c q S2 Sc f, S2 = set_fs f Sc -> exists f', stack_free_state c q S2 = set_fs f' Sc.
Proof. intros c q S2 Sc f ->. unfold stack_free_state. eexists. destruct Sc; reflexivity. Qed.
Lemma denot_atom0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite denot_lit_U, (U_atom E n v H Hv). reflexivity. Qed.
Lemma denot_add0 : forall E e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD e (SLit 0)) = Z_to_bv 64 v.
Proof.
intros E e v He Hv. rewrite denot_lit_U, (U_add0 E e), <- denot_lit_U. exact He.
Qed.
(* The machine stack is marked usable in every state the allocator invariant holds
   (lib/Reusable/YG0n.v:188-191), so the caller's 32 bytes stay usable across the
   frame this call takes on the side stack for frames. *)
Lemma stack_cells0 : forall ly S (W : world SEGS) mem md s,
AR SEGS B ly S W mem md -> SHADOW_OFF + ly_stk_lo ly / 8 <= s < SHADOW_OFF + ly_stk_hi ly / 8 ->
aview SEGS (w_H W) mem s = Some 0.
Proof.
intros ly S W mem md s HAR Hs.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow, shadow_of_addr in Hz.
assert (A : ly_stk_lo ly = 4096 * (ly_stk_lo ly / 4096)) by (pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)); lia).
assert (C : ly_stk_hi ly = 4096 * (ly_stk_hi ly / 4096)) by (pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)); lia).
assert (Dlo : ly_stk_lo ly / 8 = 512 * (ly_stk_lo ly / 4096))
by (rewrite A at 1; replace (4096 * (ly_stk_lo ly / 4096)) with (512 * (ly_stk_lo ly / 4096) * 8) by lia; apply Z.div_mul; lia).
assert (Dhi : ly_stk_hi ly / 8 = 512 * (ly_stk_hi ly / 4096))
by (rewrite C at 1; replace (4096 * (ly_stk_hi ly / 4096)) with (512 * (ly_stk_hi ly / 4096) * 8) by lia; apply Z.div_mul; lia).
assert (Dd : (ly_stk_hi ly - ly_stk_lo ly) / 8 = 512 * (ly_stk_hi ly / 4096) - 512 * (ly_stk_lo ly / 4096)).
{ rewrite A at 1. rewrite C at 1.
replace (4096 * (ly_stk_hi ly / 4096) - 4096 * (ly_stk_lo ly / 4096))
with ((512 * (ly_stk_hi ly / 4096) - 512 * (ly_stk_lo ly / 4096)) * 8) by lia. apply Z.div_mul; lia. }
specialize (Hz (s - (SHADOW_OFF + ly_stk_lo ly / 8))).
replace (SHADOW_OFF + ly_stk_lo ly / 8 + (s - (SHADOW_OFF + ly_stk_lo ly / 8))) with s in Hz by lia.
apply Hz. rewrite Dd. rewrite Dlo in Hs. rewrite Dhi in Hs. lia.
Qed.
Lemma stack_ra : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> 0 <= n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi Hn x Hx. exists 0. split; [|left; reflexivity].
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
assert (C : ly_stk_hi ly = 4096 * (ly_stk_hi ly / 4096)) by (pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)); lia).
assert (Dhi : ly_stk_hi ly / 8 = 512 * (ly_stk_hi ly / 4096))
by (rewrite C at 1; replace (4096 * (ly_stk_hi ly / 4096)) with (512 * (ly_stk_hi ly / 4096) * 8) by lia; apply Z.div_mul; lia).
apply (stack_cells0 ly S W mem md _ HAR). unfold shadow_of_addr.
split; [apply Z.add_le_mono_l, Z.div_le_mono; lia|].
apply Z.add_lt_mono_l. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.
Lemma stack_hull : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> 0 < n ->
shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi Hn s Hs.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
assert (A : ly_stk_lo ly = 4096 * (ly_stk_lo ly / 4096)) by (pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)); lia).
assert (C : ly_stk_hi ly = 4096 * (ly_stk_hi ly / 4096)) by (pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)); lia).
assert (Dlo : ly_stk_lo ly / 8 = 512 * (ly_stk_lo ly / 4096))
by (rewrite A at 1; replace (4096 * (ly_stk_lo ly / 4096)) with (512 * (ly_stk_lo ly / 4096) * 8) by lia; apply Z.div_mul; lia).
assert (Dhi : ly_stk_hi ly / 8 = 512 * (ly_stk_hi ly / 4096))
by (rewrite C at 1; replace (4096 * (ly_stk_hi ly / 4096)) with (512 * (ly_stk_hi ly / 4096) * 8) by lia; apply Z.div_mul; lia).
unfold shadow_addr in Hs.
assert (Hq1 : ly_stk_lo ly / 8 <= a / 8) by (apply Z.div_le_mono; lia).
assert (Hq2 : (a + n - 1) / 8 < ly_stk_hi ly / 8).
{ apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mul_div_le (ly_stk_hi ly) 8 ltac:(lia)). lia. }
assert (HL : SHADOW_OFF + ly_stk_lo ly / 8 <= (SHADOW_OFF + a / 8) / 8 * 8).
{ assert (HM : (SHADOW_OFF + ly_stk_lo ly / 8) mod 8 = 0)
by (rewrite Dlo; replace (SHADOW_OFF + 512 * (ly_stk_lo ly / 4096)) with ((268431360 + 64 * (ly_stk_lo ly / 4096)) * 8) by (unfold SHADOW_OFF; lia); apply Z_mod_mult).
pose proof (Z.div_mod (SHADOW_OFF + ly_stk_lo ly / 8) 8 ltac:(lia)) as Dm. rewrite HM, Z.add_0_r in Dm.
assert (Hdm : (SHADOW_OFF + ly_stk_lo ly / 8) / 8 <= (SHADOW_OFF + a / 8) / 8) by (apply Z.div_le_mono; lia). lia. }
assert (HH : (SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 + 8 <= SHADOW_OFF + ly_stk_hi ly / 8).
{ assert (HM : (SHADOW_OFF + ly_stk_hi ly / 8) mod 8 = 0)
by (rewrite Dhi; replace (SHADOW_OFF + 512 * (ly_stk_hi ly / 4096)) with ((268431360 + 64 * (ly_stk_hi ly / 4096)) * 8) by (unfold SHADOW_OFF; lia); apply Z_mod_mult).
pose proof (Z.div_mod (SHADOW_OFF + ly_stk_hi ly / 8) 8 ltac:(lia)) as Dm. rewrite HM, Z.add_0_r in Dm.
assert (Hdm : (SHADOW_OFF + (a + n - 1) / 8) / 8 < (SHADOW_OFF + ly_stk_hi ly / 8) / 8).
{ apply Z.div_lt_upper_bound; [lia|]. rewrite <- Dm. lia. }
lia. }
rewrite (stack_cells0 ly S W mem md s HAR ltac:(lia)). discriminate.
Qed.
(* the image's read-only bytes still read as the image after a journal step *)
Lemma rod_two : forall STK1 sp01 FP1 ly1 S1 W01 mem01 md01 own1 lyc1 Sc1 Wc1 memc1 mdc1 k1
own2 ly2 S2 W2 mem2 md2 k2,
ajournal SEGS B STK1 sp01 FP1 ly1 S1 W01 mem01 md01 own1 lyc1 Sc1 Wc1 memc1 mdc1 k1 ->
ajournal SEGS B STK1 sp01 FP1 ly1 S1 W01 mem01 md01 own2 ly2 S2 W2 mem2 md2 k2 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc1) memc1) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros * HJ1 HJ2 HR a Hro Ho He.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Himg : in_img SEGS a)
by (destruct Hro as [(sg & Hsg & _ & Hr) | Hgot]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hgot)]).
assert (Hsp : fp_spares FP1 a) by (apply (ro_spares SEGS pa_relro_lo pa_relro_hi FP1 a); exact Hro).
rewrite (F2 a Himg Ho He Hsp), <- (F1 a Himg Ho He Hsp). exact (HR a Hro Ho He).
Qed.
(* ---- the entry state ------------------------------------------------------ *)
Lemma lay_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - 128 <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs lay_extra)) ss_lay
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_ctrl_lay_block)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md HAR Hsplo Hsphi Hal16 Hpres.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TL) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 32 ltac:(lia)) as Hob32. pose proof (pa_obj_img 33 ltac:(lia)) as Hob33.
pose proof (palf_uar_img B TL) as Huar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs lay_extra)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j lay_extra (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth lay_extra map] in E32, E33, E34.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E274 : ew E (A_OBJ 33) = Z_to_bv 64 (VAL (A_OBJ 33))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Euar : as_uar_cell B = VAL (A_OBJ 33)) by (apply (pal_uar_cell B TL)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_lay. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold lay_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 33) 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E274, Euar, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite Euar; pose proof (pa_val_range (A_OBJ 33)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 274%nat (VAL (A_OBJ 33)) E274) by (pose proof (pa_val_range (A_OBJ 33)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 33)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r, <- Euar. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold lay_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
rewrite (VB 274%nat (VAL (A_OBJ 33)) E274) by (pose proof (pa_val_range (A_OBJ 33)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
rewrite Euar in Hsep.
revert Hsplo Hsphi Hob0 Hob1 Hob32 Hob33 Hsep. clear. intros.
repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok lay_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
split; [split; [lia | split; [exact Hal16 | lia]]|]. split; [|exact I].
unfold SB. lia.
Qed.
(* the shadow checks of the row's bytes: CTRL_FRAMES is marked usable (GrantRo.ro_usable) *)
Ltac obl_row AG E11 E32 HZS HARx :=
lazymatch goal with |- range_addressable _ (U ?Ex ?bx) (U _ (SOff 11 ?c)) ?len =>
rewrite (U_atom_off Ex 11 (VAL 259%nat) c);
[| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 11%nat) by lia; exact E11 | lia | lia];
let L := rnLAWS in
eapply (obl_of_range _ _ _ Ex bx _ len (VAL 259%nat) 24);
[ exact (ro_usable SEGS _ L _ _ _ _ _ (VAL 259%nat) 24 HARx HZS)
| rewrite (U_atom Ex 32 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32 | unfold SB; lia]
| lia | lia ] end.
(* carrying the caller's frame (the one that holds g) and its shadow across a step *)
Ltac upd_gk GP HGK HFr HGPd AG :=
let HGK2 := fresh "HGK" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HGK with forall a, GP a -> aview ?sg ?Hh _ a = aview _ _ ?me a =>
assert (HGK2 : forall a, GP a -> aview sg Hh (ms_mem msX) a = aview sg Hh me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hdd := fresh "Hdd" in
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros a Ha; pose proof (HGPd a Ha) as Hdd; try unfold SHADOW_OFF in Hdd; etransitivity; [| exact (HGK a Ha)]; apply aview_eq_of; apply HFr;
rewrite unsigned_lit_small by lia;
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first [lia | fail 2 "upd_gk: a write window meets the predicate"] |]);
solve [destruct Hin]
| clear HGK; rename HGK2 into HGK ] end end.
Ltac upd_gk_call GP HGK Hfrx HGPd :=
let HGK2 := fresh "HGK" in
lazymatch type of Hfrx with forall a, _ -> _ -> _ -> aview ?sg ?Hh ?mN a = aview _ _ _ a =>
lazymatch type of HGK with forall a, GP a -> aview _ _ _ a = aview _ _ ?me a =>
assert (HGK2 : forall a, GP a -> aview sg Hh mN a = aview sg Hh me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hdd := fresh "Hdd" in
intros a Ha; pose proof (HGPd a Ha) as Hdd; rewrite (Hfrx a ltac:(lia) ltac:(lia) ltac:(lia)); exact (HGK a Ha)
| clear HGK; rename HGK2 into HGK ] end end.
(* the bytes the epilogue's run writes: the machine stack, the frame, its shadow, the flag *)
Ltac wrange_lay AG fpos F FL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; fold FL; clear - Hr; lia
| left; left; unfold TLAY_STK, ESTACK in *; lia
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; fold F; unfold SB; clear - Hr; lia ]
| fail 2 "wrange_lay: no case for this window" ]
| ]);
solve [destruct Hin].
Ltac upd_keep HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> ~ (?q <= a < ?r) -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> ~ (q <= a < r) -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha Hn; rewrite <- (HUP a Ha Hn); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac awr_lay AG d2 d60 fpos FF EFA :=
awrFL_with ltac:(idtac; lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat d2);
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold TLAY_STK, ESTACK in *; lia | cbn [YP09.r_whi]; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat d60);
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold TLAY_STK, ESTACK in *; lia | cbn [YP09.r_whi]; lia |]
end) AG fpos FF EFA.
(* ---- the contract: CtrlLayBlockSpec.v; tcj_kept, twr_ok and tsrc_ok are
   CtrlFinish.v's ----------------------------------------------------------- *)
Theorem pb_ctrl_lay_block : tctrl_lay_block_spec B (BASE + AF_ctrl_lay_block) pa_relro_lo pa_relro_hi.
Proof.
unfold tctrl_lay_block_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p g ch pm v
HJc HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hal16 Hwlo Hwhi Hfrlen
Hp0 Hp63 Hamr Hnimg Hwr Hpstk Hpstk2 Hg0 Hsrc Hgarr Hgobj Hdisj.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJc as (HAR & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & Hstatic & _ & HQT).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TLAY_STK = 4256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct Hgobj as ((cid0 & pos0 & Hgfin & Hgcid & Hgal8 & Hglo & Hghi) & Hg8 & Hgra0).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid0 pos0 HAR Hgfin) as (HG4096 & HGceil & HGapp).
set (G0 := frame_addr lyc cid0 pos0) in *.
assert (HGbs8 : fs_frame_bytes cid0 mod 8 = 0)
by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; replace (64 * 2 ^ cid0) with ((8 * 2 ^ cid0) * 8) by lia; apply Z_mod_mult).
assert (HGbs0 : 0 <= fs_frame_bytes cid0) by (apply fs_frame_bytes_nonneg).
pose proof (Z.div_mod G0 8 ltac:(lia)) as DG. rewrite Hgal8, Z.add_0_r in DG.
pose proof (Z.div_mod (fs_frame_bytes cid0) 8 ltac:(lia)) as DB. rewrite HGbs8, Z.add_0_r in DB.
set (GP := fun a => G0 <= a < G0 + fs_frame_bytes cid0 \/
SHADOW_OFF + G0 / 8 <= a < SHADOW_OFF + G0 / 8 + fs_frame_bytes cid0 / 8) in *.
assert (HGPlo : forall a, GP a -> 0 <= a /\ a < alloc_ceiling).
{ intros a Ha. unfold GP in Ha. unfold SHADOW_OFF in *.
clear - Ha HG4096 HGceil HGapp DG DB HGbs0 C1. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp. lia. }
assert (Hsplo : 2 ^ 46 + 4256 <= spZ regs) by (unfold TLAY_STK, ESTACK in *; lia).
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
assert (Hpres128 : forall a, spZ regs - 128 <= a < spZ regs -> apresent (w_H W) memc a)
by (intros a Ha; apply Hpresc; unfold TLAY_STK, ESTACK in *; lia).
pose proof (ajournal_sub_init SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (sp0 - spZ regs + TLAY_STK) (sp0 + 0) [] 0
HJc eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) as HJL.
rewrite Z.add_0_r in HJL. pose proof HJL as HJ0L.
pose proof (lay_entry lyc Sc W regs memc mdc HAR ltac:(lia) Hsphi Hal16 Hpres128) as HS.
assert (SHOK : sh_ok SEGS Bx_LAY (@nil shent) (Eimg (Ereg regs lay_extra)) (mrestrict (w_H W) memc)) by constructor.
remember (Eimg (Ereg regs lay_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (VAL 259%nat)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E13 : ew E 13 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j lay_extra (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth lay_extra map] in E32, E33, E34.
assert (HAE : env_agree 32 (Ereg regs lay_extra) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
img_factsF E. img_hull_factsF.
unfold cfg_at. change (w64 (BASE + AF_ctrl_lay_block)) with (Z_to_bv 64 (BASE + AF_ctrl_lay_block)).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
(* the prologue, up to the realigned sp (0x83040) *)
paj_run_to_tok RUNTO HS HJL SHOK Bspan_LAY 0x2990.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | cbn [ew]; rewrite Usp; lia
| cbn [YP09.r_wlo]; unfold TLAY_STK, ESTACK in *; lia
| cbn [YP09.r_whi]; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
upd_aboveW_init HFr AG HUP.
assert (HGK : forall a, GP a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
upd_gk GP HGK HFr HGPlo AG.
clear_frames.
pose proof HJL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
(* the realigned stack pointer sp1 = (sp - 128) & -32, in sp and in s1 *)
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
as (Hsp1r & Hsp1al32 & Hsp1al16). fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(lia) ltac:(lia) ltac:(lia)) R2;
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1)
(denot_add0 Ev (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32))) sp1
(denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) R9 end.
(* sp1 becomes atom 60, in sp and in s1; the machine frame keeps its own window *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. ACj1.rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1)
by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R9; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32;
split; [clear - Hsp1 Hsplo Hsphi; lia | split; [exact Hsp1al32 | lia]])) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
(* the machine frame's live window is [sp - 96, sp): the saved registers *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs2 := eval vm_compute in (trim_stack rs (-96) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs2 HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by lia;
split; [clear - Hsp1 Hsplo; lia|]; split; [clear - Hsp1 Hsphi; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres1; unfold TLAY_STK, ESTACK in *; clear - Ho Hsp1 Hwlo Hwhi; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; clear - Hsp1 Hsplo Hsphi Hob241 Hob242 Hob273 Hob274 Huar; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
assert (SHOK2 : sh_ok SEGS Bx_LAY (@nil shent) ltac:(lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => exact Ev end)
(mrestrict (w_H W) ltac:(lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => exact (ms_mem msX) end))) by constructor.
(* on to the call of __asan_stack_malloc_1 *)
paj_run_tok RUN HS HJL SHOK2 Bspan_LAY.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0));
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold TLAY_STK, ESTACK in *; lia | cbn [YP09.r_whi]; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold TLAY_STK, ESTACK in *; lia | cbn [YP09.r_whi]; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
upd_gk GP HGK HFr HGPlo AG.
upd_aboveW HUP HFr AG. clear_frames.
aconstsF HJL Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2b end.
pmkst HS.
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msY)
(sp0 - spZ regs + TLAY_STK) sp0 [] lyc Sc W memc mdc [] lyc Sc _ 0 (sp1 - sp0) _ HJL) end.
- unfold spZ at 1. rewrite R2b. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold TLAY_STK, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [unfold AF_ctrl_lay_block; lia | reflexivity].
- change (fs_frames 1) with 8192. clear - Hcnt Hfrlen; lia. }
cbv beta. clear R1 R3 R4 R2b SHOK2.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK.
replace (sp0 + (sp1 - sp0) - 4096) with (sp1 - 4096) in HK by lia.
replace (sp0 + (sp1 - sp0)) with sp1 in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; unfold TLAY_STK, ESTACK in *; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
assert (EFA0 : forall c q, frame_addr lyc c q = frame_addr lyc c q) by reflexivity.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)
| fail]).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
(* the frame's flag address and shadow base become atoms 528 and 529 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. ACj1.rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL)
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the frame itself, with the flag pointer it carries at +120 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 516 528 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite RF, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1) with 128; rewrite RF; evalE AG; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the caller's frame that holds g, and its shadow, are left alone by this call *)
assert (HGsep : G0 + fs_frame_bytes cid0 <= F \/ F + 128 <= G0).
{ assert (HgfinS : In (cid0, pos0) (frames S2)) by (rewrite Hfrs2; right; exact Hgfin).
destruct (in_split _ _ Hgfin) as (l1 & l2 & Egf).
pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (1, fpos) (cid0, pos0) [] l1 l2 HAR2
ltac:(rewrite Hfrs2, Egf; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. lia. }
assert (HFal8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)) as DF32; rewrite HFal, Z.add_0_r in DF32;
rewrite DF32; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HFal8, Z.add_0_r in DF.
assert (HGPd : forall a, GP a ->
~ (spZ regs - 96 <= a < spZ regs) /\ ~ (sp1 <= a < sp1 + 32) /\ ~ (F <= a < F + 128) /\
~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) /\ 0 <= a < 2 ^ 64).
{ intros a Ha. unfold GP in Ha. unfold SHADOW_OFF in *.
clear - Ha HGsep HG4096 HGceil HGapp HFceil HF4096 HFapp Hsp1 Hsplo Hsphi C1 DG DF DB HGbs0
Hceil Hslo Hwlo Hwhi FFS Hes.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp, HFapp;
unfold TLAY_STK, ESTACK in *; lia. }
assert (HGK2 : forall a, GP a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. pose proof HK as (_ & _ & _ & K4 & _).
rewrite (K4 cid0 pos0 a Hgfin); [exact (HGK a Ha) | | intros []].
unfold GP in Ha. unfold frame_rng, in_zr, shadow_addr. cbn [fst snd]. fold G0.
unfold SHADOW_OFF in Ha |- *. lia. }
clear HGK. rename HGK2 into HGK.
assert (HSB : SB = SHADOW_OFF) by reflexivity.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- HSB in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E529, unsigned_lit_small by (unfold SB; lia);
split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- HSB in HFSpres;
apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; change (fs_frame_bytes 1) with 128; rewrite E529, RF; evalE AG;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
repeat split; first [zone_lia | fail])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the frame's magic, description and pc, and its shadow bytes (0xf1, 0xf3, 0) *)
paj_run_to_sh RUNTOP HS HJ2 0x2A60.
{ awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0. }
upd_gk GP HGK HFr HGPd AG.
upd_aboveW HUP HFr AG. clear_frames.
fs_roF HS. reshok HS.
paj_run_tok RUN HS HJ2 SHOK Bspan_LAY.
{ awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0. }
upd_gk GP HGK HFr HGPd AG.
upd_aboveW HUP HFr AG. clear_frames.
pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
assert (Hplo : ly_stk_lo lyc <= p + 18) by (rewrite Elo; unfold TLAY_STK, ESTACK in *; lia).
assert (Hphi : p + 50 <= ly_stk_hi lyc) by (rewrite Ehi; lia).
prreg HS (1%bv : bv 5) R1m. prreg HS (3%bv : bv 5) R3m. prreg HS (4%bv : bv 5) R4m.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (p + 18))
(denot_atom_off Ev 10 18 p ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(lia) ltac:(lia) ltac:(lia)) Ra0m;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 0) (denot_lit0 Ev 0 ltac:(lia)) Ra1m;
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 32) (denot_lit0 Ev 32 ltac:(lia)) Ra2m;
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2m end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA GS___asan_memset) AMEMSET W (ms_regs msX) (ms_mem msY)
(sp0 - spZ regs + TLAY_STK) sp0 [] lyc Sc W memc mdc [(1, fpos)] lyc S2 _ 0 (p + 18) 0 32 (sp1 - sp0) _ HJ2) end.
- rewrite Ra0m. reflexivity.
- rewrite Ra1m. reflexivity.
- rewrite Ra2m. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite R2m. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold TLAY_STK, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3m, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4m, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1m.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
  + left. unfold TLAY_STK, ESTACK in *. lia.
  + clear - Ha Hsp1 Hpstk; lia.
- exact Hamr.
- eapply (stack_ra lyc S2 W _ _ (p + 18) 32 (proj1 HJ2)); lia.
- intros _. eapply (stack_hull lyc S2 W _ _ (p + 18) 32 (proj1 HJ2)); lia.
- exact I. }
cbv beta.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3 & Hsame3).
assert (HUP3 : forall a, spZ regs <= a < 2 ^ 64 -> ~ (p + 18 <= a < p + 50) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn. rewrite (Hfr3 a ltac:(lia) ltac:(lia) ltac:(lia)). apply HUP. exact Ha. }
clear HUP. rename HUP3 into HUP.
upd_gk_call GP HGK Hfr3 HGPlo.
reseat HS HJ3 HP3 [0; 1; 2; 3]%nat AG
ltac:(idtac; first [eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr3; unfold TLAY_STK, ESTACK in *; lia | exact Hpres3]
| fail]).
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJ0L | exact HJ3 | exact HROD]) end.
(* the row CTRL_FRAMES[CTRL_HEADAMP] and the switch's jump table, read-only image regions *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => img_factsF Ev end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HEIv := rnHEI Ev in
pose proof (img_env_atomP Ev 259%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)) as E259;
pose proof (img_env_atomP Ev 265%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)) as E265;
idtac end.
pose proof HROW_rng as HROWr. pose proof HJT_rng as HJTr. pose proof HTM_rng as HTMr. pose proof HROW_JT as HRJ.
unfold A_ROW, A_JT, ROW_BYTES, A_OBJ in HROWr, HJTr, HTMr, HRJ. cbn [Nat.add] in HROWr, HJTr, HRJ.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 11%nat) 0 24 0 0
[YP09.mkChunk 2 (CVal 1 (SLit 2)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
YP09.mkChunk 16 (CVal 1 (SLit 18)); YP09.mkChunk 17 (CVal 1 (SLit 3))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite (AG 11%nat) by lia; rewrite E11, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (VAL 259) 2 1 (SLit 2) 2); [reflexivity | zside | zside | exact (HROW_k _ _ HROD3)]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (VAL 259) 8 8 (SOff 33 0) TM);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (HROW_tm _ _ HROD3)]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (VAL 259) 16 1 (SLit 18) 18); [reflexivity | zside | zside | exact (HROW_ao _ _ HROD3)]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (VAL 259) 17 1 (SLit 3) 3); [reflexivity | zside | zside | exact (HROW_al _ _ HROD3)]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite (AG 11%nat) by lia; rewrite E11; evalE AG; rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
repeat split; first [zone_lia | fail])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 265%nat) 0 40 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 34 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E265, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (VAL 265) 8 4 (SOff 34 0) JE);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (HJT_e _ _ HROD3)]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E265, (AG 11%nat) by lia; rewrite E11; evalE AG; rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB;
repeat split; first [zone_lia | fail])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 34%nat (mkAF 0 (2 ^ 31 - 1) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 11%nat (mkAF 65600 6266792 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (AG 11%nat) by lia; rewrite E11, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
reshok HS.
(* the row's kind byte, the bound check, the jump table, up to the `jr` at 0x8315c *)
paj_run_tok RUN HS HJ3 SHOK Bspan_LAY.
1: obl_row AG E11 E32 HZS_ROW (proj1 HJ3).
1: awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0.
upd_gk GP HGK HFr HGPd AG.
upd_keep HUP HFr AG. clear_frames.
(* the `jr` through the jump table: entry 2 is the template case, slot 0x1dc *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (JE + VAL 265%nat))
(denot_add_atoms Ev 34 265 JE (VAL 265%nat) E34 E265 ltac:(lia) ltac:(lia) ltac:(lia)) R10j end.
rewrite Z.add_comm in R10j.
assert (HJTk : VAL (A_OBJ 24) + JE = BASE + (AF_ctrl_lay_block + 0x1dc)) by (pose proof HJT_eq as Hq; unfold A_JT in Hq; lia).
assert (HAFk : 0 <= AF_ctrl_lay_block + 0x1dc < 2 ^ 40) by (unfold AF_ctrl_lay_block; lia).
assert (HAF2 : (AF_ctrl_lay_block + 0x1dc) mod 2 = 0) by (vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
assert (Hpcj : plookup pl_tpi (ss_pc ssx) = Some (PW 327783)) by (vm_compute; reflexivity);
assert (Hdecj : decode_any (Z_to_bv 32 327783) = Some (Jalr 0%bv (10%bv : bv 5) 0%bv, 4%Z)) by vm_refl_bv;
eapply (paj_jr_table 24 JE (AF_ctrl_lay_block + 0x1dc) W Ev ssx msx _ _ 327783 (10%bv : bv 5) HS eq_refl Hpcj Hdecj R10j HJTk HAFk HAF2) end.
intros matj HSj. clear HS R10j. rename HSj into HS.
pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matj HJ3) as HJ3j. clear HJ3. rename HJ3j into HJ3.
(* the template pointer from the row, up to the call of __asan_memcpy at 0x83244 *)
paj_run_tok RUN HS HJ3 SHOK Bspan_LAY.
all: try (obl_row AG E11 E32 HZS_ROW (proj1 HJ3)).
1: awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0.
upd_gk GP HGK HFr HGPd AG.
upd_keep HUP HFr AG. clear_frames. ACj1.rebaseE HS AG HEv2. clear HEv2.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD4 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJ0L | exact HJ3 | exact HROD]) end.
prreg HS (1%bv : bv 5) R1c. prreg HS (3%bv : bv 5) R3c. prreg HS (4%bv : bv 5) R4c.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (p + 18))
(denot_atom_off Ev 10 18 p ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(lia) ltac:(lia) ltac:(lia)) Ra0c;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 TM) (denot_atom0 Ev 33 TM E33 ltac:(lia)) Ra1c;
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 32) (denot_lit0 Ev 32 ltac:(lia)) Ra2c;
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2c end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msY)
(sp0 - spZ regs + TLAY_STK) sp0 [] lyc Sc W memc mdc [(1, fpos)] lyc S2 _ 0 (p + 18) TM 32 (sp1 - sp0) _ HJ3) end.
- rewrite Ra0c. reflexivity.
- rewrite Ra1c. reflexivity.
- rewrite Ra2c. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite R2c. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold TLAY_STK, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3c, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4c, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1c.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
  + left. unfold TLAY_STK, ESTACK in *. lia.
  + clear - Ha Hsp1 Hpstk; lia.
- exact Hamr.
- eapply (stack_ra lyc S2 W _ _ (p + 18) 32 (proj1 HJ3)); lia.
- intros _. eapply (stack_hull lyc S2 W _ _ (p + 18) 32 (proj1 HJ3)); lia.
- split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - pose proof (HTMPL _ _ HROD4) as HT.
      destruct (HT (Z.to_nat (a - TM)) ltac:(cbn [length T32z]; lia)) as [HTv _].
      specialize (HTv 0%nat ltac:(lia)).
      replace (TM + Z.of_nat (Z.to_nat (a - TM)) + Z.of_nat 0) with a in HTv by lia.
      unfold aview. rewrite HTv. discriminate.
    - unfold spZ. rewrite R2c, unsigned_lit_small by lia. lia. }
  split; [right; lia|]. split; [unfold amem_range, kLowMemEnd; left; lia|].
  split; [let L := rnLAWS in exact (ro_usable SEGS _ L _ _ _ _ _ TM 32 (proj1 HJ3) HZS_TM)|].
  intros _. eapply ro_hull; [exact HIMGSH | exact (proj1 HJ3) | lia | lia | lia]. }
cbv beta.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff4 & Hfr4 & Hpres4 & Hsame4).
assert (HUP4 : forall a, spZ regs <= a < 2 ^ 64 -> ~ (p + 18 <= a < p + 50) -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn. rewrite (Hfr4 a ltac:(lia) ltac:(lia) ltac:(lia)). apply HUP; [exact Ha | exact Hn]. }
clear HUP. rename HUP4 into HUP.
upd_gk_call GP HGK Hfr4 HGPlo.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD5 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJ0L | exact HJ4 | exact HROD]) end.
assert (HTMPL4 : garr8 SEGS (mrestrict (w_H W) mem4) (p + 18) T32z).
{ eapply (garr8_aview SEGS (w_H W) (w_H W) mem4 mem4 TM (p + 18) T32z); [| exact (HTMPL _ _ HROD5)].
intros i Hi. cbn [length T32z] in Hi. rewrite (Heff4 i ltac:(lia)). symmetry.
apply (Hfr4 (TM + i)); unfold TLAY_STK, ESTACK in *; lia. }
pose (BP := fun a => p + 18 <= a < p + 50).
assert (HBPd : forall a, BP a -> spZ regs <= a < 2 ^ 64) by (intros a Ha; unfold BP in Ha; lia).
assert (HBUF : forall a, BP a -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem4 a) by reflexivity.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr4; unfold TLAY_STK, ESTACK in *; lia | exact Hpres4]
| fail]).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 13%nat (mkAF 1 (2 ^ 63) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (AG 13%nat) by lia; rewrite E13, unsigned_lit_small by (pose proof Hsrc as (_ & _ & _ & _ & Hg0' & Hg3'); lia);
rewrite Z.pow_0_r, Z.mod_1_r; pose proof Hsrc as (_ & _ & _ & _ & Hg0' & Hg3'); lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
reshok HS.
(* the branch on g (not taken), the row's arg_len and arg_off, up to __asan_memcpy at 0x83288 *)
paj_run_tok RUN HS HJ4 SHOK Bspan_LAY.
all: try (obl_row AG E11 E32 HZS_ROW (proj1 HJ4)).
1: awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0.
upd_gk GP HGK HFr HGPd AG.
upd_gk BP HBUF HFr HBPd AG.
upd_keep HUP HFr AG. clear_frames. ACj1.rebaseE HS AG HEv5. clear HEv5.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD6 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJ0L | exact HJ4 | exact HROD]) end.
prreg HS (1%bv : bv 5) R1d. prreg HS (3%bv : bv 5) R3d. prreg HS (4%bv : bv 5) R4d.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (p + 36))
(denot_atom_off Ev 10 36 p ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(lia) ltac:(lia) ltac:(lia)) Ra0d;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 g)
(denot_atom0 Ev 13 g ltac:(rewrite (AG 13%nat) by lia; exact E13) ltac:(pose proof Hsrc as (_ & _ & _ & _ & Hg0' & Hg3'); lia)) Ra1d;
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 3) (denot_lit0 Ev 3 ltac:(lia)) Ra2d;
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2d end.
pmkst HS.
pose proof Hsrc as (Hsrc1 & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msY)
(sp0 - spZ regs + TLAY_STK) sp0 [] lyc Sc W memc mdc [(1, fpos)] lyc S2 _ 0 (p + 36) g 3 (sp1 - sp0) _ HJ4) end.
- rewrite Ra0d. reflexivity.
- rewrite Ra1d. reflexivity.
- rewrite Ra2d. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite R2d. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold TLAY_STK, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3d, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4d, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1d.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
  + left. unfold TLAY_STK, ESTACK in *. lia.
  + clear - Ha Hsp1 Hpstk; lia.
- unfold amem_range in Hamr |- *; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
- eapply (stack_ra lyc S2 W _ _ (p + 36) 3 (proj1 HJ4)); lia.
- intros _. eapply (stack_hull lyc S2 W _ _ (p + 36) 3 (proj1 HJ4)); lia.
- split; [pose proof Hsrc as (_ & _ & _ & _ & Hg0' & _); lia|].
  split; [pose proof Hsrc as (_ & _ & _ & _ & _ & Hg3'); lia|].
  split.
  { intros a Ha. split.
    - rewrite (HGK a ltac:(unfold GP; left; lia)). exact (proj1 (Hsrc1 a Ha)).
    - unfold spZ. rewrite R2d, unsigned_lit_small by lia. lia. }
  split; [clear - Hdisj Hpstk; lia|].
  split; [pose proof Hsrc as (_ & _ & _ & Hamg & _); exact Hamg|].
  split.
  { eapply ra_of_kept; [exact HGK | | exact Hgra0].
    intros x Hx. unfold GP, shadow_of_addr. right.
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
  intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cid0 pos0 g 3 (proj1 HJ4));
  [rewrite Hfrs2; right; exact Hgfin | lia | lia | lia]. }
cbv beta.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5 & Hsame5).
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> ~ (p + 18 <= a < p + 50) -> aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn. rewrite (Hfr5 a ltac:(lia) ltac:(lia) ltac:(lia)). apply HUP; [exact Ha | exact Hn]. }
clear HUP. rename HUP5 into HUP.
(* the 32 bytes now read lay_z ch pm v *)
assert (HLAY : garr8 SEGS (mrestrict (w_H W) mem5) (p + 18) (lay_z ch pm v)).
{ pose proof HTMPL4 as HTa. rewrite <- (firstn_skipn 18 T32z) in HTa.
  destruct (proj1 (garr8_app SEGS _ _ _ _) HTa) as (HT1 & _).
  pose proof HTMPL4 as HTb. rewrite <- (firstn_skipn 21 T32z) in HTb.
  destruct (proj1 (garr8_app SEGS _ _ _ _) HTb) as (_ & HT3).
  change (Z.of_nat (length (firstn 21 T32z))) with 21 in HT3.
  unfold lay_z. apply (proj2 (garr8_app SEGS _ _ _ _)). split.
  - eapply garr8_aview_kept; [| exact HT1]. change (Z.of_nat (length (firstn 18 T32z))) with 18.
    intros a Ha. rewrite (Hfr5 a ltac:(lia) ltac:(lia) ltac:(lia)). apply HBUF. unfold BP; lia.
  - change (Z.of_nat (length (firstn 18 T32z))) with 18. apply (proj2 (garr8_app SEGS _ _ _ _)). split.
    + eapply (garr8_aview SEGS (w_H W) (w_H W) memc mem5 g (p + 18 + 18) [ch; pm; v]); [| exact Hgarr].
      intros i Hi. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Hi. replace (p + 18 + 18 + i) with (p + 36 + i) by lia.
      rewrite (Heff5 i ltac:(lia)). apply HGK. unfold GP; left; lia.
    + change (Z.of_nat (length [ch; pm; v])) with 3. replace (p + 18 + 18 + 3) with (p + 18 + 21) by lia.
      eapply garr8_aview_kept; [| exact HT3].
      intros a Ha. rewrite length_skipn in Ha. change (length T32z) with 32%nat in Ha.
      rewrite (Hfr5 a ltac:(lia) ltac:(lia) ltac:(lia)). apply HBUF. unfold BP; lia. }
(* ---- the epilogue 0x8328c-0x83368: the frame marked unusable, its flag released, the return ---- *)
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr5; unfold TLAY_STK, ESTACK in *; lia | exact Hpres5]
| fail]).
pose proof (proj1 HJ5) as HAR5.
destruct (FFL _ _ _ _ _ 1 fpos HAR5 Hfin2) as (HFLpres5 & HFLown5 & HFLrng5). fold FL in HFLpres5, HFLown5, HFLrng5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin2) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5. change (128 / 8) with 16 in HFSpres5. fold F in HFpres5, HFSpres5.
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyc S2 a) by (intros a Ha; exact (proj2 (HFpres5 a Ha))).
fs_rwF HS E529 HFSpres5.
rs_hide_all.
add_flag_region HS AG E528 HFLpres5 HFLrng5 HFLown5 HnoF HnoF HnoF.
unfold rs_hold in *.
pose proof HFLrng5 as ((HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
assert (HBUF5 : forall a, BP a -> aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) mem5 a) by reflexivity.
paj_run_flag_sh RUNF HS HJ5.
- lia.
- wrange_lay AG fpos F FL.
- flag0 E528 EFA0.
- lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  upd_gk BP HBUF5 H HBPd AG; upd_keep HUP H AG end.
  clear_frames.
  prreg HS (1%bv : bv 5) R1f.
  lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
  intros matr. unfold tlay_post.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
  exists lyc, (stack_free_state 1 fpos S2), rg, mm, mdx end.
  assert (Eabf : ablocks B lyc (stack_free_state 1 fpos S2) = ablocks B lyc Sc).
  { unfold ablocks. rewrite blocks_stack_free_state. unfold ablocks in Eab. exact Eab. }
  split.
  { rewrite R1f. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
    rewrite (AG 1%nat) by lia. rewrite E1, Hra. reflexivity. }
  split.
  { unfold EV_LAY. change own with ([] ++ own).
    eapply (ajournal_sub SEGS B LAWS Hsegs); [exact HJc | apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ5 | lia | lia | intros a (rg & [] & _)]. }
  split; [apply aregs_preserved_eqs; creg HS AG EE|].
  pose proof HJ5 as (_ & _ & _ & _ & _ & Hfrsf & _ & _ & _ & _ & _ & _ & _ & Hpresf & _).
  split; [exact Hfrsf|].
  split; [exact Eabf|].
  split; [exact (sfs_set_fs 1 fpos S2 Sc fS2 ES2)|].
  split.
  { eapply garr8_aview_kept; [| exact HLAY]. intros a Ha.
    assert (Hlz : length (lay_z ch pm v) = 32%nat) by reflexivity. rewrite Hlz in Ha.
    apply HBUF5. unfold BP. lia. }
  pose proof (acall_kept_of_journal SEGS B Hsegs (sp0 - spZ regs + TLAY_STK) sp0 [] [] lyc Sc W memc mdc
  lyc (stack_free_state 1 fpos S2) W _ _ 0 (fun a => p + 18 <= a < p + 50) HJ5 HAR
  ltac:(intros a (rg & [] & _)) ltac:(intros b m i Hb _ _; rewrite Eabf; exact Hb) sink_closed_nil) as (K1 & K2 & K3 & K4 & K5 & K6).
  unfold tcj_kept. split.
  { intros a Ha Hw He. destruct (Z_lt_ge_dec a (spZ regs)) as [Hlt | Hge].
    - apply K1; [lia | unfold TLAY_STK, ESTACK in *; lia].
    - apply HUP; [lia | exact He]. }
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split.
  { intros a Ha Hw Hp. destruct (Z_lt_ge_dec a (spZ regs)) as [Hlt | Hge].
    - apply K5; [lia | unfold TLAY_STK, ESTACK in *; lia | exact Hp].
    - destruct (Z_lt_ge_dec a sp0) as [Hlt2 | Hge2].
      + apply Hpresf. unfold TLAY_STK, ESTACK in *; lia.
      + apply K5; [lia | lia | exact Hp]. }
  intros a Ha. apply Hpresf. unfold TLAY_STK, ESTACK in *; lia.
Qed.
End e.
End d.
End b.

(* WHY reac_box_model_block AND build_dt1_single NEED NO WALK. This record was kept beside the proofs as a separate file;
   it is here because a proof directory holds only the proof's files, and this file's contract (the row 0x9c670 only)
   is the place the argument lands. File:line citations of this file point above this comment.

   reac_box_model_block and build_dt1_single are not reached on fuzz_grant.asan.

   Second witness, an independent measurement from the bytes of the pinned binary fuzz_grant.asan
   (index/binaries.tsv row `libreac fuzz_grant asan`, sha256
   c2c7559b29bdf39cb13acdfb062d6b930efb2b56f84ab4e0c71bd5711d9e015e; projects/libreac/fuzz_grant/harness.yaml:53), and
   from the listing lib/A/Prog/GrantList.v. The measuring script and its output are not part of this tree: they are
   unreached_measure.py (sha256 931e85cb21d2; internal record) and its output unreached_measure.out (sha256 bc4dce139a82; internal record).

   The call graph (every call site there is; direct `jal`, every 2-byte offset of the r-x segment [0x307dc,0x9b164)):
   - reac_box_model_block 0x8354c: called at 0x8322c only, in ctrl_lay_block (+0x230); listing slot 2783
     `PCall GS_reac_box_model_block`.
   - ctrl_lay_block 0x82ffc: called at 0x82b94 only, in reac_ctrl_stamp_headamp (+0x180); listing slot 2361
     `PCall GS_ctrl_lay_block`.
   - build_dt1_single 0x843cc: called at 0x838ac and 0x84000 only, both in reac_box_model_block; slots 3199, 3668.
   No `auipc`/`lui` followed within 64 bytes by an `addi`/`jalr` on the same register forms 0x843cc anywhere in the r-x
   segment; the only one forming 0x8354c is 0x83600 `auipc a2,0x0` + 0x83614 `addi a2,a2,-180` in reac_box_model_block's
   own prologue (the frame header's PC, listing object 26). Neither value is stored as 4- or 8-byte data in any load
   segment. So no indirect call reaches either function.

   The branch in ctrl_lay_block (a1 = f, kept in s4):
   - 0x83120 `addi a0,s4,2`; 0x83134 `lbu a0,0(a0)`: a0 = f->block (byte +2 of the row).
   - 0x83138 `li a1,9`; 0x8313c `bltu a1,a0,0x83214`: block > 9 goes to the call.
   - 0x83144/0x83148 `auipc`+`addi` a1 = jump table 0x20ff4 (r-- segment); 0x8314c-0x83154 a0 = 0x20ff4 + table[block];
     0x8315c `jr a0`.
   - table: [0] -> 0x83248, [1] -> 0x83160 (the 16 x `00 7a` loop, then `j 0x83248`), [2] -> 0x831d8 (`ld a1,8(f)` =
     f->tmpl, 0x831f8 `j 0x83244`, 0x83244 `jal __asan_memcpy(frame+18, f->tmpl, 32)`, then 0x83248), [3] -> 0x83220,
     [4]..[9] -> 0x831c8/0x83204/0x8320c/0x831fc/0x8321c/0x831d0 (set a1, `j 0x83220`).
   - The call block [0x83214, 0x8322c] is entered only from 0x8313c, 0x831cc, 0x831d4, 0x83200, 0x83208, 0x83210,
     0x83218 (all branches and jumps of ctrl_lay_block were scanned) and from table entries 3..9. So
     reac_box_model_block is called exactly when f->block is in {3..9} or f->block > 9.

   The caller's argument (reac_ctrl_stamp_headamp):
   - 0x82b80 `auipc a0,0x1a`; 0x82b84 `addi s4,a0,-1296` -> s4 = 0x9c670 (CTRL_FRAMES[CTRL_HEADAMP]); 0x82b8c
     `mv a1,s4`; 0x82b94 `jal ctrl_lay_block`.
   - 0x9c670 lies in PT_GNU_RELRO [0x9c168, 0x9e000) (read-only after relocation; ET_EXEC, no .rela.dyn, so the file
     byte is the run-time byte).
   - Byte 0x9c672 = 0x02 (= BLOCK_TMPL). So ctrl_lay_block takes table[2] -> 0x831d8 and returns through 0x83248
     without reaching 0x8322c.
   Source agrees: reac_ctrlblk.c:1292 `ctrl_stamp(frame, &CTRL_FRAMES[CTRL_HEADAMP], args)` -> :967
   `ctrl_lay_block(frame, f, NULL, args)`; :1074-1075 `[CTRL_HEADAMP] = { ... .block = BLOCK_TMPL ... }`; :744
   `BLOCK_TMPL` = 2; :858-859 the `memcpy(block, f->tmpl, 32)` case; :866 the call of reac_box_model_block is the
   `default` case only.

   Fall-through out of the memory-checking runtime's reports. The `__asan_report_{load,store}{1,2,4,8}` entries END in
   `ret` on this image (e.g. `__asan_report_store1` 0x58c34..0x58c80 ends in `ret`), so a `jal __asan_report_X` that is
   the LAST instruction of a function falls through into the next function: the call graph above is complete only
   together with these edges. Measured from the pinned ELF and its symbol file (every function of the program range
   0x806b0..0x857dc whose last word is a `jal` to a report entry):
     function                         last slot  report  falls through to
     LLVMFuzzerTestOneInput           0x81b6c    load1   check_groupa 0x81b70
     reac_ctrl_parse                  0x8299c    store1  kind_of_link1 0x829a0
     reac_ctrl_stamp_headamp          0x82c5c    store1  reac_ctrl_headamp_record_verify 0x82c60
     reac_ctrl_headamp_record_verify  0x82d38    load1   reac_ctrl_identity_poll_block 0x82d3c
     reac_ctrl_build_grant_sweep      0x82ff8    load1   ctrl_lay_block 0x82ffc
     ctrl_lay_block                   0x83398    load8   ctrl_finish 0x8339c
     ctrl_finish                      0x83548    store1  reac_box_model_block 0x8354c
     reac_box_model_block             0x843c8    load8   build_dt1_single 0x843cc
     build_dt1_single                 0x84838    store1  reac_grant_alloc_fits 0x8483c
     reac_grant_allocate              0x848ec    store1  reac_grant_build_sweep 0x848f0
     reac_grant_build_sweep           0x84d18    load1   reac_headamp_tx_init 0x84d1c
     reac_headamp_tx_set              0x84e50    store4  reac_headamp_default 0x84e54
     reac_headamp_tx_effective        0x84f18    load1   reac_headamp_tx_arm_scene 0x84f1c
     reac_headamp_tx_arm_scene        0x85054    store4  reac_headamp_tx_set_resweep 0x85058
     reac_headamp_tx_set_resweep      0x850c8    store4  reac_headamp_tx_next 0x850cc
     reac_headamp_tx_next             0x857d8    store4  0x857dc (`__wrap_getenv`)
   Inside a function the report blocks chain the same way, so every branch into ANY report block of a function can end
   in the fall-through above. The edge that bears on these two functions is ctrl_finish 0x83548 -> reac_box_model_block:
   a second way in, besides the call at 0x8322c. It is taken only if a branch of ctrl_finish into one of its report
   blocks is taken, and the closed walk of ctrl_finish takes none: `pb_ctrl_finish` (lib/A/Prog/CtrlFinish.v) runs the
   whole function in one symbolic run to its `ret` with the shadow entries `cf_SH` built from the premises'
   `range_addressable` over the caller's 32 block bytes and the row's 3 bytes by `shent_ok_of_range`
   (lib/Reusable/YCbq.v); with those entries every shadow check reads a byte that makes the access good, so no branch
   into 0x83548's report chain is produced. A scan of every conditional branch and `jal` in the whole r-x segment
   [0x307dc, 0x9b164) for a target inside reac_box_model_block [0x8354c, 0x843cc) or build_dt1_single
   [0x843cc, 0x8483c) from a source outside both finds exactly one: 0x8322c -> 0x8354c, the call above. So the two ways
   in are that call and the fall-through from ctrl_finish's last report call; there is no third.

   A dependency the trace universe rests on. The trace universe (lib/A/ACej.v `Tfib_universe`) lists the call traces of
   the program's malloc/free sites and omits the allocations of libunwind's `DwarfFDECache::add` (malloc 0x861e0, free
   0x86204). That is sound only because libunwind is reached from the program solely through the memory-checking
   runtime's report path (`__asan_report_X` -> the error report, which unwinds the stack), and every walk refutes every
   branch into a report. So the same refutation that keeps the two functions unreachable also keeps those two
   allocation sites out of every run the statements cover.

   The Rocq terms that carry it. A report entry is a `PCall GS___asan_report_X` slot of the listing (lib/A/Prog/
   GrantList.v, checked against the ELF by `grant_lib_check`, GrantImg.v). The token engine's step on a `PCall` slot
   returns `PTCall s` (`sym_step_pi_tok`, lib/A/Prog/PaShadow.v), the run then stops with status `PTS_call s`, and the
   run lemma hands the walk the machine at `sigma s` (`sym_step_pi_tok_call`, PaShadow.v). From there the walk must prove
   `SRr` itself, which needs a contract for that entry. No contract for any `__asan_report_X` entry exists in this proof
   (none in lib/A/Prog, none in GrantClose.v's instances, none among the runtime hypotheses), so a walk that compiles
   never reaches a report slot: every branch into a report is closed before it, by the shadow facts of the walk. The
   same holds for `__asan_handle_no_return` and `abort`. Each closed walk of the program functions (lib/A/Prog: the walk
   lemmas `pb_<function>` and, for the entry function, `grant_lib_x_all` in GrantLibXClosed.v) discharges the shadow
   checks of its accesses from the shadow entries of the objects it touches (`ablocks` blocks via `shent_ok_of_block`,
   frame objects and caller buffers via `shent_ok_of_range`, lib/Reusable/YCbq.v), so none steps into a report entry.

   Consequence: build_dt1_single and reac_box_model_block (1212 instructions) need no walk. The only call (0x8322c) is
   not reached because the row's link kind is 2, and the only fall-through (ctrl_finish 0x83548) is not reached because
   ctrl_finish's closed walk refutes every branch into its reports. The contract of this file, stated for the row
   0x9c670 only, carries the fact the proof needs: the row's byte +2 read through `arodata_okP` over the relro range
   is 2. *)
