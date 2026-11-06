(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   relay_finish, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)),
   after lib/A/W_relay_finish_h.v (a working branch a3987bff22c: its loop rf_loop and its tail rf_tail), in the
   form of the B walks lib/B/W_check_bounded.v (a working branch 7e062bb9b9c) and lib/B/W_gse_loop.v
   (a working branch bb5ed8a0689). *)
(* Modified by Theorem Labs, 2026-10: the room `_x` form (a Theorem Labs lane, RoomRFB): the walk is pb_relay_finish_x,
   stated over any allocator relation ARx with its laws as W_contract_x.v rf_spec_x (Section c below: PST / ARx / hl /
   LAWS / HP0 / BLKN, the callees' and the allocator rules' `_x` twins, PSTR / PSTC), and it threads rf_spec_x's room
   round: the budget rp_RM RP (each round: the free's 1, then gestures_end's charge) and the count premise
   cnt_ok_pk RP rf_pk (rf_pk = 5) to the free (cnt_ok) and to gestures_end (gse_pk = 4); the round's room bound follows
   rf_room's `- cap` threading (the round frees the old g_out block).  The room argument is lib/A/W_relay_finish_h.v's
   (a working branch 9e4f84a8fb9), the ARx form that of lib/B/W_list_free.v / W_source_reset.v
   (a working branch dfa1a225350).
   B's relay_finish sets no frame pointer and calls no __asan_stack_malloc, so A's fake-frame seat, its set_fs step and rp_RPF across the seat do not apply.
   pb_relay_finish keeps its statement, byte-identical, and its Section hypotheses (the same terms in the same order;
   HPLAIN / HWSEG write rf_cells as rf_cells RG GTU GL): it is re-derived from pb_relay_finish_x at ARx := ARi0,
   PST := [], RP := RP_AR (Section cAR); pb_relay_finish_fr / _fr_tfib are unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_relay_finish.v, with its module paths, module names and numbers changed; 548 of its 618 lines of code are new or changed and 4273 lines of the source are left out. *)
(* fuzz_preset, the #102 walk of alloc.c's own on image B' (asan-ubsan, pinned d663f82d; merged alloc.c own :48-56;
   B' 0x85dbc, 62 instructions, frame 32, out of line: fuzz_malloc B' tail-calls it, fuzz_realloc B' calls it), slot
   B_prog_slot AS_own of a Theorem Labs lane's #102 whole-program listing lib/B/Listing_prog.v / PAImg_prog.v (d42e123915ae),
   against the text town_specX (lib/A/PRH_FnAlloc.v blob 83fe93bc86e2, the #102 kit of record:
   decff67d721f on AL base ef3d561e39e1; the m-form post fpostm, the ledger with g_most / g_own_ran_out as FIELDS
   (PRH_Base.v 3004a98fe2d9), errno kept), at preset's second allocator relation
   ARcfx = ARcf pa_segs B /\ xs_placed_cf (a Theorem Labs lane's YG0ncf.v; a Theorem Labs lane's YGcallcf.v) and cp := CfParams_preset,
   image B' numbers prh_img_B (lib/B/PRH_ImgB.v, generated on the unstripped twin c90d4fa5). Ported from S1's old-pin
   walk lib/B/Prog/OwnB.v (s1b 8a01e111a410, blob 7e1d0878b2af; c-omx-alloc's): the same proof script, re-run on the
   d42e listing (the internal file REWALK-102-PLAN.md section 2's "all 62 instructions equal" is a hint; the evidence is this walk).
   The runner YC80x / YC1fPx over YCbqG's ajournal_x in its memnorm-carrying form (YSRrMemnorm.srr_inv_laws_imp),
   the poison call by YGcallMxmn.aj_poison_x_m (Q5's memnorm call rule).
   The walk: the instrumented checks of the 8-byte head store at b (two shadow loads of b's granule, which is
   addressable: b is a live block not in Hp), the head := n (eight byte stores), poison (b, 16) (Hp := b :: Hp),
   g_live += n and g_peak := max (g_peak, g_live) (two stores through auipc bases: rows of B_alias_hints), the
   pointer-overflow check of b + 16 (decided by the fact b <= CEIL_MAX), return b + 16. g_own_ran_out and g_most are
   PST bytes off every window: kept, so the post's ledger carries the entry's most / own (prh_ledger_most / _own).
   RULE-24 (row AL6): `proof-index own` 0 named / 0 by address (its 591 released lemmas named `own` are other
   units'), `proof-index 0x85dbc` 0 released (24 UNRELEASED hits: the same number in other binaries), path-scoped
   named-branch git grep for 85dbc: only walkkit-next's generated PAImg_prog.v / PRH_ImgB.v (2026-10-29T14:40Z-15:25Z,
   the AL2 preparation notes); no full internal-branch sweep run. The reuse is OwnB.v above.
   Numerals: slot offsets are DERIVED (4 * slot of the listing); 32 (the frame), 16 (the head), 8 and 4 (widths) are
   LENGTH; 4128 is DERIVED (STK_own at prh_img_B); atom indices 2 / 10 / 11 / 32 / 33 / 34 / 48 are DERIVED (the
   engine's numbering: registers below 32, extra atoms from 32, the after-call band from 48); the statics by NAME
   (OBJ_g_live / OBJ_g_peak below, pins102); objects 0 and 12 are the engine's pinned GOT slot and shadow-offset cell
   (YC1fP's got_regionP / bcell_regionP); 8, 16, ..., 56 in the head chunks are WORD (byte shifts);
   2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 64, CEIL_MAX, 4096 are DERIVED / WORD bounds. No ADDRESS literal: every address is
   B_prog_val / B_prog_sigma of PAImg_prog.v or a PrhImg field of PRH_ImgB.v, computed by vm_compute. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0ncf YG0dcf YGcallx YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0sshcf YG0lawscf YGcallPx YGcfHp YGcallPcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".

Open Scope bv_scope.
Open Scope Z_scope.

(* the two alloc.c statics own writes, BY NAME (the internal file pins102.json objects[k], a working branch 5472bf2e7a82;
   the d42e listing keeps v4's numbers 9 / 10) *)
Definition OBJ_g_live : nat := A_OBJ 9.
Definition OBJ_g_peak : nat := A_OBJ 10.
(* the bound of an object atom inside the image range *)
Ltac ob_rng := (try unfold OBJ_g_live); (try unfold OBJ_g_peak); unfold A_OBJ, A_TEXT, A_LIM; lia.

(* ---- the symbolic state at own's entry ----
   atoms: 2 = entry sp, 10 = b, 11 = n, 32 = the shadow offset, 33 = g_live, 34 = g_peak;
   regions: the 32-byte frame, the shadow-offset GOT slot and cell (read-only), b's head word (written), g_live
   (object 9) and g_peak (object 10), read and written (their bytes are the program's statics PST); one shadow entry:
   b's first 16 bytes are addressable. *)
Definition OB_K : Z := B_prog_sigma AS_own - B_prog_base.
Definition OB_Bx : sv := SOff 32 0.
Definition OB_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ob_head : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 8 [].
Definition ob_stat (o x : nat) : YP09.region :=
  YP09.mkRegion (Some o) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff x 0))].
Definition ob_regions : smem :=
  [stack_region 32; got_regionP; bcell_regionP 32; ob_head; ob_stat OBJ_g_live 33; ob_stat OBJ_g_peak 34].
(* the two static stores (own + 0xa4 g_live, own + 0xac g_peak) go through auipc bases: their alias pairs are
   rows of the listing's B_alias_hints (checked by B_alias_hints_ok) *)
Definition ob_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 CEIL_MAX 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (OBJ_g_live, mkAF (B_prog_val OBJ_g_live) (B_prog_val OBJ_g_live) 3);
    (OBJ_g_peak, mkAF (B_prog_val OBJ_g_peak) (B_prog_val OBJ_g_peak) 3)]
    [] B_alias_hints.
Definition ss_ob : sstate := mkSS OB_K sr_atoms ob_regions None ob_facts.
Definition ob_SH : list shent := [mkSHE 10 0 16].
(* the head word after the eight byte stores (slots 26-29, 31-34), as the engine leaves it *)
Definition ob_head_chunks : list YP09.chunk :=
  [YP09.mkChunk 3 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 24)));
   YP09.mkChunk 2 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 16)));
   YP09.mkChunk 1 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 8)));
   YP09.mkChunk 0 (CVal 1 (SOff 11 0));
   YP09.mkChunk 7 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 56)));
   YP09.mkChunk 6 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 48)));
   YP09.mkChunk 5 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 40)));
   YP09.mkChunk 4 (CVal 1 (SAlu ALU_SRL (SOff 11 0) (SLit 32)))].

Ltac ob_bnd := match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
  let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end; lia.
(* the image bytes the walk names: the shadow GOT slot and cell, and the five statics, lie in the image's two
   writable segments (computed from the instance) *)
Lemma ob_img_in : forall a,
  (B_prog_val (A_OBJ 0) <= a < B_prog_val (A_OBJ 0) + 8 \/ B_prog_val (A_OBJ 12) <= a < B_prog_val (A_OBJ 12) + 8 \/
   Exists (in_zr a) (prh_pst (PI := prh_img_B))) -> in_img rsegs a.
Proof.
intros a H. unfold in_img.
destruct H as [H|[H|H]];
[ let v := eval vm_compute in (B_prog_val (A_OBJ 0)) in change (B_prog_val (A_OBJ 0)) with v in H
| let v := eval vm_compute in (B_prog_val (A_OBJ 12)) in change (B_prog_val (A_OBJ 12)) with v in H
| apply Exists_exists in H as (r & Hr & H); cbn in Hr;
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold in_zr in H; cbn in H ];
first [ eexists; split; [do 2 right; left; reflexivity | ob_bnd]
      | eexists; split; [do 3 right; left; reflexivity | ob_bnd] ].
Qed.

(* the eight head bytes the stores leave give the head word n (S1Ledger's prh_val_mem_hdr8) *)
Lemma ob_U_srl : forall E n s, bv_unsigned (ew E 11) = n -> 0 <= s < 64 ->
  U E (SAlu ALU_SRL (SOff 11 0) (SLit s)) = Z.shiftr n s.
Proof.
intros E n s Hn Hs. rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw].
pose proof (u64_range (ew E 11)) as Hr. rewrite Hn in Hr.
unfold zcanon, M64. rewrite Z.add_0_r, (Z.mod_small n) by lia. rewrite (Z.mod_small s) by lia.
replace (Z.land s 63) with s.
- apply Z.mod_small. split; [apply Z.shiftr_nonneg; lia|].
  rewrite Z.shiftr_div_pow2 by lia. apply (Z.le_lt_trans _ n); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|];
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)); nia | lia].
- symmetry. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
Definition OB_EI (regs : bvmap 5 word) (live peak : Z) : env :=
  Eimg (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; live; peak])).

(* the listing objects the walk names, computed from the instance (never typed) *)
Ltac ob_vals :=
  let v0 := eval vm_compute in (B_prog_val (A_OBJ 0)) in let v12 := eval vm_compute in (B_prog_val (A_OBJ 12)) in
  let v9 := eval vm_compute in (B_prog_val OBJ_g_live) in let v10 := eval vm_compute in (B_prog_val OBJ_g_peak) in
  change (VAL (A_OBJ 0)) with v0 in *; change (VAL (A_OBJ 12)) with v12 in *;
  change (VAL OBJ_g_live) with v9 in *; change (VAL OBJ_g_peak) with v10 in *;
  change (B_prog_val (A_OBJ 0)) with v0 in *; change (B_prog_val (A_OBJ 12)) with v12 in *;
  change (B_prog_val OBJ_g_live) with v9 in *; change (B_prog_val OBJ_g_peak) with v10 in *.

Lemma ob_head_val : forall (E : env) (m : word -> option byte) (b n : Z),
  bv_unsigned (ew E 10) = b -> bv_unsigned (ew E 11) = n ->
  Forall (YP09.chunk_ok SEGS E m b) ob_head_chunks -> val_mem SEGS m b 8 n.
Proof.
intros E m b n E10 E11 HF.
assert (Hc : forall off s, In (YP09.mkChunk off (CVal 1 s)) ob_head_chunks ->
  mbyte SEGS m (b + off) = Some (YP09.byte_of_word (sv_denot E s) 0)).
{ intros off s Hin. rewrite Forall_forall in HF. specialize (HF _ Hin).
  destruct (HF 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
  injection Hb1 as <-. rewrite Z.add_0_r in Hb2. exact Hb2. }
pose proof (u64_range (ew E 11)) as Hr. rewrite E11 in Hr.
assert (H0 : U E (SOff 11 0) = n) by (rewrite U_SOff, E11, Z.add_0_r; unfold zcanon, M64; apply Z.mod_small; lia).
apply (prh_val_mem_hdr8 (L := B_prog_listing) (PA := PI_prog_B) m b n ltac:(lia)).
intros k Hk.
assert (Hk' : exists off s, In (YP09.mkChunk off (CVal 1 s)) ob_head_chunks /\ Z.of_nat k = off /\
  U E s = Z.shiftr n (8 * off)).
{ destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|lia];
  [ exists 0, (SOff 11 0) | exists 1, (SAlu ALU_SRL (SOff 11 0) (SLit 8))
  | exists 2, (SAlu ALU_SRL (SOff 11 0) (SLit 16)) | exists 3, (SAlu ALU_SRL (SOff 11 0) (SLit 24))
  | exists 4, (SAlu ALU_SRL (SOff 11 0) (SLit 32)) | exists 5, (SAlu ALU_SRL (SOff 11 0) (SLit 40))
  | exists 6, (SAlu ALU_SRL (SOff 11 0) (SLit 48)) | exists 7, (SAlu ALU_SRL (SOff 11 0) (SLit 56)) ];
  (split; [cbn; tauto | split; [reflexivity|]]);
  first [ rewrite H0; reflexivity | rewrite (ob_U_srl E n _ E11) by lia; reflexivity ]. }
destruct Hk' as (off & s & Hin & Hoff & Hs). rewrite Hoff. rewrite (Hc off s Hin). f_equal.
unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r. change (bv_unsigned (sv_denot E s)) with (U E s).
rewrite Hs. reflexivity.
Qed.

(* a run's frame keeps the reader's view off the run's write windows *)
Lemma ob_aview_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hf Ha Hn. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* an 8-byte chunk gives the word it holds *)
Lemma ob_val_of_chunk8 : forall E (m : word -> option byte) base e v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CVal 8 e)) -> U E e = v -> val_mem SEGS m base 8 v.
Proof.
intros E m base e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-. rewrite Z.add_0_r in Hb2. rewrite Hb2.
f_equal. unfold YP09.byte_of_word, YO0f.le_byte. change (bv_unsigned (sv_denot E e)) with (U E e).
pose proof (U_range E e) as Hr. rewrite He in Hr |- *. unfold M64 in Hr.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small v) by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section f.
Variable B : asyms.
(* the allocator relation the texts are instantiated at (S1KitAlloc's YGcallcf.v ARλ': ARcf and the placed
   error-buffer extents) *)
#[local] Notation ARcfx := (fun ly S Hp (W : world SEGS) mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* STAND-IN for the unit's PALib binding of B at the program listing (a Theorem Labs lane): swap by citation *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
(* STAND-IN for the unit's static-placement binding of B (PST off as_owned_static B and off errno) (a Theorem Labs lane): swap by citation *)
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* STAND-IN for the unit's binding of the poison entry (pa_sigma of __asan_poison_memory_region = cf_pc_poison) (a Theorem Labs lane):
   swap by citation *)
Hypothesis pal_poison : SIGMA AS___asan_poison_memory_region = cf_pc_poison.
(* callee text: h-rw-man-5's poison contract over ARcf (YGcfHp.v), lifted to ARcfx by YGcallPcf.v *)
Hypothesis APOISON : apoison_realizes_cf SEGS B.
Let APOISONx : apoison_realizes_x SEGS B ARcfx cf_head cf_pc_poison := apoison_realizes_cf_xs SEGS B APOISON.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B).

(* the statics g_live, g_peak are the first two of prh_pst *)
Lemma ob_stat_pst : forall x a, (x = OBJ_g_live \/ x = OBJ_g_peak) -> VAL x <= a < VAL x + 8 -> Exists (in_zr a) prh_pst.
Proof.
intros x a Hx Ha. unfold prh_pst. change (VAL x) with (B_prog_val x) in Ha.
destruct Hx as [->| ->]; [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd]; unfold in_zr; cbn [fst snd];
[replace pi_g_live with (B_prog_val OBJ_g_live) by (vm_compute; reflexivity)
|replace pi_g_peak with (B_prog_val OBJ_g_peak) by (vm_compute; reflexivity)]; exact Ha.
Qed.
Lemma ob_obj_img : forall x a, (x = A_OBJ 0 \/ x = A_OBJ 12 \/ x = OBJ_g_live \/ x = OBJ_g_peak) ->
  VAL x <= a < VAL x + 8 -> in_img SEGS a.
Proof.
intros x a Hx Ha. apply ob_img_in.
destruct Hx as [->|[->|Hx]]; [left; exact Ha | right; left; exact Ha | right; right; exact (ob_stat_pst x a Hx Ha)].
Qed.

Lemma ob_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. intros a H. split; [apply ob_img_in; right; right; exact H | exact (proj1 (pal_pst_ok a H))]. Qed.

Let RUN := @paj_run_x_m fx rc SK B_prog_listing PL_prog_B PI_prog_B B prh_pst ARcfx _ LAWS ob_pst_ok.
(* the same runner carrying the memnorm keep from a fixed memory m0 (h-hpreset-7's carrier, YSRrMemnorm.v:40) *)
Let RUNM (m0 : word -> option byte) := @paj_run_x_m_inv fx rc SK B_prog_listing PL_prog_B PI_prog_B B prh_pst ARcfx _
  LAWS ob_pst_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
Let BR := paj_branch (L := B_prog_listing) (PI := PI_prog_B).
Let RET := paj_ret_at (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B).

Lemma ob_entry : forall ly S Hp (W : world SEGS) regs mem md ch b n live peak,
  afn_pre_x SEGS B ARcfx STK_own ly S Hp W regs mem md ch ->
  getr regs 10 = w64 b -> In (b, n + cf_head) (ablocks B ly S) -> ~ In b Hp -> 0 <= n ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_live 8 live -> val_mem SEGS (mrestrict (w_H W) mem) pi_g_peak 8 peak ->
  0 <= live < 2 ^ 64 -> 0 <= peak < 2 ^ 64 ->
  st_ok_pi SEGS VAL (OB_EI regs live peak) ss_ob (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + OB_K)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS OB_Bx ob_SH (OB_EI regs live peak) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch b n live peak HPRE H10 Hin Hnh Hn Hlive Hpeak Rl Rp.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_own = 4128) by reflexivity.
assert (Hcf : cf_head = 16) by reflexivity.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b (n + cf_head) HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
assert (Hreq : req_size (n + cf_head) = n + 16) by (unfold req_size; rewrite Hcf; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
pose proof (pal_got_cell B PAL) as HgcD.
assert (Hbimg : forall a, b <= a < b + 8 -> ~ in_img SEGS a).
{ intros a Ha. apply (blk_img_x SEGS B ARcfx LAWS ly S Hp W mem md b (n + cf_head) a HAR Hin). rewrite Hreq. lia. }
assert (Himg : forall x, (x = A_OBJ 0 \/ x = A_OBJ 12 \/ x = OBJ_g_live \/ x = OBJ_g_peak) ->
  b + 8 <= VAL x \/ VAL x + 8 <= b).
{ intros x Hx.
  destruct (Z_le_gt_dec (b + 8) (VAL x)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (VAL x + 8) b) as [H2|H2]; [right; exact H2|].
  exfalso. destruct (Z_le_gt_dec b (VAL x)) as [H3|H3].
  - apply (Hbimg (VAL x) (conj H3 (Z.gt_lt _ _ H1))). apply (ob_obj_img x _ Hx).
    split; [apply Z.le_refl | apply Z.lt_add_pos_r; lia].
  - apply (Hbimg b ltac:(lia)). apply (ob_obj_img x _ Hx).
    split; [apply Z.lt_le_incl, Z.gt_lt; exact H3 | apply Z.gt_lt; exact H2]. }
rewrite restrict_mkst_fx.
set (E := OB_EI regs live peak).
assert (HEI : img_env VAL A_LIM E) by (unfold E, OB_EI; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; live; peak])) k)
by (intros k Hk; unfold E, OB_EI; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 live) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 peak) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EI : forall x, (A_TEXT <= x < A_LIM)%nat -> ew E x = Z_to_bv 64 (VAL x))
by (intros x Hx; unfold E, OB_EI; apply Eimg_img; exact Hx).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (VBI : forall x, (A_TEXT <= x < A_LIM)%nat -> base_val E (Some x) = VAL x).
{ intros x Hx. apply VB; [apply EI; exact Hx | apply pa_val_range]. }
assert (Hw : forall x o, (x = OBJ_g_live \/ x = OBJ_g_peak) -> 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (VAL x + o)).
{ intros x o Hx Ho. apply pst_writable_B. apply (ob_stat_pst x _ Hx). lia. }
split.
- unfold ss_ob. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ob_regions, stack_region, got_regionP, bcell_regionP, ob_head, ob_stat.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VBI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
      pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 0)). split; [lia|]. split; [ob_vals; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite (EI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VBI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
      pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)). split; [lia|]. split; [ob_vals; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 OB_Bx SHADOW_OFF);
      [cbn [sv_denot OB_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat b E10) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hbpres; lia | constructor].
    * rewrite (VBI OBJ_g_live ltac:(ob_rng)).
      pose proof (@pa_val_range _ B_prog_listing PI_prog_B OBJ_g_live). split; [lia|]. split; [ob_vals; lia|].
      split; [intros o Ho; apply Hw; [left; reflexivity | lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL OBJ_g_live) 0 8 (SOff 33 0) live);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Hlive.
    * rewrite (VBI OBJ_g_peak ltac:(ob_rng)).
      pose proof (@pa_val_range _ B_prog_listing PI_prog_B OBJ_g_peak). split; [lia|]. split; [ob_vals; lia|].
      split; [intros o Ho; apply Hw; [right; reflexivity | lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL OBJ_g_peak) 0 8 (SOff 34 0) peak);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Hpeak.
  + apply pairwise_disjoint_of_extents.
    unfold ob_regions, stack_region, got_regionP, bcell_regionP, ob_head, ob_stat, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat b E10) by lia.
    rewrite (VBI (A_OBJ 0)), (VBI (A_OBJ 12)), (VBI OBJ_g_live), (VBI OBJ_g_peak) by ob_rng.
    cbn [base_val]. rewrite Usp.
    pose proof (Himg (A_OBJ 0) ltac:(tauto)) as I0. pose proof (Himg (A_OBJ 12) ltac:(tauto)) as I12.
    pose proof (Himg OBJ_g_live ltac:(tauto)) as I1. pose proof (Himg OBJ_g_peak ltac:(tauto)) as I2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    ob_vals. rewrite WS in *.
    revert I0 I12 I1 I2 HgcD Rsp Hb4096 Hbceil C1 Hstk0 Hceil Hslo Hshi H47 Hbot Htop Htop2 Hn. clear. intros.
    repeat split; lia.
  + split; [|split].
    * cbn [ob_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      pose proof HEI as HEI'. unfold img_env in HEI'.
      rewrite !HEI' by ob_rng.
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      ob_vals. repeat match goal with |- _ /\ _ => split end; try lia; reflexivity.
    * exact I.
    * cbn [ob_facts f_alias]. exact (B_alias_hints_ok E HEI).
- unfold sh_ok, ob_SH. constructor; [|constructor].
  assert (Hhd : hd_skip Hp b = 0).
  { unfold hd_skip. destruct (existsb (Z.eqb b) Hp) eqn:Ex; [|reflexivity].
    apply existsb_exists in Ex as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. subst x. contradiction. }
  destruct (AR_shadow_law_ok_cf SEGS B ly S Hp W mem md b (n + cf_head) (proj1 HAR) Hin) as [Hbs _].
  rewrite Hhd, Hreq, Z.add_0_r, Z.sub_0_r in Hbs.
  apply (shent_ok_of_range SEGS (w_H W) mem E OB_Bx 10%nat b 16 b 0 16).
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + unfold U, OB_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 16) with 0 in Hx. change (Z.max 0 16) with 16 in Hx.
    unfold in_app in Happ. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* the write premise of a stretch after the call (frame window, g_live, g_peak), and its negation off them *)
Ltac ob_wr2 OLD Usp WS HV9 HV10 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros a (r & Hr & Ha); cbn [In ss_mem add_cond] in Hr;
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  [ left; left; rewrite (OLD 2%nat ltac:(lia)), Usp in Ha; rewrite WS; lia
  | right; apply (ob_stat_pst OBJ_g_live); [left; reflexivity|]; rewrite HV9 in Ha; lia
  | right; apply (ob_stat_pst OBJ_g_peak); [right; reflexivity|]; rewrite HV10 in Ha; lia ].
Ltac ob_notw OLD Usp HV9 HV10 :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha); cbn [In ss_mem add_cond] in Hr;
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  [ rewrite (OLD 2%nat ltac:(lia)), Usp in Ha; lia | rewrite HV9 in Ha; lia | rewrite HV10 in Ha; lia ].
(* the seven statics' addresses and their generated widths, computed from the image record (never typed) *)
Ltac ob_pis :=
  let l := eval vm_compute in (@pi_g_live prh_img_B) in let p := eval vm_compute in (@pi_g_peak prh_img_B) in
  let c := eval vm_compute in (@pi_g_count prh_img_B) in let f := eval vm_compute in (@pi_g_fail prh_img_B) in
  let r := eval vm_compute in (@pi_g_ran_out prh_img_B) in
  let mo := eval vm_compute in (@pi_g_most prh_img_B) in let ow := eval vm_compute in (@pi_g_own_ran_out prh_img_B) in
  let zc := eval vm_compute in (@pi_gz_count prh_img_B) in let zf := eval vm_compute in (@pi_gz_fail prh_img_B) in
  let zr := eval vm_compute in (@pi_gz_ran_out prh_img_B) in
  let zm := eval vm_compute in (@pi_gz_most prh_img_B) in let zo := eval vm_compute in (@pi_gz_own_ran_out prh_img_B) in
  change (@pi_g_live prh_img_B) with l in *; change (@pi_g_peak prh_img_B) with p in *;
  change (@pi_g_count prh_img_B) with c in *; change (@pi_g_fail prh_img_B) with f in *;
  change (@pi_g_ran_out prh_img_B) with r in *;
  change (@pi_g_most prh_img_B) with mo in *; change (@pi_g_own_ran_out prh_img_B) with ow in *;
  change (@pi_gz_count prh_img_B) with zc in *; change (@pi_gz_fail prh_img_B) with zf in *;
  change (@pi_gz_ran_out prh_img_B) with zr in *;
  change (@pi_gz_most prh_img_B) with zm in *; change (@pi_gz_own_ran_out prh_img_B) with zo in *.

(* The kit's own text at image B, its whole-program listing, preset's CfParams, the non-primary room instance
   (prh_room_live_a8) and the allocator relation ARcfx *)
Theorem own_holds_B :
  town_specX (cp := CfParams_preset) (PI := prh_img_B) (RL := prh_room_live_a8) (L := B_prog_listing) (PA := PI_prog_B)
    B ARcfx SK.
Proof.
unfold town_specX, fpre, fpostm, fpost, fQmn.
intros ly S Hp W regs mem md ch b n Lam peak cnt fail ran most own (HPRE & HRO & HSHI & HRAC) H10 H11 Hn Hin Hb16
  Hb4096 Hfresh Hsum HL.
assert (Hcf : cf_head = 16) by reflexivity.
assert (WS : STK_own = 4128) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HL as HL0. apply prh_ledger_iff in HL0 as [HGl HLB].
(* the ledger's facts, by PRH_Base's named projections *)
pose proof (prh_ledger_live B ly S Hp W mem Lam peak cnt fail ran most own HL) as Glive.
pose proof (prh_ledger_peak B ly S Hp W mem Lam peak cnt fail ran most own HL) as Gpeak.
pose proof (prh_ledger_count B ly S Hp W mem Lam peak cnt fail ran most own HL) as Gcnt.
pose proof (prh_ledger_fail B ly S Hp W mem Lam peak cnt fail ran most own HL) as Gfail.
pose proof (prh_ledger_ran B ly S Hp W mem Lam peak cnt fail ran most own HL) as Gran.
pose proof (prh_ledger_most B ly S Hp W mem Lam peak cnt fail ran most own HL) as (Gmost & Rmost).
(* PRH_Base's projection; S1Ledger's prh_ledger_own (the OWN arm, used below) shares its short name *)
pose proof (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt fail ran most own HL) as (Gown & Rown).
destruct (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HL) as (Rlp & Rpk & Rcnt & Rfail & Rran).
pose proof (prh_hp_fresh B ly S Hp W mem Lam b HLB Hfresh) as Hnh.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b (n + cf_head) HAR Hin) as (_ & _ & Hbceil & Happ & Hbpres & _).
assert (Hreq : req_size (n + cf_head) = n + 16) by (unfold req_size; rewrite Hcf; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
destruct (ob_entry ly S Hp W regs mem md ch b n (Ledger.lsum Lam) peak HPRE H10 Hin Hnh Hn Glive Gpeak ltac:(lia) ltac:(lia))
  as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B prh_pst ARcfx STK_own [(b, b + 8)] ly S Hp W regs mem md ch HPRE) as HJ.
assert (Hent : SIGMA AS_own = BASE + OB_K) by (vm_compute; reflexivity).
unfold cfg_at. rewrite Hent. change (w64 (BASE + OB_K)) with (Z_to_bv 64 (BASE + OB_K)).
remember (OB_EI regs (Ledger.lsum Lam) peak) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat ->
  ew E k = ew (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; Ledger.lsum Lam; peak])) k)
by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 b)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E33 : ew E 33 = Z_to_bv 64 (Ledger.lsum Lam)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 peak) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; Ledger.lsum Lam; peak])) E)
by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EL.
(* the stretch to the poison call: the shadow checks, the head stores, the poison arguments *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM OB_Bspan.
{ intros a (r & Hr & Ha). cbn [ss_mem ss_ob ob_regions In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [stack_region got_regionP bcell_regionP ob_head ob_stat YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. left. rewrite Usp in Ha. rewrite WS. lia.
  - lia.
  - lia.
  - left. right. left. rewrite E10, unsigned_lit_small in Ha by lia. split.
    + exists (b, b + 8). split; [left; reflexivity | cbn [fst snd]; lia].
    + exists b, (n + cf_head). split; [exact Hin | rewrite Hreq; lia].
  - right. apply (ob_stat_pst OBJ_g_live); [left; reflexivity|].
    rewrite (HEI OBJ_g_live ltac:(ob_rng)) in Ha. lia.
  - right. apply (ob_stat_pst OBJ_g_peak); [right; reflexivity|].
    rewrite (HEI OBJ_g_peak ltac:(ob_rng)) in Ha. lia. }
(* the head word, read off the head region before the call *)
assert (Hb10 : bv_unsigned (ew E 10) = b) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Hn11 : bv_unsigned (ew E 11) = n) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Hhead1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) b 8 n).
{ pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & HMO & _). cbn [ms_mem restrict ss_mem setpc] in HMO.
  do 3 apply Forall_inv_tail in HMO. apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HMO).
  cbn [YP09.r_chunks YP09.r_base base_val] in HMO. rewrite Hb10 in HMO.
  exact (ob_head_val E _ b n Hb10 Hn11 HMO). }
rename HFr into HFr1. clear HF HG HEI0.
pose proof HEI as HEIu. unfold img_env in HEIu.
assert (HV9 : bv_unsigned (ew E OBJ_g_live) = VAL OBJ_g_live) by (apply HEIu; ob_rng).
assert (HV10 : bv_unsigned (ew E OBJ_g_peak) = VAL OBJ_g_peak) by (apply HEIu; ob_rng).
(* the first stretch writes the frame, the head word and the two statics' windows only *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) ->
  ~ (VAL OBJ_g_live <= a < VAL OBJ_g_live + 8) -> ~ (VAL OBJ_g_peak <= a < VAL OBJ_g_peak + 8) ->
  ~ (b <= a < b + 8) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2 H3 H5. apply (ob_aview_frame _ _ _ _ _ a HFr1 Ha).
  intros (r & Hr & Ha'). cbn [ss_mem ss_ob ob_regions In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [stack_region got_regionP bcell_regionP ob_head ob_stat YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha'.
  - rewrite Usp in Ha'. lia.
  - lia.
  - lia.
  - rewrite Hb10 in Ha'. lia.
  - rewrite HV9 in Ha'. lia.
  - rewrite HV10 in Ha'. lia. }
(* the poison call (YGcallMxmn.aj_poison_x_m, with its keep and memnorm): Hp := b :: Hp, b's two head shadow bytes
   poisoned *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
eapply SRr_bind.
{ eapply (@YGcallMxmn.aj_poison_x_m fx rc SK SEGS B prh_pst ARcfx cf_head _ LAWS (@pa_segs_low _ B_prog_listing PI_prog_B)
    cf_pc_poison APOISONx W E _ ms STK_own (spZ regs) [(b, b + 8)] ly S Hp W mem md [] ly S Hp _ 0 b (n + cf_head)
    (-32) (ew E 2) _ HS).
  - cbn [ss_pc setpc]. exact pal_poison.
  - reflexivity.
  - exact HJ.
  - rewrite Ra0, E10. reflexivity.
  - rewrite Ra1. reflexivity.
  - reflexivity.
  - exact Hin.
  - rewrite Hreq, Hcf. lia.
  - exact (st_ok_restrict_reg SEGS (w_H W) E _ ms 2%bv HS).
  - reflexivity.
  - exact Usp.
  - reflexivity.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Rgp, E3. exact Hgp.
  - rewrite Rtp, E4. exact Htp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PI_prog_B)); [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hshd & Hkeep & Hpres2 & Hmn2).
pose proof (fun H0 => Hmn2 (HPM H0)) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
pose proof (YCbq.shadow_addr_bounds b ltac:(lia)) as Hsh. unfold kLowMemEnd, kHighShadowEnd in Hsh.
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 4; 5]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
  pose proof HV9 as HV9n. pose proof HV10 as HV10n.
  let i9 := eval vm_compute in OBJ_g_live in change OBJ_g_live with i9 in HV9n at 1.
  let i10 := eval vm_compute in OBJ_g_peak in change OBJ_g_peak with i10 in HV10n at 1.
  cbn [ms_mem restrict].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply Hkeep; rewrite ?Hes, ?Hcf; [lia | lia |].
    change (16 / 8) with 2. lia.
  - intros _. apply (apresent_writable SEGS). apply HJpres2. rewrite Usp in Ha. rewrite WS. lia.
  - rewrite HV9n in Ha. apply (mbyte_of_aview SEGS). apply Hkeep; rewrite ?Hes, ?Hcf; ob_vals; [lia | lia |].
    change (16 / 8) with 2. lia.
  - intros _. apply pst_writable_B. rewrite HV9n in Ha. exact (ob_stat_pst OBJ_g_live a (or_introl eq_refl) Ha).
  - rewrite HV10n in Ha. apply (mbyte_of_aview SEGS). apply Hkeep; rewrite ?Hes, ?Hcf; ob_vals; [lia | lia |].
    change (16 / 8) with 2. lia.
  - intros _. apply pst_writable_B. rewrite HV10n in Ha. exact (ob_stat_pst OBJ_g_peak a (or_intror eq_refl) Ha). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E')
by (rewrite HE'; apply (img_env_havoc (L := B_prog_listing) (PI := PI_prog_B)); [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 48)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; Ledger.lsum Lam; peak])) E')
by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (SHOK' : sh_ok SEGS OB_Bx [] E' (mrestrict (w_H W) mem2)) by constructor.
clear SHOK.
pose proof HEI' as HEIu'. unfold img_env in HEIu'.
assert (HV9' : bv_unsigned (ew E' OBJ_g_live) = VAL OBJ_g_live) by (apply HEIu'; ob_rng).
assert (HV10' : bv_unsigned (ew E' OBJ_g_peak) = VAL OBJ_g_peak) by (apply HEIu'; ob_rng).
(* the same at the atom numbers the computed states carry *)
pose proof HV9' as HV9n'. pose proof HV10' as HV10n'.
let i9 := eval vm_compute in OBJ_g_live in change OBJ_g_live with i9 in HV9n' at 1.
let i10 := eval vm_compute in OBJ_g_peak in change OBJ_g_peak with i10 in HV10n' at 1.
(* the stretch to the g_peak branch: the statics' loads, g_live's store *)
paj_run_tok_x_inv (RUNM mem) HS HJ2 SHOK' HPM OB_Bspan.
{ ob_wr2 OLD Usp WS HV9n' HV10n'. }
rename HFr into HFr2.
(* the g_peak branch, both arms, then the pointer-overflow check (decided) and the return *)
psrr_branch_tok RUN BR HS SHOK' OB_Bspan.
all: paj_run_tok_x_inv (RUNM mem) HS HJ2 SHOK' HPM OB_Bspan; [ob_wr2 OLD Usp WS HV9n' HV10n' |].
all: rename HFr into HFr3.
all: lazymatch goal with HSz : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ => set (mF := ms_mem msc) in * end.
(* what the walk after the entry keeps: everything off the frame window, the two statics and b's head shadow *)
all: assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) ->
  ~ (VAL OBJ_g_live <= a < VAL OBJ_g_live + 8) -> ~ (VAL OBJ_g_peak <= a < VAL OBJ_g_peak + 8) ->
  ~ (shadow_addr b <= a < shadow_addr b + 2) -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) (ms_mem ms) a);
  [ intros a Ha H1 H2 H3 H4;
    rewrite (ob_aview_frame _ _ _ _ _ a HFr3 Ha) by (ob_notw OLD Usp HV9n' HV10n');
    rewrite (ob_aview_frame _ _ _ _ _ a HFr2 Ha) by (ob_notw OLD Usp HV9n' HV10n');
    apply Hkeep; [exact Ha | rewrite Hes; lia | rewrite Hcf; change (16 / 8) with 2; exact H4] |].
all: assert (HbimgM : forall a, b <= a < b + 8 -> ~ in_img SEGS a);
  [ intros a Ha; apply (blk_img_x SEGS B ARcfx LAWS ly S Hp W mem md b (n + cf_head) a HAR Hin); rewrite Hreq; lia |].
all: assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) ->
  ~ (VAL OBJ_g_live <= a < VAL OBJ_g_live + 8) -> ~ (VAL OBJ_g_peak <= a < VAL OBJ_g_peak + 8) ->
  ~ (shadow_addr b <= a < shadow_addr b + 2) -> ~ (b <= a < b + 8) -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a);
  [ intros a Ha H1 H2 H3 H4 H5; rewrite KEEP by assumption; apply KEEP1; assumption |].
(* the other statics and errno: image bytes off every window *)
all: assert (KS : forall a, in_img SEGS a -> ~ (VAL OBJ_g_live <= a < VAL OBJ_g_live + 8) ->
  ~ (VAL OBJ_g_peak <= a < VAL OBJ_g_peak + 8) -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a);
  [ intros a Hi H2 H3; pose proof (B_prog_segs_low a Hi) as Hlo; unfold kLowMemEnd in Hlo;
    apply KEEPA; [lia | lia | exact H2 | exact H3 | lia | intros Hb'; exact (HbimgM a Hb' Hi)] |].
all: assert (KST : forall a w v, (a = pi_g_count /\ w = pi_gz_count \/ a = pi_g_fail /\ w = pi_gz_fail \/
    a = pi_g_ran_out /\ w = pi_gz_ran_out) ->
  val_mem SEGS (mrestrict (w_H W) mem) a w v -> val_mem SEGS (mrestrict (w_H W) mF) a w v);
  [ intros a w v Haw Hv0; apply (prh_val_mem_keep (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ Hv0);
    intros k Hk; apply (prh_mbyte_of_aview (L := B_prog_listing) (PA := PI_prog_B));
    assert (Hx : Exists (in_zr (a + Z.of_nat k)) prh_pst)
      by (unfold prh_pst; destruct Haw as [[-> ->]|[[-> ->]|[-> ->]]];
          [ apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
          | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
          | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd ];
          unfold in_zr; cbn [fst snd]; ob_pis; lia);
    apply KS; [exact (pst_in_img_B _ Hx) | |];
    destruct Haw as [[-> ->]|[[-> ->]|[-> ->]]]; ob_vals; ob_pis; lia |].
all: assert (Hcnt' : val_mem SEGS (mrestrict (w_H W) mF) pi_g_count pi_gz_count cnt)
  by (apply KST; [left; split; reflexivity | exact Gcnt]).
all: assert (Hfail' : val_mem SEGS (mrestrict (w_H W) mF) pi_g_fail pi_gz_fail fail)
  by (apply KST; [right; left; split; reflexivity | exact Gfail]).
all: assert (Hran' : val_mem SEGS (mrestrict (w_H W) mF) pi_g_ran_out pi_gz_ran_out ran)
  by (apply KST; [right; right; split; reflexivity | exact Gran]).
(* g_own_ran_out and g_most (the ledger's prh_own / prh_most fields): PST bytes off every window *)
all: assert (KOM : forall a w v, (a = pi_g_own_ran_out /\ w = pi_gz_own_ran_out \/ a = pi_g_most /\ w = pi_gz_most) ->
  val_mem SEGS (mrestrict (w_H W) mem) a w v -> val_mem SEGS (mrestrict (w_H W) mF) a w v);
  [ intros a w v Haw Hv0; apply (prh_val_mem_keep (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ Hv0);
    intros k Hk; apply (prh_mbyte_of_aview (L := B_prog_listing) (PA := PI_prog_B));
    assert (Hx : Exists (in_zr (a + Z.of_nat k)) prh_pst)
      by (unfold prh_pst; destruct Haw as [[-> ->]|[-> ->]];
          [ do 6 apply Exists_cons_tl; apply Exists_cons_hd
          | do 5 apply Exists_cons_tl; apply Exists_cons_hd ];
          unfold in_zr; cbn [fst snd]; ob_pis; lia);
    apply KS; [exact (pst_in_img_B _ Hx) | |];
    destruct Haw as [[-> ->]|[-> ->]]; ob_vals; ob_pis; lia |].
all: assert (Herr : forall a, as_errno B <= a < as_errno B + 4 -> aview SEGS (w_H W) mF a = aview SEGS (w_H W) mem a);
  [ intros a Ha; destruct (pal_env B PAL) as [_ [Herri _]]; apply KS; [exact (Herri a Ha) | |];
    intros Hs; [pose proof (ob_stat_pst OBJ_g_live a (or_introl eq_refl) Hs) as Hx
               | pose proof (ob_stat_pst OBJ_g_peak a (or_intror eq_refl) Hs) as Hx];
    exact (proj2 (pal_pst_ok a Hx) Ha) |].
(* the head word n, written in the first stretch, survives the call and the second stretch *)
all: assert (Hv : val_mem SEGS (mrestrict (w_H W) mF) b 8 n);
  [ apply (prh_val_mem_keep (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ Hhead1); intros k Hk;
    apply (prh_mbyte_of_aview (L := B_prog_listing) (PA := PI_prog_B));
    assert (Hni : ~ in_img SEGS (b + Z.of_nat k)) by (apply HbimgM; lia);
    apply KEEP; [lia | rewrite WS in Hslo; lia | intros Hs; exact (Hni (ob_obj_img OBJ_g_live _ ltac:(tauto) Hs))
                | intros Hs; exact (Hni (ob_obj_img OBJ_g_peak _ ltac:(tauto) Hs)) |];
    unfold in_app, kLowShadowBeg, kHighMemBeg in Happ; unfold shadow_addr, SHADOW_OFF;
    pose proof (Z.mul_div_le b 8 ltac:(lia)) as Hq; pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)) as Hq2; lia |].
(* the two statics' final values, off the last symbolic state *)
all: assert (HUadd : U E' (SAlu ALU_ADD (SOff 11 0) (SOff 33 0)) = Ledger.lsum Lam + n);
  [ rewrite U_SAlu, !U_SOff, (OLD 11%nat ltac:(lia)), (OLD 33%nat ltac:(lia)), E11, E33; cbn [zalu_raw];
    rewrite !unsigned_lit_small by lia; unfold zcanon, M64; rewrite !Z.add_0_r, (Z.mod_small n), (Z.mod_small (Ledger.lsum Lam)) by lia;
    rewrite Z.mod_small by lia; lia |].
all: assert (HUp : U E' (SOff 34 0) = peak) by (apply U_atom; [rewrite (OLD 34%nat ltac:(lia)); exact E34 | lia]).
all: pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HMOF & _).
all: cbn [ms_mem restrict ss_mem abs_ss setpc add_cond] in HMOF.
all: pose proof (Forall_inv (Forall_inv_tail HMOF)) as HRL; pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HMOF))) as HRP.
all: destruct HRL as (_ & _ & _ & HRL); destruct HRP as (_ & _ & _ & HRP).
all: cbn [YP09.r_chunks YP09.r_base base_val] in HRL, HRP; rewrite HV9n' in HRL; rewrite HV10n' in HRP.
all: apply Forall_inv in HRL; apply Forall_inv in HRP.
all: pose proof (ob_val_of_chunk8 E' _ _ _ _ HRL HUadd) as Hlive'.
all: rewrite branch_geu_U, HUp, HUadd in Hc.
all: assert (Hpeak' : val_mem SEGS (mrestrict (w_H W) mF) pi_g_peak 8 (Z.max peak (Ledger.lsum Lam + n))).
1: { apply Bool.negb_true_iff, Z.ltb_ge in Hc. rewrite Z.max_l by lia. exact (ob_val_of_chunk8 E' _ _ _ _ HRP HUp). }
2: { apply Bool.negb_false_iff, Z.ltb_lt in Hc. rewrite Z.max_r by lia. exact (ob_val_of_chunk8 E' _ _ _ _ HRP HUadd). }
all: assert (Hmost' : prh_most W mF most) by (split; [apply KOM; [right; split; reflexivity | exact Gmost] | exact Rmost]).
all: assert (Hown' : prh_own W mF own) by (split; [apply KOM; [left; split; reflexivity | exact Gown] | exact Rown]).
all: assert (HG' : prh_glob W mF (Ledger.lsum Lam + n) (Z.max peak (Ledger.lsum Lam + n)) cnt fail ran most own)
  by exact (prh_glob_final (L := B_prog_listing) (PA := PI_prog_B) W mem W mF (Ledger.lsum Lam) peak cnt fail ran
    (Ledger.lsum Lam + n) cnt fail ran most own HGl Hlive' ltac:(lia) Hpeak' Hcnt' Rcnt Hfail' Rfail Hran' Rran
    Hmost' Hown').
(* the ledger after own (S1Ledger's prh_ledger_own) *)
all: assert (HLn : prh_ledger B ly S (b :: Hp) W mF ((b + cf_head, n) :: Lam) (Z.max peak (Ledger.lsum Lam + n)) cnt fail
  ran most own).
1,3: (
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HJblk & _);
  apply (S1Ledger.prh_ledger_own B ly S Hp W mem ly S (b :: Hp) W mF Lam peak cnt fail ran _ cnt fail ran b n most own
    HL HG');
  [ intros a k i Hak Hi; destruct HLB as (_ & HLF & _); rewrite Forall_forall in HLF;
    destruct (HLF _ Hak) as (Hk0 & Hkin & _); cbn [fst snd] in Hk0, Hkin;
    apply (prh_mbyte_of_aview (L := B_prog_listing) (PA := PI_prog_B));
    apply (HJblk (a - cf_head) (k + cf_head) i Hkin Hkin);
    [ unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia |];
    intros (r & [<-|[]] & Hr); cbn [fst snd] in Hr;
    assert (Hne : (a - cf_head, k + cf_head) <> (b, n + cf_head))
      by (intros Heq; injection Heq as Ha0 _; apply Hfresh; apply in_map_iff; exists (a, k); split; [cbn; lia | exact Hak]);
    pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md _ _ _ _ HAR Hkin Hin Hne) as Hd;
    unfold zdisjoint in Hd; cbn [fst snd] in Hd; rewrite Hreq in Hd;
    unfold req_size in Hd; destruct (Z.eqb_spec (k + cf_head) 0); lia
  | intros a k _ H; exact H
  | exact Hn
  | exact Hin
  | rewrite Hcf; replace (b + 16) with (b + 1 * 16) by lia; rewrite Z.mod_add by lia; exact Hb16
  | exact Hv
  | exact Hfresh
  | reflexivity ]).
(* the return: apost_base_x from the journal *)
all: lazymatch goal with HSz : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
  prreg HSz (10%bv : bv 5) R10; prreg HSz (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HSz eq_refl ltac:(vm_compute; reflexivity));
  let mq := fresh "mq" in intros mq;
  unfold apost_base_x; cbv beta;
  exists ly, S, (b :: Hp), (ms_regs msc), (ms_mem msc); eexists; exists 0
end.
all: split; [cbn [ms_regs]; rewrite R1, (OLD 1%nat ltac:(lia)), E1, Hra; reflexivity|].
all: repeat rewrite wvb_collapse in HJ2.
all: split; [eapply (ajournal_x_materialize (SK := SK));
  solve [exact HJ2 | exact LAWS | exact (@pa_segs_low _ B_prog_listing PI_prog_B) | exact ob_pst_ok] |].
all: split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs _ HS); [exact HAE' | vm_compute; reflexivity] |].
(* the memory stays normal (fpostm's keep): the carried invariant at the end memory *)
all: cbv beta; split; [|exact HPM].
all: split; [exact (fun H => H)|]. all: split; [reflexivity|]. all: split; [reflexivity|].
all: split; [rewrite R10, (OLD 10%nat ltac:(lia)), E10, unsigned_lit_small by lia; rewrite Hcf; reflexivity |].
all: split; [reflexivity|]. all: split; [reflexivity|].
all: split; [exact Herr|]. all: exact HLn.
Qed.
End f.
End d.
