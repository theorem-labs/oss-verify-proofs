(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACeh.v at c8557374ad2e, with its module paths changed (AB1v's tfibsegs is A/AWalkFw0.v's; AF0l and ACej are knock's lib/A copies) and its image constants relocated to libreac/fuzz_knock's asan image (sha256 61768cf4739b...): the ASan GOT slots and cells of lines 18-21 (port_addr_check.py MAPS, same symbol), the read-only range of line 44 (knock .data.rel.ro start .. .got end), and the image bounds: cgif's image end 0x5fb000 (lines 76, 87, 108, 120) and image start 0x10000 (lines 76, 86, 107, 109, 119, 121) are cited from lib/Reusable/YImgTop.v (knock: IMG_TOP 0x5f3000 = last PT_LOAD 0x982c8 + 0x55aae8 = 0x5f2db0, page-rounded; IMG_LO 0x10000): TFIB_IMG_LO / TFIB_IMG_END are YImgTop.IMG_LO / IMG_TOP (lines 86-87 moved before line 76), the proofs unfold them where cgif's had the literals, and every unfold of off_img also unfolds YImgTop.IMG_LO / IMG_TOP. lib_const_addr (line 24) is False: its two cgif ranges are cgif program cells only (see the comment there). *)
(* Modified by Theorem Labs, 2026-10 (--patch, reac-pw/fuzz_rate): this unit's lib/Reusable/YImgTop.v states IMG_LO / IMG_TOP in fuzz_scene's notation form (only parsing: they are the numerals 0x10000 / 0x5fa000), which unfold cannot name, so the names YImgTop.IMG_LO and YImgTop.IMG_TOP are dropped from the unfold lists of fuzz_knock's text; nothing else changes. The two .got comments name rate's loads (ld at 0x8076c / 0x80768 in LLVMFuzzerTestOneInput, auipc at 0x80760 / 0x80764) in place of knock's pcs. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/ACeh.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/ACeh.v at d73b6a8fb639, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/ACeh.v was made and quote that file's image-A values; the code below carries image B's values. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YP00 YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.reac_pw.fuzz_rate.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import AWalkFw0 YF0l YCej.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition A_GOT_shadow : Z := 0x9c170.   (* .got slot of __asan_shadow_memory_dynamic_address; ld at 0x807c4 (LLVMFuzzerTestOneInput) *)
Definition A_shadow_glob : Z := 0xa4f38.  (* __asan_shadow_memory_dynamic_address *)
Definition A_GOT_uar : Z := 0x9c1c8.      (* .got slot of __asan_option_detect_stack_use_after_return; ld at 0x807c0 (LLVMFuzzerTestOneInput) *)
Definition A_uar_glob : Z := 0xa4f40.     (* __asan_option_detect_stack_use_after_return *)
Definition SB : Z := 0x7fff8000.
Lemma SB_SHADOW_OFF : SB = SHADOW_OFF. Proof. reflexivity. Qed.
(* cgif: (0x103b0 <= a < 0x103b8) \/ (0x9ec10 <= a < 0x9ec28). Both are cgif program cells with no knock counterpart:
   0x103b0 is the 8-byte .rodata constant 02 01 01 01 01 01 01 01, which knock's .rodata does not hold (cgif 0x103a0-0x103c0
   = ffff0f0000ffffaf 0000000000006003 0201010101010101 bf5d3dcd92a31802; knock 0x10390-0x103a8 = ffff0f0000ffffaf
   0000000000006003 bf5d3dcd92a31802); the .got slots 0x9ec10/0x9ec18/0x9ec20 hold cgif library code pointers 0x81404,
   0x84178, 0x84894. Knock's own set is EMPTY by measurement, not by relocation: every pc-relative reference (auipc +
   addi / load / store) of knock's four program functions LLVMFuzzerTestOneInput 0x7eed0, reac_knock_init 0x7f44c,
   reac_knock_heard 0x7f4e8, reac_knock_step 0x7f570, decoded with capstone on fuzz_knock.asan sha256 61768cf4739b...
   (symbols of the unstripped twin fff563b30957...), loads no .rodata constant: the only data cells they read are the
   .got slots A_GOT_shadow 0x965d0 and A_GOT_uar 0x96628 above, and the one .rodata address they form, 0x1e6a5 (ASan's
   frame descriptor string `1 32 40 4 k:56`, addi at 0x7ef98), is only stored to the ASan frame header (sd at 0x7efa4),
   never loaded (h-small-a9 and h-rw-kno-6; the stored 0x1e6a5 by h-rw-ide-5 and h-small-a9, 2026-10-29). Hence
   lib_const_addr is False. *)
Definition lib_const_addr (a : Z) : Prop := False.
Record TfibLib (B : asyms) : Prop := {
tl_code : as_code B = Tfib_code;
tl_got_shadow : as_got_shadow B = A_GOT_shadow;
tl_shadow_cell : as_shadow_cell B = A_shadow_glob;
tl_got_uar : as_got_uar B = A_GOT_uar;
tl_uar_cell : as_uar_cell B = A_uar_glob;
tl_errno : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd;
tl_errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img tfibsegs a;
tl_universe : as_universe B = Tfib_universe;
tl_lib_consts : forall a, lib_const_addr a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
tl_gp : 0 <= as_gp B < 2 ^ 64
}.
Lemma tl_env : forall B, TfibLib B -> api_env tfibsegs B.
Proof.
intros B TL. split; [exact (tl_errno B TL)|]. split; [exact (tl_errno_img B TL)|]. rewrite (tl_code B TL), (tl_universe B TL).
split; apply memZL_In; vm_compute; reflexivity.
Qed.
Definition in_ro_tfa (a : Z) : Prop :=
(exists s, In s tfibsegs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (0x9b9e0 <= a < 0x9ce68).   (* knock asan .data.rel.ro start 0x96070 .. .got end 0x972c8 (section headers), not all of PT_GNU_RELRO 0x96040..0x98000 *)
Definition arodata_ok (B : asyms) (rd : reader) : Prop :=
forall a, in_ro_tfa a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Class ro_tfa_below_ofl {SK : YI16.sink_head} : Prop := ro_tfa_below : forall a, in_ro_tfa a -> a < YI16.sk_ofl_head.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ro_tfa_below_ofl}.
Lemma arodata_ok_journal : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_ok B (aview tfibsegs (w_H W) mem) -> arodata_ok B (aview tfibsegs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | apply YCbq.fp_spares_below; exact (ro_tfa_below a Hro)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma Hwx_tfa : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma tfib_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Definition TFIB_IMG_LO : Z := YImgTop.IMG_LO.
Definition TFIB_IMG_END : Z := YImgTop.IMG_TOP.
Lemma tfib_img_range : forall a, in_img tfibsegs a -> TFIB_IMG_LO <= a < TFIB_IMG_END.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; unfold TFIB_IMG_LO, TFIB_IMG_END; lia.
Qed.
Lemma tfib_img_cover : forall ly S md, ALedger tfibsegs ly S md ->
fst (ly_img ly) <= TFIB_IMG_LO /\ TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md L. split.
- destruct (al_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (al_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFIB_IMG_END. lia.
Qed.
Lemma zone2_of_app : forall a n, in_app a n -> off_img a n -> zone2 a n.
Proof. intros a n [_ H] Hi. split; [exact Hi|]. unfold kLowShadowBeg, kHighMemBeg in H. lia. Qed.
Lemma blk_off_img : forall B ly S (W : world tfibsegs) mem md p n,
AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
off_img p (req_size n).
Proof.
intros B ly S W mem md p n (M & L & _) Hin. unfold off_img. pose proof (tfib_img_cover ly S md L) as [C1 C2]. unfold TFIB_IMG_LO, TFIB_IMG_END in C1, C2.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _). rewrite Hn in G7.
pose proof (req_size_pos n ltac:(lia)) as [Q _].
destruct (Z.le_gt_cases (p + req_size n) TFIB_IMG_LO) as [H1|H1]; unfold TFIB_IMG_LO in H1; [left; lia|].
destruct (Z.le_gt_cases TFIB_IMG_END p) as [H2|H2]; unfold TFIB_IMG_END in H2; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max p TFIB_IMG_LO) M); unfold TFIB_IMG_LO.
- left. exists k. rewrite Hu. unfold ck_n. rewrite Hn. refine (conj Hk (conj Hst _)). lia.
- unfold in_zr. lia.
Qed.
Lemma frm_off_img : forall B ly S (W : world tfibsegs) mem md cid pos,
AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
off_img (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros B ly S W mem md cid pos (M & L & _) Hin. unfold off_img. pose proof (tfib_img_cover ly S md L) as [C1 C2]. unfold TFIB_IMG_LO, TFIB_IMG_END in C1, C2.
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) TFIB_IMG_LO) as [H1|H1]; unfold TFIB_IMG_LO in H1; [left; lia|].
destruct (Z.le_gt_cases TFIB_IMG_END (frame_addr ly cid pos)) as [H2|H2]; unfold TFIB_IMG_END in H2; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) TFIB_IMG_LO) M); unfold TFIB_IMG_LO.
- right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- unfold in_zr. lia.
Qed.
End c.
Ltac zones := unfold zone2, off_img, in_app, app_addr, kLowShadowBeg, kHighMemBeg in *.
Ltac req_lits := unfold RAW_SIZE, CGIF_SIZE, FRAME_SIZE in *; change (req_size 96) with 96 in *; change (req_size 48) with 48 in *; change (req_size 40) with 40 in *;
change (req_size 72) with 72 in *; change (req_size 32) with 32 in *; change (req_size 8192) with 8192 in *;
change (req_size 4096) with 4096 in *.
Ltac zone_lia := first [lia | zones; req_lits; lia].
Ltac flag_disj_cheap HFLown :=
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [lia_cheap | exact HFLown] end end.
Definition stack_region (frame : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- frame) 0 (- frame) 0 [].
Definition got_region : YP09.region :=
YP09.mkRegion None A_GOT_shadow (A_GOT_shadow + 8) 0 0 [YP09.mkChunk A_GOT_shadow (CVal 8 (SLit A_shadow_glob))].
Definition bcell_region (bx : nat) : YP09.region :=
YP09.mkRegion None A_shadow_glob (A_shadow_glob + 8) 0 0 [YP09.mkChunk A_shadow_glob (CVal 8 (SOff bx 0))].
Lemma req_size_pos0 : forall m, 0 <= m -> 0 < req_size m /\ m <= req_size m.
Proof. intros m Hm. unfold req_size. destruct (Z.eqb_spec m 0); cbn; lia. Qed.
Ltac shent_U_norm :=
rewrite ?U_SOff; rewrite ?ew_havoc_old by (cbn; lia); cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by (cbn; lia);
repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => progress rewrite H end;
repeat match goal with H : forall n : nat, _ -> ew ?E1 n = _ |- context [ew ?E1 ?m] => progress (rewrite (H m) by (cbn; lia)) end;
repeat match goal with H : ew ?E ?n = _ |- context [ew ?E ?n] => progress rewrite H end;
repeat match goal with H : getr ?rg ?r = _ |- context [getr ?rg ?r] => progress rewrite H end;
rewrite ?Z_to_bv_bv_unsigned;
rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r; rewrite ?zcanon_id by (unfold SB, M64; lia).
Ltac shent_Bx_tac :=
first [ assumption
| lazymatch goal with |- U ?E ?Bx = SHADOW_OFF =>
first [ progress (unfold Bx) | idtac ]; shent_U_norm; unfold SHADOW_OFF, SB; first [reflexivity | lia] end ].
Ltac shent_req_hi n :=
shent_U_norm; unfold RAW_SIZE, CGIF_SIZE, FRAME_SIZE in *;
first [ lazymatch goal with |- _ <= _ + req_size ?n' => pose proof (req_size_pos0 n' ltac:(lia)) end; lia
| pose proof (req_size_pos0 n ltac:(lia)); lia
| cbv [req_size Z.eqb]; lia ].
Ltac shent_syn b := lazymatch goal with |- _ <= ?vv => match vv with context [b] => idtac end end.
Ltac shent_syn2 b := lazymatch goal with |- ?g => match g with context [b] => idtac end end.
Ltac shent_app_solve_old :=
let LAWS := aj_laws in
lazymatch goal with |- shent_ok ?segs ?Bx ?E ?M (mkSHE ?m ?whi ?wlo) =>
first
[
match goal with
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HAR : AR _ _ ?ly ?S ?W ?mem ?md |- _ =>
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m (U E (SOff m 0)) b n wlo whi M HAR Hin);
[ shent_Bx_tac | reflexivity | shent_U_norm; shent_syn b; lia | lia | shent_req_hi n ]
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m (U E (SOff m 0)) b n wlo whi M (proj1 HJ) Hin);
[ shent_Bx_tac | reflexivity | shent_U_norm; shent_syn b; lia | lia | shent_req_hi n ]
end
|
match goal with
| H : in_app ?p ?n |- _ =>
apply (shent_app_of_app segs E Bx m (U E (SOff m 0)) wlo whi M);
[ shent_Bx_tac | reflexivity
| shent_U_norm; shent_syn2 p; clear - H; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
| lia ]
end
|
match goal with
| Hin : In (?cid, ?pos) (frames ?S), HAR : AR _ ?B ?ly ?S ?W ?mem ?md |- _ =>
apply (shent_app_of_frame segs B LAWS ly S W mem md E Bx m (U E (SOff m 0)) cid pos wlo whi M HAR Hin);
[ shent_Bx_tac | reflexivity | shent_U_norm; lia | lia | shent_U_norm; lia ]
| Hin : In (?cid, ?pos) (frames ?S), HJ : ajournal _ ?B _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
apply (shent_app_of_frame segs B LAWS ly S W mem md E Bx m (U E (SOff m 0)) cid pos wlo whi M (proj1 HJ) Hin);
[ shent_Bx_tac | reflexivity | shent_U_norm; lia | lia | shent_U_norm; lia ]
end
|
match goal with
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HAR : AR _ _ ?ly ?S ?W ?mem ?md |- _ =>
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m (U E (SOff m 0)) b n wlo whi M HAR Hin);
[ shent_Bx_tac | reflexivity | shent_U_norm; lia | lia | shent_req_hi n ]
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m (U E (SOff m 0)) b n wlo whi M (proj1 HJ) Hin);
[ shent_Bx_tac | reflexivity | shent_U_norm; lia | lia | shent_req_hi n ]
end
|
apply (shent_app_of_high segs E Bx m (U E (SOff m 0)) wlo whi M);
[ shent_Bx_tac | reflexivity | shent_U_norm; zlia | lia ]
|
apply (shent_app_of_app segs E Bx m (U E (SOff m 0)) wlo whi M);
[ shent_Bx_tac | reflexivity
| shent_U_norm; unfold zone2, off_img, in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
| lia ]
| fail 1 "shent_app_solve: no block / frame / stack justification found for the writable window of atom" m ]
end.
Ltac shent_app_solve_fast :=
let LAWS := aj_laws in
lazymatch goal with |- shent_ok ?segs ?Bx ?E ?M (mkSHE ?m ?whi ?wlo) =>
let Hu := fresh "Hu" in let HBx := fresh "HBx" in
eassert (Hu : U E (SOff m 0) = _) by (shent_U_norm; reflexivity);
assert (HBx : U E Bx = SHADOW_OFF) by shent_Bx_tac;
lazymatch type of Hu with _ = ?q =>
first
[ match goal with
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HAR : AR _ _ ?ly ?S ?W ?mem ?md |- _ =>
lazymatch q with context [b] => idtac end;
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m q b n wlo whi M HAR Hin);
[ exact HBx | exact Hu | lia_cheap | lia | shent_req_hi n ]
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
lazymatch q with context [b] => idtac end;
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m q b n wlo whi M (proj1 HJ) Hin);
[ exact HBx | exact Hu | lia_cheap | lia | shent_req_hi n ]
end
| match goal with
| H : in_app ?p ?n |- _ =>
lazymatch q with context [p] => idtac end;
apply (shent_app_of_app segs E Bx m q wlo whi M);
[ exact HBx | exact Hu | clear - H; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia | lia ]
end
| apply (shent_app_of_high segs E Bx m q wlo whi M); [ exact HBx | exact Hu | appn; lia_cheap | lia ]
| apply (shent_app_of_app segs E Bx m q wlo whi M);
[ exact HBx | exact Hu
| unfold zone2, off_img, in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
first [ solve [YM03.lf_prune0; YM03.lf_lia_orig] | solve [YM03.lf_prune1; YM03.lf_lia_orig] ]
| lia ]
| match goal with
| Hin : In (?cid, ?pos) (frames ?S), HAR : AR _ ?B ?ly ?S ?W ?mem ?md |- _ =>
apply (shent_app_of_frame segs B LAWS ly S W mem md E Bx m q cid pos wlo whi M HAR Hin);
[ exact HBx | exact Hu | lia_cheap | lia | lia_cheap ]
| Hin : In (?cid, ?pos) (frames ?S), HJ : ajournal _ ?B _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
apply (shent_app_of_frame segs B LAWS ly S W mem md E Bx m q cid pos wlo whi M (proj1 HJ) Hin);
[ exact HBx | exact Hu | lia_cheap | lia | lia_cheap ]
end
| match goal with
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HAR : AR _ _ ?ly ?S ?W ?mem ?md |- _ =>
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m q b n wlo whi M HAR Hin);
[ exact HBx | exact Hu | lia_cheap | lia | shent_req_hi n ]
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
apply (shent_app_of_block segs B LAWS ly S W mem md E Bx m q b n wlo whi M (proj1 HJ) Hin);
[ exact HBx | exact Hu | lia_cheap | lia | shent_req_hi n ]
end
|
apply (shent_app_of_app segs E Bx m q wlo whi M);
[ exact HBx | exact Hu
| unfold zone2, off_img, in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
| lia ] ] end end.
Ltac shent_app_solve := first [ shent_app_solve_fast | shent_app_solve_old ].
Ltac shent_range_app_slow :=
let LAWS := aj_laws in
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [Z.min Z.max] in Hx;
first
[ unfold zone2, off_img, in_app, app_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
| match goal with
| Hin : In (?cid, ?pos) (frames ?S), HAR : AR ?segs ?B ?ly ?S ?W ?mem ?md |- _ =>
generalize (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hin);
unfold zone2, off_img, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
| Hin : In (?cid, ?pos) (frames ?S), HJ : ajournal ?segs ?B _ _ _ _ _ _ _ _ _ ?ly ?S ?W ?mem ?md _ |- _ =>
generalize (frames_bounds segs B LAWS ly S W mem md cid pos (proj1 HJ) Hin);
unfold zone2, off_img, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
| Hin : In (?b, ?n) (ablocks ?B ?ly ?S), HAR : AR ?segs ?B ?ly ?S ?W ?mem ?md |- _ =>
generalize (al_blocks segs B LAWS ly S W mem md b n HAR Hin);
unfold zone2, off_img, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
end
| fail 1 "shent_range_app: cannot show the range is app memory" ].
Ltac shent_range_app :=
first
[ let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [Z.min Z.max] in Hx;
match goal with
| H : in_app ?p ?n |- _ => clear - Hx H; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia
| H : in_app ?p (req_size ?n) |- _ =>
let Hq := fresh "Hq" in pose proof (req_size_pos0 n ltac:(clear - Hx; lia)) as Hq;
clear - Hx H Hq; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia
end
| shent_range_app_slow ].
Ltac shok_assert SHOK segs Bx SH E M tac0 :=
assert (SHOK : sh_ok segs Bx SH E M);
[ unfold sh_ok; repeat (apply Forall_cons; [first [tac0 | shent_app_solve] |]); apply Forall_nil | ].
Ltac shok_auto_with SHOK Bx E M SH0 tac0 :=
lazymatch goal with
| HS : st_ok ?segs E ?ss _ |- _ =>
let tmp := fresh "shtmp" in
first
[ timeout 30   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
(let SH := eval lazy in (SH0 ++ app_entries (ss_facts ss) (ss_mem ss)) in
lazymatch SH with
| context [flat_map] => fail
| context [app_entries] => fail
| _ => pose (tmp := SH)
end)
| idtac "shok_auto: FALLBACK to the given entries only (the app entries of this state are not computable)";
pose (tmp := SH0) ];
let SH := eval cbv delta [tmp] in tmp in
clear tmp; shok_assert SHOK segs Bx SH E M tac0
| _ => fail "shok_auto: no hypothesis  st_ok segs E ss ms  for that valuation"
end.
Ltac shok_auto SHOK Bx E M := shok_auto_with SHOK Bx E M (@nil shent) fail.
