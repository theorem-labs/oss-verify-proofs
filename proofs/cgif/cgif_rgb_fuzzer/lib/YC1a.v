(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YQ0j YQ0c YQ0b YQ03 YQ0i YQ04 YQ00 YC02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YG00 YG0a YG01 YG0h YG0u YG0y YG0d YC04.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition A_GOT_shadow : Z := 0xa2160.
Definition A_shadow_glob : Z := 0xaa1b8.
Definition A_GOT_uar : Z := 0xa21b8.
Definition A_uar_glob : Z := 0xaa1c0.
Definition SB : Z := 0x7fff8000.
Lemma SB_SHADOW_OFF : SB = SHADOW_OFF. Proof. reflexivity. Qed.
Definition lib_const_addr (a : Z) : Prop := (0x103b8 <= a < 0x103c0) \/ (0xa2dd8 <= a < 0xa2e00).
Record TraLib (B : asyms) : Prop := {
tl_code : as_code B = Tra_code;
tl_got_shadow : as_got_shadow B = A_GOT_shadow;
tl_shadow_cell : as_shadow_cell B = A_shadow_glob;
tl_got_uar : as_got_uar B = A_GOT_uar;
tl_uar_cell : as_uar_cell B = A_uar_glob;
tl_errno : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd;
tl_errno_img : forall a, as_errno B <= a < as_errno B + 4 -> in_img trasegs a;
tl_universe : forall t, In t Tra_universe -> In t (as_universe B);
tl_lib_consts : forall a, lib_const_addr a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4);
tl_gp : 0 <= as_gp B < 2 ^ 64
}.
Lemma tl_env : forall B, TraLib B -> api_env trasegs B.
Proof.
intros B TL. split; [exact (tl_errno B TL)|]. split; [exact (tl_errno_img B TL)|]. rewrite (tl_code B TL).
split; apply (tl_universe B TL); apply memZL_In; vm_compute; reflexivity.
Qed.
Definition in_ro_tfa (a : Z) : Prop :=
(exists s, In s trasegs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (0xa1c00 <= a < 0xa2e80).
Definition arodata_ok (B : asyms) (rd : reader) : Prop :=
forall a, in_ro_tfa a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom trasegs (Z_to_bv 64 a)).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma arodata_ok_journal : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal trasegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_ok B (aview trasegs (w_H W) mem) -> arodata_ok B (aview trasegs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma Hwx_tfa : wx_segs_nowrap trasegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma tra_segs_low : forall a, in_img trasegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) trasegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) trasegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma tra_img_range : forall a, in_img trasegs a -> 0x10000 <= a < 0x5ff000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) trasegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) trasegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Definition TRA_IMG_LO : Z := 0x10000.
Definition TRA_IMG_END : Z := 0x5ff000.
Lemma tra_img_cover : forall ly S md, ALedger trasegs ly S md ->
fst (ly_img ly) <= TRA_IMG_LO /\ TRA_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md L. split.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TRA_IMG_LO. lia.
- destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TRA_IMG_END. lia.
Qed.
Lemma zone2_of_app : forall a n, in_app a n -> off_img a n -> zone2 a n.
Proof. intros a n [_ H] Hi. split; [exact Hi|]. unfold kLowShadowBeg, kHighMemBeg in H. lia. Qed.
Lemma blk_off_img : forall B ly S (W : world trasegs) mem md p n,
AR trasegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
off_img p (req_size n).
Proof.
intros B ly S W mem md p n (M & L & _) Hin. unfold off_img. pose proof (tra_img_cover ly S md L) as [C1 C2]. unfold TRA_IMG_LO, TRA_IMG_END in C1, C2.
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _). rewrite Hn in G7.
pose proof (req_size_pos n ltac:(lia)) as [Q _].
destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases 0x5ff000 p) as [|H2]; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max p 0x10000) M).
- left. exists k. rewrite Hu. unfold ck_n. rewrite Hn. refine (conj Hk (conj Hst _)). lia.
- unfold in_zr. lia.
Qed.
Lemma frm_off_img : forall B ly S (W : world trasegs) mem md cid pos,
AR trasegs B ly S W mem md -> In (cid, pos) (frames S) ->
off_img (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros B ly S W mem md cid pos (M & L & _) Hin. unfold off_img. pose proof (tra_img_cover ly S md L) as [C1 C2]. unfold TRA_IMG_LO, TRA_IMG_END in C1, C2.
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases 0x5ff000 (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) 0x10000) M).
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
Definition stack_region (frame : Z) : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- frame) 0 (- frame) 0 [].
Definition got_region : YQ0b.region :=
YQ0b.mkRegion None A_GOT_shadow (A_GOT_shadow + 8) 0 0 [YQ0b.mkChunk A_GOT_shadow (CVal 8 (SLit A_shadow_glob))].
Definition bcell_region (bx : nat) : YQ0b.region :=
YQ0b.mkRegion None A_shadow_glob (A_shadow_glob + 8) 0 0 [YQ0b.mkChunk A_shadow_glob (CVal 8 (SOff bx 0))].
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
first [ solve [YN03.lf_prune0; YN03.lf_lia_orig] | solve [YN03.lf_prune1; YN03.lf_lia_orig] ]
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
