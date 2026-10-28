(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP0e YP09 YP02 YP0l YP03 YP00 YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI09 YN3v YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition SB : Z := 0x7fff8000.
Lemma SB_SHADOW_OFF : SB = SHADOW_OFF. Proof. reflexivity. Qed.
Ltac zones := unfold zone2, off_img, in_app, app_addr, kLowShadowBeg, kHighMemBeg in *.
Ltac req_lits := unfold RAW_SIZE, CGIF_SIZE, FRAME_SIZE in *; change (req_size 96) with 96 in *; change (req_size 48) with 48 in *; change (req_size 40) with 40 in *;
change (req_size 72) with 72 in *; change (req_size 32) with 32 in *; change (req_size 8192) with 8192 in *;
change (req_size 4096) with 4096 in *.
Ltac zone_lia := first [lia | zones; req_lits; lia].
Ltac flag_disj_cheap HFLown :=
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
match goal with Hn : forall a, _ -> ~ aowned _ _ _ a |- _ => apply (Hn fl); [lia_cheap | exact HFLown] end end.
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
| HS : st_ok_pi ?segs _ E ?ss _ |- _ =>
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
