(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI0f.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a.
Variables (g : gcfg) (cur : frame) (bef : option frame).
Definition fl_useLCT : bool := flag (f_attr cur) 1.
Definition fl_hasAlpha : bool := flag (g_attr g) 8 || flag (f_attr cur) 2.
Definition fl_hasSet : bool := flag (f_attr cur) 4.
Definition fl_npal : Z := if fl_useLCT then f_nlp cur else g_ngp g.
Definition fl_gen1 : Z := match bef with None => clr (f_gen cur) 3 | Some _ => if fl_hasAlpha then clr (f_gen cur) 3 else f_gen cur end.
Definition fl_gen2 : Z := if fl_hasSet then clr fl_gen1 1 else fl_gen1.
Definition fl_gen3 : Z := if fl_npal =? 256 then clr fl_gen2 1 else fl_gen2.
Definition fl_dims : Z * Z * Z * Z :=
match bef with
| None => (g_w g, g_h g, 0, 0)
| Some b => if flag fl_gen3 2 then match diff_area g cur b with Some d => d | None => (1, 1, 0, 0) end else (g_w g, g_h g, 0, 0)
end.
Definition fl_w : Z := let '(w, _, _, _) := fl_dims in w.
Definition fl_h : Z := let '(_, h, _, _) := fl_dims in h.
Definition fl_top : Z := let '(_, _, t, _) := fl_dims in t.
Definition fl_left : Z := let '(_, _, _, l) := fl_dims in l.
Definition fl_tmp : list Z :=
match bef with
| None => f_img cur
| Some _ => if flag fl_gen3 2 then window (g_w g) (f_img cur) fl_w fl_h fl_top fl_left else f_img cur
end.
Definition fl_p : Z := Z.max 2 (calcNextPower2Ex fl_npal).
Definition fl_t0 : Z := (2 ^ fl_p - 1) mod 256.
Definition fl_tOpt : Z := if fl_t0 <? fl_npal then (2 ^ (fl_p + 1) - 1) mod 256 else fl_t0.
Definition fl_tidx : Z :=
match bef with
| None => f_trans cur
| Some _ => if flag fl_gen3 1 then fl_tOpt else f_trans cur
end.
Definition fl_img : list Z :=
match bef with
| None => f_img cur
| Some b => if flag fl_gen3 1
then map (fun pq => if cmp_pixel g cur b (fst pq) (snd pq) then fst pq else fl_tidx) (combine fl_tmp (window (g_w g) (f_img b) fl_w fl_h fl_top fl_left))
else fl_tmp
end.
Definition fl_trans_on : bool := match bef with None => false | Some _ => flag fl_gen3 1 end.
Definition fl_rattr : Z := (if fl_hasAlpha || fl_trans_on || fl_hasSet then 1 else 0) + (if flag (f_attr cur) 8 then 2 else 0).
Definition fl_slct : Z := if fl_useLCT then f_nlp cur else 0.
Lemma flush_frame_split : forall rcur,
flush_frame g rcur cur bef =
raw_addframe (flag (g_attr g) 2) (if flag (g_attr g) 4 then 0 else g_ngp g) rcur fl_img fl_rattr fl_w fl_h fl_top fl_left
(f_delay cur) fl_slct (f_lpal cur) (f_disp cur) fl_tidx.
Proof.
intros rcur. unfold flush_frame, fl_img, fl_rattr, fl_trans_on, fl_slct, fl_tidx, fl_tmp, fl_w, fl_h, fl_top, fl_left, fl_dims,
fl_tOpt, fl_t0, fl_p, fl_gen3, fl_gen2, fl_gen1, fl_npal, fl_hasSet, fl_hasAlpha, fl_useLCT.
destruct bef as [b|].
- destruct (flag (if (if flag (f_attr cur) 1 then f_nlp cur else g_ngp g) =? 256
then clr (if flag (f_attr cur) 4 then clr (if flag (g_attr g) 8 || flag (f_attr cur) 2 then clr (f_gen cur) 3 else f_gen cur) 1
else if flag (g_attr g) 8 || flag (f_attr cur) 2 then clr (f_gen cur) 3 else f_gen cur) 1
else if flag (f_attr cur) 4 then clr (if flag (g_attr g) 8 || flag (f_attr cur) 2 then clr (f_gen cur) 3 else f_gen cur) 1
else if flag (g_attr g) 8 || flag (f_attr cur) 2 then clr (f_gen cur) 3 else f_gen cur) 2);
[destruct (diff_area g cur b) as [[[[w h] t] l]|] |]; cbn; reflexivity.
- cbn. rewrite Bool.orb_false_r. reflexivity.
Qed.
Lemma fl_first : bef = None -> fl_w = g_w g /\ fl_h = g_h g /\ fl_top = 0 /\ fl_left = 0 /\ fl_img = f_img cur /\ fl_tidx = f_trans cur /\ fl_trans_on = false.
Proof. intros H. unfold fl_img, fl_tidx, fl_trans_on, fl_tmp, fl_w, fl_h, fl_top, fl_left, fl_dims. rewrite H. repeat split; reflexivity. Qed.
End a.
