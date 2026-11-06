(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the shadow map of a whole image range is present in the view, for ANY image, from two
   laws of the invariant and one computed cover check over the image's own lists:
   - the zero-shadow law: the shadow bytes of every range of as_zero_shadow B are 0 (ARm's am_zshadow, YG0n.v:190-191;
     ARmcf's amc_zshadow is the same field);
   - the const law: every cell of as_const B ly holds in memory (am_const, YG0n.v:211; amc_const);
   - img_shadow_cover zs cs L H: every granule of [L, H) has its shadow byte, at a / 8 + SHADOW_OFF, inside the shadow of one
     range of zs or at a byte of one cell of cs. It is decided over the list of granule intervals, one per range and one
     per cell byte, never per granule: shv_cover_from moves a cursor from the first granule to the end of an interval that
     holds it, until it passes the last granule. The intervals need no order.
   A unit instantiates img_shadow_vis_of_cover with its own zero-shadow ranges, its own shadow cells and its own image
   bounds, and proves img_shadow_cover by vm_compute. No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The cursor cover over [start, end) intervals.                               *)
Fixpoint shv_cover_from (iv : list (Z * Z)) (fuel : nat) (cur hi : Z) : bool :=
if hi <=? cur then true else
match fuel with
| O => false
| S f =>
  match find (fun r => (fst r <=? cur) && (cur <? snd r)) iv with
  | Some r => shv_cover_from iv f (snd r) hi
  | None => false
  end
end.

Lemma shv_cover_from_sound : forall iv fuel cur hi, shv_cover_from iv fuel cur hi = true ->
forall g, cur <= g < hi -> exists r, In r iv /\ fst r <= g < snd r.
Proof.
intros iv fuel. induction fuel as [|f IH]; intros cur hi H g Hg; cbn [shv_cover_from] in H.
- destruct (hi <=? cur) eqn:E; [apply Z.leb_le in E; lia | discriminate].
- destruct (hi <=? cur) eqn:E; [apply Z.leb_le in E; lia|].
destruct (find (fun r => (fst r <=? cur) && (cur <? snd r)) iv) as [r|] eqn:F; [|discriminate].
destruct (find_some _ _ F) as [Hr Hb]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (Z_lt_le_dec g (snd r)) as [Hlt|Hge].
+ exists r. split; [exact Hr | lia].
+ exact (IH (snd r) hi H g (conj Hge (proj2 Hg))).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The intervals of an image's lists, in granule numbers (a / 8).             *)
(* zero_shadow rd SHADOW_OFF lo len reads the len / 8 shadow bytes from lo / 8 + SHADOW_OFF (YG0v.v:35-36). *)
Definition shv_zs_iv (r : Z * Z) : Z * Z := (fst r / 8, fst r / 8 + snd r / 8).
(* the byte at x is the shadow byte of granule x - SHADOW_OFF *)
Definition shv_cell_iv (x : Z) : Z * Z := (x - SHADOW_OFF, x - SHADOW_OFF + 1).
(* the bytes a cell at a fixed address pins: all w bytes of a value cell, the one byte of a mask cell *)
Definition shv_acell_bytes (c : acell) : list Z :=
match c_at c with
| ANum x => match c_val c with
            | AV _ => map (fun k => x + Z.of_nat k) (seq 0 (c_w c))
            | AVmask _ _ => [x]
            end
| _ => []
end.
Definition shv_cell_bytes (cs : list acell) : list Z := flat_map shv_acell_bytes cs.
Definition shv_ivs (zs : list (Z * Z)) (cs : list acell) : list (Z * Z) :=
map shv_zs_iv zs ++ map shv_cell_iv (shv_cell_bytes cs).
(* The cover check: the granules of [L, H) are L / 8 .. (H - 1) / 8. Each step uses a new interval (the cursor
   passes the end of the one it used), so the fuel of one step per interval is enough. *)
Definition img_shadow_cover (zs : list (Z * Z)) (cs : list acell) (L H : Z) : bool :=
let iv := shv_ivs zs cs in shv_cover_from iv (S (length iv)) (L / 8) ((H - 1) / 8 + 1).

(* ---------------------------------------------------------------------------- *)
(* 3. Soundness over any reader.                                                  *)
Lemma img_shadow_cover_sound : forall (rd : reader) zs cs L H,
img_shadow_cover zs cs L H = true ->
(forall r, In r zs -> zero_shadow rd SHADOW_OFF (fst r) (snd r)) ->
(forall x, In x (shv_cell_bytes cs) -> rd x <> None) ->
forall a, L <= a < H -> rd (shadow_addr a) <> None.
Proof.
intros rd zs cs L H Hc HZ HC a Ha. unfold img_shadow_cover in Hc.
assert (Hg : L / 8 <= a / 8 < (H - 1) / 8 + 1).
{ assert (G1 : L / 8 <= a / 8) by (apply Z.div_le_mono; lia).
assert (G2 : a / 8 <= (H - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
destruct (shv_cover_from_sound _ _ _ _ Hc (a / 8) Hg) as (r & Hr & Hin).
unfold shv_ivs in Hr. apply in_app_iff in Hr as [Hr|Hr]; apply in_map_iff in Hr as (q & <- & Hq).
- unfold shv_zs_iv in Hin. cbn [fst snd] in Hin.
pose proof (HZ q Hq (a / 8 - fst q / 8) ltac:(lia)) as E. unfold shadow_of_addr in E.
unfold shadow_addr. replace (SHADOW_OFF + a / 8) with (SHADOW_OFF + fst q / 8 + (a / 8 - fst q / 8)) by ring.
rewrite E. discriminate.
- unfold shv_cell_iv in Hin. cbn [fst snd] in Hin.
assert (E : shadow_addr a = q) by (unfold shadow_addr; lia). rewrite E. exact (HC q Hq).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The two laws of the invariant, read at the lists.                           *)
Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma shv_acell_bytes_vis : forall B ly (rd : reader) c x,
cell_holds B ly rd c -> In x (shv_acell_bytes c) -> rd x <> None.
Proof.
intros B ly rd [ca cw cv] x Hh Hx. unfold shv_acell_bytes in Hx. unfold cell_holds in Hh. cbn [c_at c_val c_w] in Hx, Hh.
destruct ca; try (cbn [In] in Hx; contradiction). destruct cv as [e | m v]; cbn [aeval In] in Hh, Hx.
- apply in_map_iff in Hx as (k & <- & Hk). apply in_seq in Hk.
rewrite (Hh k ltac:(lia)). discriminate.
- destruct Hx as [<- | []]. destruct Hh as (b & Hb & _). rewrite Hb. discriminate.
Qed.

Lemma shv_zshadow_ok_in : forall B ly (rd : reader) r,
zshadow_ok B ly rd -> In r (as_zero_shadow B) -> zero_shadow rd SHADOW_OFF (fst r) (snd r).
Proof.
intros B ly rd r H Hr. apply (proj1 (Forall_forall _ _) H). unfold zero_shadow_ranges. right. exact Hr.
Qed.

(* The reader form: the zero-shadow law and the const law at ly, and the cover of the lists. *)
Lemma shadow_vis_of_cover : forall B ly (rd : reader) zs cs L H,
img_shadow_cover zs cs L H = true -> incl zs (as_zero_shadow B) -> incl cs (as_const B ly) ->
zshadow_ok B ly rd -> Forall (cell_holds B ly rd) (as_const B ly) ->
forall a, L <= a < H -> rd (shadow_addr a) <> None.
Proof.
intros B ly rd zs cs L H Hc Iz Ic HZ HC. apply (img_shadow_cover_sound rd zs cs L H Hc).
- intros r Hr. exact (shv_zshadow_ok_in B ly rd r HZ (Iz r Hr)).
- intros x Hx. unfold shv_cell_bytes in Hx. apply in_flat_map in Hx as (c & Hc' & Hx).
exact (shv_acell_bytes_vis B ly rd c x (proj1 (Forall_forall _ _) HC c (Ic c Hc')) Hx).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The AR form (cgif's AR, YG0n.v:490-491), for any image bounds L, H.         *)
Definition img_shadow_vis_at (segs : list Segment) (B : asyms) (L H : Z) : Prop :=
forall ly S (W : world segs) mem md a, AR segs B ly S W mem md -> L <= a < H ->
aview segs (w_H W) mem (shadow_addr a) <> None.

Theorem img_shadow_vis_of_cover : forall segs B zs cs L H,
img_shadow_cover zs cs L H = true -> incl zs (as_zero_shadow B) -> (forall ly, incl cs (as_const B ly)) ->
img_shadow_vis_at segs B L H.
Proof.
intros segs B zs cs L H Hc Iz Ic ly S W mem md a HAR Ha. destruct HAR as (M & _).
exact (shadow_vis_of_cover B ly _ zs cs L H Hc Iz (Ic ly) (am_zshadow _ _ _ _ M) (am_const _ _ _ _ M) a Ha).
Qed.
End v.
