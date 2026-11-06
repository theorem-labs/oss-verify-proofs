(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Spec Require Import Prelim PrintfModel.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.G3 Require Import LeptFormats LeptShapes Printf_sn2 LeptModel.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import D_kit FX_lib F_achk F_printf_iface I_qck I_pck I_pcseg I_pcgen I_leptfmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sx32w (w : word) : Z := (bv_unsigned w + 2^31) mod 2^32 - 2^31.

Lemma sx32w_ok : forall w, -2^31 <= sx32w w < 2^31 /\ bv_unsigned w mod 2^32 = sx32w w mod 2^32.
Proof.
  intros w. unfold sx32w. pose proof (Z.mod_pos_bound (bv_unsigned w + 2^31) (2^32) ltac:(lia)) as B. split; [lia|].
  rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. lia.
Qed.

Fixpoint largs (sh : pshape) (ws : list word) (strs : list (list byte)) : list parg :=
  match sh, ws with
  | (k, _, _) :: r, w :: ws' =>
      match k with
      | LK_s => PA_s (map bv_unsigned (hd [] strs)) :: largs r ws' (tl strs)
      | LK_d => PA_i (sx32w w) :: largs r ws' strs
      | LK_zu => PA_z (bv_unsigned w) :: largs r ws' strs
      end
  | _, _ => []
  end.

Fixpoint lsargs (sh : pshape) (ws : list word) (strs : list (list byte)) : list (Z * list byte) :=
  match sh, ws with
  | (k, _, _) :: r, w :: ws' =>
      match k with
      | LK_s => (bv_unsigned w, hd [] strs) :: lsargs r ws' (tl strs)
      | _ => lsargs r ws' strs
      end
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition lstr (m : mem) (lo D dn S : Z) (str : list byte) : Prop :=
  exists slack : list byte,
    bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
    /\ (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ 0 < S /\ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo
    /\ chkr m S (Z.of_nat (length str) + 1)
    /\ (D + dn <= S \/ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= D)
    /\ Z.of_nat (length str) < 96.

Fixpoint lstrs_ok (m : mem) (lo D dn : Z) (sh : pshape) (ws : list word) (strs : list (list byte)) : Prop :=
  match sh, ws with
  | (k, _, _) :: r, w :: ws' =>
      match k with
      | LK_s => lstr m lo D dn (bv_unsigned w) (hd [] strs) /\ lstrs_ok m lo D dn r ws' (tl strs)
      | _ => lstrs_ok m lo D dn r ws' strs
      end
  | [], _ => True
  | _ :: _, [] => False
  end.

(* [comment removed for export] *)
Lemma largs_lept_arg_ok : forall sh ws strs m lo D dn, lstrs_ok m lo D dn sh ws strs ->
  Forall2 lept_arg_ok (map (fun it => fst (fst it)) sh) (largs sh ws strs).
Proof.
  induction sh as [|[[k nx] t] r IH]; intros ws strs m lo D dn H; [constructor|].
  destruct ws as [|w ws']; [destruct H|]. cbn [map fst largs lstrs_ok] in *.
  destruct k.
  - destruct H as [(sl & BY & NZ & PAD & S0 & SB & CHK & SEP & L96) Hr]. constructor; [| exact (IH ws' (tl strs) m lo D dn Hr)].
    cbn [lept_arg_ok]. split.
    + apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
      pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
      destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [| lia]. exfalso. apply NZ.
      replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
    + unfold zlength. rewrite length_map. exact L96.
  - constructor; [| exact (IH ws' strs m lo D dn H)]. cbn [lept_arg_ok]. exact (proj1 (sx32w_ok w)).
  - constructor; [| exact (IH ws' strs m lo D dn H)]. cbn [lept_arg_ok]. pose proof (bv_unsigned_in_range 64 w) as R.
    unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma largs_pargs : forall sh ws strs m lo D dn VA, lstrs_ok m lo D dn sh ws strs ->
  (forall i w, nth_error ws i = Some w -> ro_cells asegs m (VA + 8 * Z.of_nat i) [C8 w]) -> lo < 2^47 ->
  pargs m (2^64) lo VA (fill sh (lsargs sh ws strs)).
Proof.
  induction sh as [|[[k nx] t] r IH]; intros ws strs m lo D dn VA H SL LO; [exact I|].
  destruct ws as [|w ws']; [destruct H|].
  assert (SL' : forall i w0, nth_error ws' i = Some w0 -> ro_cells asegs m (VA + 8 + 8 * Z.of_nat i) [C8 w0]).
  { intros i w0 Hi. replace (VA + 8 + 8 * Z.of_nat i) with (VA + 8 * Z.of_nat (S i)) by lia. apply SL. exact Hi. }
  cbn [lstrs_ok lsargs] in *. destruct k; cbn [fill kind_dir hd tl pargs fst snd].
  - destruct H as [(sl & BY & NZ & PAD & S0 & SB & CHK & SEP & L96) Hr].
    split; [| exact (IH ws' (tl strs) m lo D dn (VA + 8) Hr SL' LO)].
    pose proof (SL 0%nat w eq_refl) as SL0. rewrite Z.mul_0_r, Z.add_0_r in SL0.
    split; [rewrite Z_to_bv_bv_unsigned; exact SL0|].
    split. { split; [| exact NZ]. replace (hd [] strs ++ Z_to_bv 8 0 :: sl) with ((hd [] strs ++ [z8]) ++ sl) in BY
               by (rewrite <- app_assoc; reflexivity). apply bytes_at_app in BY. exact (proj1 BY). }
    split; [exact S0|]. split; [left; lia|]. split; [lia|]. exact (chkr_chk_ok _ _ _ CHK).
  - split; [exact I| exact (IH ws' strs m lo D dn (VA + 8) H SL' LO)].
  - split; [exact I| exact (IH ws' strs m lo D dn (VA + 8) H SL' LO)].
Qed.

(* [comment removed for export] *)
Lemma lstrs_ok_munch : forall sh ws strs W m m' lo D dn, lstrs_ok m lo D dn sh ws strs -> munch W m m' ->
  (forall x, x < lo -> ~ (D <= x < D + dn) -> outside W x) -> (forall x, SHADOW_LO <= x < SHADOW_HI -> outside W x) ->
  lstrs_ok m' lo D dn sh ws strs.
Proof.
  induction sh as [|[[k nx] t] r IH]; intros ws strs W m m' lo D dn H MU HW HS; [exact I|].
  destruct ws as [|w ws']; [destruct H|]. cbn [lstrs_ok] in *.
  destruct k; [| exact (IH ws' strs W m m' lo D dn H MU HW HS) | exact (IH ws' strs W m m' lo D dn H MU HW HS)].
  destruct H as [(sl & BY & NZ & PAD & S0 & SB & CHK & SEP & L96) Hr]. split; [| exact (IH ws' (tl strs) W m m' lo D dn Hr MU HW HS)].
  exists sl. split.
  { apply (bytes_at_agree asegs m m' _ _ BY). apply (agree_of_munch _ _ _ _ MU). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
    apply HW; lia. }
  split; [exact NZ|]. split; [exact PAD|]. split; [exact S0|]. split; [exact SB|].
  split; [exact (chkr_munch W m m' _ _ CHK MU HS)|]. split; [exact SEP | exact L96].
Qed.

(* [comment removed for export] *)
Lemma largs_args_ok : forall sh ws strs m lo D dn sp, lstrs_ok m lo D dn sh ws strs ->
  args_ok lo lo 0 (lo + 8) 0 lo 0 m lo sp lo ws (largs sh ws strs).
Proof.
  induction sh as [|[[k nx] t] r IH]; intros ws strs m lo D dn sp H; [cbn [largs]; destruct ws; exact I|].
  destruct ws as [|w ws']; [destruct H|]. cbn [lstrs_ok largs] in *.
  destruct k; cbn [args_ok].
  - destruct H as [(sl & BY & NZ & PAD & S0 & SB & CHK & SEP & L96) Hr]. split; [| exact (IH ws' (tl strs) m lo D dn sp Hr)].
    cbn [arg_ok]. exists sl. unfold zlength. rewrite length_map.
    assert (E : zb (map bv_unsigned (hd [] strs)) = hd [] strs).
    { generalize (hd [] strs). induction l as [|b l IHl]; [reflexivity|]. unfold zb in *. cbn [map]. rewrite IHl. f_equal.
      exact (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b). }
    rewrite E. split; [exact BY|].
    split. { apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
             pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
             destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [| lia]. exfalso. apply NZ.
             replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity. }
    split; [exact PAD|]. split; [exact S0|]. split; [left; lia|]. split; [left; lia|]. split; [repeat split; left; lia|]. split; [left; lia|]. exact CHK.
  - split; [| exact (IH ws' strs m lo D dn sp H)]. cbn [arg_ok]. exact (sx32w_ok w).
  - split; [| exact (IH ws' strs m lo D dn sp H)]. cbn [arg_ok]. reflexivity.
Qed.
