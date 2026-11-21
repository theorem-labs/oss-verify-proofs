(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import MemRel MemFill DSLayout ZSLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import LmatchModel AdlerModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Lemma land_mod32_mask : forall y m, 0 <= m < 2 ^ 32 -> Z.land y m = Z.land (y mod 2 ^ 32) m.
Proof.
  intros y m Hm. rewrite <- (Z.land_ones y 32) by lia.
  rewrite <- Z.land_assoc. f_equal.
  rewrite Z.land_comm. symmetry. rewrite Z.land_ones_low; [reflexivity| lia |].
  destruct (Z.eq_dec m 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_mod_pow2 : forall a b n, 0 <= n ->
  (Z.lxor a b) mod 2 ^ n = Z.lxor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros k Hk.
  destruct (Z_lt_le_dec k n).
  - rewrite Z.mod_pow2_bits_low, !Z.lxor_spec, !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high, Z.lxor_spec, !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma szwrap32_mod : forall v, (szwrap 32 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  rewrite Zminus_mod, Z.mod_mod by lia.
  rewrite <- Zminus_mod. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. reflexivity.
Qed.

Lemma mod64_mod32 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
  rewrite Z.rem_mul_r by lia. rewrite Z.add_mod, Z.mod_mod by lia.
  rewrite (Z.mul_comm (2 ^ 32)), Z.mod_mul by lia. rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma zaluw_sll_mod32 : forall a b, (zaluw ALU_SLL a b) mod 2 ^ 32 = (a * 2 ^ (b mod 32)) mod 2 ^ 32.
Proof.
  intros a b. unfold zaluw. rewrite zw_sllw. rewrite u_zw. rewrite mod64_mod32. apply szwrap32_mod.
Qed.

Lemma uh_sllw : forall h sh c mask,
  0 <= mask < 2 ^ 32 -> 0 <= sh < 32 ->
  Z.land (Z.lxor (zaluw ALU_SLL h sh) c) mask = Z.land (Z.lxor (wrap32 (Z.shiftl h sh)) c) mask.
Proof.
  intros h sh c mask Hm Hsh.
  rewrite (land_mod32_mask (Z.lxor (zaluw ALU_SLL h sh) c)) by exact Hm.
  rewrite (land_mod32_mask (Z.lxor (wrap32 (Z.shiftl h sh)) c)) by exact Hm.
  rewrite !lxor_mod_pow2 by lia. f_equal. f_equal.
  rewrite zaluw_sll_mod32, wrap32_mod, Z.mod_mod, Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small sh) by lia. reflexivity.
Qed.

Lemma update_hash_sllw : forall s h sh c mask,
  ds_hash_shift s = sh -> ds_hash_mask s = mask -> 0 <= mask < 2 ^ 32 -> 0 <= sh < 32 ->
  Z.land (Z.lxor (zaluw ALU_SLL h sh) c) mask = update_hash s h c.
Proof.
  intros s h sh c mask <- <- Hm Hsh. unfold update_hash. apply uh_sllw; assumption.
Qed.


Lemma szwrap32_u64 : forall a, 0 <= a < 2 ^ 32 ->
  szwrap 32 a mod 2 ^ 64 = a + (if a <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32).
Proof.
  intros a Ha. unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  destruct (Z.ltb_spec a (2 ^ 31)).
  - rewrite (Z.mod_small (a + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (a + 2 ^ 31) (-1) (2 ^ 32)) by lia.
    rewrite (Z.mod_small (a + 2 ^ 31 + -1 * 2 ^ 32)) by lia.
    rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma szwrap32_u64_zero : forall a, 0 <= a < 2 ^ 32 -> (szwrap 32 a mod 2 ^ 64 = 0 <-> a = 0).
Proof. intros a Ha. rewrite szwrap32_u64 by lia. destruct (Z.ltb_spec a (2 ^ 31)); lia. Qed.




Fixpoint fbytes (f : Z -> Z) (a : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => Z_to_bv 8 (f a) :: fbytes f (a + 1) k'
  end.

Lemma fbytes_length : forall f k a, length (fbytes f a k) = k.
Proof. induction k as [|k IH]; intros a; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma fbytes_nth : forall f k a j, (j < k)%nat -> (forall i, a <= i < a + Z.of_nat k -> 0 <= f i < 256) ->
  bnth (fbytes f a k) j = f (a + Z.of_nat j).
Proof.
  induction k as [|k IH]; intros a j Hj Hf; [lia|].
  destruct j as [|j].
  - cbn [fbytes bnth nth]. unfold bnth. cbn [nth]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (2 ^ Z.of_N 8) with 256. rewrite Z.add_0_r. apply Z.mod_small. apply Hf. lia.
  - cbn [fbytes]. unfold bnth. cbn [nth]. fold (bnth (fbytes f (a + 1) k) j).
    rewrite IH by (try lia; intros i Hi; apply Hf; lia). f_equal. lia.
Qed.

Lemma bZ_fbytes_slice : forall (A : arr) ofs k,
  (forall i, ofs <= i < ofs + Z.of_nat k -> 0 <= arr_get A i < 256) ->
  bZ (fbytes (arr_get A) ofs k) = arr_slice_nat A ofs k.
Proof.
  intros A ofs k. revert ofs. induction k as [|k IH]; intros ofs Hf; [reflexivity|].
  cbn [fbytes arr_slice_nat bZ map]. unfold bZ in IH |- *. cbn [map]. f_equal.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. apply Hf. lia.
  - apply IH. intros i Hi. apply Hf. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma cells_ext : forall mem P st w n (f g : Z -> Z),
  (forall i, 0 <= i < n -> f i = g i) -> cells segs mem P st w n f -> cells segs mem P st w n g.
Proof. intros mem P st w n f g Hfg Hc i Hi. unfold cell. rewrite <- (Hfg i Hi). exact (Hc i Hi). Qed.

Lemma cells_rdn : forall mem P n f k a,
  cells segs mem P 1 1 n f -> 0 <= a -> a + Z.of_nat k <= n -> 0 <= P -> P + n <= 2 ^ 64 ->
  rdn segs mem (zw (P + a)) k = Some (fbytes f a k).
Proof.
  intros mem P n f k. induction k as [|k IH]; intros a Hc Ha Hak HP HPn; [reflexivity|].
  cbn [fbytes].
  change (rdn segs mem (zw (P + a)) (1 + k) = Some ([Z_to_bv 8 (f a)] ++ fbytes f (a + 1) k)).
  apply rdn_app.
  - pose proof (Hc a ltac:(lia)) as H1. unfold cell in H1. replace (P + 1 * a) with (P + a) in H1 by lia.
    exact H1.
  - change (nat_to_word 1) with (nat_to_word 1). rewrite <- (zw_add_nat (P + a) 1).
    change (Z.of_nat 1) with 1. replace (P + a + 1) with (P + (a + 1)) by lia.
    apply IH; try assumption; lia.
Qed.

Lemma cells_wbytes_bytes : forall mem P n f off (bs : list byte),
  cells segs mem P 1 1 n f -> 0 <= off -> off + Z.of_nat (length bs) <= n -> 0 <= P -> P + n <= 2 ^ 64 ->
  cells segs (wbytes mem (zw (P + off)) bs) P 1 1 n
        (fun i => if (off <=? i) && (i <? off + Z.of_nat (length bs)) then bnth bs (Z.to_nat (i - off)) else f i).
Proof.
  intros mem P n f off bs Hc Hoff Hlen HP HPn i Hi.
  destruct (Z.leb_spec off i), (Z.ltb_spec i (off + Z.of_nat (length bs))); cbn [andb].
  - unfold cell.
    pose proof (rdn_wbytes_hit segs bs mem (zw (P + off)) ltac:(rewrite u_zw_small by lia; lia)) as Hh.
    replace (P + 1 * i) with (P + off + Z.of_nat (Z.to_nat (i - off))) by lia.
    rewrite zw_add_nat, (rdn_nth segs _ _ _ _ (Z.to_nat (i - off)) Hh) by lia.
    unfold bnth, b0. cbn [Z_to_le_bytes]. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - apply cell_write_other; try lia. exact (Hc i Hi).
  - apply cell_write_other; try lia. exact (Hc i Hi).
  - lia.
Qed.

Lemma cells_filled0 : forall mem m' P n f a k,
  cells segs mem P 1 1 n f -> filled m' (P + a) (P + a + k) (ms_bb 0) -> same_outside mem m' (P + a) (P + a + k) ->
  0 <= a -> 0 <= k -> a + k <= n -> 0 <= P -> P + n <= 2 ^ 64 ->
  cells segs m' P 1 1 n (fun i => if (a <=? i) && (i <? a + k) then 0 else f i).
Proof.
  intros mem m' P n f a k Hc Hf Hs Ha Hk Hak HP HPn i Hi.
  unfold cell. cbn [rdn Z_to_le_bytes].
  destruct (Z.leb_spec a i), (Z.ltb_spec i (a + k)); cbn [andb].
  - rewrite (Hf (zw (P + 1 * i))) by (rewrite u_zw_small by lia; lia). reflexivity.
  - pose proof (Hc i Hi) as H1. unfold cell in H1. cbn [rdn Z_to_le_bytes] in H1.
    rewrite (Hs (zw (P + 1 * i))) by (rewrite u_zw_small by lia; lia). exact H1.
  - pose proof (Hc i Hi) as H1. unfold cell in H1. cbn [rdn Z_to_le_bytes] in H1.
    rewrite (Hs (zw (P + 1 * i))) by (rewrite u_zw_small by lia; lia). exact H1.
  - lia.
Qed.


Lemma cell_mod : forall mem a w v, cell segs mem a w (v mod 2 ^ (8 * Z.of_nat w)) <-> cell segs mem a w v.
Proof. intros mem a w v. unfold cell. rewrite SymExec.Z_to_le_bytes_mod. tauto. Qed.

Lemma Z_to_le_bytes_eqm : forall w u v, u mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) ->
  Z_to_le_bytes w u = Z_to_le_bytes w v.
Proof.
  intros w u v E. rewrite <- (SymExec.Z_to_le_bytes_mod w u), <- (SymExec.Z_to_le_bytes_mod w v), E. reflexivity.
Qed.

Lemma same_outside_agree_out : forall mem m' lo hi F,
  same_outside mem m' lo hi -> (forall x, lo <= x < hi -> in_franges F x) -> agree_out F mem m'.
Proof. intros mem m' lo hi F Hs HF x Hx. apply Hs. intros Hin. exact (Hx (HF _ Hin)). Qed.

Lemma cell_same_outside : forall mem m' lo hi a w v,
  cell segs mem a w v -> same_outside mem m' lo hi -> (a + Z.of_nat w <= lo \/ hi <= a) ->
  0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> cell segs m' a w v.
Proof.
  intros mem m' lo hi a w v Hc Hs Hd Ha Haw.
  apply (cell_agree_out segs [(lo, hi - lo)] mem m' a w v).
  - apply (same_outside_agree_out mem m' lo hi). exact Hs. intros x Hx. cbn. lia.
  - apply disj_franges_cons; [lia | apply disj_franges_nil].
  - exact Ha. - exact Haw. - exact Hc.
Qed.


Variables SL SD SB : Z.

Definition zst (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : Prop :=
  dsl_scalars segs SL SD SB mem S p ds
  /\ dsl_windowA segs mem p ds /\ dsl_prevA segs mem p ds /\ dsl_headA segs mem p ds
  /\ zsl_scalars segs mem (p_strm p) zp S (ds_strm ds)
  /\ zsl_input segs mem zp (ds_strm ds).

End WithSegs.


Definition apart (r1 r2 : Z * Z) : Prop := fst r1 + snd r1 <= fst r2 \/ fst r2 + snd r2 <= fst r1.

Fixpoint apart_from (r : Z * Z) (l : list (Z * Z)) : Prop :=
  match l with [] => True | r' :: l' => apart r r' /\ apart_from r l' end.

Fixpoint apart_all (l : list (Z * Z)) : Prop :=
  match l with [] => True | r :: l' => apart_from r l' /\ apart_all l' end.

Lemma apart_from_nth : forall r l j d, apart_from r l -> (j < length l)%nat -> apart r (nth j l d).
Proof.
  intros r l. induction l as [|r' l IH]; intros j d H Hj; [cbn in Hj; lia|].
  destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn. apply IH; [exact H2|]. cbn in Hj. lia.
Qed.

Lemma apart_get : forall l i j d, apart_all l -> (i < j)%nat -> (j < length l)%nat ->
  apart (nth i l d) (nth j l d).
Proof.
  intros l. induction l as [|r l IH]; intros i j d H Hij Hj; [cbn in Hj; lia|].
  destruct H as [H1 H2]. destruct i as [|i].
  - destruct j as [|j]; [lia|]. cbn. apply apart_from_nth; [exact H1|]. cbn in Hj. lia.
  - destruct j as [|j]; [lia|]. cbn. apply IH; [exact H2| lia |]. cbn in Hj. lia.
Qed.


Section Pre.
Variable segs : list Segment.
Variables SL SD SB : Z.

Definition fw_regions (FR S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : list (Z * Z) :=
  [(sp - FR, FR); (S, dsl_SIZE); (p_window p, 2 * ds_w_size ds); (p_prev p, 2 * ds_w_size ds);
   (p_head p, 2 * ds_hash_size ds); (p_strm p, zsl_SIZE); (zp_in zp, arr_len (cs_input (ds_strm ds)))].

Record fw_pre (FR : Z) (mem : word -> option byte) (S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : Prop := FWPRE {
  fp_zst  : zst segs SL SD SB mem S p zp ds;
  fp_wf   : fw_wf (ds_w_size ds) (ds_hash_size ds) ds;
  fp_look : ds_lookahead ds < MIN_LOOKAHEAD;
  fp_map  : mapped mem (sp - FR) FR;
  fp_mapS : mapped mem S dsl_SIZE;
  fp_mapW : mapped mem (p_window p) (2 * ds_w_size ds);
  fp_mapP : mapped mem (p_prev p) (2 * ds_w_size ds);
  fp_mapH : mapped mem (p_head p) (2 * ds_hash_size ds);
  fp_mapZ : mapped mem (p_strm p) zsl_SIZE;
  fp_sp   : FR <= sp <= 2 ^ 63;
  fp_S    : 0 <= S /\ S + dsl_SIZE <= 2 ^ 63;
  fp_W    : 0 < p_window p /\ p_window p + 2 * ds_w_size ds <= 2 ^ 63;
  fp_PV   : 0 <= p_prev p /\ p_prev p + 2 * ds_w_size ds <= 2 ^ 63;
  fp_HD   : 0 <= p_head p /\ p_head p + 2 * ds_hash_size ds <= 2 ^ 63;
  fp_strm : 0 <= p_strm p /\ p_strm p + zsl_SIZE <= 2 ^ 63;
  fp_IN   : 0 <= zp_in zp /\ zp_in zp + arr_len (cs_input (ds_strm ds)) < 2 ^ 63;
  fp_apart : apart_all (fw_regions FR S sp p zp ds)
}.
End Pre.


Definition fam (w h pv inp : arr) : nat -> Z -> Z :=
  fun f => match f with 0%nat => wb w | 1%nat => pb h | 2%nat => pb pv | _ => wb inp end.

End FXG.
Ltac fam_bounds := cbn [fam]; intros; first [apply wb_range | apply pb_range].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac open_fwpre HFW :=
  pose proof (fp_sp _ _ _ _ _ _ _ _ _ _ _ HFW) as Lsp;
  pose proof (fp_S _ _ _ _ _ _ _ _ _ _ _ HFW) as LS;
  pose proof (fp_W _ _ _ _ _ _ _ _ _ _ _ HFW) as LW;
  pose proof (fp_PV _ _ _ _ _ _ _ _ _ _ _ HFW) as LPV;
  pose proof (fp_HD _ _ _ _ _ _ _ _ _ _ _ HFW) as LHD;
  pose proof (fp_strm _ _ _ _ _ _ _ _ _ _ _ HFW) as Lstrm;
  pose proof (fp_IN _ _ _ _ _ _ _ _ _ _ _ HFW) as LIN;
  pose proof (wf_wsr _ _ _ (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW)) as Lws;
  pose proof (wf_hsr _ _ _ (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW)) as Lhs;
  pose proof (wf_ni _ _ _ (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW)) as Lni0;
  pose proof (wf_ai _ _ _ (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW)) as Lai0;
  pose proof (wf_inlen _ _ _ (fp_wf _ _ _ _ _ _ _ _ _ _ _ HFW)) as Lil0;
  unfold dsl_SIZE, zsl_SIZE in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac apart_of HFW i j :=
  let H := fresh "AP" in
  pose proof (apart_get _ i j (0, 0) (fp_apart _ _ _ _ _ _ _ _ _ _ _ HFW)
                ltac:(lia) ltac:(cbn; lia)) as H;
  cbn [nth fw_regions] in H; unfold apart in H; cbn [fst snd] in H; unfold dsl_SIZE, zsl_SIZE in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac open_wf H :=
  pose proof (wf_ws _ _ _ H) as Vws; pose proof (wf_wl _ _ _ H) as Vwl; pose proof (wf_wsz _ _ _ H) as Vwsz;
  pose proof (wf_pl _ _ _ H) as Vpl; pose proof (wf_wmask _ _ _ H) as Vwmask; pose proof (wf_hs _ _ _ H) as Vhs;
  pose proof (wf_hl _ _ _ H) as Vhl; pose proof (wf_hmask _ _ _ H) as Vhmask; pose proof (wf_hshift _ _ _ H) as Vhshift;
  pose proof (wf_ins _ _ _ H) as Vins; pose proof (wf_look _ _ _ H) as Vlook; pose proof (wf_sl _ _ _ H) as Vsl;
  pose proof (wf_ms _ _ _ H) as Vms; pose proof (wf_ih _ _ _ H) as Vih; pose proof (wf_hw _ _ _ H) as Vhw;
  pose proof (wf_ni _ _ _ H) as Vni; pose proof (wf_ai _ _ _ H) as Vai; pose proof (wf_inlen _ _ _ H) as Vinlen;
  pose proof (wf_ti _ _ _ H) as Vti; pose proof (wf_wrap _ _ _ H) as Vwrap.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac cellS Hz acc name :=
  pose proof (acc _ _ _ _ _ _ _ _ (proj1 Hz)) as name.
