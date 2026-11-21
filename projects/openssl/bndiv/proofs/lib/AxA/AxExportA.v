(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry block and [eb_facts] take the CONFIG_RSEQ flag; [ex_argv_rep] reads the new block layout, strings at the stack top, through BootLayout and AsanWEb in place of P/InitMem, with the USTACK_TOP - 9 string bound). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Mem Arr ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require RzCPS.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require BootLayout.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require AsanWEntry AsanWEb.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import RT_iface D_defs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxAcct AxMeasure AxLz AxEntryRel AxFd AxModelRel.
From OSSVerify.Proofs.openssl.bndiv.lib.AxA Require Import AxExport AxExportH AxExportV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Lemma dec_argvB_eq (r0 : bool) (ρ : valuation) : eb_facts r0 ρ -> dec_argvB ρ = dec_argv ρ.
Proof.
  intros (Hc & _ & Hl & _). unfold dec_argvB, dec_argv, dec_strs. rewrite Z.mod_small by lia.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. destruct (Hl (Z.of_nat k) ltac:(lia)) as [Hlen _].
  unfold dec_str. replace ((0 <=? Z.of_nat k) && (Z.of_nat k <? 1048576))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma extract_byte_eq' : forall (v : word) (k : N),
  bv_extract k 8 v = Z_to_bv 8 (Z.shiftr (bv_unsigned v) (Z.of_N k)).
Proof. intros v k. apply bv_eq. rewrite bv_extract_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

(** the model's little-endian word bytes are the runtime's [le8] (as in P/InitMem.v) *)
Lemma word_le8_le8' : forall v : word, word_le8 v = le8 v.
Proof.
  intros v. unfold word_le8, le8, word_to_le_bytes. cbn [Z_to_le_bytes].
  rewrite !extract_byte_eq'. rewrite !Z.shiftr_shiftr by lia. cbn [Z.of_N Z.add].
  rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma flat_map_word_le8' : forall ws, flat_map word_le8 ws = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [flat_map u64s]. rewrite word_le8_le8', IH. reflexivity. Qed.

Lemma length_word_le8' : forall v : word, length (word_le8 v) = 8%nat.
Proof. reflexivity. Qed.

Lemma bytes_at_slice' (segs : list Segment) (m : word -> option byte) (a : Z) (bs : list byte) (off k : nat) :
  bytes_at segs m a bs -> (off + k <= length bs)%nat -> bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros H Hk. rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Section Argv.
Hypothesis Hlow : segs_low asegs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R asegs amodel (MR asegs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.
Variable X : list (Z * Z).

Local Notation AFx := (AF ρ W J X).
Local Notation m := (AxExport.mX ms model AFx).
Let HM : MR asegs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.

Hypothesis Hent : existsb is_entry (a_mem B) = true.
(* [comment removed for export] *)
Hypothesis Hat : alloc_top (m_vmmaps model) <= sp_val ρ.

Local Notation usp := (sp_val ρ).
Local Notation spw := (Z_to_bv 64 (sp_val ρ)).
Local Notation argv := (dec_argv ρ).
Local Notation envp := (dec_envp ρ).
Local Notation uid := (Z_to_bv 64 (ρ v_uid)).
Local Notation hw := (Z_to_bv 64 (ρ v_hw)).

(** the entry region: the block the valuation describes, at sp, for the launch's rseq flag [r0] *)
Lemma entry_block : exists r0 ph, eb_facts r0 ρ
  /\ forall z, 0 <= z < Z.of_nat (length (eb_image r0 ph ρ)) ->
       ms_mem ms (Z_to_bv 64 (usp + z)) = Some (nth (Z.to_nat z) (eb_image r0 ph ρ) (Z_to_bv 8 0)).
Proof.
  apply existsb_exists in Hent as [Rq [HIn He]]. pose proof (r_mem _ _ _ _ _ _ _ HR) as [_ HF]. cbn [cfg_ms] in HF.
  pose proof (proj1 (Forall_forall _ _) HF Rq HIn) as HRq. unfold RRegion in HRq. unfold is_entry in He.
  destruct (rg_kind Rq) as [| | | | r0 ph]; try discriminate He. exists r0, ph. destruct HRq as (Hf & Hb & _ & Hm). split; [exact Hf|].
  intros z Hz. rewrite Hb in Hm. exact (Hm z Hz).
Qed.

Lemma eb_sp (r0 : bool) (ph : PhdrInfo) : eb_facts r0 ρ -> bv_unsigned spw = usp /\ sp_window_lo <= usp.
Proof.
  intros Hf. pose proof (AsanWEb.facts_win r0 ph ρ Hf) as [Hs1 _]. split; [|exact Hs1].
  exact (AsanWEb.u_sp r0 ph ρ Hf).
Qed.

(* [comment removed for export] *)
Lemma high_vis (z : Z) : 0 <= usp -> usp <= z < 2 ^ 47 -> RzCPS.HID AFx model (wz z) = false.
Proof.
  intros H0 Hz. apply (not_in_entries_vis asegs fs0 LIM ρ B ms model HR W J X z); [lia|].
  intros e He _ Hin.
  pose proof (mr_top asegs fs0 ρ _ model HM (ent_val ρ e) (MR_ent_in asegs fs0 ρ _ model e HM He)) as Ht.
  pose proof (MR_ent asegs fs0 ρ _ model e HM He) as Hok.
  rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok) in Ht. unfold ent_lo, ent_hi in Hin. lia.
Qed.

Lemma nth_error_firstn_some {T : Type} (k : nat) (l : list T) (i : nat) (x : T) : nth_error (firstn k l) i = Some x -> nth_error l i = Some x.
Proof.
  revert l i. induction k as [|k IH]; intros l i H; [destruct i; discriminate H|].
  destruct l as [|y r]; [destruct i; discriminate H|]. destruct i as [|i]; cbn [firstn nth_error] in *; [exact H | exact (IH r i H)].
Qed.

Lemma argc_len (r0 : bool) : eb_facts r0 ρ -> Z.of_nat (length (dec_argvB ρ)) = ρ v_argc.
Proof.
  intros Hf. rewrite (dec_argvB_eq r0 ρ Hf). destruct Hf as (Hc & _). unfold dec_argv, dec_strs. rewrite length_map, length_seq. lia.
Qed.

(** argv for the runtime: the pointer vector at sp + 8 and the first two strings, which at LPS 08b1429
    sit at the TOP of the block (argv strings, envp strings, the execfn and its NUL, 8 zero bytes, the
    stack top).  A string therefore ends at most 9 bytes below the top and its slack, up to the next
    8-byte boundary, at most 8 below it: hence the [USTACK_TOP - 9] string bound and the
    [USTACK_TOP - 8] slack bound of [argv_rep].  The two differ by one and must: [region_in_mem]
    (A/I_consts.v:41-42) asks [b + n + 8 <= kHighMemEnd] and [kHighMemEnd = USTACK_TOP - 1]
    (A/R_m2s.v:17, A/RT_iface.v:27), so a string end at [USTACK_TOP - 8] is exactly one byte too
    high for it.  This sentence was already right while the code said [- 8] in both places. *)
Theorem ex_argv_rep : argv_rep (dec_argvB ρ) m (usp + 8).
Proof.
  destruct entry_block as (r0 & ph & Hf & Hm). rewrite (dec_argvB_eq r0 ρ Hf).
  pose proof (AsanWEb.facts_win r0 ph ρ Hf) as [Hlo Htop].
  pose proof (AsanWEb.facts_top8 r0 ph ρ Hf) as Htop8.
  pose proof (AsanWEb.facts_argc r0 ph ρ Hf) as Hac.
  pose proof (AsanWEb.facts_envc r0 ph ρ Hf) as Hec.
  pose proof (AsanWEb.facts_g r0 ph ρ Hf) as Hg.
  pose proof (AsanWEb.facts_par r0 ph ρ Hf) as Hpar.
  pose proof (AsanWEb.facts_xl r0 ph ρ Hf) as Hxl.
  pose proof (AsanWEb.len_av r0 ph ρ Hf) as Lav.
  pose proof (AsanWEb.tab_av r0 ph ρ Hf) as Tav.
  pose proof (AsanWEb.tab_ev r0 ph ρ Hf) as Tev.
  pose proof (AsanWEb.u_sp r0 ph ρ Hf) as Eu.
  pose proof (AsanWEb.R7_length r0 ph ρ Hf) as HL.
  pose proof (AsanWEb.HSPAD r0 ph ρ Hf) as HHP.
  pose proof (AsanWEb.str_base_eq r0 ph ρ Hf) as Esb.
  pose proof (AsanWEb.B_eq r0 ph ρ Hf) as EB.
  cbn [dec_la la_rseq] in *.
  pose proof (Nat2Z.is_nonneg (AsanWEntry.tab envp)) as Te0.
  unfold dec_top, str_off in Htop, Htop8.
  unfold sp_window_lo, sp_window_hi in Hlo, Htop.
  set (SO := 24 + Z.of_nat (auxv_size r0) + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g) in *.
  set (img := eb_image r0 ph ρ) in *.
  set (LB := Z.of_nat (length img)) in *.
  assert (HSO : 24 + 8 * ρ v_argc + 8 * ρ v_envc + 16 <= SO) by (unfold SO; lia).
  assert (Hend : usp + LB = sp_val ρ + SO + ρ v_ta + ρ v_te + ρ v_xl + 1 + 8) by lia.
  assert (Hmz : forall z, 0 <= z < LB -> m (wz (usp + z)) = Some (nth (Z.to_nat z) img (Z_to_bv 8 0))).
  { intros z Hz. unfold AxExport.mX, mrestrict. rewrite (high_vis (usp + z) ltac:(lia) ltac:(lia)). exact (Hm z Hz). }
  assert (BX : bytes_at asegs m usp img).
  { unfold bytes_at. split; [lia|]. split; [fold LB; lia|]. intros i Hi. unfold mrd. change (wa (usp + Z.of_nat i)) with (wz (usp + Z.of_nat i)).
    rewrite (Hmz (Z.of_nat i) ltac:(unfold LB; lia)), Nat2Z.id. symmetry. apply nth_error_nth'. exact Hi. }
  assert (WX : forall a n, usp <= a -> 0 <= n -> a + n <= usp + LB -> wr_at asegs m a n).
  { intros a n H1 H2 H3. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. unfold wview. change (wa (a + i)) with (wz (a + i)).
    replace (a + i) with (usp + (a + i - usp)) by lia. rewrite (Hmz (a + i - usp) ltac:(lia)). discriminate. }
  set (topw := Z_to_bv 64 (dec_top r0 ρ)).
  set (P := BootLayout.argv_ptrs topw argv envp (dec_execfn ρ)).
  set (k := Nat.min 2 (length argv)).
  assert (PL : length P = length argv) by (unfold P; apply BootLayout.length_argv_ptrs).
  assert (Hk : (k <= length P)%nat) by (rewrite PL; unfold k; lia).
  assert (Hlen : length (firstn k P) = k) by (rewrite length_firstn; lia).
  (* the pointer slots: the bytes right after argc *)
  assert (BP : bytes_at asegs m (usp + 8) (u64s (firstn k P))).
  { pose proof BX as BX'. rewrite EB, AsanWEntry.B_split in BX'. unfold BootLayout.struct_prefix in BX'.
    fold topw in BX'. fold P in BX'. rewrite <- (firstn_skipn k P) in BX'. rewrite flat_map_app, <- !app_assoc in BX'.
    apply bytes_at_app in BX' as [_ BX']. apply bytes_at_app in BX' as [BX' _].
    rewrite length_word_le8' in BX'. rewrite <- flat_map_word_le8'. exact BX'. }
  (* where the k-th argv string sits *)
  assert (Hp : forall i, (i < length argv)%nat ->
            nth i P (Z_to_bv 64 0) = Z_to_bv 64 (usp + SO + Z.of_nat (AsanWEntry.pre i argv))).
  { intros i Hi. unfold P. rewrite BootLayout.argv_ptr_eq by exact Hi. fold topw in Esb. rewrite Esb.
    unfold nat_to_word. rewrite AsanWEb.zadd. reflexivity. }
  assert (Hstr : forall i s p, nth_error argv i = Some s -> nth_error (firstn k P) i = Some p ->
               bv_unsigned p = usp + SO + Z.of_nat (AsanWEntry.pre i argv)
               /\ usp + SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat (length s) + 1 <= usp + SO + ρ v_ta
               /\ bytes_at asegs m (bv_unsigned p) (s ++ [Z_to_bv 8 0])).
  { intros i s p Hs Hpi. apply nth_error_firstn_some in Hpi.
    assert (Hi : (i < length argv)%nat) by (apply nth_error_Some; congruence).
    assert (Es : s = nth i argv []) by (symmetry; apply nth_error_nth; exact Hs).
    assert (Ep : p = nth i P (Z_to_bv 64 0)) by (symmetry; apply nth_error_nth; exact Hpi).
    (* [pre_le_tab] closes over the whole Block section ("Proof Using All"): pass the block's own arguments *)
    pose proof (AsanWEntry.pre_le_tab (dec_la r0 ρ) ph (Z_to_bv 64 (ρ v_ent)) spw topw argv envp (dec_execfn ρ)
                  uid (Z_to_bv 64 (ρ v_gid)) hw (dec_draw r0 ρ) argv i (length s) Hi ltac:(rewrite Es; lia)) as Hpt.
    assert (Hpu : bv_unsigned p = usp + SO + Z.of_nat (AsanWEntry.pre i argv)).
    { rewrite Ep, (Hp i Hi), Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    split; [exact Hpu|]. split; [lia|].
    rewrite Hpu. unfold bytes_at. split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. unfold mrd.
    replace (usp + SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat j) with (usp + (SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat j)) by lia.
    change (wa (usp + (SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat j))) with (wz (usp + (SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat j))).
    rewrite (Hmz (SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat j) ltac:(lia)).
    rewrite (nth_error_nth' (s ++ [Z_to_bv 8 0]) (n := j) (Z_to_bv 8 0) ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
    replace (Z.to_nat (SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat j))
      with (block_head_size r0 argv envp + block_pad_len r0 (Z_to_bv 64 (sp_val ρ)) topw argv envp (dec_execfn ρ)
            + AsanWEntry.pre i argv + j)%nat by (fold topw in HHP; lia).
    rewrite EB. rewrite Es. apply (AsanWEntry.E5_argv_str (dec_la r0 ρ)); [exact Hi | rewrite <- Es; lia]. }
  exists (firstn k P). split; [|split; [exact Hlen|]].
  - unfold u64arr. split; [exact BP|]. apply WX; [lia | lia |]. rewrite Hlen. unfold k. lia.
  - split.
    + intros i s p Hs Hpi. destruct (Hstr i s p Hs Hpi) as (Hpu & Hpe & Bp). split; [exact Bp|].
      rewrite Hpu. unfold USTACK_TOP. split; lia.
    + intros i s p Hs Hpi. destruct (Hstr i s p Hs Hpi) as (Hpu & Hpe & _). rewrite Hpu.
      set (q := usp + SO + Z.of_nat (AsanWEntry.pre i argv) + Z.of_nat (length s) + 1).
      set (rq := (- q) mod 8).
      assert (Hr : 0 <= rq < 8) by (unfold rq; apply Z.mod_pos_bound; lia).
      (* the block ends at the 8-aligned stack top, 9 or more bytes past the string's NUL *)
      assert (Hq8 : q + rq <= usp + LB - 8).
      { assert (BE8 : (usp + LB - 8) mod 8 = 0).
        { replace (usp + LB - 8) with (sp_val ρ + SO + ρ v_ta + ρ v_te + ρ v_xl + 1 + 8 + (-1) * 8) by lia.
          rewrite Z_mod_plus_full. exact Htop8. }
        assert (Hqe : q <= usp + LB - 9) by (unfold q; lia).
        unfold rq. clear - BE8 Hqe. Z.div_mod_to_equations. lia. }
      exists (firstn (Z.to_nat rq) (skipn (Z.to_nat (q - usp)) img)).
      assert (Hsl : length (firstn (Z.to_nat rq) (skipn (Z.to_nat (q - usp)) img)) = Z.to_nat rq).
      { rewrite length_firstn, length_skipn. unfold LB in Hq8. unfold q in *. lia. }
      split; [|split; [rewrite Hsl; fold q; fold rq; lia | rewrite Hsl; fold q; unfold USTACK_TOP; lia]].
      pose proof (bytes_at_slice' asegs m usp img (Z.to_nat (q - usp)) (Z.to_nat rq) BX ltac:(unfold LB in Hq8; unfold q in *; lia)) as S.
      replace (usp + Z.of_nat (Z.to_nat (q - usp))) with q in S by (unfold q; lia). exact S.
Qed.

End Argv.
