(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require InitMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxAcct AxMeasure AxLz AxEntryRel AxFd AxModelRel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AxA Require Import AxExport AxExportH AxExportV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Lemma dec_argvB_eq (ρ : valuation) : eb_facts ρ -> dec_argvB ρ = dec_argv ρ.
Proof.
  intros (Hc & _ & Hl & _). unfold dec_argvB, dec_argv, dec_strs. rewrite Z.mod_small by lia.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. destruct (Hl (Z.of_nat k) ltac:(lia)) as [Hlen _].
  unfold dec_str. replace ((0 <=? Z.of_nat k) && (Z.of_nat k <? 1048576))%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma bytes_at_slice' (segs : list Segment) (m : word -> option byte) (a : Z) (bs : list byte) (off k : nat) :
  bytes_at segs m a bs -> (off + k <= length bs)%nat -> bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros H Hk. rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Section Argv.
Hypothesis Hlow : segs_low ctasegs.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R ctasegs amodel (MR ctasegs fs0 ρ) LIM ρ B (mkCfg ms model).
Variable W : list (lin * Z).
Variable J : Z.
Variable X : list (Z * Z).

Local Notation AFx := (AF ρ W J X).
Local Notation m := (AxExport.mX ms model AFx).
Let HM : MR ctasegs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.

Hypothesis Hent : existsb is_entry (a_mem B) = true.
(* [comment removed for export] *)
Hypothesis Hat : alloc_top (m_vmmaps model) <= sp_val ρ.

Local Notation usp := (sp_val ρ).
Local Notation spw := (Z_to_bv 64 (sp_val ρ)).
Local Notation argv := (dec_argv ρ).
Local Notation envp := (dec_envp ρ).
Local Notation uid := (Z_to_bv 64 (ρ v_uid)).
Local Notation hw := (Z_to_bv 64 (ρ v_hw)).

(* [comment removed for export] *)
Lemma entry_block : exists ph, eb_facts ρ
  /\ forall z, 0 <= z < Z.of_nat (length (build_stack_bytes ph spw argv envp uid hw (dec_draw ρ))) ->
       ms_mem ms (Z_to_bv 64 (usp + z)) = Some (nth (Z.to_nat z) (build_stack_bytes ph spw argv envp uid hw (dec_draw ρ)) (Z_to_bv 8 0)).
Proof.
  apply existsb_exists in Hent as [Rq [HIn He]]. pose proof (r_mem _ _ _ _ _ _ _ HR) as [_ HF]. cbn [cfg_ms] in HF.
  pose proof (proj1 (Forall_forall _ _) HF Rq HIn) as HRq. unfold RRegion in HRq. unfold is_entry in He.
  destruct (rg_kind Rq) as [| | | |ph]; try discriminate He. exists ph. destruct HRq as (Hf & Hb & _ & Hm). split; [exact Hf|].
  intros z Hz. rewrite Hb in Hm. exact (Hm z Hz).
Qed.

Lemma eb_sp : eb_facts ρ -> bv_unsigned spw = usp /\ sp_window_lo <= usp.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hs2). split; [|exact Hs1].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold sp_window_lo, sp_window_hi in *.
  pose proof (Zle_0_nat (length (eb_image (mkPhdrInfo 0 0 0) ρ))). lia.
Qed.

(* [comment removed for export] *)
Lemma high_vis (z : Z) : 0 <= usp -> usp <= z < 2 ^ 47 -> RzCPS.HID AFx model (wz z) = false.
Proof.
  intros H0 Hz. apply (not_in_entries_vis ctasegs fs0 LIM ρ B ms model HR W J X z); [lia|].
  intros e He _ Hin.
  pose proof (mr_top ctasegs fs0 ρ _ model HM (ent_val ρ e) (MR_ent_in ctasegs fs0 ρ _ model e HM He)) as Ht.
  pose proof (MR_ent ctasegs fs0 ρ _ model e HM He) as Hok.
  rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok) in Ht. unfold ent_lo, ent_hi in Hin. lia.
Qed.

Lemma nth_error_firstn_some {T : Type} (k : nat) (l : list T) (i : nat) (x : T) : nth_error (firstn k l) i = Some x -> nth_error l i = Some x.
Proof.
  revert l i. induction k as [|k IH]; intros l i H; [destruct i; discriminate H|].
  destruct l as [|y r]; [destruct i; discriminate H|]. destruct i as [|i]; cbn [firstn nth_error] in *; [exact H | exact (IH r i H)].
Qed.

Lemma argc_len : eb_facts ρ -> Z.of_nat (length (dec_argvB ρ)) = ρ v_argc.
Proof.
  intros Hf. rewrite (dec_argvB_eq ρ Hf). destruct Hf as (Hc & _). unfold dec_argv, dec_strs. rewrite length_map, length_seq. lia.
Qed.

(* [comment removed for export] *)
Theorem ex_argv_rep : argv_rep (dec_argvB ρ) m (usp + 8).
Proof.
  destruct entry_block as (ph & Hf & Hm). destruct (eb_sp Hf) as [Eu Hlo]. rewrite (dec_argvB_eq ρ Hf).
  pose proof (InitMem.build_stack_bytes_length ph spw argv envp uid hw (dec_draw ρ)) as HL.
  pose proof (InitMem.build_stack_bytes_length (mkPhdrInfo 0 0 0) spw argv envp uid hw (dec_draw ρ)) as HL0.
  assert (Hhi : usp + Z.of_nat (length (build_stack_bytes ph spw argv envp uid hw (dec_draw ρ))) <= 2 ^ 47).
  { destruct Hf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs2). unfold eb_image in Hs2. unfold sp_window_hi in Hs2. rewrite HL. rewrite HL0 in Hs2.
    change (2 ^ 47) with 140737488355328. lia. }
  set (img := build_stack_bytes ph spw argv envp uid hw (dec_draw ρ)) in *.
  set (LB := Z.of_nat (length img)) in *.
  unfold sp_window_lo in Hlo.
  assert (Hmz : forall z, 0 <= z < LB -> m (wz (usp + z)) = Some (nth (Z.to_nat z) img (Z_to_bv 8 0))).
  { intros z Hz. unfold AxExport.mX, mrestrict. rewrite (high_vis (usp + z) ltac:(lia) ltac:(lia)). exact (Hm z Hz). }
  assert (BX : bytes_at ctasegs m usp img).
  { unfold bytes_at. split; [lia|]. split; [fold LB; lia|]. intros i Hi. unfold mrd. change (wa (usp + Z.of_nat i)) with (wz (usp + Z.of_nat i)).
    rewrite (Hmz (Z.of_nat i) ltac:(unfold LB; lia)), Nat2Z.id. symmetry. apply nth_error_nth'. exact Hi. }
  assert (WX : forall a n, usp <= a -> 0 <= n -> a + n <= usp + LB -> wr_at ctasegs m a n).
  { intros a n H1 H2 H3. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. unfold wview. change (wa (a + i)) with (wz (a + i)).
    replace (a + i) with (usp + (a + i - usp)) by lia. rewrite (Hmz (a + i - usp) ltac:(lia)). discriminate. }
  assert (SPLO : stack_max_size <= bv_unsigned spw) by (rewrite Eu; unfold stack_max_size; lia).
  assert (IMGHI : bv_unsigned spw + Z.of_nat (length (build_stack_bytes ph spw argv envp uid hw (dec_draw ρ))) <= 2 ^ 64) by (rewrite Eu; fold img; fold LB; lia).
  pose proof (InitMem.init_stack_bytes ctasegs ph spw argv envp uid hw (dec_draw ρ) SPLO IMGHI) as B0. rewrite Eu in B0. fold img in B0.
  (* [comment removed for export] *)
  assert (xfer : forall a bs, bytes_at ctasegs (OssFuzzTheorems.Proofs.openssl.ct.lib.Common.PropExec.wrap_mem ph spw argv envp uid hw (dec_draw ρ)) a bs -> usp <= a ->
                   a + Z.of_nat (length bs) <= usp + LB -> bytes_at ctasegs m a bs).
  { intros a bs (F1 & F2 & F3) H1 H2. split; [lia|]. split; [lia|]. intros i Hi. rewrite <- (F3 i Hi).
    destruct B0 as (_ & _ & G0). destruct BX as (_ & _ & GX).
    replace (a + Z.of_nat i) with (usp + Z.of_nat (Z.to_nat (a - usp) + i)) by lia.
    rewrite (G0 (Z.to_nat (a - usp) + i)%nat ltac:(unfold LB in H2; lia)), (GX (Z.to_nat (a - usp) + i)%nat ltac:(unfold LB in H2; lia)). reflexivity. }
  destruct (InitMem.init_pieces ctasegs ph spw argv envp uid hw (dec_draw ρ) SPLO IMGHI) as (_ & P2 & _). rewrite Eu in P2.
  pose proof (InitMem.raw_len_nonneg ph spw argv envp uid hw (dec_draw ρ)) as (RN1 & RN2 & RN3 & RN4).
  pose proof (InitMem.argv_ptrs_length spw argv envp) as PL.
  assert (Ess : InitMem.struct_size argv envp = 8 * (Z.of_nat (length argv) + Z.of_nat (length envp)) + 184) by reflexivity.
  assert (Esb : InitMem.str_base spw argv envp = usp + InitMem.struct_size argv envp) by (unfold InitMem.str_base; rewrite Eu; reflexivity).
  assert (Eeb : InitMem.env_base spw argv envp = InitMem.str_base spw argv envp + total_arg_bytes argv) by reflexivity.
  assert (Erl : InitMem.raw_len argv envp = InitMem.struct_size argv envp + total_arg_bytes argv + total_arg_bytes envp) by reflexivity.
  set (k := Nat.min 2 (length argv)).
  exists (firstn k (InitMem.argv_ptrs spw argv envp)).
  assert (Hk : (k <= length (InitMem.argv_ptrs spw argv envp))%nat) by (rewrite PL; unfold k; lia).
  assert (Hlen : length (firstn k (InitMem.argv_ptrs spw argv envp)) = k) by (rewrite firstn_length; lia).
  split; [|split; [exact Hlen|]].
  - unfold u64arr. split.
    + rewrite <- (firstn_skipn k (InitMem.argv_ptrs spw argv envp)) in P2. rewrite <- app_assoc, u64s_app in P2.
      apply xfer in P2; [|lia|].
      * apply bytes_at_app in P2. exact (proj1 P2).
      * rewrite <- u64s_app, u64s_length, length_app, length_app, firstn_length, skipn_length. cbn [length]. lia.
    + apply WX; [lia | lia |]. rewrite Hlen. unfold k. lia.
  - assert (Hstr : forall i s p, nth_error argv i = Some s -> nth_error (firstn k (InitMem.argv_ptrs spw argv envp)) i = Some p ->
               exists p', p = Z_to_bv 64 p' /\ bv_unsigned p = p' /\ InitMem.str_base spw argv envp <= p'
                          /\ p' + Z.of_nat (length s) + 1 <= InitMem.env_base spw argv envp /\ bytes_at ctasegs m p' (s ++ [Z_to_bv 8 0])).
    { intros i s p Hs Hp. apply nth_error_firstn_some in Hp.
      destruct (InitMem.init_argv_string ctasegs ph spw argv envp uid hw (dec_draw ρ) SPLO IMGHI i s Hs) as (p' & Np & H1 & H2 & Bp).
      rewrite Np in Hp. injection Hp as <-. exists p'. split; [reflexivity|].
      split; [rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia|].
      split; [exact H1|]. split; [exact H2|]. apply xfer; [exact Bp | lia |]. rewrite length_app. cbn [length]. lia. }
    split.
    + intros i s p Hs Hp. destruct (Hstr i s p Hs Hp) as (p' & -> & Ep & H1 & H2 & Bp). rewrite Ep.
      split; [exact Bp|]. split; [lia|]. unfold USTACK_TOP. lia.
    + intros i s p Hs Hp. destruct (Hstr i s p Hs Hp) as (p' & -> & Ep & H1 & H2 & Bp). rewrite Ep.
      set (q := p' + Z.of_nat (length s) + 1). set (r := (- q) mod 8).
      assert (Hr : 0 <= r < 8) by (unfold r; apply Z.mod_pos_bound; lia).
      assert (Hal : usp mod 8 = 0).
      { unfold sp_val, sp_terms. cbn [teval]. rewrite Z.add_0_r.
        replace (16 * ρ v_x0 + (64 * ρ v_x1 + (4096 * ρ v_x2 + 32768 * ρ v_x3))) with ((2 * ρ v_x0 + 8 * ρ v_x1 + 512 * ρ v_x2 + 4096 * ρ v_x3) * 8) by lia.
        apply Z_mod_mult. }
      assert (Hend : q + r <= usp + LB - 16).
      { assert (BE8 : (usp + LB - 16) mod 8 = 0).
        { rewrite HL. unfold InitMem.pad_len. clear - Hal. Z.div_mod_to_equations. lia. }
        assert (Hqe : q <= usp + LB - 16) by (unfold q; lia).
        unfold r. clear - BE8 Hqe. Z.div_mod_to_equations. lia. }
      exists (firstn (Z.to_nat r) (skipn (Z.to_nat (q - usp)) img)).
      assert (Hsl : length (firstn (Z.to_nat r) (skipn (Z.to_nat (q - usp)) img)) = Z.to_nat r).
      { rewrite firstn_length, skipn_length. unfold LB in Hend. unfold q in *. lia. }
      split; [|split; [rewrite Hsl; fold q; fold r; lia | rewrite Hsl; fold q; unfold USTACK_TOP; lia]].
      pose proof (bytes_at_slice' ctasegs m usp img (Z.to_nat (q - usp)) (Z.to_nat r) BX ltac:(unfold LB in Hend; unfold q in *; lia)) as S.
      replace (usp + Z.of_nat (Z.to_nat (q - usp))) with q in S by (unfold q; lia). exact S.
Qed.

End Argv.
