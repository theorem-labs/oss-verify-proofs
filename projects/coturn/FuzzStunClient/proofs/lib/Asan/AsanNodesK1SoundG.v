(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanNodesPG AsanNodesPGSoundG AsanNodesK1 AsanClzArith AsanWordLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition clz_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (x L : Z) (v : word) (regs : bvmap 5 word),
    1 <= x < 2 ^ 64 -> 0 <= L /\ L + 56 <= 2 ^ 64 ->
    rdn SEGS mem (Z_to_bv 64 (L + 48)) 8 = Some (word_to_le_bytes 8 v) ->
    getr regs 18%bv = Z_to_bv 64 x -> getr regs 9%bv = Z_to_bv 64 L ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (K1N.CLZ_ENTRY T)) mem rom) (mkst regs' (Z_to_bv 64 (K1N.CLZ_EXIT T)) mem rom)
      /\ getr regs' 19%bv = Z_to_bv 64 (63 - Z.log2 x)
      /\ getr regs' 14%bv = v
      /\ (forall r, r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 19%bv -> getr regs' r = getr regs r).



(* [comment removed for export] *)
Definition bsl_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall (mem rom : word -> option byte) (L idx : Z) (a2w : word) (bs : list byte) (regs : bvmap 5 word),
    0 <= L /\ L + 624 <= 2 ^ 64 -> 0 <= idx <= 63 ->
    rdn SEGS mem (Z_to_bv 64 (L + 104 + 8 * idx)) 8 = Some bs -> length bs = 8%nat ->
    (forall j, 0 <= j < 8 -> store_ok SEGS mem (Z_to_bv 64 (L + 96 + j)) 1 = true) ->
    (forall j, 0 <= j < 8 -> store_ok SEGS mem (Z_to_bv 64 (L + 104 + 8 * idx + j)) 1 = true) ->
    getr regs 9%bv = Z_to_bv 64 L -> getr regs 11%bv = Z_to_bv 64 idx -> getr regs 12%bv = a2w ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (K1N.BSL_ENTRY T)) mem rom)
                  (mkst regs' (Z_to_bv 64 (K1N.BSL_EXIT T))
                        (wbytes (wbytes mem (Z_to_bv 64 (L + 96)) (word_to_le_bytes 8 a2w))
                                (Z_to_bv 64 (L + 104 + 8 * idx)) (word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs + 1)))) rom)
      /\ (forall r, r <> 11%bv -> r <> 13%bv -> getr regs' r = getr regs r).



(* [comment removed for export] *)
Definition initcache_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall (mem rom : word -> option byte) (c : Z) (regs : bvmap 5 word),
    0 <= c /\ c + K1N.IC_END < 2 ^ 64 ->
    (forall j, 0 <= j < K1N.IC_WLEN -> store_ok SEGS mem (Z_to_bv 64 (c + 84 + j)) 1 = true) ->
    getr regs 10%bv = Z_to_bv 64 c ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (K1N.IC_ENTRY T)) mem rom) (mkst regs' (Z_to_bv 64 (K1N.IC_EXIT T)) (K1N.ic_mem c mem) rom)
      /\ (forall r, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv
                  -> r <> 28%bv -> r <> 29%bv -> r <> 30%bv -> getr regs' r = getr regs r).

(* [comment removed for export] *)
Definition st_ok (c : Z) (tab : list (Z * nat * Z)) : Prop :=
  Forall (fun t : Z * nat * Z => let '(o, w, v) := t in 0 <= c + o /\ c + o + Z.of_nat w <= 2 ^ 64 /\ (1 <= w <= 8)%nat) tab.
Fixpoint disj_later (tab : list (Z * nat * Z)) : bool :=
  match tab with
  | [] => true
  | (o, w, _) :: rest =>
      (forallb (fun t : Z * nat * Z => let '(o', w', _) := t in (Z.leb (o' + Z.of_nat w') o || Z.leb (o + Z.of_nat w) o')%bool) rest
       && disj_later rest)%bool
  end.
Lemma ic_mem_cons : forall c t tab mem,
  fold_left (fun m (t : Z * nat * Z) => let '(o, w, v) := t in wbytes m (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v))) (t :: tab) mem
  = fold_left (fun m (t : Z * nat * Z) => let '(o, w, v) := t in wbytes m (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v))) tab
      (let '(o, w, v) := t in wbytes mem (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v))).
Proof. reflexivity. Qed.
Lemma st_mem_out : forall c tab mem (x : word), st_ok c tab ->
  Forall (fun t : Z * nat * Z => let '(o, w, v) := t in bv_unsigned x < c + o \/ c + o + Z.of_nat w <= bv_unsigned x) tab ->
  fold_left (fun m (t : Z * nat * Z) => let '(o, w, v) := t in wbytes m (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v))) tab mem x = mem x.
Proof.
  intros c tab. induction tab as [|[[o w] v] tab IH]; intros mem x Hok Hx; [reflexivity|].
  rewrite ic_mem_cons. inversion Hok as [|? ? Ht Hok']. inversion Hx as [|? ? Hxt Hx']. subst.
  rewrite (IH _ x Hok' Hx'). destruct Ht as (H1 & H2 & H3).
  apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
Qed.
Lemma st_mem_grows : forall c tab mem,
  mem_grows mem (fold_left (fun m (t : Z * nat * Z) => let '(o, w, v) := t in wbytes m (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v))) tab mem).
Proof.
  intros c tab. induction tab as [|[[o w] v] tab IH]; intros mem; [apply mem_grows_refl|].
  rewrite ic_mem_cons. eapply mem_grows_trans; [apply wbytes_grows | apply IH].
Qed.
Lemma st_mem_hit : forall segs c tab mem, st_ok c tab -> disj_later tab = true ->
  Forall (fun t : Z * nat * Z => let '(o, w, v) := t in
            rdn segs (fold_left (fun m (t : Z * nat * Z) => let '(o, w, v) := t in wbytes m (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v))) tab mem)
                (Z_to_bv 64 (c + o)) w = Some (word_to_le_bytes w (Z_to_bv 64 v))) tab.
Proof.
  intros segs c tab. induction tab as [|[[o w] v] tab IH]; intros mem Hok Hd; [constructor|].
  inversion Hok as [|? ? Ht Hok']. subst. cbn [disj_later] in Hd. apply andb_prop in Hd as [Hall Hd].
  destruct Ht as (H1 & H2 & H3).
  constructor.
  - rewrite ic_mem_cons.
    rewrite (rdn_ext segs w _ (wbytes mem (Z_to_bv 64 (c + o)) (word_to_le_bytes w (Z_to_bv 64 v)))); [| rewrite u64_lit by lia; lia |].
    + pose proof (rdn_wbytes_hit segs (word_to_le_bytes w (Z_to_bv 64 v)) mem (Z_to_bv 64 (c + o))) as Hh.
      rewrite length_N_to_le_bytes in Hh. apply Hh. rewrite u64_lit by lia. lia.
    + intros x Hx. rewrite u64_lit in Hx by lia. apply st_mem_out; [exact Hok'|].
      apply Forall_forall. intros [[o' w'] v'] Hin. pose proof (proj1 (forallb_forall _ _) Hall _ Hin) as Hb.
      cbn beta iota in Hb. apply orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
  - rewrite ic_mem_cons. apply IH; assumption.
Qed.
Lemma st_havoc_ok : forall segs E b o tab M k, 
  st_ok (bv_unsigned (edenot E b) + o) tab ->
  know_ok segs E M k ->
  know_ok segs E (fold_left (fun m (t : Z * nat * Z) => let '(o', w, v) := t in wbytes m (Z_to_bv 64 (bv_unsigned (edenot E b) + o + o')) (word_to_le_bytes w (Z_to_bv 64 v))) tab M)
          (fold_left (fun k' (t : Z * nat * Z) => let '(o', w, _) := t in kn_havoc k' b (o + o') (ELit (Z.of_nat w))) tab k).
Proof.
  intros segs E b o tab. induction tab as [|[[o' w] v] tab IH]; intros M k Hok HK; [exact HK|].
  inversion Hok as [|? ? Ht Hok']. subst. destruct Ht as (H1 & H2 & H3).
  cbn [fold_left]. apply IH; [exact Hok'|].
  eapply (w_know_ok_havoc segs E M); [exact HK | | apply wbytes_grows].
  intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite u64_lit in Hx by lia.
  apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable T : RPN.rptab.   (* [comment removed for export] *)
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Hypothesis CSPEC : clz_spec SEGS T.
Hypothesis BSPEC : bsl_spec SEGS T.
Hypothesis ICSPEC : initcache_spec SEGS T.   (* [comment removed for export] *)

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

(* [comment removed for export] *)
Lemma kread8e_rdn : forall E M k b off v,
  know_ok SEGS E M k -> kread8e SEGS k b off = Some v -> flat E (SA b off) 8 ->
  rdn SEGS M (adenot E (SA b off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros E M k b off v HK H Hfl. unfold kread8e in H.
  pose proof (know_lookup_sound SEGS E M k b off 8 false [] [] HK ltac:(lia) ltac:(lia)) as Hs.
  destruct (know_lookup SEGS k b off 8 false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3.
  rewrite P1, <- P3. f_equal. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite P2 in Hbnd. change (8 * Z.of_nat 8) with 64 in Hbnd.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.mod_small by lia. rewrite <- P2. symmetry. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_updn : forall E sr regs (rd : bv 5) (n : nat) v e,
  rd <> 0%bv -> ridx rd = n -> regs_ok E sr regs -> edenot E e = v ->
  regs_ok E (sr_upd sr n e) (regupd regs rd v).
Proof.
  intros E sr regs rd n v e Hrd Hn HR He. pose proof (regs_ok_upd E sr regs rd v e HR He) as H.
  destruct (bv_eqb rd 0) eqn:B.
  - exfalso. apply Hrd. apply bv_eq. unfold bv_eqb in B. apply Z.eqb_eq in B. exact B.
  - rewrite <- Hn. exact H.
Qed.

Theorem node_clz_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => K1N.node_clz SEGS nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold K1N.node_clz, K1N.clz_tests in Hn. destruct args; [|discriminate].
  destruct (reg cs 9) as [L| | | | | | | ] eqn:Hr9; try discriminate.
  destruct (xlo (kn cs) (reg cs 18)) as [lo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 18)) as [hi|] eqn:Hxhi; [|discriminate].
  destruct (kread8e SEGS (kn cs) (ELit 0) (L + 48)) as [v|] eqn:Hrd8; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hall; [|discriminate] end.
  cbn [forallb andb] in Hall.
  repeat match type of Hall with (?a && ?b)%bool = true => apply andb_prop in Hall; destruct Hall as [?X Hall]; revert X end.
  intros Hfresh Hvv HL56 HL0 Hhi Hlohi Hlo1 Hpc. clear Hall.
  apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo1. apply Z.leb_le in Hlohi. apply Z.ltb_lt in Hhi.
  apply Z.leb_le in HL0. apply Z.leb_le in HL56. unfold two64 in Hhi, HL56.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 18 HC ltac:(lia)) as R18.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  rewrite Hr9 in R9. cbn [edenot] in R9.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hxlo) as Blo.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hxhi) as Bhi.
  set (xw := edenot E (reg cs 18)) in *. set (x := bv_unsigned xw) in *.
  assert (HxW : Z_to_bv 64 x = xw) by (apply Z_to_bv_bv_unsigned).
  assert (Hfl : flat E (SA (ELit 0) (L + 48)) 8).
  { unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  pose proof (kread8e_rdn E M (kn cs) (ELit 0) (L + 48) v HKN Hrd8 Hfl) as Hcell.
  match type of Hcell with rdn _ _ ?a 8 = _ => replace a with (Z_to_bv 64 (L + 48)) in Hcell
      by (unfold adenot; cbn [a_base a_off edenot]; rewrite v_addi_zbv by lia; rewrite Z.add_0_l; reflexivity) end.
  (* [comment removed for export] *)
  destruct (CSPEC M (seg_rom SEGS) x L (edenot E v) R ltac:(lia) ltac:(lia) Hcell ltac:(rewrite HxW; exact R18) R9)
    as (regs' & Hms & H19 & H14 & Hout).
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (nx := nxt cs) in *.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HREG.
  assert (Hv : forall E', env_agree nx E E' -> edenot E' v = getr regs' 14%bv).
  { intros E' Hag. rewrite <- (edenot_agree' nx E E' v Hag Hvv). symmetry. exact H14. }
  assert (Hlog : Z.log2 lo <= Z.log2 x <= Z.log2 hi).
  { split; apply Z.log2_le_mono; lia. }
  assert (Hlog64 : 0 <= Z.log2 lo /\ Z.log2 hi < 64).
  { split; [apply Z.log2_nonneg|]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Hpc in Hms.
  destruct (Z.eqb (Z.log2 lo) (Z.log2 hi)) eqn:HK; injection Hn as <-.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in HK.
    set (Rf := regupd (regupd regs' 14%bv (getr R 14%bv)) 19%bv (getr R 19%bv)).
    set (E4 := ext_list E nx (map (fun r => getr Rf (Z_to_bv 5 (Z.of_nat r))) K1N.CLZ_REGS)).
    assert (Hag4 : env_agree nx E E4) by (unfold E4; apply ext_list_agree).
    assert (HRf : regs_ok E4 (sr_fresh (s_regs (a_ss cs)) K1N.CLZ_REGS nx) Rf).
    { unfold E4. apply (regs_ok_region K1N.CLZ_REGS E (s_regs (a_ss cs)) R Rf nx HREG Fsr).
      - unfold K1N.CLZ_REGS. repeat constructor.
      - intros r Hr0 Hnot. unfold K1N.CLZ_REGS in Hnot. unfold Rf.
        destruct (bv_eq_dec 5 r 19%bv) as [->|N19]; [rewrite getr_same by (intros X; discriminate X); reflexivity|].
        rewrite getr_other by exact N19.
        destruct (bv_eq_dec 5 r 14%bv) as [->|N14]; [rewrite getr_same by (intros X; discriminate X); reflexivity|].
        rewrite getr_other by exact N14.
        apply Hout; try assumption; intros ->; apply Hnot; cbv; auto 10. }
    pose proof (regs_ok_updn E4 _ Rf 19%bv 19%nat (Z_to_bv 64 (63 - Z.log2 lo)) (ELit (63 - Z.log2 lo))
                  ltac:(intros X; discriminate X) eq_refl HRf eq_refl) as HR19.
    pose proof (regs_ok_updn E4 _ _ 14%bv 14%nat (getr regs' 14%bv) v ltac:(intros X; discriminate X) eq_refl HR19 (Hv E4 Hag4)) as HR14.
    assert (HR2 : regs_ok E4 (sr_upd (sr_upd (sr_fresh (s_regs (a_ss cs)) K1N.CLZ_REGS nx) 19 (ELit (63 - Z.log2 lo))) 14 v) regs').
    { intros r. rewrite <- (HR14 r). unfold Rf.
      destruct (bv_eq_dec 5 r 14%bv) as [->|N14]; [rewrite getr_same by (intros X; discriminate X); reflexivity|].
      rewrite (getr_other _ _ _ _ N14).
      destruct (bv_eq_dec 5 r 19%bv) as [->|N19].
      { rewrite getr_same by (intros X; discriminate X). rewrite H19. f_equal. lia. }
      rewrite (getr_other _ _ _ _ N19). rewrite (getr_other _ _ _ _ N19). rewrite (getr_other _ _ _ _ N14). reflexivity. }
    eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
              cs E E4 R FULL model TT (K1N.CLZ_EXIT T) _ (kn cs) (nx + 4)%N regs' (M_of E cs model FULL) HC Hfresh Hag4 Hms HR2).
    + eapply know_ok_agree'; [exact Hag4 | exact Fkn | exact HKN].
    + intros R' FULL' model' HC' Hfs'. apply (Hk E4 R' FULL' model'); [| exact HC' | exact Hfs'].
      split; [eapply env_agree_le; [exact Hag4 | exact Fle] | exact Hag4].
  - (* [comment removed for export] *)
    set (Rf := regupd regs' 14%bv (getr R 14%bv)).
    set (E5 := ext_list E nx (map (fun r => getr Rf (Z_to_bv 5 (Z.of_nat r))) (K1N.CLZ_REGS ++ [19%nat]))).
    assert (Hag5 : env_agree nx E E5) by (unfold E5; apply ext_list_agree).
    assert (HRf : regs_ok E5 (sr_fresh (s_regs (a_ss cs)) (K1N.CLZ_REGS ++ [19%nat]) nx) Rf).
    { unfold E5. apply (regs_ok_region (K1N.CLZ_REGS ++ [19%nat]) E (s_regs (a_ss cs)) R Rf nx HREG Fsr).
      - unfold K1N.CLZ_REGS. cbn [app]. repeat constructor.
      - intros r Hr0 Hnot. unfold K1N.CLZ_REGS in Hnot. cbn [app] in Hnot. unfold Rf.
        destruct (bv_eq_dec 5 r 14%bv) as [->|N14]; [rewrite getr_same by (intros X; discriminate X); reflexivity|].
        rewrite getr_other by exact N14.
        apply Hout; try assumption; intros ->; apply Hnot; cbv; auto 10. }
    pose proof (regs_ok_updn E5 _ _ 14%bv 14%nat (getr regs' 14%bv) v ltac:(intros X; discriminate X) eq_refl HRf (Hv E5 Hag5)) as HR14.
    assert (HR2 : regs_ok E5 (sr_upd (sr_fresh (s_regs (a_ss cs)) (K1N.CLZ_REGS ++ [19%nat]) nx) 14 v) regs').
    { intros r. rewrite <- (HR14 r). unfold Rf.
      destruct (bv_eq_dec 5 r 14%bv) as [->|N14]; [rewrite getr_same by (intros X; discriminate X); reflexivity|].
      rewrite !(getr_other _ _ _ _ N14). reflexivity. }
    assert (HE5c : ev E5 (nx + 4)%N = getr regs' 19%bv).
    { unfold E5, K1N.CLZ_REGS. cbn [map app ext_list].
      replace (nx + 4)%N with (N.succ (N.succ (N.succ (N.succ nx)))) by lia. rewrite ext1_at.
      unfold Rf. rewrite getr_other by (intros X; discriminate X). reflexivity. }
    eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
              cs E E5 R FULL model TT (K1N.CLZ_EXIT T) _ (KRange (EVar (nx + 4)%N) (63 - Z.log2 hi) (63 - Z.log2 lo) :: kn cs) (nx + 5)%N regs' (M_of E cs model FULL) HC Hfresh Hag5 Hms HR2).
    + constructor.
      * cbn [kentry_ok edenot]. rewrite HE5c, H19.
        pose proof (clz_lt64 x). rewrite u64_lit by lia. lia.
      * eapply know_ok_agree'; [exact Hag5 | exact Fkn | exact HKN].
    + intros R' FULL' model' HC' Hfs'. apply (Hk E5 R' FULL' model'); [| exact HC' | exact Hfs'].
      split; [eapply env_agree_le; [exact Hag5 | exact Fle] | exact Hag5].
Qed.

(* [comment removed for export] *)
Lemma store_ok_bytes_g : forall nb m (a : Z),
  (0 <= a)%Z -> (a + Z.of_nat nb < 2 ^ 64)%Z ->
  (forall j, (0 <= j < Z.of_nat nb)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) nb = true.
Proof.
  induction nb as [|nb IH]; intros m a Ha Hw H; [reflexivity|].
  cbn [store_ok]. pose proof (H 0%Z ltac:(lia)) as H0. cbn [store_ok] in H0. rewrite Z.add_0_r in H0.
  destruct (wview SEGS m (Z_to_bv 64 a)); [|discriminate].
  rewrite zbv_add1. apply IH; [lia|lia|].
  intros j Hj. replace (a + 1 + j)%Z with (a + (1 + j))%Z by lia. apply H. lia.
Qed.
Lemma store_ok8_bytes_g : forall m (a : Z),
  (0 <= a)%Z -> (a + 8 < 2 ^ 64)%Z ->
  (forall j, (0 <= j < 8)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) 8 = true.
Proof. intros m a Ha Hw H. apply store_ok_bytes_g; [exact Ha | cbn; lia | exact H]. Qed.

Theorem node_bysizelog_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => K1N.node_bysizelog nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold K1N.node_bysizelog, K1N.bsl_tests in Hn. destruct args; [|discriminate].
  destruct (reg cs 9) as [L| | | | | | | ] eqn:Hr9; try discriminate.
  destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hall; [|discriminate] end.
  cbn [forallb andb] in Hall.
  repeat match type of Hall with (?a && ?b)%bool = true => apply andb_prop in Hall; destruct Hall as [?X Hall]; revert X end.
  intros Hfresh Hv12 HwW Hw96 HL624 HL0 Hhi Hlohi Hlo0 Hpc. clear Hall.
  apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo0. apply Z.leb_le in Hlohi. apply Z.leb_le in Hhi.
  apply Z.leb_le in HL0. apply Z.leb_le in HL624. unfold two64 in HL624.
  injection Hn as <-.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 HC ltac:(lia)) as R12.
  rewrite Hr9 in R9. cbn [edenot] in R9.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hxlo) as Blo.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hxhi) as Bhi.
  set (iw := edenot E (reg cs 11)) in *. set (idx := bv_unsigned iw) in *.
  assert (HiW : Z_to_bv 64 idx = iw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) (ELit 0) (L + 96) 8 HKN HKN Hw96 ltac:(lia)) as (S96 & _ & _).
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) (ELit 0) (L + 104 + 8 * lo) (8 * (hi - lo) + 8) HKN HKN HwW ltac:(lia)) as (SW & _ & _).
  rewrite estart_lit0 in S96, SW.
  assert (Hok96 : forall j, 0 <= j < 8 -> store_ok SEGS M (Z_to_bv 64 (L + 96 + j)) 1 = true).
  { intros j Hj. pose proof (store_ok_all SEGS M (Z.to_nat 8) (Z_to_bv 64 (L + 96)) ltac:(rewrite u64_lit by lia; cbn; lia) S96
                 (Z_to_bv 64 (L + 96 + j)) ltac:(rewrite !u64_lit by lia; cbn; lia)) as X.
    cbn [store_ok]. destruct (wview SEGS M (Z_to_bv 64 (L + 96 + j))); [reflexivity | exfalso; exact (X eq_refl)]. }
  assert (HokW : forall j, 0 <= j < 8 -> store_ok SEGS M (Z_to_bv 64 (L + 104 + 8 * idx + j)) 1 = true).
  { intros j Hj. pose proof (store_ok_all SEGS M (Z.to_nat (8 * (hi - lo) + 8)) (Z_to_bv 64 (L + 104 + 8 * lo))
                 ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) SW
                 (Z_to_bv 64 (L + 104 + 8 * idx + j)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as X.
    cbn [store_ok]. destruct (wview SEGS M (Z_to_bv 64 (L + 104 + 8 * idx + j))); [reflexivity | exfalso; exact (X eq_refl)]. }
  assert (HokW8 : store_ok SEGS M (Z_to_bv 64 (L + 104 + 8 * idx)) 8 = true).
  { apply store_ok8_bytes_g; [lia | lia | exact HokW]. }
  destruct (store_ok_rdn SEGS SEGS_wr 8 M (Z_to_bv 64 (L + 104 + 8 * idx)) ltac:(rewrite u64_lit by lia; cbn; lia) HokW8) as (bs & Hrd & Hlen).
  (* [comment removed for export] *)
  destruct (BSPEC M (seg_rom SEGS) L idx (edenot E (reg cs 12)) bs R ltac:(lia) ltac:(lia) Hrd Hlen Hok96 HokW
              R9 ltac:(rewrite HiW; exact R11) R12) as (regs' & Hms & Hout).
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (nx := nxt cs) in *.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HREG.
  rewrite <- Hpc in Hms.
  set (M1 := wbytes M (Z_to_bv 64 (L + 96)) (word_to_le_bytes 8 (edenot E (reg cs 12)))) in *.
  set (nv := Z_to_bv 64 (bytes_le_to_Z bs + 1)) in *.
  set (M2 := wbytes M1 (Z_to_bv 64 (L + 104 + 8 * idx)) (word_to_le_bytes 8 nv)) in *.
  set (MW := wbytes M (Z_to_bv 64 (L + 104 + 8 * idx)) (word_to_le_bytes 8 nv)).
  set (E2 := ext_list E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) K1N.BSL_REGS)).
  assert (Hag2 : env_agree nx E E2) by (unfold E2; apply ext_list_agree).
  assert (HR2 : regs_ok E2 (sr_fresh (s_regs (a_ss cs)) K1N.BSL_REGS nx) regs').
  { unfold E2. apply (regs_ok_region K1N.BSL_REGS E (s_regs (a_ss cs)) R regs' nx HREG Fsr).
    - unfold K1N.BSL_REGS. repeat constructor.
    - intros r Hr0 Hnot. unfold K1N.BSL_REGS in Hnot. apply Hout; intros ->; apply Hnot; cbv; auto 10. }
  assert (WL8 : length (word_to_le_bytes 8 (edenot E (reg cs 12))) = 8%nat) by (apply length_N_to_le_bytes).
  assert (WLn : length (word_to_le_bytes 8 nv) = 8%nat) by (apply length_N_to_le_bytes).
  (* [comment removed for export] *)
  assert (HK2 : know_ok SEGS E2 M2 (K1N.bsl_kn (kn cs) L lo hi (reg cs 12))).
  { unfold K1N.bsl_kn. constructor.
    - (* [comment removed for export] *)
      cbn [kentry_ok]. split; [lia|]. split.
      + unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
      + unfold adenot. cbn [a_base a_off edenot]. rewrite v_addi_zbv by lia. rewrite Z.add_0_l.
        rewrite <- (edenot_agree' nx E E2 (reg cs 12) Hag2 Hv12).
        unfold M2. rewrite rdn_wbytes_out; [| rewrite !u64_lit by lia; rewrite WLn; cbn; lia | rewrite u64_lit by lia; cbn; lia | rewrite u64_lit by lia; rewrite WLn; cbn; lia].
        unfold M1. apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia.
    - (* [comment removed for export] *)
      eapply (w_know_ok_havoc SEGS E2 MW M2).
      + eapply (w_know_ok_havoc SEGS E2 M MW).
        * eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN].
        * intros x Hx. rewrite estart_lit0, elenZ_lit in Hx by lia. unfold MW.
          destruct Hx as [Hx|Hx]; [apply wbytes_below | apply wbytes_above]; rewrite ?u64_lit by lia; rewrite ?WLn; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
        * unfold MW. apply wbytes_grows.
      + intros x Hx. rewrite estart_lit0, elenZ_lit in Hx by lia. unfold M2, MW, M1.
        pose proof (u64_range x) as Ux.
        assert (OW : forall m, (bv_unsigned x < L + 104 + 8 * idx \/ L + 104 + 8 * idx + 8 <= bv_unsigned x) ->
                     wbytes m (Z_to_bv 64 (L + 104 + 8 * idx)) (word_to_le_bytes 8 nv) x = m x).
        { intros m Ho. apply wbytes_out; rewrite u64_lit by lia; rewrite WLn; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
        assert (O96 : forall m, wbytes m (Z_to_bv 64 (L + 96)) (word_to_le_bytes 8 (edenot E (reg cs 12))) x = m x).
        { intros m. apply wbytes_out; rewrite u64_lit by lia; rewrite WL8; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
        destruct (Z_lt_le_dec (bv_unsigned x) (L + 104 + 8 * idx)) as [Xlo|Xge]; [rewrite !OW by lia; apply O96|].
        destruct (Z_lt_le_dec (bv_unsigned x) (L + 104 + 8 * idx + 8)) as [Ilo|Ige]; [|rewrite !OW by lia; apply O96].
        (* [comment removed for export] *)
        set (j := Z.to_nat (bv_unsigned x - (L + 104 + 8 * idx))).
        assert (Hxj : x = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (L + 104 + 8 * idx)) + Z.of_nat j)).
        { unfold j. rewrite u64_lit by lia. rewrite Z2Nat.id by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. f_equal. lia. }
        rewrite Hxj. rewrite !wbytes_nth; [reflexivity | | | |]; rewrite ?u64_lit by lia; rewrite ?WLn; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold j; lia.
      + unfold M2, MW. intros x Hx. 
        (* [comment removed for export] *)
        pose proof (u64_range x) as Ux.
        destruct (Z_lt_le_dec (bv_unsigned x) (L + 104 + 8 * idx)) as [Xlo|Xge].
        { rewrite wbytes_out in Hx |- *; try (rewrite u64_lit by lia; rewrite WLn; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
          exact (wbytes_grows _ _ _ x Hx). }
        destruct (Z_lt_le_dec (bv_unsigned x) (L + 104 + 8 * idx + 8)) as [Ilo|Ige].
        { set (j := Z.to_nat (bv_unsigned x - (L + 104 + 8 * idx))).
          assert (Hxj : x = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (L + 104 + 8 * idx)) + Z.of_nat j)).
          { unfold j. rewrite u64_lit by lia. rewrite Z2Nat.id by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. f_equal. lia. }
          rewrite Hxj. rewrite wbytes_nth; [discriminate | |]; rewrite ?u64_lit by lia; rewrite ?WLn; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold j; lia. }
        rewrite wbytes_out in Hx |- *; try (rewrite u64_lit by lia; rewrite WLn; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
        exact (wbytes_grows _ _ _ x Hx).
  }
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs E E2 R FULL model TT (K1N.BSL_EXIT T) _ _ (nx + 2)%N regs' M2 HC Hfresh Hag2 Hms HR2 HK2).
  intros R' FULL' model' HC' Hfs'. apply (Hk E2 R' FULL' model'); [| exact HC' | exact Hfs'].
  split; [eapply env_agree_le; [exact Hag2 | exact Fle] | exact Hag2].
Qed.
(* [comment removed for export] *)
Lemma ic_tab_facts : disj_later K1N.ic_tab = true
  /\ Forall (fun t : Z * nat * Z => let '(o, w, v) := t in 84 <= o /\ o + Z.of_nat w <= K1N.IC_END /\ (1 <= w <= 8)%nat /\ 0 <= v < 2 ^ 32) K1N.ic_tab.
Proof.
  split; [vm_compute; reflexivity|].
  unfold K1N.ic_tab, K1N.ic_cnt, K1N.ic_size, K1N.IC_END. cbn [K1N.ic_mk].
  repeat (apply Forall_cons; [lia|]). apply Forall_nil.
Qed.
Theorem node_initcache_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => K1N.node_initcache nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold K1N.node_initcache, K1N.ic_tests in Hn. destruct args; [|discriminate].
  destruct (split_lit (reg cs 10)) as [b o] eqn:Hsl.
  destruct (base_range (kn cs) b) as [[lo hi]|] eqn:Hbr; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hall; [|discriminate] end.
  cbn [forallb andb] in Hall.
  repeat match type of Hall with (?a && ?b)%bool = true => apply andb_prop in Hall; destruct Hall as [?X Hall]; revert X end.
  intros Hfresh Hvb Hw Hhi Hlo Hpc. clear Hall.
  apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. unfold two64, K1N.IC_END in Hhi.
  injection Hn as <-.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (base_range_sound SEGS E M (kn cs) b lo hi HKN Hbr) as [Bl Bh].
  set (c := bv_unsigned (edenot E b) + o) in *.
  assert (Hc10 : edenot E (reg cs 10) = Z_to_bv 64 c) by (unfold c; apply split_lit_denot; exact Hsl).
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) b (o + 84) K1N.IC_WLEN HKN HKN Hw ltac:(unfold K1N.IC_WLEN; lia)) as (SW & _ & _).
  assert (Hst : estart E (SA b (o + 84)) = c + 84) by (unfold estart, c; cbn [a_base a_off]; lia).
  rewrite Hst in SW.
  assert (HokW : forall j, 0 <= j < K1N.IC_WLEN -> store_ok SEGS M (Z_to_bv 64 (c + 84 + j)) 1 = true).
  { intros j Hj. unfold K1N.IC_WLEN in *.
    pose proof (store_ok_all SEGS M (Z.to_nat 2412) (Z_to_bv 64 (c + 84)) ltac:(rewrite u64_lit by lia; cbn; lia) SW
                 (Z_to_bv 64 (c + 84 + j)) ltac:(rewrite !u64_lit by lia; cbn; lia)) as X.
    cbn [store_ok]. destruct (wview SEGS M (Z_to_bv 64 (c + 84 + j))); [reflexivity | exfalso; exact (X eq_refl)]. }
  (* [comment removed for export] *)
  destruct (ICSPEC M (seg_rom SEGS) c R ltac:(unfold K1N.IC_END; lia) HokW ltac:(rewrite <- Hc10; exact R10)) as (regs' & Hms & Hout).
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (nx := nxt cs) in *.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HREG.
  rewrite <- Hpc in Hms.
  set (E2 := ext_list E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) K1N.IC_REGS)).
  assert (Hag2 : env_agree nx E E2) by (unfold E2; apply ext_list_agree).
  assert (HR2 : regs_ok E2 (sr_fresh (s_regs (a_ss cs)) K1N.IC_REGS nx) regs').
  { unfold E2. apply (regs_ok_region K1N.IC_REGS E (s_regs (a_ss cs)) R regs' nx HREG Fsr).
    - unfold K1N.IC_REGS. repeat constructor.
    - intros r Hr0 Hnot. unfold K1N.IC_REGS in Hnot. apply Hout; intros ->; apply Hnot; cbv; auto 20. }
  assert (Hbv : edenot E2 b = edenot E b) by (symmetry; eapply (edenot_agree' nx); [exact Hag2 | exact Hvb]).
  destruct ic_tab_facts as [Hdisj Htab].
  assert (Hok : st_ok c K1N.ic_tab).
  { eapply Forall_impl; [|exact Htab]. intros [[o' w] v] (T1 & T2 & T3 & T4). unfold K1N.IC_END in T2. unfold c. lia. }
  (* [comment removed for export] *)
  assert (HK2 : know_ok SEGS E2 (K1N.ic_mem c M) (K1N.ic_kn (kn cs) b o)).
  { unfold K1N.ic_kn. apply Forall_app. split.
    - (* [comment removed for export] *)
      unfold K1N.ic_facts. apply Forall_map. pose proof (st_mem_hit SEGS c K1N.ic_tab M Hok Hdisj) as Hh.
      eapply Forall_impl; [|exact (Forall_and Hh Htab)]. intros [[o' w] v] [Hr (T1 & T2 & T3 & T4)].
      unfold K1N.IC_END in T2.
      cbn [kentry_ok]. split; [lia|]. split.
      + unfold flat, estart. cbn [a_base a_off]. rewrite Hbv. unfold c in *. lia.
      + unfold adenot, v_addi. cbn [a_base a_off]. rewrite Hbv.
        replace (bv_unsigned (edenot E b) + (o + o')) with (c + o') by (unfold c; lia). exact Hr.
    - (* [comment removed for export] *)
      unfold K1N.ic_havoc, K1N.ic_mem.
      assert (Hc2 : bv_unsigned (edenot E2 b) + o = c) by (rewrite Hbv; reflexivity).
      pose proof (st_havoc_ok SEGS E2 b o K1N.ic_tab M (kn cs) ltac:(rewrite Hc2; exact Hok)
                    ltac:(eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN])) as HH.
      rewrite Hc2 in HH. exact HH. }
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs E E2 R FULL model TT (K1N.IC_EXIT T) _ _ (nx + 11)%N regs' (K1N.ic_mem c M) HC Hfresh Hag2 Hms HR2 HK2).
  intros R' FULL' model' HC' Hfs'. apply (Hk E2 R' FULL' model'); [| exact HC' | exact Hfs'].
  split; [eapply env_agree_le; [exact Hag2 | exact Fle] | exact Hag2].
Qed.
End Sound.

Section Table.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable T : RPN.rptab.   (* [comment removed for export] *)
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Hypothesis CSPEC : clz_spec SEGS T.
Hypothesis BSPEC : bsl_spec SEGS T.
Theorem k1_xn_sound : ext_stmt SEGS A nx0 LIMIT (K1N.xn SEGS nx0 T) SINV argH FS0.
Proof.
  intros id args. unfold K1N.xn.
  destruct (Nat.eqb id 111); [apply node_clz_sound; assumption|].
  destruct (Nat.eqb id 112); [apply node_bysizelog_sound; assumption|].
  intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End Table.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
