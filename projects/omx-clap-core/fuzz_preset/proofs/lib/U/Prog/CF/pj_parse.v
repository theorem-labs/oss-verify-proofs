From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjIn PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memset_c ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import ReaderKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require skip_ws_c.
Import ListNotations.
Open Scope Z_scope.

Definition pp_pro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (text len out : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (j : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x16004) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 out) s1
                  (Z_to_bv 64 (bv_unsigned sp + -40)) (Z_to_bv 64 out) a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x16044) fc None m' (seg_rom rsegs) /\
    rw_cells rsegs m' (bv_unsigned sp + -48)
      [CB 8 j; C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 (text + len)); C8 (Z_to_bv 64 0); C8 s0; C8 ra] /\
    munch [(bv_unsigned sp + -48, bv_unsigned sp); (out, out + 56)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' out [CB 56 (repeat (Z_to_bv 8 0) 56)].

Lemma pp_stk_after : forall m m' lo hi a n, stk rsegs m lo hi -> munch [(a, a + n)] m m' -> wmono rsegs m m' ->
  stk rsegs m' a (a + n) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a n (H1 & H2 & H) MU WM (_ & _ & K). split; [lia|]. split; [lia|].
  intros x Hx. destruct (H x Hx) as [W (b & B)]. split; [apply WM, W|].
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + n)).
  - apply (K x). lia.
  - exists b. unfold mrd in *. rewrite MU; [exact B|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact B|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact B|]. cbn [outside]. rewrite wa_unsigned by lia. split; [lia|exact I].
Qed.

Lemma pp_pro : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo text len out : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> mem_inv rsegs m ->
  0 < text -> 0 <= len -> text + len < 2 ^ 62 ->
  pj_rw rsegs m out -> out + 56 <= lo \/ bv_unsigned sp <= out ->
  evt rsegs (pp_pro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m text len out)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 text) (Z_to_bv 64 len) (Z_to_bv 64 out) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15fb4) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSET_H ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo text len out ST LO MI T0 L0 TL PJ DJ.
  destruct PJ as (AL & PS).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (Llo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof PS as (O1 & O2 & _).
  destruct (stk_carve rsegs m out (out + 56) 56 PS ltac:(lia)) as [_ (junk2 & RV)].
  replace (out + 56 - Z.of_nat 56) with out in RV by lia.
  clear PS.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (out, out + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 5 zstep.
  step. if_cases HB0; [zify_cond HB0; rewrite ?unsigned_lit in HB0 by lia; lia|].
  do 4 zstep.
  step. if_cases HB1.
  { zify_cond HB1. replace (0 <? text) with true in HB1 by (symmetry; apply Z.ltb_lt; lia).
    replace (len + text <? 1) with false in HB1 by (symmetry; apply Z.ltb_ge; lia). cbn in HB1. discriminate HB1. }
  do 6 zstep.
  eapply evt_cut.
  { eapply MEMSET_H with (junk := junk2).
    - rewrite (unsigned_lit out) by lia. exact RV.
    - exact MI. }
  intros ms' POST. unfold memset_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
    E & MUc & WMc & MIc & RVc).
  subst ms'.
  rewrite (unsigned_lit out) in MUc, RVc by lia.
  change (bv_unsigned (Z_to_bv 64 56)) with 56 in MUc.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat in RVc.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RVc.
  match goal with |- context [ret_pc (Z_to_bv 64 ?k)] =>
    replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (apply bv_eq; vm_compute; reflexivity) end.
  assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -48)).
  { apply (pp_stk_after m0 m2 lo (bv_unsigned sp + -48) out 56 ST MUc WMc).
    exact (stk_of_rw_cells rsegs m2 out _ RVc). }
  assert (MU2 : munch [(bv_unsigned sp + -48, bv_unsigned sp); (out, out + 56)] m m2).
  { apply (munch_trans _ m m0 m2 MU). eapply munch_weaken; [|exact MUc].
    unfold sub_fp. cbn [outside]. intros x Hx. tauto. }
  pose proof (wmono_trans rsegs m m0 m2 WM WMc) as WM2.
  apply (rw_cells_transport rsegs [(out, out + 56)] m0 m2) in FR;
    [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize]; lia].
  clear ST MU WM MI RV MUc WMc.
  rename ST2 into ST, MU2 into MU, WM2 into WM, MIc into MI, RVc into RV.
  do 3 zstep.
  apply evt_done. unfold pp_pro_post.
  do 13 eexists. exists m2. eexists.
  split; [reflexivity|].
  split; [replace (text + len) with (len + text) by lia; exact FR|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact RV.
Qed.

Definition pp_ret (rav sp gp tp s0v s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (v : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0' t1' t2' s0v s1 (Z_to_bv 64 v)
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc rav) fc None m (seg_rom rsegs).

Definition pp_call_free (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR (Z_to_bv 64 0x16024) sp gp tp t0' t1' t2' s0 s1 s0 a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x16340) fc None m (seg_rom rsegs).

Definition pp_scan_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (rav s0v : word) (text p : Z) (tb : list byte) : machine_state -> Prop :=
  fun ms' => exists m', munch [(bv_unsigned sp + 8, bv_unsigned sp + 16)] m m' /\ wmono rsegs m m' /\
    (mem_inv rsegs m -> mem_inv rsegs m') /\
    ((skip (zb (skipn (Z.to_nat (p - text)) tb)) = [] /\
       pp_ret rav sp gp tp s0v s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' 0 ms') \/
     (skip (zb (skipn (Z.to_nat (p - text)) tb)) <> [] /\
       pp_call_free sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' ms')).

Lemma pp_ret_at : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v : word) (v : Z),
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 s0v; C8 rav] -> bv_unsigned sp + 48 < 2 ^ 64 ->
  evt rsegs (pp_ret rav sp gp tp s0v s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m v)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16028) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rav s0v v
    FR HS.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 4 zstep.
  apply evt_done. unfold pp_ret. do 14 eexists. reflexivity.
Qed.

Lemma pp_free_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v : word),
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 s0v; C8 rav] -> bv_unsigned sp + 48 < 2 ^ 64 ->
  evt rsegs (pp_ret rav sp gp tp s0v s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (-1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16024) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rav s0v
    FR HS.
  zstep.
  apply pp_ret_at; assumption.
Qed.

Lemma pp_skip_zb : forall bs, skip (zb bs) = zb (skipn (skip_ws_c.ws_len bs) bs).
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [skip_ws_c.ws_len]. unfold zb at 1. cbn [map skip].
  change (PjGrammar.ws (bv_unsigned b)) with (skip_ws_c.ws b).
  destruct (skip_ws_c.ws b); [exact IH | reflexivity].
Qed.

Lemma pp_scan : skip_ws_c.skip_ws_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rav s0v : word) (text len p d : Z) (tb : list byte),
  pj_in_ok rsegs m (bv_unsigned sp + 8) text len p d tb ->
  rw_cells rsegs m (bv_unsigned sp + 32) [C8 s0v; C8 rav] -> bv_unsigned sp + 48 < 2 ^ 64 ->
  evt rsegs (pp_scan_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m rav s0v text p tb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16004) fc None m (seg_rom rsegs)).
Proof.
  intros SW ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m rav s0v
    text len p d tb PJ FR HS.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  step. try if_false.
  step. step.
  eapply evt_cut.
  { eapply SW; [|exact PJ]. reflexivity. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU & WM & MI & PJ').
  match goal with |- context [ret_pc (Z_to_bv 64 ?k)] =>
    replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (apply bv_eq; vm_compute; reflexivity) end.
  replace (bv_unsigned sp + 8 + 8) with (bv_unsigned sp + 16) in MU by lia.
  set (P := p + Z.of_nat (skip_ws_c.ws_len (skipn (Z.to_nat (p - text)) tb))) in PJ'.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ') as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
  pose proof (pj_in_ok_rd_p rsegs _ _ _ _ _ _ _ PJ') as RQ.
  pose proof (pj_in_ok_rd_end rsegs _ _ _ _ _ _ _ PJ') as RE.
  assert (FR' : rw_cells rsegs m' (bv_unsigned sp + 32) [C8 s0v; C8 rav]).
  { apply (rw_cells_transport rsegs _ m m' _ _ FR MU WM). cbn [disjoint_from cells_size csize]. lia. }
  assert (SKP : skip (zb (skipn (Z.to_nat (p - text)) tb)) = zb (skipn (Z.to_nat (P - text)) tb)).
  { rewrite pp_skip_zb. unfold P. rewrite skipn_skipn. f_equal. f_equal. lia. }
  step. step. step.
  if_cases HB; rewrite rk_eqb in HB by lia.
  - apply Z.eqb_eq in HB.
    step. step.
    eapply evt_mono; [apply pp_ret_at; [exact FR' | exact HS]|].
    intros ms'' H. exists m'. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. left. split; [|exact H].
    rewrite SKP. replace (Z.to_nat (P - text)) with (length tb) by lia. rewrite skipn_all. reflexivity.
  - apply Z.eqb_neq in HB.
    step. step.
    apply evt_done. exists m'. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. right. split.
    + rewrite SKP. destruct (skipn (Z.to_nat (P - text)) tb) eqn:E; [|discriminate].
      exfalso. pose proof (length_skipn (Z.to_nat (P - text)) tb) as LL. rewrite E in LL. cbn in LL. lia.
    + unfold pp_call_free. do 14 eexists. reflexivity.
Qed.

Lemma pp_refuse : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (pp_call_free sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16004) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. try if_true.
  step. step.
  apply evt_done. unfold pp_call_free. do 14 eexists. reflexivity.
Qed.

Lemma pp_rest : forall tb ok t r tr okr, jr_value jr_strtod 0 (zb tb) ok = (Some (t, r), tr, okr) ->
  zb (skipn (Z.to_nat (Z.of_nat (length tb) - Z.of_nat (length r))) tb) = r.
Proof.
  intros tb ok t r tr okr H. unfold jr_value in H.
  destruct (proj1 (rk_suf_fuel _) 0%nat (zb tb) ok t r tr okr H) as (u & Hu).
  assert (L : length tb = (length u + length r)%nat).
  { unfold zb in Hu. apply (f_equal (@length Z)) in Hu. rewrite length_map, length_app in Hu. exact Hu. }
  replace (Z.to_nat (Z.of_nat (length tb) - Z.of_nat (length r))) with (length u) by lia.
  unfold zb. rewrite <- skipn_map. fold (zb tb). rewrite Hu. apply skipn_app_exact.
Qed.

Lemma pp_c17 : forall x ok cnt fail, oks ok cnt fail (calls (snd (jr_run jr_strtod x ok))) ->
  cnt <= fail < cnt + Z.of_nat (ncalls jr_strtod x) -> fst (jr_run jr_strtod x ok) = None.
Proof.
  intros x ok cnt fail HO HF.
  destruct (ok_upto_dec ok (ncalls jr_strtod x)) as [Hu | (j & Hj & Hf & Hu)].
  - exfalso. pose proof (G7_1_calls jr_strtod x ok Hu) as HC. rewrite HC in HO.
    specialize (HO (Z.to_nat (fail - cnt)) ltac:(lia)).
    rewrite (Hu (Z.to_nat (fail - cnt)) ltac:(lia)) in HO.
    replace (cnt + Z.of_nat (Z.to_nat (fail - cnt)) =? fail) with true in HO by (symmetry; apply Z.eqb_eq; lia).
    discriminate HO.
  - exact (proj1 (G7_2 jr_strtod x ok j Hj Hf Hu)).
Qed.

Lemma pp_c18 : forall x ok cnt fail, oks ok cnt fail (calls (snd (jr_run jr_strtod x ok))) ->
  (fail < cnt \/ cnt + Z.of_nat (ncalls jr_strtod x) <= fail) ->
  jr_run jr_strtod x ok = (json_read jr_strtod x, snd (jr_run jr_strtod x [])) /\
  calls (snd (jr_run jr_strtod x ok)) = ncalls jr_strtod x.
Proof.
  intros x ok cnt fail HO HF.
  destruct (ok_upto_dec ok (ncalls jr_strtod x)) as [Hu | (j & Hj & Hf & Hu)].
  - split; [exact (G7_1 jr_strtod x ok Hu) | exact (G7_1_calls jr_strtod x ok Hu)].
  - exfalso. destruct (G7_2 jr_strtod x ok j Hj Hf Hu) as [_ HC]. rewrite HC in HO.
    specialize (HO j ltac:(lia)). rewrite Hf in HO.
    destruct (Z.eqb_spec (cnt + Z.of_nat j) fail); [lia | cbn in HO; discriminate HO].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YK14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import parse_value_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Module YK11 := YK11.
Module YM05 := YM05.
Module MemNorm := U.MemNorm.
Module strtod_c := U.Prog.strtod_c.
Local Open Scope Z_scope.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEG : ms_segs B = rsegs.

Lemma pp_frame_bytes : forall m A j a b c d e, rw_cells rsegs m A [CB 8 j; C8 a; C8 b; C8 c; C8 d; C8 e] ->
  bytes_at rsegs m (A + 8) (le8 a) /\ bytes_at rsegs m (A + 16) (le8 b) /\ bytes_at rsegs m (A + 24) (le8 c) /\
  wr_at rsegs m (A + 8) 24 /\ rw_cells rsegs m (A + 32) [C8 d; C8 e].
Proof.
  intros m A j a b c d e [[Hwf Hb] (W1 & W2 & W3)].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Hj & _).
  cbn [cells_bytes cbytes cells_size csize] in Hb, W2, W3.
  apply bytes_at_app in Hb as [_ Hb]. rewrite Hj in Hb. change (Z.of_nat 8) with 8 in Hb.
  apply bytes_at_app in Hb as [Ha Hb]. rewrite length_le8 in Hb. change (A + 8 + Z.of_nat 8) with (A + 8 + 8) in Hb.
  apply bytes_at_app in Hb as [Hbb Hb]. rewrite length_le8 in Hb.
  apply bytes_at_app in Hb as [Hc Hb]. rewrite length_le8 in Hb.
  split; [exact Ha|].
  split; [replace (A + 16) with (A + 8 + 8) by lia; exact Hbb|].
  split; [replace (A + 24) with (A + 8 + 8 + Z.of_nat 8) by (cbn; lia); exact Hc|].
  split; [split; [lia|]; split; [cbn in W2; lia|]; intros i Hi; replace (A + 8 + i) with (A + (8 + i)) by lia; apply W3; cbn; lia|].
  split; [split; [cbn; tauto|]; replace (A + 32) with (A + 8 + 8 + Z.of_nat 8 + Z.of_nat 8) by (cbn; lia); exact Hb|].
  split; [lia|]. split; [cbn in W2 |- *; lia|]. intros i Hi. replace (A + 32 + i) with (A + (32 + i)) by lia. apply W3. cbn in Hi |- *. lia.
Qed.

Definition pp_after_pro (regs : bvmap 5 word) (mem : word -> option byte) (S t0 len out : Z) (ms1 : machine_state) : Prop :=
  exists regs1 mem1 j,
    ms1 = @mkst fx regs1 (Z_to_bv 64 0x16044) mem1 (seg_rom rsegs) /\
    getr regs1 1 = Z_to_bv 64 0x16004 /\ spZ regs1 = S - 48 /\
    getr regs1 10 = Z_to_bv 64 (S - 40) /\ getr regs1 11 = Z_to_bv 64 out /\ getr regs1 8 = Z_to_bv 64 out /\
    (forall r, r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
    munch [(S - 48, S); (out, out + 56)] mem mem1 /\ wmono rsegs mem mem1 /\ MemNorm.ro_same rsegs mem mem1 /\
    rw_cells rsegs mem1 (S - 48)
      [CB 8 j; C8 (Z_to_bv 64 t0); C8 (Z_to_bv 64 (t0 + len)); C8 (Z_to_bv 64 0); C8 (reg_get regs 8); C8 (reg_get regs 1)] /\
    rw_cells rsegs mem1 out [CB 56 (repeat (Z_to_bv 8 0) 56)].

Lemma pp_stage_pro : memset_contract -> forall regs mem md (P : config -> Prop) t0 len out K,
  m_halted md = None -> m_vm_lazy md = [] -> MemNorm.ro_agree rsegs mem ->
  (forall a, spZ regs - K <= a < spZ regs -> writable_at rsegs mem a) -> alloc_ceiling + K <= spZ regs -> 48 <= K ->
  getr regs 10 = Z_to_bv 64 t0 -> getr regs 11 = Z_to_bv 64 len -> getr regs 12 = Z_to_bv 64 out ->
  0 < t0 -> 0 <= len -> t0 + len < 2 ^ 62 ->
  pj_rw rsegs mem out -> (forall i, 0 <= i < 56 -> ~ in_img B (out + i)) -> out + 56 <= spZ regs - K \/ spZ regs <= out ->
  (forall ms1, pp_after_pro regs mem (spZ regs) t0 len out ms1 -> SR (ms_segs B) (mkCfg ms1 md) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 PJ_PARSE) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros MEMSET regs mem md P t0 len out K Hh Hl RO HWS HAC HK R10 R11 R12 T0 L0 TE PRW NI DJ CONT.
  pose proof rk_ceil as HC.
  pose proof (zr_word (getr regs 2)) as Rsp. unfold inr64 in Rsp.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 t0) by exact R10.
  assert (E11 : reg_get regs 11 = Z_to_bv 64 len) by exact R11.
  assert (E12 : reg_get regs 12 = Z_to_bv 64 out) by exact R12.
  assert (ES : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in Rsp.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite rk_canon. rewrite SEG. unfold mkR_of. rewrite E10, E11, E12.
    apply (MemNorm.evt_normalize rsegs); [exact rk_wx | exact RO |].
    eapply (pp_pro MEMSET) with (lo := spZ regs - K).
    - rewrite ES. apply rk_stk_norm; [intros a Ha; apply rk_high_nofs; lia|].
      apply rk_stk_of_wr; [lia | lia | exact HWS].
    - rewrite ES. lia.
    - apply MemNorm.mem_inv_normalize.
    - lia.
    - lia.
    - lia.
    - destruct PRW as [AL PS]. split; [exact AL|]. apply rk_stk_norm; [|exact PS].
      intros a Ha. apply (rk_noimg_fs SEG). replace a with (out + (a - out)) by lia. apply NI. lia.
    - rewrite ES. exact DJ. }
  intros ms1 (can & (s0 & Q0 & REL & ROS) & EQV). apply CONT.
  destruct Q0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' & j & Es0 &
    FR & MU & WM & MI & OZ).
  subst s0.
  destruct (rk_rel_shape _ _ _ _ _ _ REL EQV) as (Ems & XR & MR1).
  rewrite ES in FR, MU.
  replace (spZ regs + -48) with (spZ regs - 48) in FR, MU by lia.
  exists (ms_regs ms1), (ms_mem can), j.
  split; [exact Ems|].
  split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
  split.
  { unfold spZ. rewrite (rk_getr_eqv _ _ XR). change (bv_unsigned (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -48)) = spZ regs - 48).
    rewrite ES. rewrite unsigned_lit by lia. lia. }
  split.
  { rewrite (rk_getr_eqv _ _ XR). change (Z_to_bv 64 (bv_unsigned (reg_get regs 2) + -40) = Z_to_bv 64 (spZ regs - 40)).
    rewrite ES. f_equal; lia. }
  split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
  split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
  split.
  { intros r Hr. rewrite (rk_getr_eqv _ _ XR).
    assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                 r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]; reflexivity. }
  pose proof (MemNorm.mem_rel_normalize rsegs mem RO) as MR0.
  split; [exact (MemNorm.munch_rel rsegs _ _ _ _ _ MR0 MR1 ROS MU)|].
  split; [exact (MemNorm.wmono_rel rsegs _ _ _ _ MR0 MR1 ROS WM)|].
  split; [exact ROS|].
  split; [exact (rk_rw_cells_rel _ _ _ _ MR1 FR)|].
  exact (rk_rw_cells_rel _ _ _ _ MR1 OZ).
Qed.

Lemma pp_final_regs : forall regs regsP R' x5 x6 x7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  xregs_eqv (mkR (reg_get regs 1) (Z_to_bv 64 (bv_unsigned (reg_get regsP 2) + 48)) (reg_get regsP 3) (reg_get regsP 4)
     x5 x6 x7 (reg_get regs 8) (reg_get regsP 9) (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
     (reg_get regsP 18) (reg_get regsP 19) (reg_get regsP 20) (reg_get regsP 21) (reg_get regsP 22) (reg_get regsP 23)
     (reg_get regsP 24) (reg_get regsP 25) (reg_get regsP 26) (reg_get regsP 27) x28 x29 x30 x31) R' ->
  spZ regsP + 48 = spZ regs -> rk_cs regs regsP ->
  regs_preserved regs R' /\ getr R' 10 = Z_to_bv 64 v.
Proof.
  intros regs regsP R' x5 x6 x7 v x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 XR HS CS.
  split; [|rewrite (rk_getr_eqv _ _ XR); reflexivity].
  intros r Hr. unfold callee_saved in Hr.
  assert (Hc : r = 2 \/ r = 8 \/ (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27)) by lia.
  destruct Hc as [-> | [-> | Hc]].
  - rewrite (rk_getr_eqv _ _ XR).
    change (Z_to_bv 64 (bv_unsigned (reg_get regsP 2) + 48) = getr regs 2).
    change (bv_unsigned (reg_get regsP 2)) with (spZ regsP). rewrite HS. exact (Z_to_bv_lit_self (getr regs 2)).
  - rewrite (rk_getr_eqv _ _ XR). reflexivity.
  - pose proof (rk_cs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as CS'.
    exact (rk_cs_trans _ _ _ CS CS' r Hc).
Qed.

Lemma pj_parse_main : skip_ws_c.skip_ws_contract -> memset_contract -> parse_value_contract B API RF 0 ->
  (forall fx', @pj_free_contract fx' rc B API RF) ->
  pj_parse_contract B API RF.
Proof.
  intros SW MEMSET PV PF. unfold pj_parse_contract.
  intros L A regs mem md Lam peak cnt fail b t0 len out tb ENV LG RES R10 R11 R12 LEN T0 TE TL TB MXR TOK ONZ PRW RPL
    OUTL DJT DJS CNT ROOM.
  pose proof ENV as (_ & TP & ERR & GG & GD & PRE & SP47 & GTOP & FRM & RDC).
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & HAUX).
  destruct (mr_model B _ (aa_laws API) L A mem md HM) as (Hh & Hl & _).
  pose proof RDC as (RO & RGG & RGD).
  pose proof RPL as (PLC & PAUX & PEX).
  pose proof rk_ceil as HCEIL.
  pose proof (zr_word (getr regs 2)) as Rsp. unfold inr64 in Rsp. change (bv_unsigned (getr regs 2)) with (spZ regs) in Rsp.
  assert (HK : 48 + PARSE_VALUE_K 0 <= PJ_PARSE_K /\ 48 + PJ_FREE_K 33 <= PJ_PARSE_K /\
               0 <= PARSE_VALUE_K 0 /\ 0 <= PJ_FREE_K 33).
  { unfold PJ_PARSE_K, PJ_PARSE_F. split; [lia|]. split; [lia|]. split; vm_compute; discriminate. }
  cbn [disjoint_from] in DJS, DJT.
  assert (OUTS : spZ regs <= out \/ out + 56 <= spZ regs - PJ_PARSE_K) by lia.
  assert (TXS : spZ regs <= t0 \/ t0 + len <= spZ regs - PJ_PARSE_K) by lia.
  assert (LEN0 : 0 <= len) by lia.
  assert (ERRL : errno_addr B + 4 <= 2 ^ 33) by (rewrite ERR; unfold strtod_c.STRTOD_ERRNO; lia).
  assert (STL : forall a, alloc_statics a -> 0 <= a < 2 ^ 33) by (intros a Ha; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia).
  assert (OWL : forall L0 A0 mem0 md0 x, aa_MR API L0 A0 mem0 md0 -> owned B L0 A0 x -> 0 <= x < alloc_ceiling)
    by (intros L0 A0 mem0 md0 x HM0 Ho; exact (mr_owned_low B _ (aa_laws API) L0 A0 mem0 md0 x HM0 Ho)).
  assert (OUTN : forall x, out <= x < out + 56 -> ~ owned B L A x /\ ~ alloc_statics x /\
                  ~ (errno_addr B <= x < errno_addr B + 4) /\ ~ in_img B x).
  { intros x Hx. replace x with (out + (x - out)) by lia. apply PEX. lia. }
  rewrite SEG in RO, HWS, PRW, TB.
  eapply (pp_stage_pro MEMSET regs mem md _ t0 len out PJ_PARSE_K); try assumption;
    [lia | intros i Hi; exact (proj2 (proj2 (proj2 (PEX i Hi)))) | lia |].
  intros ms1 (regs1 & mem1 & j & -> & G1 & S1 & G10 & G11 & G8 & GCS & MU1 & WM1 & ROS1 & FR1 & OZ1).
  pose proof (MemNorm.ro_agree_same rsegs mem mem1 RO ROS1) as RO1.
  destruct (pp_frame_bytes _ _ _ _ _ _ _ _ FR1) as (Bq & Be & Bd & Wq & SAV1).
  assert (W1 : forall x, 0 <= x < 2 ^ 64 -> ~ outside [(spZ regs - 48, spZ regs); (out, out + 56)] x ->
                (spZ regs - 48 <= x < spZ regs) \/ (out <= x < out + 56)).
  { intros x Hx Ho. cbn [outside] in Ho. lia. }
  assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 48 <= x < spZ regs) -> ~ (out <= x < out + 56) ->
                   mbyte (ms_segs B) mem1 x = mbyte (ms_segs B) mem x).
  { intros x Hx H1 H2. apply (MemNorm.mbyte_munch _ _ _ _ _ MU1); [exact Hx|]. cbn [outside]. tauto. }
  assert (OWK1 : forall x, owned B L A x -> mbyte (ms_segs B) mem1 x = mbyte (ms_segs B) mem x).
  { intros x Ho. pose proof (OWL _ _ _ _ x HM Ho). apply KEEP1; [lia | lia |].
    intros Hx. exact (proj1 (OUTN x Hx) Ho). }
  assert (HM1 : aa_MR API L A mem1 md).
  { apply (rk_MR_A SEG L A mem mem1 md _ HM MU1); [rewrite SEG; exact WM1 | |].
    - intros x Ho. pose proof (OWL _ _ _ _ x HM Ho). cbn [outside]. split; [lia|]. split; [|exact I].
      intros Hx. exact (proj1 (OUTN x Hx) Ho).
    - intros x Hx Ho. destruct (W1 x Hx Ho) as [Hs|Hs].
      + intros Hi. pose proof (rk_img_bound SEG x Hi). lia.
      + exact (proj2 (proj2 (proj2 (OUTN x Hs)))). }
  assert (WM1' : wmono (ms_segs B) mem mem1) by (rewrite SEG; exact WM1).
  assert (HEADS : forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ (out <= a - 16 + i < out + 56)).
  { intros a k i HI Hi Hx.
    pose proof LG as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ HI) as (Hk & HB & _ & _).
    cbn [fst snd] in Hk, HB.
    pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM LG HI) as (Ra & Rb & _).
    unfold pj_place in PLC.
    destruct PLC as [P1 | [(a' & k' & HB' & NL & Pa & Pb) | (a' & k' & HL' & Pa & Pb)]].
    - lia.
    - destruct (Z.eq_dec a' (a - 16)) as [E1|E1]; [destruct (Z.eq_dec k' (k + 16)) as [E2|E2]|].
      + apply NL. unfold lin. replace (a' + 16) with a by lia. replace (k' - 16) with k by lia. exact HI.
      + pose proof (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) as PW.
        destruct (rk_pairwise_in _ _ _ _ PW HB HB' ltac:(intros E; injection E as E3 E4; lia)) as [R|R];
          unfold ranges_disjoint in R; cbn [fst snd] in R; lia.
      + pose proof (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) as PW.
        destruct (rk_pairwise_in _ _ _ _ PW HB HB' ltac:(intros E; injection E as E3 E4; lia)) as [R|R];
          unfold ranges_disjoint in R; cbn [fst snd] in R; lia.
    - destruct (OUTL a' k' HL'); lia. }
  assert (LG1 : ledger B L A mem1 Lam peak cnt fail).
  { apply (rk_ledger_keep L A mem mem1 Lam peak cnt fail LG).
    - intros a Ha. pose proof (STL a Ha). apply KEEP1; [lia | lia |]. intros Hx. exact (proj1 (proj2 (OUTN a Hx)) Ha).
    - intros a k i HI Hi. pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM LG HI) as (Ra & Rb & _).
      pose proof LG as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ HI) as (Hk & _). cbn [fst snd] in Hk.
      apply KEEP1; [lia | lia | exact (HEADS a k i HI Hi)]. }
  assert (LIBK1 : forall i, 0 <= i < 8 -> mbyte (ms_segs B) mem1 (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)).
  { intros i Hi. apply OWK1. right. unfold static_owned. right; right; left; lia. }
  assert (AUXB1 : st_init_done A = false ->
    (spZ regs <= out /\ auxv_pre B (ly_sec L) (out + 56) mem1) \/
    (out + 56 <= spZ regs - PJ_PARSE_K /\ auxv_pre B (ly_sec L) (spZ regs) mem1)).
  { intros HI. destruct OUTS as [Ho|Ho]; [left | right]; (split; [exact Ho|]).
    - apply (rk_auxv_keep _ _ mem mem1 (PAUX Ho HI) LIBK1). intros a Ha. apply KEEP1; lia.
    - apply (rk_auxv_keep _ _ mem mem1 (HAUX HI) LIBK1). intros a Ha. apply KEEP1; lia. }
  assert (TB1 : bytes_at rsegs mem1 t0 tb).
  { apply (bytes_at_transport rsegs _ mem mem1 t0 tb TB MU1). rewrite TL. cbn [disjoint_from]. lia. }
  assert (RDC1 : rd_cells B mem1).
  { split; [rewrite SEG; exact RO1|]. split.
    - apply (rk_word_keep mem mem1 _ _ RGG). intros k Hk. apply OWK1. right. unfold static_owned. do 4 right. left. lia.
    - destruct RGD as (g & Hg). exists g. apply (rk_word_keep mem mem1 _ _ Hg). intros k Hk. apply OWK1. right.
      unfold static_owned. do 5 right. left. lia. }
  assert (PIN : pj_in_ok (ms_segs B) mem1 (spZ regs - 40) t0 len t0 (Z.of_nat 0) tb).
  { rewrite SEG. unfold pj_in_ok.
    replace (spZ regs - 40) with (spZ regs - 48 + 8) by lia.
    split; [exact Bq|].
    split; [replace (spZ regs - 48 + 8 + 8) with (spZ regs - 48 + 16) by lia; exact Be|].
    split.
    { replace (spZ regs - 48 + 8 + 16) with (spZ regs - 48 + 24) by lia. change (Z.of_nat 0) with 0.
      rewrite pj_le8_0 in Bd. rewrite pj_le4_0.
      change (repeat (Z_to_bv 8 0) 8) with (repeat (Z_to_bv 8 0) 4 ++ repeat (Z_to_bv 8 0) 4) in Bd.
      apply bytes_at_app in Bd. exact (proj1 Bd). }
    split; [exact Wq|].
    split; [Z.div_mod_to_equations; lia|].
    split; [exact T0|]. split; [exact TE|]. split; [lia|]. split; [exact TL|]. split; [exact TB1|].
    split; [cbn [disjoint_from]; lia|]. lia. }
  assert (REST0 : rest_at tb t0 t0 = zb tb) by (unfold rest_at; rewrite Z.sub_diag; reflexivity).
  replace (seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite SEG; reflexivity).
  eapply SR_bind.
  { apply (PV L A regs1 mem1 md Lam peak cnt fail b (spZ regs - 40) t0 len t0 tb out).
    - split; [exact SEG|]. split; [exact TP|]. split; [exact ERR|]. split; [exact GG|]. split; [exact GD|].
      split.
      { split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite G1; apply ret_ok_even; vm_compute; reflexivity|].
        split; [rewrite S1; Z.div_mod_to_equations; lia|].
        split; [rewrite S1; lia|].
        split; [rewrite S1; lia|].
        split; [intros a Ha; rewrite S1 in Ha; unfold writable_at; apply WM1'; rewrite SEG; apply HWS; lia|].
        split; [transitivity (getr regs1 (Z_to_bv 5 4)); [reflexivity|]; rewrite (GCS 4 ltac:(lia)); exact HTP|].
        split; [intros a Ha; unfold writable_at; apply WM1'; apply HER; exact Ha|].
        intros HI. rewrite S1. destruct (AUXB1 HI) as [[Ho AV]|[Ho AV]]; (eapply auxv_pre_mono; [|exact AV]); lia. }
      split; [rewrite S1; lia|]. split; [rewrite S1; lia|]. split; [exact FRM|]. exact RDC1.
    - exact LG1.
    - exact RES.
    - exact G10.
    - exact G11.
    - exact PIN.
    - rewrite S1. lia.
    - intros HI. destruct (AUXB1 HI) as [[Ho AV]|[Ho AV]]; (eapply auxv_pre_mono; [|exact AV]); lia.
    - exact MXR.
    - destruct TOK as [TK1 TK2]. split; [|exact TK2].
      destruct TK1 as [H|H]; [left; rewrite S1; lia | right; exact H].
    - exact ONZ.
    - split; [split; [exact (proj1 PRW) | rewrite SEG; exact (stk_of_rw_cells rsegs mem1 out _ OZ1)]|].
      rewrite SEG. destruct OZ1 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
    - split; [|split; [|exact PEX]].
      + unfold pj_place in PLC |- *. destruct PLC as [P1|[P2|P3]]; [left; rewrite S1; lia | right; left; exact P2 | right; right; exact P3].
      + intros Hs HI. rewrite S1 in Hs. destruct (AUXB1 HI) as [[_ AV]|[Ho _]]; [exact AV | lia].
    - cbn [disjoint_from]. lia.
    - rewrite S1. cbn [disjoint_from]. lia.
    - rewrite REST0. unfold zb. rewrite length_map. lia.
    - rewrite REST0. rewrite (jr_run_eq jr_strtod (zb tb) []) in ROOM. exact ROOM. }
  intros c2 (fx2 & L1 & A1 & regs2 & mem2 & md1 & Lam1 & peak1 & cnt1 & fail1 & ok & res & tr & okr & D & -> & FRM2 &
    FK2 & RP2 & RDC2 & LG2 & JV & OKS & CNT1 & FA1 & PERM1 & HELD & NLV & NB & PK1 & HP1 & RES1 & ARM).
  rewrite REST0 in JV, HP1.
  pose proof RP2 as (M2 & WF2 & B2 & Y2 & I2 & X2 & G2 & S2' & P2 & RP2r & D2 & H2 & IM2 & K2 & C2).
  destruct (mr_model B _ (aa_laws API) L1 A1 mem2 md1 M2) as (Hh1 & Hl1 & _).
  assert (SP2 : spZ regs2 = spZ regs - 48).
  { rewrite <- S1. unfold spZ. change (bv_unsigned (getr regs2 (Z_to_bv 5 2)) = bv_unsigned (getr regs1 (Z_to_bv 5 2))).
    rewrite (RP2r 2); [reflexivity | unfold callee_saved; lia]. }
  assert (CS2 : rk_cs regs regs2) by exact (rk_cs_rp regs regs1 regs2 GCS RP2r).
  assert (G82 : getr regs2 8 = Z_to_bv 64 out).
  { transitivity (getr regs2 (Z_to_bv 5 8)); [reflexivity|]. rewrite (RP2r 8); [exact G8 | unfold callee_saved; lia]. }
  assert (DF : forall a k, In (a, k) D -> In (a - 16, k + 16) (blocks L1 A1) /\ 4112 <= a /\ a + k <= alloc_ceiling /\
                 0 <= k /\ (forall i, -16 <= i < k -> ~ in_img B (a + i)))
    by (intros a k HD; exact (rk_D_facts L1 A1 mem2 md1 Lam1 peak1 cnt1 fail1 D Lam a k M2 LG2 PERM1 HD)).
  assert (BLKH : forall x, alloc_ceiling <= x -> ~ blk_set D x).
  { intros x Hx (a & k & HD & Hr). destruct (DF a k HD) as (_ & _ & R2 & _). lia. }
  assert (BLKI : forall x, in_img B x -> ~ blk_set D x).
  { intros x Hx (a & k & HD & Hr). destruct (DF a k HD) as (_ & _ & _ & Hk & NI). apply (NI (x - a)); [lia|].
    replace (a + (x - a)) with x by lia. exact Hx. }
  assert (BLKB : forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> 0 <= i < n ->
                   ~ blk_set D (ptr_addr L p + i)).
  { intros p n i Hp Hp1 Hi (a & k & HD & Hr). destruct (DF a k HD) as (HB & _).
    exact (rk_fresh L A L1 A1 mem2 md1 D p n i a k M2 NB Hp Hp1 (P2 p n Hp Hp1) HD HB Hi Hr). }
  assert (WRQ2 : Mem.wr_at (ms_segs B) mem2 (spZ regs - 40) 24).
  { destruct res as [[t r]|].
    - destruct ARM as (_ & (_ & _ & _ & W & _) & _). exact W.
    - destruct ARM as (_ & (p' & d' & _ & _ & _ & _ & _ & W) & _). exact W. }
  assert (NE1 : forall a, ~ (out <= a < out + 56) -> ~ alloc_statics a -> ~ pj_in_set (spZ regs - 40) a ->
                  ~ blk_set D a -> ~ rd_writes (spZ regs - 40) out D a).
  { intros a N1 N2 N3 N4 [H|[H|[H|H]]]; tauto. }
  assert (RPA : rpost B API PJ_PARSE_K L A regs mem md (pj_parse_writes out) (fun _ _ => False) L A regs mem1 md).
  { assert (LB1 : 0 <= ms_libc B + 8 /\ ms_libc B + 16 <= alloc_ceiling).
    { pose proof (OWL _ _ _ _ (ms_libc B + 8) HM ltac:(right; unfold static_owned; right; right; left; lia)).
      pose proof (OWL _ _ _ _ (ms_libc B + 15) HM ltac:(right; unfold static_owned; right; right; left; lia)). lia. }
    apply (rk_of_A SEG PJ_PARSE_K L A regs mem md _ mem1 [(spZ regs - 48, spZ regs); (out, out + 56)] regs HM1 HWF HBD).
    - intros r _. reflexivity.
    - exact MU1.
    - exact WM1'.
    - intros a [Ha|Ha]; [rewrite SEG; apply HWS; exact Ha | apply HER; exact Ha].
    - intros x Hx Hs He. unfold scratch_k, pj_parse_writes in Hs, He. cbn [outside]. split; [lia|]. split; [|exact I]. tauto.
    - intros i Hi. cbn [outside]. split; [lia|]. split; [|exact I].
      intros Hx. exact (proj1 (OUTN _ Hx) ltac:(right; unfold static_owned; right; right; left; lia)).
    - lia.
    - lia.
    - intros p n i Hp Hi He. destruct (mr_blocks B _ (aa_laws API) L A mem md p n i HM Hp Hi) as (_ & R1 & R2 & _).
      unfold pj_parse_writes in He. split; [lia|]. cbn [outside]. split; [lia|]. split; [|exact I]. tauto. }
  assert (RPV : rpost B API PJ_PARSE_K L A regs mem md (pj_parse_writes out) (fun _ _ => False) L1 A1 regs mem2 md1).
  { apply (rk_seq PJ_PARSE_K L A regs mem md _ L A regs mem1 md (PARSE_VALUE_K 0) regs1 _ _ L1 A1 regs2 mem2 md1 regs
      RPA RP2).
    - intros r _. reflexivity.
    - rewrite S1. lia.
    - rewrite S1. lia.
    - exact HAC.
    - lia.
    - intros a Ha Hs He. unfold scratch_k, pj_parse_writes in Hs, He.
      apply NE1; [tauto | tauto | unfold pj_in_set; lia | apply BLKH; lia].
    - intros a Ha Hs He. pose proof (rk_img_bound SEG a Ha). unfold scratch_k, pj_parse_writes in Hs, He.
      apply NE1; [tauto | tauto | unfold pj_in_set; lia | apply BLKI; exact Ha].
    - intros p n i Hp Hp1 Hi He. destruct (mr_blocks B _ (aa_laws API) L A mem md p n i HM Hp Hi) as (_ & R1 & R2 & _).
      unfold pj_parse_writes in He. apply NE1; [tauto | tauto | unfold pj_in_set; lia |].
      exact (BLKB p n i Hp (S2' p n Hp ltac:(tauto)) Hi).
    - intros p n _ _ F. exact F.
    - intros a Ha Hd. unfold scratch_k in Ha, Hd. rewrite S1 in Hd.
      assert (Hq : (spZ regs - 40 <= a < spZ regs - 32 \/ spZ regs - 24 <= a < spZ regs - 20) \/
                   ~ (spZ regs - 40 <= a < spZ regs - 32 \/ spZ regs - 24 <= a < spZ regs - 20)) by lia.
      destruct Hq as [Hq|Hq].
      + right. destruct WRQ2 as (_ & _ & W). unfold writable_at.
        replace a with (spZ regs - 40 + (a - (spZ regs - 40))) by lia. apply W. lia.
      + left. apply NE1; [lia | intros Hs; pose proof (STL a Hs); lia | unfold pj_in_set; lia | apply BLKH; lia]. }
  assert (AUXB2 : st_init_done A1 = false ->
    (spZ regs <= out /\ auxv_pre B (ly_sec L) (out + 56) mem2) \/
    (out + 56 <= spZ regs - PJ_PARSE_K /\ auxv_pre B (ly_sec L) (spZ regs) mem2)).
  { intros HI1. assert (HI : st_init_done A = false)
      by (case_eq (st_init_done A); intros E; [rewrite (I2 E) in HI1; discriminate HI1 | reflexivity]).
    assert (KH : forall a, spZ regs <= a < 2 ^ 63 -> ~ (out <= a < out + 56) ->
                   mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a).
    { intros a Ha Ho. refine (proj1 (H2 a _ _ _)); [lia | unfold scratch_k; rewrite S1; lia |].
      apply NE1; [exact Ho | intros Hs; pose proof (STL a Hs); lia | unfold pj_in_set; lia | apply BLKH; lia]. }
    destruct (AUXB1 HI) as [[Ho AV]|[Ho AV]]; [left|right]; (split; [exact Ho|]);
      (apply (rk_auxv_keep _ _ mem1 mem2 AV (X2 HI1)); intros a Ha; apply KH; lia). }
  assert (SAV2 : rw_cells rsegs mem2 (spZ regs - 48 + 32) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rk_rw_cells_keep mem1 mem2 _ _ SAV1). intros i Hi. cbn in Hi.
    destruct (H2 (spZ regs - 48 + 32 + i)) as [E1 E2]; [lia | unfold scratch_k; rewrite S1; lia | | ].
    - apply NE1; [lia | intros Hs; pose proof (STL _ Hs); lia | unfold pj_in_set; lia | apply BLKH; lia].
    - rewrite SEG in E1, E2. split; [exact E1 | tauto]. }
  assert (OUTB1 : spZ regs <= out \/ exists a' k', In (a', k') (blocks L1 A1) /\ ~ lin Lam1 (a' + 16) (k' - 16) /\
                    a' <= out /\ out + 56 <= a' + k').
  { unfold pj_place in PLC. destruct PLC as [P1|[(a' & k' & HB' & NL & Pa & Pb)|(a' & k' & HL' & Pa & Pb)]].
    - left. lia.
    - right. exists a', k'. destruct (rk_blk_user L A a' k' HB') as (p & Hp & Ep).
      assert (Hp1 : In (p, k') (user_blocks A1)) by (apply S2'; [exact Hp | tauto]).
      split; [rewrite <- Ep, <- (P2 p k' Hp Hp1); exact (rk_blk_of_user L1 A1 p k' Hp1)|].
      split; [|split; assumption].
      intros HL1. unfold lin in HL1. apply (Permutation_in _ PERM1) in HL1. apply in_app_or in HL1.
      destruct HL1 as [HD|HLm].
      + apply (NB _ _ HD). replace (a' + 16 - 16) with a' by lia. replace (k' - 16 + 16) with k' by lia. exact HB'.
      + exact (NL HLm).
    - exfalso. destruct (OUTL a' k' HL'); lia. }
  assert (RUN : jr_run jr_strtod (zb tb) ok = (post res, tr)) by (rewrite jr_run_eq, JV; reflexivity).
  assert (KEEP : forall mem2', munch [(spZ regs - 40, spZ regs - 32)] mem2 mem2' -> wmono rsegs mem2 mem2' ->
    aa_MR API L1 A1 mem2' md1 /\ ledger B L1 A1 mem2' Lam1 peak1 cnt1 fail1 /\ rd_cells B mem2' /\
    rpost B API PJ_PARSE_K L A regs mem md (pj_parse_writes out) (fun _ _ => False) L1 A1 regs mem2' md1 /\
    rw_cells rsegs mem2' (spZ regs - 48 + 32) [C8 (reg_get regs 8); C8 (reg_get regs 1)] /\
    (st_init_done A1 = false ->
      (spZ regs <= out /\ auxv_pre B (ly_sec L) (out + 56) mem2') \/
      (out + 56 <= spZ regs - PJ_PARSE_K /\ auxv_pre B (ly_sec L) (spZ regs) mem2')) /\
    (forall a, scratch_k B (PARSE_VALUE_K 0) regs1 a -> writable_at (ms_segs B) mem2' a) /\
    (forall a, spZ regs - PJ_PARSE_K <= a < spZ regs - 48 - PARSE_VALUE_K 0 -> writable_at (ms_segs B) mem2' a) /\
    (forall t D', pj_node (ms_segs B) mem2 (lin Lam1) out t D' ->
       (forall a k, In (a, k) D' -> lin Lam1 a k /\ a + k <= alloc_ceiling) ->
       pj_node (ms_segs B) mem2' (lin Lam1) out t D')).
  { intros mem2' MUs WMs.
    assert (WMs' : wmono (ms_segs B) mem2 mem2') by (rewrite SEG; exact WMs).
    assert (KS : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 40 <= x < spZ regs - 32) ->
                   mbyte (ms_segs B) mem2' x = mbyte (ms_segs B) mem2 x).
    { intros x Hx Hn. apply (MemNorm.mbyte_munch _ _ _ _ _ MUs); [exact Hx|]. cbn [outside]. split; [lia | exact I]. }
    assert (M2' : aa_MR API L1 A1 mem2' md1).
    { apply (rk_MR_A SEG L1 A1 mem2 mem2' md1 _ M2 MUs WMs').
      - intros x Ho. pose proof (OWL _ _ _ _ x M2 Ho). cbn [outside]. split; [lia | exact I].
      - intros x Hx Ho Hi. pose proof (rk_img_bound SEG x Hi).
        destruct (Z_lt_le_dec x (spZ regs - 40)) as [Q|Q]; [exfalso; apply Ho; cbn [outside]; split; [lia | exact I]|].
        lia. }
    split; [exact M2'|].
    split.
    { apply (rk_ledger_keep L1 A1 mem2 mem2' Lam1 peak1 cnt1 fail1 LG2).
      - intros a Ha. pose proof (STL a Ha). apply KS; lia.
      - intros a k i HI Hi.
        pose proof (ledger_block_range B API L1 A1 mem2 md1 Lam1 peak1 cnt1 fail1 a k M2 LG2 HI) as (Ra & Rb & _).
        pose proof LG2 as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF. destruct (HF _ HI) as (Hk & _).
        cbn [fst snd] in Hk. apply KS; lia. }
    split.
    { destruct RDC2 as (RO2 & RG2 & (g & RD2)). split; [|split].
      - apply (MemNorm.ro_agree_same _ mem2 mem2' RO2). intros w Hw. apply MUs. cbn [outside]. split; [|exact I].
        revert Hw. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.ro_addr.
        match goal with |- context [find_segment ?sg ?ad ?nn] => destruct (find_segment sg ad nn) as [s|] eqn:E end;
          intros Hw; [|discriminate Hw].
        rewrite ?SEG in E. destruct (rk_fs_some _ _ _ _ E) as (Hin & Hs1 & Hs2). pose proof (rk_seg_top s Hin). lia.
      - apply (rk_word_keep mem2 mem2' _ _ RG2). intros k Hk. apply KS; rewrite GG; unfold strtod_c.STRTOD_GOT_GUARD; lia.
      - exists g. apply (rk_word_keep mem2 mem2' _ _ RD2). intros k Hk. apply KS; rewrite GD; unfold strtod_c.STRTOD_GUARD; lia. }
    split.
    { apply (rk_scr SEG PJ_PARSE_K L A regs mem md _ _ L1 A1 regs mem2 md1 mem2' [(spZ regs - 40, spZ regs - 32)] RPV M2' MUs WMs').
      - intros x Hx Ho.
        destruct (Z_lt_le_dec x (spZ regs - 40)) as [Q|Q]; [exfalso; apply Ho; cbn [outside]; split; [lia | exact I]|].
        destruct (Z_lt_le_dec x (spZ regs - 32)) as [Q'|Q']; [lia|].
        exfalso; apply Ho; cbn [outside]; split; [lia | exact I].
      - lia. }
    split.
    { apply (rw_cells_transport rsegs [(spZ regs - 40, spZ regs - 32)] mem2 mem2' _ _ SAV2 MUs WMs).
      cbn [disjoint_from cells_size csize]. lia. }
    split.
    { intros HI1. destruct (AUXB2 HI1) as [[Ho AV]|[Ho AV]]; [left|right]; (split; [exact Ho|]);
        (apply (rk_auxv_keep _ _ mem2 mem2' AV);
         [intros i Hi; pose proof (OWL _ _ _ _ (ms_libc B + 8 + i) M2 ltac:(right; unfold static_owned; right; right; left; lia));
          apply KS; lia
         | intros a Ha; apply KS; lia]). }
    split; [intros a Ha; unfold writable_at; apply WMs'; exact (C2 a Ha)|].
    split.
    { intros a Ha. unfold writable_at. apply WMs'.
      destruct (H2 a ltac:(lia) ltac:(unfold scratch_k; rewrite S1; lia)
                  ltac:(apply NE1; [lia | intros Hs; pose proof (STL a Hs); lia | unfold pj_in_set; lia | apply BLKH; lia]))
        as [_ HW2].
      apply HW2. unfold writable_at. apply WM1'. rewrite SEG. apply HWS. lia. }
    intros t D' PN HD. eapply (pj_node_munch (ms_segs B) [(spZ regs - 40, spZ regs - 32)]); [exact PN | | exact MUs |].
    - intros a k Hk. exact (proj1 (HD a k Hk)).
    - intros z [Hz|(bb & Hb & Hz)]; cbn [outside]; (split; [|exact I]).
      + lia.
      + destruct bb as [a k]. unfold pj_holds in Hz. cbn [fst snd] in Hz. pose proof (proj2 (HD a k Hb)). lia. }
  match goal with |- SR _ _ ?P => set (POST := P) end.
  assert (FREEP : forall regs3 mem2', munch [(spZ regs - 40, spZ regs - 32)] mem2 mem2' -> wmono rsegs mem2 mem2' ->
      jr_run jr_strtod (zb tb) ok = (None, tr) ->
      getr regs3 1 = Z_to_bv 64 0x16024 -> spZ regs3 = spZ regs - 48 -> getr regs3 10 = Z_to_bv 64 out ->
      rk_cs regs regs3 -> pj_fd (ms_segs B) mem2' (lin Lam1) 33 out D ->
      SR rsegs (mkCfg (@mkst fx2 regs3 (Z_to_bv 64 0x16340) mem2' (seg_rom rsegs)) md1) POST).
  { intros regs3 mem2' MUs WMs RUNN F1 F2 F10 CS3 FD.
    destruct (KEEP mem2' MUs WMs) as (M2' & LG2' & RDC2' & RPV' & SAV2' & AUXB2' & C2' & WR2' & _).
    rewrite <- SEG.
    eapply SR_bind.
    { apply (PF fx2 L1 A1 regs3 mem2' md1 Lam1 peak1 cnt1 fail1 (rf_run RF b tr) out 33%nat D).
      - split; [exact SEG|]. split; [exact TP|]. split; [exact ERR|]. split; [exact GG|]. split; [exact GD|].
        split.
        { split; [exact M2'|]. split; [exact WF2|]. split; [exact B2|].
          split; [rewrite F1; apply ret_ok_even; vm_compute; reflexivity|].
          split; [rewrite F2; Z.div_mod_to_equations; lia|].
          split; [rewrite F2; lia|].
          split; [rewrite F2; lia|].
          split.
          { intros a Ha. rewrite F2 in Ha.
            assert (Hd : spZ regs - 48 - PARSE_VALUE_K 0 <= a \/ a < spZ regs - 48 - PARSE_VALUE_K 0) by lia.
            destruct Hd as [Hd|Hd].
            - apply C2'. left. rewrite S1. lia.
            - apply WR2'. lia. }
          split; [transitivity (getr regs3 (Z_to_bv 5 4)); [reflexivity|]; rewrite (CS3 4 ltac:(lia)); exact HTP|].
          split; [intros a Ha; apply C2'; right; exact Ha|].
          intros HI1. rewrite F2. destruct Y2 as (_ & YS & _). rewrite YS.
          destruct (AUXB2' HI1) as [[Ho AV]|[Ho AV]]; (eapply auxv_pre_mono; [|exact AV]); lia. }
        split; [rewrite F2; lia|]. split; [rewrite F2; lia|]. split; [exact FRM2|]. exact RDC2'.
      - exact LG2'.
      - exact RES1.
      - exact F10.
      - right. split; [exact ONZ|]. split; [exact FD|]. split; [|rewrite F2; cbn [disjoint_from]; lia].
        split; [|split].
        + unfold pj_place. destruct OUTB1 as [Ho|(a' & k' & HB' & NL & Pa & Pb)];
            [left; rewrite F2; pose proof (proj1 (proj2 (proj2 PRW))); lia | right; left; exists a', k'; tauto].
        + intros Hs HI1. rewrite F2 in Hs. destruct Y2 as (_ & YS & _). rewrite YS.
          destruct (AUXB2' HI1) as [[_ AV]|[Ho _]]; [exact AV | lia].
        + intros i Hi. destruct (PEX i Hi) as (_ & Hs & He & Hn). split; [|tauto].
          destruct OUTB1 as [Ho|(a' & k' & HB' & NL & Pa & Pb)].
          * intros Ho'. pose proof (OWL _ _ _ _ _ M2 Ho'). lia.
          * destruct (rk_blk_facts L1 A1 mem2 md1 a' k' M2 HB') as (_ & _ & BF).
            destruct (BF (out + i - a') ltac:(lia)) as (_ & NO). replace (a' + (out + i - a')) with (out + i) in NO by lia.
            exact NO. }
    intros c3 (L2 & A2 & regs4 & mem3 & md2 & Lam2 & -> & RP3 & RDC3 & PERM2 & LG3 & (D3 & PD3 & RES3) & _ & PZ3).
    pose proof RP3 as (M3 & _ & _ & _ & _ & _ & _ & _ & _ & RP3r & _ & H3 & _ & _ & _).
    destruct (mr_model B _ (aa_laws API) L2 A2 mem3 md2 M3) as (Hh2 & Hl2 & _).
    assert (SP4 : spZ regs4 = spZ regs - 48).
    { rewrite <- F2. unfold spZ. change (bv_unsigned (getr regs4 (Z_to_bv 5 2)) = bv_unsigned (getr regs3 (Z_to_bv 5 2))).
      rewrite (RP3r 2); [reflexivity | unfold callee_saved; lia]. }
    assert (CS4 : rk_cs regs regs4) by exact (rk_cs_rp regs regs3 regs4 CS3 RP3r).
    assert (SAV3 : rw_cells rsegs mem3 (spZ regs - 48 + 32) [C8 (reg_get regs 8); C8 (reg_get regs 1)]).
    { apply (rk_rw_cells_keep mem2' mem3 _ _ SAV2'). intros i Hi. cbn in Hi.
      destruct (H3 (spZ regs - 48 + 32 + i)) as [E1 E2]; [lia | unfold scratch_k; rewrite F2; lia | |].
      - unfold pj_free_writes. intros (_ & [H|[H|H]]);
          [lia | exact (BLKH (spZ regs - 48 + 32 + i) ltac:(lia) H) | pose proof (STL _ H); lia].
      - rewrite SEG in E1, E2. split; [exact E1 | tauto]. }
    rewrite F1. rewrite SEG.
    eapply rk_kA; [exact Hh2 | exact Hl2 | |].
    { unfold mkR_of. apply pp_free_tail with (rav := reg_get regs 1) (s0v := reg_get regs 8).
      - change (bv_unsigned (reg_get regs4 2)) with (spZ regs4). rewrite SP4. exact SAV3.
      - change (bv_unsigned (reg_get regs4 2)) with (spZ regs4). rewrite SP4. lia. }
    intros ms' (can & PR & EQV).
    destruct PR as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
    destruct (pp_final_regs regs regs4 (ms_regs ms') _ _ _ (-1) _ _ _ _ _ _ _ _ _ _ _ XR ltac:(lia) CS4) as (RPF & R10F).
    rewrite Ems. apply SR_ret. unfold POST. cbv beta.
    exists fx2, L2, A2, (ms_regs ms'), mem3, md2, Lam2, peak1, cnt1, fail1, ok, None, tr.
    split.
    { change (reg_get regs 1) with (getr regs 1). rewrite (rk_ret_pc _ HRA). rewrite SEG. reflexivity. }
    split; [exact FRM2|]. split; [exact FK2|].
    split.
    { apply (rk_seq PJ_PARSE_K L A regs mem md _ L1 A1 regs mem2' md1 (PJ_FREE_K 33) regs3 _ _ L2 A2 regs4 mem3 md2
        (ms_regs ms') RPV' RP3 RPF).
      - rewrite F2. lia.
      - rewrite F2. lia.
      - exact HAC.
      - lia.
      - intros a Ha Hs He. unfold pj_free_writes, scratch_k, pj_parse_writes in *.
        intros (_ & [H|[H|H]]); [tauto | exact (BLKH a ltac:(lia) H) | tauto].
      - intros a Ha Hs He. unfold pj_free_writes, pj_parse_writes in *.
        intros (_ & [H|[H|H]]); [tauto | exact (BLKI a Ha H) | tauto].
      - intros p n i Hp Hp1 Hi He. unfold pj_free_writes, pj_parse_writes in *.
        intros (_ & [H|[H|H]]); [tauto | exact (BLKB p n i Hp Hp1 Hi H) | tauto].
      - intros p n Hp Hp1 HF. unfold freed in HF. apply (NB _ _ HF).
        replace (ptr_addr L p + 16 - 16) with (ptr_addr L p) by lia. replace (n - 16 + 16) with n by lia.
        exact (rk_blk_of_user L A p n Hp).
      - intros a Ha Hd. left. unfold pj_free_writes, scratch_k in *. rewrite F2 in Hd.
        intros (_ & [H|[H|H]]); [lia | apply (BLKH a); [lia | exact H] | pose proof (STL a H); lia]. }
    split; [exact RDC3|]. split; [exact LG3|]. split; [exact RUNN|].
    split; [exact OKS|]. split; [exact CNT1|]. split; [exact FA1|]. split; [exact PK1|].
    split; [unfold zb in HP1; rewrite length_map in HP1; change (Z.of_nat (MAXD - 0)) with 32 in HP1; lia|].
    split; [intros _; reflexivity|].
    split.
    { intros HF. assert (HO : oks ok cnt fail (PjGrammar.calls (snd (jr_run jr_strtod (zb tb) ok)))) by (rewrite RUNN; exact OKS).
      destruct (pp_c18 (zb tb) ok cnt fail HO HF) as [E1 E2]. rewrite RUNN in E1, E2. injection E1 as E1a E1b.
      cbn [snd] in E2. split; [exact E1a | exact E2]. }
    split; [exact R10F|].
    split; [exists D, D3; split; [exact PD3|]; split; [exact HELD|]; split; [exact NLV | exact RES3]|]. split.
    + apply (Permutation_app_inv_l D). exact (perm_trans (Permutation_sym PERM2) PERM1).
    + exact (PZ3 ONZ). }
  rewrite G1, SEG.
  destruct res as [[t r]|] eqn:ERES.
  - destruct ARM as (R102 & PIN2 & PN2 & LSD).
    assert (RR : zb (skipn (Z.to_nat (t0 + len - Z.of_nat (length r) - t0)) tb) = r).
    { replace (Z.to_nat (t0 + len - Z.of_nat (length r) - t0)) with (Z.to_nat (Z.of_nat (length tb) - Z.of_nat (length r)))
        by (f_equal; lia).
      exact (pp_rest tb ok t r tr okr JV). }
    eapply rk_kA; [exact Hh1 | exact Hl1 | |].
    { unfold mkR_of. replace (reg_get regs2 10) with (Z_to_bv 64 0) by (symmetry; exact R102).
      apply (pp_scan SW) with (rav := reg_get regs 1) (s0v := reg_get regs 8) (len := len) (d := Z.of_nat 0).
      - change (bv_unsigned (reg_get regs2 2)) with (spZ regs2). rewrite SP2.
        replace (spZ regs - 48 + 8) with (spZ regs - 40) by lia. rewrite <- SEG. exact PIN2.
      - change (bv_unsigned (reg_get regs2 2)) with (spZ regs2). rewrite SP2. exact SAV2.
      - change (bv_unsigned (reg_get regs2 2)) with (spZ regs2). rewrite SP2. lia. }
    intros ms' (can & PS & EQV).
    destruct PS as (m' & MUs & WMs & MIs & PS).
    change (bv_unsigned (reg_get regs2 2)) with (spZ regs2) in MUs. rewrite SP2 in MUs.
    replace (spZ regs - 48 + 8) with (spZ regs - 40) in MUs by lia.
    replace (spZ regs - 48 + 16) with (spZ regs - 32) in MUs by lia.
    destruct (KEEP m' MUs WMs) as (M2' & LG2' & RDC2' & RPV' & SAV2' & AUXB2' & C2' & WR2' & PNK).
    assert (HDD : forall a k, In (a, k) D -> lin Lam1 a k /\ a + k <= alloc_ceiling).
    { intros a k Hk. split.
      - unfold lin. apply (Permutation_in _ (Permutation_sym PERM1)). apply in_or_app. left. exact Hk.
      - destruct (DF a k Hk) as (_ & _ & R & _). exact R. }
    pose proof (PNK t D PN2 HDD) as PN2'.
    destruct PS as [(SK & PR) | (SK & PCF)]; rewrite RR in SK.
    + destruct PR as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
      destruct (pp_final_regs regs regs2 (ms_regs ms') _ _ _ 0 _ _ _ _ _ _ _ _ _ _ _ XR ltac:(lia) CS2) as (RPF & R10F).
      assert (RUNS : jr_run jr_strtod (zb tb) ok = (Some t, tr)) by (rewrite RUN; unfold post; rewrite SK; reflexivity).
      rewrite Ems. apply SR_ret. unfold POST. cbv beta.
      exists fx2, L1, A1, (ms_regs ms'), m', md1, Lam1, peak1, cnt1, fail1, ok, (Some t), tr.
      split; [change (reg_get regs 1) with (getr regs 1); rewrite (rk_ret_pc _ HRA); rewrite SEG; reflexivity|].
      split; [exact FRM2|]. split; [exact FK2|].
      split; [exact (rk_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPV' RPF)|].
      split; [exact RDC2'|]. split; [exact LG2'|]. split; [exact RUNS|].
      split; [exact OKS|]. split; [exact CNT1|]. split; [exact FA1|]. split; [exact PK1|].
      split; [unfold zb in HP1; rewrite length_map in HP1; change (Z.of_nat (MAXD - 0)) with 32 in HP1; lia|].
      split.
      { intros HF. assert (HO : oks ok cnt fail (PjGrammar.calls (snd (jr_run jr_strtod (zb tb) ok)))) by (rewrite RUNS; exact OKS).
        pose proof (pp_c17 (zb tb) ok cnt fail HO HF) as E. rewrite RUNS in E. discriminate E. }
      split.
      { intros HF. assert (HO : oks ok cnt fail (PjGrammar.calls (snd (jr_run jr_strtod (zb tb) ok)))) by (rewrite RUNS; exact OKS).
        destruct (pp_c18 (zb tb) ok cnt fail HO HF) as [E1 E2]. rewrite RUNS in E1, E2. injection E1 as E1a E1b.
        cbn [snd] in E2. split; [exact E1a | exact E2]. }
      split; [exact R10F|]. split; [exact RES1|]. exists D. split; [exact PERM1|]. split; [exact HELD|].
      split; [exact NLV|]. split; [exact NB|]. exact PN2'.
    + destruct PCF as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
      rewrite Ems.
      apply (FREEP _ m' MUs WMs).
      * rewrite RUN. unfold post. destruct (skip r) as [|c rr]; [contradiction | reflexivity].
      * rewrite (rk_getr_eqv _ _ XR). reflexivity.
      * unfold spZ. rewrite (rk_getr_eqv _ _ XR). change (bv_unsigned (reg_get regs2 2) = spZ regs - 48). exact SP2.
      * rewrite (rk_getr_eqv _ _ XR). change (reg_get regs2 8 = Z_to_bv 64 out). exact G82.
      * exact (rk_cs_trans _ _ _ CS2 (rk_cs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR)).
      * eapply pj_fd_mono; [|exact (pj_node_fd _ t _ _ _ _ PN2')].
        pose proof (jr_value_depth jr_strtod 0 (zb tb) ok t r tr okr JV). unfold MAXD in *. lia.
  - destruct ARM as (R102 & PIA & FD2).
    eapply rk_kA; [exact Hh1 | exact Hl1 | |].
    { unfold mkR_of. replace (reg_get regs2 10) with (Z_to_bv 64 (-1)) by (symmetry; exact R102). apply pp_refuse. }
    intros ms' (can & PCF & EQV).
    destruct PCF as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
    rewrite Ems.
    apply (FREEP _ mem2 (munch_refl _ mem2) (wmono_refl rsegs mem2)).
    + rewrite RUN. reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + unfold spZ. rewrite (rk_getr_eqv _ _ XR). change (bv_unsigned (reg_get regs2 2) = spZ regs - 48). exact SP2.
    + rewrite (rk_getr_eqv _ _ XR). change (reg_get regs2 8 = Z_to_bv 64 out). exact G82.
    + exact (rk_cs_trans _ _ _ CS2 (rk_cs_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR)).
    + eapply pj_fd_mono; [|exact FD2]. unfold MAXD. lia.
Qed.

End KB.

Section Final.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Theorem pj_parse_holds : skip_ws_c.skip_ws_contract -> memset_contract -> parse_value_contract B API RF 0 ->
  (forall fx', @pj_free_contract fx' rc B API RF) ->
  pj_parse_contract B API RF.
Proof.
  intros SW MEMSET PV PF. unfold pj_parse_contract. intros L A regs mem md Lam peak cnt fail b t0 len out tb ENV.
  exact (pj_parse_main B API RF (proj1 ENV) SW MEMSET PV PF L A regs mem md Lam peak cnt fail b t0 len out tb ENV).
Qed.

End Final.
