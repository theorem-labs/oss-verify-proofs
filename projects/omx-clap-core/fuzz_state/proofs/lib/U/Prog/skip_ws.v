From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import skip_ws_c.
Import ListNotations.
Open Scope Z_scope.

Lemma eqb0_word : forall z, -2 ^ 64 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0).
Proof.
  intros z Hz. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec z 0) as [E|E]; [subst z; reflexivity|].
  apply Z.eqb_neq. intro E2. apply E. Z.div_mod_to_equations. lia.
Qed.

Lemma mask_ws : forall c : byte, bv_unsigned c <= 32 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (bv_unsigned (zxb c) mod 64)))) 1 = if ws c then 1 else 0.
Proof.
  intros c Hc. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. cbn in R.
  unfold zxb, ws. rewrite (unsigned_lit (bv_unsigned c)) by lia.
  revert Hc R. generalize (bv_unsigned c) as x. intros x Hc R.
  assert (A : forallb (fun y => Z.eqb (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (y mod 64)))) 1)
                                      (if (y =? 32) || (y =? 9) || (y =? 10) || (y =? 13) then 1 else 0))
                      (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A x). cbv beta in A.
  apply Z.eqb_eq, A. apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia].
Qed.

Lemma skip_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q text len p d : Z) (txt : list byte) (n : nat)
  (a7 : word) (mm : word -> option byte) (P : Z),
  Z.to_nat (text + len - P) = n ->
  pj_in_ok rsegs mm q text len P d txt -> P < text + len ->
  munch [(q, q + 8)] m mm -> wmono rsegs m mm -> (mem_inv rsegs m -> mem_inv rsegs mm) ->
  p + Z.of_nat (ws_len (skipn (Z.to_nat (p - text)) txt)) = P + Z.of_nat (ws_len (skipn (Z.to_nat (P - text)) txt)) ->
  evt rsegs (skip_ws_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d txt)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 P) (Z_to_bv 64 (text + len))
             (Z_to_bv 64 32) (Z_to_bv 64 4294977024) (Z_to_bv 64 1) (Z_to_bv 64 P) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x147ac) fc None mm (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q text len p d txt n.
  induction n as [|n IH]; intros a7 mm P HN PJ HP MU WM MI INV; [exfalso; lia|].
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof PJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PT & _ & _).
  destruct (skipn (Z.to_nat (P - text)) txt) as [|c rest] eqn:SK.
  { exfalso. pose proof (length_skipn (Z.to_nat (P - text)) txt) as L. rewrite SK in L. cbn in L. lia. }
  try rewrite SK in INV. cbn [ws_len] in INV.
  assert (RB : ov_read_bytes rsegs mm (wa P) 1 = Some [c]).
  { replace P with (text + (P - text)) at 1 by lia.
    rewrite (bytes_at_read rsegs mm text txt (P - text) 1 PT) by lia. rewrite SK. reflexivity. }
  pose proof (bv_unsigned_in_range 8 c) as HZc. unfold bv_modulus in HZc. cbn in HZc.
  assert (EXIT : ws c = false ->
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    evt rsegs (skip_ws_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m q text len p d txt)
      (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (ret_pc ra) fc None mm (seg_rom rsegs))).
  { intros WSf t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
    apply evt_done. unfold skip_ws_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    rewrite INV, WSf. cbn [Z.of_nat]. rewrite Z.add_0_r. exact PJ. }
  step.
  if_cases HA; rewrite eqb0_word in HA by lia.
  { apply Z.eqb_eq in HA. lia. }
  step. step.
  if_cases HC; rewrite bv_ltu_Z in HC; unfold zxb in HC; rewrite !unsigned_lit in HC by lia.
  - apply Z.ltb_lt in HC. step. apply EXIT.
    unfold ws. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); [lia|] end. reflexivity.
  - apply Z.ltb_ge in HC.
    step. step. step.
    if_cases HD; rewrite mask_ws in HD by lia; destruct (ws c) eqn:WS; vm_compute in HD; try discriminate HD.
    + step. apply EXIT. first [exact WS | reflexivity].
    + pose proof (pj_in_ok_store_p rsegs _ _ _ _ _ _ _ PJ) as HSq.
      assert (SK1 : skipn (Z.to_nat (P + 1 - text)) txt = rest).
      { replace (Z.to_nat (P + 1 - text)) with (1 + Z.to_nat (P - text))%nat by lia.
        rewrite <- skipn_skipn, SK. reflexivity. }
      step. step.
      if_cases HE; rewrite bv_ltu_Z, !unsigned_lit in HE by lia.
      { apply negb_true_iff, Z.ltb_ge in HE. lia. }
      step. step. step.
      if_cases HF; rewrite bv_ltu_Z, !unsigned_lit in HF by lia.
      * apply Z.ltb_lt in HF.
        eapply IH with (P := P + 1);
          [ lia
          | eapply pj_in_ok_set_p; [exact PJ | lia]
          | lia
          | apply munch_write; [exact MU | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]
          | apply wmono_write; exact WM
          | intro HM; apply mem_inv_store; [exact (MI HM) | rewrite length_le8; exact HSq]
          | rewrite INV, SK1; lia ].
      * apply Z.ltb_ge in HF.
        assert (RN : rest = []).
        { apply length_zero_iff_nil. pose proof (length_skipn (Z.to_nat (P + 1 - text)) txt) as L. rewrite SK1 in L. lia. }
        step.
        apply evt_done. unfold skip_ws_post. do 16 eexists. split; [reflexivity|].
        split; [apply munch_write; [exact MU | lia | rewrite length_le8; lia | cbn [inside]; rewrite length_le8; lia]|].
        split; [apply wmono_write; exact WM|].
        split; [intro HM; apply mem_inv_store; [exact (MI HM) | rewrite length_le8; exact HSq]|].
        rewrite INV, RN. cbn [ws_len]. replace (P + Z.of_nat 1) with (P + 1) by lia.
        eapply pj_in_ok_set_p; [exact PJ | lia].
Qed.

Theorem skip_ws_holds : skip_ws_contract.
Proof.
  unfold skip_ws_contract, SKIP_WS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    q text len p d txt E0 PJ.
  subst a0.
  pose proof (pj_in_ok_bounds rsegs _ _ _ _ _ _ _ PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (pj_in_ok_rd_p rsegs _ _ _ _ _ _ _ PJ) as RQ.
  pose proof (pj_in_ok_rd_end rsegs _ _ _ _ _ _ _ PJ) as RE.
  assert (HLq : Z.land q 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact B8).
  step. step.
  if_cases HA; rewrite (unsigned_lit q), HLq in HA by lia.
  { vm_compute in HA. discriminate HA. }
  step. step. step.
  if_cases HB; rewrite bv_ltu_Z, !unsigned_lit in HB by lia.
  - apply negb_true_iff, Z.ltb_ge in HB.
    step.
    apply evt_done. unfold skip_ws_post. do 16 eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [tauto|].
    replace (skipn (Z.to_nat (p - text)) txt) with (@nil byte).
    + cbn [ws_len Z.of_nat]. rewrite Z.add_0_r. exact PJ.
    + symmetry. apply length_zero_iff_nil. rewrite length_skipn. lia.
  - apply negb_false_iff, Z.ltb_lt in HB.
    do 6 step.
    eapply skip_loop with (P := p) (n := Z.to_nat (text + len - p));
      [reflexivity | exact PJ | exact HB | apply munch_refl | apply wmono_refl | tauto | reflexivity].
Qed.
