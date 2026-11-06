From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ex_ws_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ex_ws_skipn_cons : forall (l : list byte) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof. induction l as [|a l IH]; intros [|k] d H; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.

Lemma ex_ws_p1_stop : forall x0 i (x : list byte), 0 <= i < Z.of_nat (length x) ->
  ws (bv_unsigned (nth (Z.to_nat i) x (Z_to_bv 8 0))) = false -> ex_ws_p1 x0 i x = x0 + i.
Proof.
  intros x0 i x Hi W. unfold ex_ws_p1. rewrite (ex_ws_skipn_cons x (Z.to_nat i) (Z_to_bv 8 0)) by lia.
  cbn [map skip]. rewrite W. cbn [length]. rewrite length_map, length_skipn. lia.
Qed.

Lemma ex_ws_p1_next : forall x0 i (x : list byte), 0 <= i < Z.of_nat (length x) ->
  ws (bv_unsigned (nth (Z.to_nat i) x (Z_to_bv 8 0))) = true -> ex_ws_p1 x0 i x = ex_ws_p1 x0 (i + 1) x.
Proof.
  intros x0 i x Hi W. unfold ex_ws_p1. rewrite (ex_ws_skipn_cons x (Z.to_nat i) (Z_to_bv 8 0)) by lia.
  cbn [map skip]. rewrite W. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma ex_ws_p1_end : forall x0 (x : list byte), ex_ws_p1 x0 (Z.of_nat (length x)) x = x0 + Z.of_nat (length x).
Proof. intros x0 x. unfold ex_ws_p1. rewrite Nat2Z.id, skipn_all. cbn. lia. Qed.

Lemma ex_ws_mask : forall z, 0 <= z <= 32 ->
  bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (bv_unsigned (Z_to_bv 64 z) mod 64)))) 1))
  = if ws z then 1 else 0.
Proof.
  intros z Hz. rewrite <- (Z2Nat.id z) by lia. assert (Hk : (Z.to_nat z <= 32)%nat) by lia.
  revert Hk. generalize (Z.to_nat z) as k. intros k Hk.
  do 33 (destruct k as [|k]; [vm_compute; reflexivity | ]). exfalso. lia.
Qed.

Lemma ex_ws_gt32 : forall z, 32 < z -> ws z = false.
Proof. intros z Hz. unfold ws. repeat rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity. Qed.

Local Ltac done_ret := apply evt_done; cbv beta; do 15 eexists; split; [reflexivity | ].

Lemma ex_ws_loop : forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (q x0 i : Z) (x : list byte),
  n = Z.to_nat (Z.of_nat (length x) - i) ->
  bytes_at rsegs m q (le8 (Z_to_bv 64 (x0 + i))) ->
  wr_at rsegs m q 8 ->
  bytes_at rsegs m x0 x -> 0 < x0 -> x0 + Z.of_nat (length x) < 2 ^ 62 -> 0 <= i < Z.of_nat (length x) ->
  (q + 16 <= x0 \/ x0 + Z.of_nat (length x) <= q) ->
  mem_inv rsegs m -> munch [(q, q + 8)] m0 m -> wmono rsegs m0 m ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       munch [(q, q + 8)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
       bytes_at rsegs m' q (le8 (Z_to_bv 64 (ex_ws_p1 x0 i x))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 (x0 + i)) (Z_to_bv 64 (x0 + Z.of_nat (length x)))
           (Z_to_bv 64 32) (Z_to_bv 64 0x100002600) (Z_to_bv 64 1) (Z_to_bv 64 (x0 + i)) a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14ce8) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m q x0 i x
      Hn HQ HW HX Hx0 Hlen Hi HD HM MU WM; [lia | ].
  pose proof (bytes_at_bound _ _ _ _ HQ) as HQb. rewrite length_le8 in HQb.
  assert (RD : ov_read_bytes rsegs m (wa (x0 + i)) 1 = Some [nth (Z.to_nat i) x (Z_to_bv 8 0)]).
  { rewrite (bytes_at_read rsegs m x0 x i 1 HX) by lia. rewrite (ex_ws_skipn_cons _ _ (Z_to_bv 8 0)) by lia.
    reflexivity. }
  set (c := nth (Z.to_nat i) x (Z_to_bv 8 0)) in RD.
  assert (Hc : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  assert (ST : store_ok rsegs m (wa q) 8 = true).
  { pose proof (wr_at_store_ok rsegs m q 8 0 8%nat HW ltac:(lia) ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H. }
  step. if_cases HB1; [zify_cond HB1; lia | clear HB1].
  step.
  step. if_cases HB2.
  - zify_cond HB2. rewrite (unsigned_lit (bv_unsigned c)) in HB2 by lia.
    pose proof (ex_ws_gt32 _ HB2) as W.
    step. done_ret.
    split; [exact MU | ]. split; [exact WM | ]. split; [exact HM | ].
    rewrite (ex_ws_p1_stop x0 i x Hi W). exact HQ.
  - zify_cond HB2. rewrite (unsigned_lit (bv_unsigned c)) in HB2 by lia.
    step. step. step. if_cases HB3.
    + zify_cond HB3. rewrite ex_ws_mask in HB3 by lia.
      destruct (ws (bv_unsigned c)) eqn:W; [lia | ].
      step. done_ret.
      split; [exact MU | ]. split; [exact WM | ]. split; [exact HM | ].
      rewrite (ex_ws_p1_stop x0 i x Hi W). exact HQ.
    + zify_cond HB3. rewrite ex_ws_mask in HB3 by lia.
      destruct (ws (bv_unsigned c)) eqn:W; [ | lia].
      step. step. if_cases HB4; [zify_cond HB4; lia | clear HB4].
      step. step. step. if_cases HB5.
      * zify_cond HB5.
        rewrite (ex_ws_p1_next x0 i x Hi W).
        replace (x0 + i + 1) with (x0 + (i + 1)) by lia.
        eapply (IH ra sp gp tp t0 t1 t2 s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ q x0 (i + 1) x).
        -- lia.
        -- apply bytes_at_write_same; rewrite ?length_le8; lia.
        -- apply wr_at_write. exact HW.
        -- apply bytes_at_write_other; [exact HX | lia | rewrite length_le8; lia | rewrite length_le8; lia].
        -- exact Hx0.
        -- exact Hlen.
        -- lia.
        -- exact HD.
        -- apply mem_inv_store; [exact HM | rewrite length_le8; exact ST].
        -- apply munch_write; [exact MU | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; lia].
        -- apply wmono_write. exact WM.
      * zify_cond HB5.
        assert (EP : ex_ws_p1 x0 i x = x0 + i + 1).
        { rewrite (ex_ws_p1_next x0 i x Hi W). replace (i + 1) with (Z.of_nat (length x)) by lia.
          rewrite ex_ws_p1_end. lia. }
        rewrite EP.
        step. done_ret.
        split; [apply munch_write; [exact MU | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; lia] | ].
        split; [apply wmono_write; exact WM | ].
        split; [apply mem_inv_store; [exact HM | rewrite length_le8; exact ST] | ].
        apply bytes_at_write_same; rewrite ?length_le8; lia.
Qed.

Theorem ex_ws_holds : ex_ws_contract.
Proof.
  unfold ex_ws_contract, EX_WS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q x0 i0 x
    E0 HQM HP HE HW HX Hx0 Hlen Hi HD HM.
  subst a0.
  pose proof (bytes_at_bound _ _ _ _ HP) as HQb. rewrite length_le8 in HQb.
  pose proof (bytes_at_bound _ _ _ _ HE) as HEb. rewrite length_le8 in HEb.
  assert (HL : Z.land q 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact HQM).
  assert (RP : ov_read_bytes rsegs m (wa q) 8 = Some (le8 (Z_to_bv 64 (x0 + i0)))).
  { pose proof (bytes_at_read rsegs m q _ 0 8 HP ltac:(lia) ltac:(rewrite length_le8; lia)) as H.
    rewrite Z.add_0_r in H. rewrite H. reflexivity. }
  assert (RE : ov_read_bytes rsegs m (wa (q + 8)) 8 = Some (le8 (Z_to_bv 64 (x0 + Z.of_nat (length x))))).
  { pose proof (bytes_at_read rsegs m (q + 8) _ 0 8 HE ltac:(lia) ltac:(rewrite length_le8; lia)) as H.
    rewrite Z.add_0_r in H. rewrite H. reflexivity. }
  step. step. if_cases HA; [zify_cond HA; lia | clear HA].
  step. step. step. if_cases HG.
  - zify_cond HG.
    assert (Ei : i0 = Z.of_nat (length x)) by lia. subst i0.
    step. done_ret.
    split; [apply munch_refl | ]. split; [apply wmono_refl | ]. split; [exact HM | ].
    rewrite ex_ws_p1_end. exact HP.
  - zify_cond HG.
    step. step. step. step. step. step.
    apply (ex_ws_loop (Z.to_nat (Z.of_nat (length x) - i0)) ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m m q x0 i0 x);
      [reflexivity | exact HP | exact HW | exact HX | exact Hx0 | exact Hlen | lia | lia | exact HM
      | apply munch_refl | apply wmono_refl].
Qed.
