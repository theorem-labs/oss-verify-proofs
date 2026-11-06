From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_peer_lock_init_c.
Import ListNotations.
Open Scope Z_scope.

Lemma lock0_split : repeat (zb 0) 12 = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0).
Proof. vm_compute. reflexivity. Qed.

Lemma lock0_ok : lock_ok (repeat (zb 0) 12).
Proof. split; [reflexivity | left; vm_compute; reflexivity]. Qed.

Ltac lock_st HW k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "ST" in
      lazymatch type of HW with
      | wr_at ?sg _ ?l _ =>
          assert (H : store_ok sg mm (wa (l + k)) 4 = true)
            by (apply (wr_at_store_ok sg mm l 12 k 4); [repeat apply wr_at_write; exact HW | lia | lia])
      end
  end.

Theorem reac_disco_peer_lock_init_holds : reac_disco_peer_lock_init_contract.
Proof.
  unfold reac_disco_peer_lock_init_contract, REAC_DISCO_PEER_LOCK_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m l
         E H4 HW HI.
  subst a0. pose proof HW as (HWl & HWh & _).
  lock_st HW 0. step.
  lock_st HW 4. step.
  lock_st HW 8. step.
  step.
  apply evt_done. cbv beta.
  eexists. split; [reflexivity |].
  repeat match goal with H : store_ok _ _ _ _ = true |- _ => clear H end.
  set (z4 := le4 (Z_to_bv 64 0)).
  split.
  { repeat (apply munch_write; [ | lia | unfold z4; rewrite length_le4; cbn; lia | cbn [inside]; unfold z4; rewrite length_le4; cbn; lia ]).
    apply munch_refl. }
  split; [repeat apply wmono_write; apply wmono_refl |].
  split.
  { repeat (apply mem_inv_store; [ | first [ apply (wr_at_store_ok rsegs _ l 12 _ 4); [repeat apply wr_at_write; exact HW | lia | lia ]
                                            | rewrite <- (wa_of_var _ _); apply (wr_at_store_ok rsegs _ l 12 _ 4);
                                              [repeat apply wr_at_write; exact HW | lia | lia ] ] ]).
    exact HI. }
  split; [| exact lock0_ok].
  unfold z4 in *. rewrite lock0_split.
  assert (L4 : Z.of_nat (length (le4 (Z_to_bv 64 0))) = 4) by (rewrite length_le4; reflexivity).
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [ | lia | lia | lia ].
    apply bytes_at_write_other; [ | lia | lia | lia ].
    rewrite ?Z.add_0_r. apply bytes_at_write_same; lia.
  - apply bytes_at_app. split.
    + apply bytes_at_write_other; [ | lia | lia | lia ].
      rewrite L4. apply bytes_at_write_same; lia.
    + rewrite L4. replace (l + 4 + 4) with (l + 8) by lia.
      apply bytes_at_write_same; lia.
Qed.
