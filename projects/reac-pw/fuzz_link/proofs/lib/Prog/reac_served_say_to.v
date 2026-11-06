(* reac_served_say_to (reac_served_mark.c:16-19), PLAIN build: the walk of its contract
   (lib/Prog/reac_served_say_to_c.v) on the plain image. Three instructions: auipc a1, 0x5f;
   sd a0, 0x138(a1) (the store into g_say, 0x75530); ret. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf reac_served_say_to_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

Theorem reac_served_say_to_holds : reac_served_say_to_contract.
Proof.
  unfold reac_served_say_to_contract. apply leaf_intro.
  - intros r1 r2 m _ H. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' E _ H. unfold arg in *. rewrite <- E. exact H.
  - unfold leaf_walk, REAC_SERVED_SAY_TO, A_G_SAY.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HW MI ST LO SP.
    pose proof (wr_at_store_ok rsegs m 0x75530 8 0 8 HW ltac:(lia) ltac:(lia)) as HS.
    replace (0x75530 + 0) with 0x75530 in HS by reflexivity.
    zstep. zstep. zstep.
    change (Z_to_bv 64 480560) with (wa 480560).
    apply evt_done. eexists. exists (write_to_mem m (wa 480560) (le8 a0)).
    split; [reflexivity|].
    split; [exact (regs_preserved_mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                     s8 s9 s10 s11 t3 t4 t5 t6 ra t0 t1 t2 a0 (Z_to_bv 64 480248) a2 a3 a4 a5 a6 a7
                     t3 t4 t5 t6)|].
    split; [apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia
                               | cbn [inside]; rewrite length_le8; right; left; lia]|].
    split; [apply wmono_write, wmono_refl|].
    split; [apply mem_inv_store; [exact MI | rewrite length_le8; exact HS]|].
    split; [apply stk_write; [exact ST | lia | rewrite length_le8; lia]|].
    unfold u64_at, wz. rewrite mkR_a0, Z_to_bv_bv_unsigned.
    apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.
