From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_main_inv.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** [addiw s6, s6, 1] at 0x14a5c: no 32-bit wrap while the count is at most 254. *)
Lemma ops_succ : forall x, 0 <= x <= 254 -> bv_swrap 32 (x + 1) = x + 1.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite (Z.mod_small (x + 1 + 2^31) (2^32)) by lia. lia.
Qed.

(** 0x14b78-0x14bb4: a0 := 0, the 13 saved words reloaded, the frame released, ret. *)
Lemma codec_main_exit : seg_exit_stmt.
Proof.
  unfold seg_exit_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] ENV.
  cenv_cbn.
  unfold env_ok in ENV. cenv_cbn.
  destruct ENV as (_ & _ & _ & LO & _).
  intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9'
         s10' s11' t3' t4' t5' t6' cs m1 HS FR ST MU WM HMI.
  cenv_cbn.
  pose proof (rw_cells_app_split _ _ _ _ FR) as [_ FS].
  rewrite HS in FS.
  replace (bv_unsigned sp + -416 + Z.of_nat 312) with (bv_unsigned sp + -104) in FS by lia.
  unfold saved in FS. cenv_cbn.
  do 15 zstep.
  clear FS.
  eapply stk_release in FR; [ | exact ST | lia ].
  rewrite cells_size_app, HS in FR. cbn [saved cells_size csize Nat.add] in FR.
  lazymatch type of FR with
  | stk _ _ _ ?h => replace h with (bv_unsigned sp) in FR by lia
  end.
  clear ST.
  zstep.
  unfold Qk. cenv_cbn.
  finish.
Qed.

(** 0x14a54-0x14a64 and 0x14b1c-0x14b20: leave when ops > 254 or no byte is left, else ops + 1
    and back to the head with the reloaded in.n. *)
Lemma codec_main_latch : seg_latch_stmt.
Proof.
  unfold seg_latch_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV EXIT LOOP.
  cenv_cbn.
  clear ENV.
  split;
   ( intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
           cur rem kc u0 pj tj plj c ops m1 HF HO HC HC0 HCN FR ST MU WM HMI;
    cenv_cbn;
    pose proof FR as FR0; unfold fr in FR0; cenv_cbn;
    destruct FR0 as (_ & _ & _ & _ & FIN & _);
    pose proof (bv_unsigned_in_range 64 rem) as Rrem;
    zstep;
    if_cases G1;
    [ destruct (fr_exit _ _ _ _ _ _ _ _ _ FR) as (cs & HCS & HCX);
      eapply EXIT; [exact HCS | exact HCX | exact ST | exact MU | exact WM | exact HMI]
    | ];
    zify_cond G1;
    try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x14b20) _ _ _ _) => zstep end);
    zstep; zstep; zstep;
    if_cases G2;
    [ destruct (fr_exit _ _ _ _ _ _ _ _ _ FR) as (cs & HCS & HCX);
      eapply EXIT; [exact HCS | exact HCX | exact ST | exact MU | exact WM | exact HMI]
    | ];
    zify_cond G2;
    zstep;
    replace (bv_swrap 32 (ops + 1)) with (ops + 1) by (symmetry; apply ops_succ; lia);
    eapply LOOP; [ | | | exact HC | exact HC0 | exact HCN | exact FR | exact ST | exact MU | exact WM | exact HMI ];
    lia ).
Qed.
