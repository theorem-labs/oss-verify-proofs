From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes is_tagged_reac_c rp_ds_accept_c is_tagged_reac.
Import ListNotations.
Open Scope Z_scope.

(* rp_ds_accept at 0x1379c (19 words). When is_reac(f) fails it jumps (0x137e0, `j`, ra kept) to is_tagged_reac
   (0x137e8), whose contract is the NAMED Section hypothesis is_tagged_reac_ok (lib/U/Prog/is_tagged_reac_c.v); after
   the Section, rp_ds_accept_closed discharges it with is_tagged_reac_holds. UBSan traps: the unimp at 0x137e4, reached
   from 0x137ac (f = 0: refuted by the premise a0 <> 0), 0x137b4 (f >= 2^64 - 12) and 0x137c8 (f > 2^64 - 14) (both
   refuted by bytes_at with 18 <= length bs: f + 18 <= 2^64). *)

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

Local Ltac fin :=
  apply evt_done; unfold ds_accept_result, ds_byte, tagged_result, tag_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  bfacts;
  repeat match goal with |- context [Z.eqb ?x ?c] => destruct (Z.eqb_spec x c); try (exfalso; lia) end;
  do 2 eexists; reflexivity.

Section W.
Hypothesis is_tagged_reac_ok : is_tagged_reac_contract.

Local Ltac tagcall bs NZ LEN BA :=
  eapply evt_cut;
  [ eapply (is_tagged_reac_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs);
    [ exact NZ | exact LEN | exact BA ]
  | let ms' := fresh "ms'" in let x1 := fresh "x1" in let x2 := fresh "x2" in
    intros ms' (x1 & x2 & ->); fin ].

Theorem rp_ds_accept_holds : rp_ds_accept_contract.
Proof.
  unfold rp_ds_accept_contract, RP_DS_ACCEPT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs HB.
  step. step. if_cases HL.
  2:{ zc HL. step. step. fin. }
  zc HL. destruct (HB ltac:(lia)) as [NZ [LEN BA]].
  pose proof BA as (B0 & B1 & _).
  pose proof (rd1 m _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
  pose proof (rd1 m _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  step. if_false. step. step. if_false.
  step. step. step. if_cases H88.
  { zc H88. step. tagcall bs NZ LEN BA. }
  zc H88. step. step. if_false. step. step. step. if_cases H19.
  { zc H19. step. tagcall bs NZ LEN BA. }
  zc H19. step. step. fin.
Qed.

End W.

Theorem rp_ds_accept_closed : rp_ds_accept_contract.
Proof. exact (rp_ds_accept_holds is_tagged_reac_holds). Qed.
