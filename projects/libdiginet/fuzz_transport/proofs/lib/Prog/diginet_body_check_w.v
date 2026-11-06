(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/Prog/diginet_body_check_w.v at b8f2ecf2c3ff0406d93584348ebba6e5957c14ce to fuzz_transport's images *)
(* Walk of diginet_body_check in fuzz_transport.plain against diginet_body_check_contract_w.
   For body <> 0 the walk is diginet_body_check_holds. For body = 0 the body is empty, and the
   entry state with a0 = 0 is the entry state of diginet_body_check_contract with body = 2^64
   (Z_to_bv 64 (2^64) = Z_to_bv 64 0), which that contract admits: diginet_body_check_holds walks
   this case in bc_main (diginet_cursor_init gets body 0 and length 0, the first
   diginet_msg_next answers 0, the prefix scan does not run). So no new instruction is walked.
   diginet_body_check_contract_of_w: the wide contract gives the narrow one.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import diginet_cursor_init_c diginet_msg_next_c
  diginet_body_check_c diginet_body_check diginet_body_check_w_c.
Import ListNotations.
Open Scope Z_scope.

(* The register value of the address 2^64 is that of NULL. *)
Lemma bcw_null : Z_to_bv 64 0 = Z_to_bv 64 (2^64).
Proof. apply bv_eq. rewrite !unsigned_lit_wrap. reflexivity. Qed.

(* The empty body at the address 2^64. *)
Lemma bcw_empty_at : forall m (bb : list byte), length bb = 0%nat -> bytes_at rsegs m (2^64) bb.
Proof.
  intros m bb L0. split; [lia|]. split; [rewrite L0; cbn; lia|]. intros i Hi. rewrite L0 in Hi. lia.
Qed.

Theorem diginet_body_check_holds_w :
  diginet_cursor_init_contract -> diginet_msg_next_contract -> diginet_body_check_contract_w.
Proof.
  intros CI MN. pose proof (diginet_body_check_holds CI MN) as N. unfold diginet_body_check_contract in N.
  unfold diginet_body_check_contract_w.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body lo bb
    HB BB ST LO DJ MI.
  destruct (Z.eq_dec body 0) as [B0|B0].
  - (* body = 0: an empty body (body_len = 0, a0 = NULL) *)
    assert (L0 : length bb = 0%nat) by (destruct HB as [HB|HB]; [contradiction | exact HB]).
    subst body. rewrite bcw_null.
    pose proof (u64_range sp) as Rsp.
    apply (N ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (2^64) lo bb); [ lia | exact (bcw_empty_at m bb L0) | exact ST | exact LO | right; lia | exact MI ].
  - exact (N ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             body lo bb B0 BB ST LO DJ MI).
Qed.

Lemma diginet_body_check_contract_of_w : diginet_body_check_contract_w -> diginet_body_check_contract.
Proof.
  unfold diginet_body_check_contract_w, diginet_body_check_contract.
  intros W ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m body lo bb
    HB. apply W. left. exact HB.
Qed.
