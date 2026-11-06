From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import strcmp_c reac_rate_refuse_code_c check_code_c.
Import ListNotations.
Open Scope Z_scope.

(** check_code of the UBSan image (0x14744, 21 instructions), from strcmp_contract, walked with Lib/Tac.v and
    Lib/Step.v in the form of reac-pw/fuzz_role's check_code walk; the code is the plain one (Prog/check_code.v) at
    another address, plus an `unimp` after `jal abort` that no path reaches. The walk substitutes r = a1 by its
    literal (0..4, the premise). The prologue saves ra in the 16-byte frame; `addiw a1, a1, -1; addi a2, zero, 3;
    bltu a2, a1` sends r = 0 to "none" (auipc/addi) and r in 1..4 to the relative table at CODE_TBL (.rodata:
    mem_inv makes the `lw` read the image). Either way a1 is the address refuse_code_addr r that a0 already holds, so
    strcmp compares one image string, refuse_code_res r, with itself and returns 0 ([code_str_at]); the `bnez a0` is
    not taken and the epilogue reloads ra and frees the frame. *)

(** The string reac_rate_refuse_code answers for r, read through any word whose value is its address. *)
Lemma code_str_at : forall m r (w : word), mem_inv rsegs m -> bv_unsigned w = refuse_code_addr r ->
  bytes_at rsegs m (bv_unsigned w) (refuse_code_res r ++ [Z_to_bv 8 0]).
Proof.
  intros m r w MI ->. unfold refuse_code_addr, refuse_code_res. pose proof (refuse_idx_lt r) as H.
  destruct (refuse_idx r) as [|[|[|[|[|k]]]]]; [ | | | | | exfalso; lia];
    (apply ro_bytes_at;
       [ exact MI
       | apply Z.leb_le; vm_compute; reflexivity
       | apply Z.leb_le; vm_compute; reflexivity
       | apply ro_bytes_b_sound; vm_compute; reflexivity ]).
Qed.

(** A branch whose condition the context decides. *)
Ltac br := first [ if_false | if_true | idtac ].

(** strcmp of the code string with itself, then `bnez a0` (not taken), `ld ra, 8(sp)`, `addi sp, sp, 16`, `ret`. *)
Ltac strcmp_tail HSC k :=
  eapply evt_cut;
  [ eapply HSC with (sx := refuse_code_res k) (sy := refuse_code_res k);
      first [ apply code_str_at; [ assumption | vm_compute; reflexivity ] | apply refuse_code_res_nonul ]
  | let ms' := fresh "ms'" in let r := fresh "r" in let HR := fresh "HR" in
    intros ms' (r & ? & ? & ? & -> & HR);
    assert (r = Z_to_bv 64 0) by (apply HR; reflexivity); subst r; clear HR;
    rewrite ret_pc_even by (try lia; reflexivity);
    step; br; step; step; step ].

Theorem check_code_holds : strcmp_contract -> check_code_contract.
Proof.
  intros HSC. unfold check_code_contract, CHECK_CODE, CHECK_CODE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo HA1 HA0 ST HK HW MI.
  clear HW.
  (* r = a1 is one of 0..4: substitute the literal *)
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  assert (E : exists k, 0 <= k <= 4 /\ a1 = Z_to_bv 64 k).
  { exists (bv_unsigned a1). split; [lia|]. symmetry. apply Z_to_bv_lit_self. }
  destruct E as (k & Hk & ->). clear HA1 R1.
  rewrite unsigned_lit in HA0 by lia. subst a0.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 16, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia. clear Hk.
  destruct Ek as [-> | Ek].
  - (* r = 0: addi sp, sp, -16; sd ra, 8(sp); addiw a1, a1, -1; addi a2, zero, 3; bltu a2, a1: taken *)
    step. step. zstep. zstep. zstep. br.
    (* auipc a1; addi a1, a1, -0x393 ("none"); jal strcmp *)
    step. step. step.
    strcmp_tail HSC 0.
    release_frame FR ST Sp.
    finish.
  - destruct Ek as [-> | [-> | [-> | ->]]].
    all: (* addi sp, sp, -16; sd ra, 8(sp); addiw a1, a1, -1; addi a2, zero, 3; bltu a2, a1: not taken *)
      step; step; zstep; zstep; zstep; br;
      (* slli a1, a1, 2; auipc a2; addi a2 (CODE_TBL); add a1, a2, a1; lw a1, 0(a1); add a1, a2, a1; j; jal strcmp *)
      do 8 step.
    + strcmp_tail HSC 1. release_frame FR ST Sp. finish.
    + strcmp_tail HSC 2. release_frame FR ST Sp. finish.
    + strcmp_tail HSC 3. release_frame FR ST Sp. finish.
    + strcmp_tail HSC 4. release_frame FR ST Sp. finish.
Qed.
