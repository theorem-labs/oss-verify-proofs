(** Segment RD8 of the UBSan LLVMFuzzerTestOneInput walk: the COUNTER_LEDS reader (b = fuzz_u32),
    from the reader switch through the join 0x1438c to run()'s switch. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img codec_main_inv
  codec_main_rdlib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Section RD8.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** 0x13ac8-0x13b64, 0x13e34-0x13e40, 0x14278-0x14290, 0x1438c: b = fuzz_u32 with in.n loaded from
    the frame, stored at 0x3c; to run()'s switch. *)
Lemma rd8_b : forall (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kw k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kab k 0 0)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13ac8 m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14390.
  all: rd_to_run k RUN.
  all: first [ apply KW; bnd | eassumption | bnd ].
Qed.

(** T1[8] = 0x13ac8. *)
Lemma rd8_ok : forall i, 0 <= i <= 2 -> rd_ok E n 8 i.
Proof.
  intros i HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC0 HCN FR ST MU WM HMI.
  change (pc_rd 8) with 0x13ac8.
  pose proof (kw_head 8 i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HI) as KW.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  exact (rd8_b (k_head 8 i) (bv_unsigned cur) (bv_unsigned rem) ops
           ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
           u0 pj tj plj m1 KW Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
           F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD8.

Lemma codec_main_rd8 : seg_rd8_stmt.
Proof.
  unfold seg_rd8_stmt. intros E n ENV RUN i HI. exact (rd8_ok E n ENV RUN i HI).
Qed.
