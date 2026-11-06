(** Segment RD5 of the UBSan LLVMFuzzerTestOneInput walk: the RING reader (a = fuzz_u32,
    b = fuzz_u16), from the reader switch through the joins 0x14388 / 0x1438c to run()'s switch. *)
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

(** Every u32 a and u16 b give a record run() accepts. *)
Definition kw5 (k : kcall) : Prop :=
  forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 16 -> rec_wf (kab k a b).

Lemma kw5_head : forall i, 0 <= i <= 2 -> kw5 (k_head 5 i).
Proof.
  intros i HI a b Ha Hb.
  exact (rec_wf_head 5 i a b 0 0 ltac:(lia) HI
           (reader_ok_zero 5 a b 0 0 Ha ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

(** The bytes left when the u16 read starts: none, one, or the whole u16. *)
Lemma rem_cases2 : forall rem, 0 <= rem -> rem = 0 \/ rem = 1 \/ 2 <= rem.
Proof. intros. lia. Qed.

Section RD5.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** 0x14228-0x14274, 0x14af4-0x14af8, 0x14388-0x1438c: b = fuzz_u16 with in.n in a1, stored at
    0x3c; to run()'s switch. *)
Lemma rd5_b : forall (k : kcall) (x cz rz ops : Z)
    (ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kw5 k -> 0 <= x < 2 ^ 32 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kab k x 0)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' a0' (Z_to_bv 64 rz) a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x14228 m1).
Proof.
  intros k x cz rz ops ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW5 Hx Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases2 rz Hrz) as [R | [R | R]]; try subst rz.
  all: rd_p0.
  all: drive 0x14390.
  all: rd_to_run k RUN.
  all: first [ apply KW5; bnd | eassumption | bnd ].
Qed.

(** The end of the a read at 0x14228: a stored, in.n in a1 and in memory. *)
Ltac rd5_to_b :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384) (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?X) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)],
    KW5 : kw5 ?k |- _ =>
      eapply (rd5_b k X CZ RZ); first [ exact KW5 | eassumption | bnd ]
  end.

(** 0x139fc-0x13a98, 0x13dd4-0x13de0, 0x13e7c-0x13e80, 0x14208-0x14224: a = fuzz_u32. *)
Lemma rd5_a : forall (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kw5 k ->
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
                          ops 0x139fc m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW5 Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14228.
  all: rd5_to_b.
Qed.

(** T1[5] = 0x139fc. *)
Lemma rd5_ok : forall i, 0 <= i <= 2 -> rd_ok E n 5 i.
Proof.
  intros i HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC0 HCN FR ST MU WM HMI.
  change (pc_rd 5) with 0x139fc.
  pose proof (kw5_head i HI) as KW5.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  exact (rd5_a (k_head 5 i) (bv_unsigned cur) (bv_unsigned rem) ops
           ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
           u0 pj tj plj m1 KW5 Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
           F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD5.

Lemma codec_main_rd5 : seg_rd5_stmt.
Proof.
  unfold seg_rd5_stmt. intros E n ENV RUN i HI. exact (rd5_ok E n ENV RUN i HI).
Qed.
