(** Segment RD6 of the UBSan LLVMFuzzerTestOneInput walk: the METER reader (a = fuzz_u32,
    c = fuzz_u32, b = fuzz_u32), from the reader switch to run()'s switch; the b read is the tail it
    shares with FADER / STRIP_LEDS. *)
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

(** Every a, b and c three u32 reads can produce give a record run() accepts. *)
Definition kw3 (k : kcall) : Prop :=
  forall a b c, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> rec_wf (kfl k a b c (k_delta k)).

Lemma kw3_head : forall i, 0 <= i <= 2 -> kw3 (k_head 6 i).
Proof.
  intros i HI a b c Ha Hb Hc.
  exact (rec_wf_head 6 i a b c 0 ltac:(lia) HI
           (reader_ok_zero 6 a b c 0 Ha Hb Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

(** The tail's [kwb] goal from [kw3] and the ranges of the stored a and c. *)
Ltac kwb_of_kw3 KW3 :=
  let y := fresh "y" in let Hy := fresh "Hy" in
  intros y Hy; apply KW3; first [ exact Hy | bnd ].

Section RD6.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** 0x14148-0x141e8, 0x1434c-0x1436c: c = fuzz_u32 with in.n in a0, stored at 0x40; then the branch
    on in.n at 0x1436c into the shared b tail. *)
Lemma rd6_c : forall (k : kcall) (x cz rz ops : Z)
    (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kw3 k -> 0 <= x < 2 ^ 32 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k x 0 0 (k_delta k))) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 cz); C8 (Z_to_bv 64 rz)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -184) [CB 5 pj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -179) [CB 65 tj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -114) [CB 10 plj] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -104) (saved E) ->
  stk rsegs m1 (c_lo E) (bv_unsigned (c_sp E) + -416) ->
  munch [(bv_unsigned (c_sp E) - 640, bv_unsigned (c_sp E))] (c_m E) m1 ->
  wmono rsegs (c_m E) m1 ->
  mem_inv rsegs m1 ->
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' (Z_to_bv 64 rz) a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x14148 m1).
Proof.
  intros k x cz rz ops ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW3 Hx Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x1436c.
  (* 0x1436c: bnez a0, 0x13c4c; keep the branch fact, the tail lemma needs it *)
  all: zstep.
  all: let BR := fresh "BR" in if_cases BR; zify_cond BR; try (exfalso; lia).
  all: rd_to_tail E n ENV RUN k.
  all: kwb_of_kw3 KW3.
Qed.

(** The end of the a read at 0x14148: a stored, in.n in a0 and in memory. *)
Ltac rd6_to_c :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384) (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?X) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)],
    KW3 : kw3 ?k |- _ =>
      eapply (rd6_c k X CZ RZ); first [ exact KW3 | eassumption | bnd ]
  end.

(** 0x13854-0x138f0, 0x13db4-0x13dc0, 0x13e74-0x13e78, 0x14128-0x14144: a = fuzz_u32. *)
Lemma rd6_a : forall (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kw3 k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k 0 0 0 (k_delta k))) ->
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
                          ops 0x13854 m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW3 Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14148.
  all: rd6_to_c.
Qed.

(** T1[6] = 0x13854. *)
Lemma rd6_ok : forall i, 0 <= i <= 2 -> rd_ok E n 6 i.
Proof.
  intros i HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC0 HCN FR ST MU WM HMI.
  change (pc_rd 6) with 0x13854.
  pose proof (kw3_head i HI) as KW3.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  exact (rd6_a (k_head 6 i) (bv_unsigned cur) (bv_unsigned rem) ops
           ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
           u0 pj tj plj m1 KW3 Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
           F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD6.

Lemma codec_main_rd6 : seg_rd6_stmt.
Proof.
  unfold seg_rd6_stmt. intros E n ENV RUN i HI. exact (rd6_ok E n ENV RUN i HI).
Qed.
