(** Segment RD1/RD2 of the UBSan LLVMFuzzerTestOneInput walk: the BUTTON reader (a = fuzz_u32,
    b = fuzz_u32, c = fuzz_u32) and the TOUCH reader (a = fuzz_u32, c = fuzz_u32), from the reader
    switch to run()'s switch; the c read is the tail the two share. *)
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

(** Every a, b and c three u32 reads can produce give a record run() accepts (delta stays the
    record's). *)
Definition kwabc (k : kcall) : Prop :=
  forall a b c, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> rec_wf (kfl k a b c (k_delta k)).

Lemma kwabc_head : forall kind i, (kind = 1 \/ kind = 2) -> 0 <= i <= 2 -> kwabc (k_head kind i).
Proof.
  intros kind i HK HI a b c Ha Hb Hc.
  exact (rec_wf_head kind i a b c 0 ltac:(lia) HI
           (reader_ok_zero kind a b c 0 Ha Hb Hc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

(** The record well-formed for every u32 c, with a, b and delta already stored: what the shared
    c-reading tail of BUTTON and TOUCH needs. *)
Definition kwc (k : kcall) (x y w : Z) : Prop :=
  forall z, 0 <= z < 2 ^ 32 -> rec_wf (kfl k x y z w).

(** The tail's [kwc] goal from [kwabc] and the ranges of the stored a and b. *)
Ltac kwc_of_kwabc KW :=
  let z := fresh "z" in let Hz := fresh "Hz" in
  intros z Hz; apply KW; first [ exact Hz | bnd ].

(** ---- the tail RD1+2: c = fuzz_u32, shared by BUTTON and TOUCH ---- *)

Section RD12TAIL.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** 0x14328-0x14348: in.n was 0 when the c read started (a0 = 0), so c = 0; to run()'s switch. *)
Lemma rd12_tail_zero : forall (k : kcall) (x y w cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwc k x y w -> bv_unsigned a0' = 0 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k x y 0 w)) ->
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
                          ops 0x14328 m1).
Proof.
  intros k x y w cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KWC HA0 Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rewrite <- (Z_to_bv_lit_self a0'), HA0.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  drive 0x14390.
  rd_to_run k RUN.
  all: first [ apply KWC; bnd | eassumption | bnd ].
Qed.

(** 0x14094-0x14124, 0x14334-0x14348: c = fuzz_u32 with in.n = rz >= 1 in a0; to run()'s switch. *)
Lemma rd12_tail_go : forall (k : kcall) (x y w cz rz ops : Z)
    (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwc k x y w -> 1 <= rz ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k x y 0 w)) ->
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
                          ops 0x14094 m1).
Proof.
  intros k x y w cz rz ops ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KWC H1 Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; [exfalso; lia | ..]; try subst rz.
  all: rd_p0.
  all: drive 0x14390.
  all: rd_to_run k RUN.
  all: first [ apply KWC; bnd | eassumption | bnd ].
Qed.

End RD12TAIL.

(** The c read of the shared tail from a reader's branch on in.n (0x14324 for BUTTON, 0x14090 for
    TOUCH), the goal at 0x14094 or 0x14328 and the record hypothesis unfolded: a, b, delta and the
    cursor read off the frame. Leaves only the record's [kwc] goal. *)
Ltac rd12_to_tail E n ENV RUN k :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384)
           (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?X) :: C4 (Z_to_bv 64 ?Y) :: _ :: C4 (Z_to_bv 64 ?W) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)] |- ?G =>
    lazymatch G with
    | evt _ _ (MS _ _ (Z_to_bv 64 0x14094) _ _ _ _) => eapply (rd12_tail_go E n ENV RUN k X Y W CZ RZ)
    | evt _ _ (MS _ _ (Z_to_bv 64 0x14328) _ _ _ _) => eapply (rd12_tail_zero E n ENV RUN k X Y W CZ RZ)
    end;
    try first [ eassumption | (rewrite unsigned_lit by lia; lia) | bnd ]
  end.

Section RD12.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** 0x13fcc-0x1406c, 0x14304-0x14324: BUTTON's b = fuzz_u32 with in.n in a0, stored at 0x3c; then
    the branch on in.n at 0x14324 into the shared c tail. *)
Lemma rd1_b : forall (k : kcall) (x cz rz ops : Z)
    (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwabc k -> 0 <= x < 2 ^ 32 ->
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
                          ops 0x13fcc m1).
Proof.
  intros k x cz rz ops ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW Hx Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14324.
  (* 0x14324: bnez a0, 0x14094; keep the branch fact, the tail lemma needs it *)
  all: zstep.
  all: let BR := fresh "BR" in if_cases BR; zify_cond BR; try (exfalso; lia).
  all: rd12_to_tail E n ENV RUN k.
  all: kwc_of_kwabc KW.
Qed.

(** The end of BUTTON's a read at 0x13fcc: a stored, in.n in a0 and in memory. *)
Ltac rd1_to_b :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384) (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?X) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)],
    KW : kwabc ?k |- _ =>
      eapply (rd1_b k X CZ RZ); first [ exact KW | eassumption | bnd ]
  end.

(** 0x13714-0x137b0, 0x13d94-0x13da0, 0x13e64-0x13e68, 0x13fac-0x13fc8: BUTTON's a = fuzz_u32. *)
Lemma rd1_a : forall (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwabc k ->
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
                          ops 0x13714 m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x13fcc.
  all: rd1_to_b.
Qed.

(** 0x137b4-0x13850, 0x13da4-0x13db0, 0x13e6c-0x13e70, 0x14070-0x14090: TOUCH's a = fuzz_u32,
    stored at 0x38; then the branch on in.n at 0x14090 into the shared c tail. *)
Lemma rd2_a : forall (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwabc k ->
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
                          ops 0x137b4 m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14090.
  (* 0x14090: beqz a0, 0x14328; keep the branch fact, the tail lemma needs it *)
  all: zstep.
  all: let BR := fresh "BR" in if_cases BR; zify_cond BR; try (exfalso; lia).
  all: rd12_to_tail E n ENV RUN k.
  all: kwc_of_kwabc KW.
Qed.

(** T1[1] = 0x13714 (BUTTON), T1[2] = 0x137b4 (TOUCH). *)
Lemma rd12_ok : forall kind i, (kind = 1 \/ kind = 2) -> 0 <= i <= 2 -> rd_ok E n kind i.
Proof.
  intros kind i HK HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (kwabc_head kind i HK HI) as KW.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  destruct HK as [-> | ->].
  - change (pc_rd 1) with 0x13714.
    exact (rd1_a (k_head 1 i) (bv_unsigned cur) (bv_unsigned rem) ops
             ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
             u0 pj tj plj m1 KW Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
             F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
  - change (pc_rd 2) with 0x137b4.
    exact (rd2_a (k_head 2 i) (bv_unsigned cur) (bv_unsigned rem) ops
             ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
             u0 pj tj plj m1 KW Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
             F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD12.

Lemma codec_main_rd1 : seg_rd1_stmt.
Proof.
  unfold seg_rd1_stmt. intros E n ENV RUN i HI. split.
  - apply (rd12_ok E n ENV RUN 1 i); [left; reflexivity | exact HI].
  - apply (rd12_ok E n ENV RUN 2 i); [right; reflexivity | exact HI].
Qed.
