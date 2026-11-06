(** Segment RD0/7 of the UBSan LLVMFuzzerTestOneInput walk: the reader block that FADER and
    STRIP_LEDS share (a = fuzz_u32, b = fuzz_u32), from the reader switch to run()'s switch. *)
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

Section RD07.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** 0x13c48: the branch on in.n (a0) into the shared b tail of the library. *)
Lemma rd07_mid : forall (k : kcall) (x cz rz ops : Z)
    (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kw k -> 0 <= x < 2 ^ 32 ->
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
  evt rsegs (Qk E) (rd_st E ra' t0' t1' t2' (Z_to_bv 64 rz) a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6'
                          ops 0x13c48 m1).
Proof.
  intros k x cz rz ops ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW Hx Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. rd_p0. unfold rd_st. rd_unfold_k FK.
  destruct (Z.eq_dec rz 0) as [R | R]; [subst rz; drive 0x14370 | drive 0x13c4c].
  all: rd_to_tail E n ENV RUN k.
  all: exact (fun y Hy => KW x y Hx Hy).
Qed.

(** The end of the first u32 at 0x13c48: a stored, in.n in a0 and in memory. *)
Ltac rd_to_mid :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384) (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?X) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)],
    KW : kw ?k |- _ =>
      eapply (rd07_mid k X CZ RZ); first [ exact KW | eassumption | bnd ]
  end.

(** 0x13448-0x134e4, 0x13c10-0x13c44: a = fuzz_u32. *)
Lemma rd07_a : forall (k : kcall) (cz rz ops : Z)
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
                          ops 0x13448 m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KW Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x13c48.
  all: rd_to_mid.
Qed.

(** T1[0] = T1[7] = 0x13448. *)
Lemma rd07_ok : forall kind i, (kind = 0 \/ kind = 7) -> 0 <= i <= 2 -> rd_ok E n kind i.
Proof.
  intros kind i HK HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC0 HCN FR ST MU WM HMI.
  replace (pc_rd kind) with 0x13448 by (destruct HK as [-> | ->]; reflexivity).
  pose proof (kw_head kind i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HI) as KW.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  exact (rd07_a (k_head kind i) (bv_unsigned cur) (bv_unsigned rem) ops
           ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
           u0 pj tj plj m1 KW Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
           F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD07.

Lemma codec_main_rd0 : seg_rd0_stmt.
Proof.
  unfold seg_rd0_stmt. intros E n ENV RUN i HI. split.
  - apply (rd07_ok E n ENV RUN 0 i); [left; reflexivity | exact HI].
  - apply (rd07_ok E n ENV RUN 7 i); [right; reflexivity | exact HI].
Qed.
