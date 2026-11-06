(** Segments RD3 and RD4 of the UBSan LLVMFuzzerTestOneInput walk: the VPOT reader (a = fuzz_u32,
    delta = (int32_t) fuzz_u32) and the JOG reader (delta = (int32_t) fuzz_u32), from the reader switch
    through their shared delta store 0x142fc-0x14300 to run()'s switch. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img codec_main_inv
  codec_main_lib codec_main_rdlib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the signed delta ---- *)

Lemma s32_range : forall v, 0 <= v < 2 ^ 32 -> - 2 ^ 31 <= s32 v < 2 ^ 31.
Proof. intros v Hv. unfold s32. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.

(** The 4 bytes of the int field holding (int32_t) v are those of v. *)
Lemma le4_s32 : forall v, 0 <= v < 2 ^ 32 -> le4 (Z_to_bv 64 (s32 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v Hv. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 (s32 v mod 2 ^ 64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2 ^ 64) 32) by (cbn; lia).
  f_equal. unfold s32. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
  Z.div_mod_to_equations. lia.
Qed.

(** The delta cell (index 7 of the record) as the record's (int32_t) of the stored u32. *)
Lemma rw_cells_delta_s32 : forall m A c0 c1 c2 c3 c4 c5 c6 rest X, 0 <= X < 2 ^ 32 ->
  rw_cells rsegs m A (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: C4 (Z_to_bv 64 X) :: rest) ->
  rw_cells rsegs m A (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: C4 (Z_to_bv 64 (s32 X)) :: rest).
Proof.
  intros m A c0 c1 c2 c3 c4 c5 c6 rest X HX H. pose proof H as [[W _] _].
  refine (rw_cells_same_bytes m A _ _ _ _ _ H).
  - cbn [cells_wf cell_wf] in *. tauto.
  - cbn [cells_bytes cbytes]. rewrite le4_s32 by exact HX. reflexivity.
  - reflexivity.
Qed.

(** Every u32 a and int delta give a record run() accepts (b and c 0). *)
Definition kwd (k : kcall) : Prop :=
  forall a d, 0 <= a < 2 ^ 32 -> - 2 ^ 31 <= d < 2 ^ 31 -> rec_wf (kfl k a 0 0 d).

Lemma kwd_head : forall kind i, 0 <= kind <= 11 -> kind <> 5 -> kind <> 10 -> kind <> 11 -> 0 <= i <= 2 ->
  kwd (k_head kind i).
Proof.
  intros kind i HK H5 H10 H11 HI a d Ha Hd.
  exact (rec_wf_head kind i a 0 0 d HK HI
           (reader_ok_zero kind a 0 0 d Ha ltac:(lia) ltac:(lia) Hd ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

Section RD34.
Variable E : cenv.
Variable n : nat.
Hypothesis ENV : env_ok E.
Hypothesis RUN : rd_run E n.

(** At 0x14390 after the delta store: the delta cell as s32 of the stored u32, then [rd_end]. *)
Ltac rd_delta_end k :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384)
           (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: C4 (Z_to_bv 64 ?X) :: ?rest) |- _ =>
      let FK' := fresh "FK" in
      pose proof (rw_cells_delta_s32 _ _ c0 c1 c2 c3 c4 c5 c6 rest X ltac:(bnd) FK) as FK';
      clear FK
  end;
  lazymatch goal with KWD : kwd k |- _ =>
    rd_to_run k RUN;
    first [ apply KWD; [ bnd | apply s32_range; bnd ] | eassumption | bnd ]
  end.

(** 0x13eac-0x13f44, 0x142e4-0x14300: VPOT's delta = fuzz_u32 with in.n in a0; to run()'s switch. *)
Lemma rd3_d : forall (k : kcall) (x cz rz ops : Z)
    (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwd k -> 0 <= x < 2 ^ 32 ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k x 0 0 0)) ->
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
                          ops 0x13eac m1).
Proof.
  intros k x cz rz ops ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KWD Hx Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14390.
  all: rd_delta_end k.
Qed.

(** The end of VPOT's a read at 0x13eac: a stored, in.n in a0 and in memory. *)
Ltac rd3_to_d :=
  lazymatch goal with
  | FK : rw_cells _ _ (bv_unsigned (c_sp E) + -384) (_ :: _ :: _ :: _ :: C4 (Z_to_bv 64 ?X) :: _),
    FIN : rw_cells _ _ (bv_unsigned (c_sp E) + -200) [C8 (Z_to_bv 64 ?CZ); C8 (Z_to_bv 64 ?RZ)],
    KWD : kwd ?k |- _ =>
      eapply (rd3_d k X CZ RZ); first [ exact KWD | eassumption | bnd ]
  end.

(** 0x13588-0x13624, 0x13d30-0x13d3c, 0x13e54-0x13e58, 0x13e8c-0x13ea8: VPOT's a = fuzz_u32. *)
Lemma rd3_a : forall (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwd k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k 0 0 0 0)) ->
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
                          ops 0x13588 m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KWD Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x13eac.
  all: rd3_to_d.
Qed.

(** 0x138f4-0x13990, 0x13dc4-0x13dd0, 0x141ec-0x14204, 0x142fc-0x14300: JOG's delta = fuzz_u32 (in.n
    in a3); to run()'s switch. *)
Lemma rd4_d : forall (k : kcall) (cz rz ops : Z)
    (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
    (u0 pj tj plj : list byte) (m1 : word -> option byte),
  kwd k ->
  256 - ops <= Z.of_nat n -> 0 <= ops <= 255 ->
  bv_unsigned (c_p E) <= cz -> 0 <= rz -> cz - bv_unsigned (c_p E) + rz = Z.of_nat (length (c_data E)) ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416) [CB 8 u0] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -408)
    [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ->
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -384) (kcall_cells (kfl k 0 0 0 0)) ->
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
                          ops 0x138f4 m1).
Proof.
  intros k cz rz ops ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' u0 pj tj plj m1
    KWD Ho1 Ho2 Hcz Hrz Hcr F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI.
  rd_pre. unfold rd_st. rd_unfold_k FK.
  destruct (rem_cases rz Hrz) as [R | [R | [R | [R | R]]]]; try subst rz.
  all: rd_p0.
  all: drive 0x14390.
  all: rd_delta_end k.
Qed.

(** T1[3] = 0x13588 (VPOT) and T1[4] = 0x138f4 (JOG). *)
Lemma rd34_ok : forall kind i, (kind = 3 \/ kind = 4) -> 0 <= i <= 2 -> rd_ok E n kind i.
Proof.
  intros kind i HK HI. unfold rd_ok.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
    _ Ho1 Ho2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof (kwd_head kind i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HI) as KWD.
  destruct FR as (_ & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  rewrite <- (Z_to_bv_lit_self cur), <- (Z_to_bv_lit_self rem) in FIN.
  pose proof (bv_unsigned_in_range 64 rem) as Rr. unfold bv_modulus in Rr.
  destruct HK as [-> | ->].
  - change (pc_rd 3) with 0x13588.
    exact (rd3_a (k_head 3 i) (bv_unsigned cur) (bv_unsigned rem) ops
             ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
             u0 pj tj plj m1 KWD Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
             F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
  - change (pc_rd 4) with 0x138f4.
    exact (rd4_d (k_head 4 i) (bv_unsigned cur) (bv_unsigned rem) ops
             ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (pers_of i)) s7' t3' t4' t5' t6'
             u0 pj tj plj m1 KWD Ho1 Ho2 ltac:(lia) ltac:(lia) ltac:(lia)
             F0 F8 FK FIN FPD FTX FPL FSV ST MU WM HMI).
Qed.

End RD34.

Lemma codec_main_rd3 : seg_rd3_stmt.
Proof.
  unfold seg_rd3_stmt. intros E n ENV RUN i HI. split.
  - apply (rd34_ok E n ENV RUN 3 i); [left; reflexivity | exact HI].
  - apply (rd34_ok E n ENV RUN 4 i); [right; reflexivity | exact HI].
Qed.
