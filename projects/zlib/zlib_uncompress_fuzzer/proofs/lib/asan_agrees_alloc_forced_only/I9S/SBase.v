(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.I9S Require Export Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Export ZArr ZArr4 ZRd IDefs IMem ITac ISpecs IGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition ROMHI_S : Z := 135168.
Definition FR_INF : Z := 224.
Definition FR_UW : Z := 48.
Definition FR_IT : Z := 192.
Definition FR_IF : Z := 112.
Definition FR_AD : Z := 32.

Definition L_INFLATE : Z := 86600.
Definition L_DISP    : Z := 86964.
Definition L_DISP10  : Z := 86960.
Definition L_SETMODE : Z := 86956.
Definition L_DISP0   : Z := 86972.
Definition L_LEAVE   : Z := 93624.
Definition L_LEAVE_LD : Z := 93620.
Definition L_RET     : Z := 94020.
Definition L_NEED_DICT : Z := 94156.
Definition L_MEM     : Z := 93928.
Definition L_RELOAD_A1 : Z := 91724.
Definition L_RELOAD_RA : Z := 91728.
Definition L_RELOAD  : Z := 91732.
Definition L_BADMSG_S11 : Z := 91752.
Definition L_BADMSG_S10 : Z := 93024.
Definition L_BADMSG_A3 : Z := 92872.
Definition L_LEAVE_A4 : Z := 93484.
Definition L_HEAD : Z := 87008.
Definition L_DICTID : Z := 87200.
Definition L_DICT : Z := 87760.
Definition L_TYPE : Z := 87832.
Definition L_TYPEDO : Z := 87848.
Definition L_STORED : Z := 87280.
Definition L_COPY_ : Z := 88028.
Definition L_COPY : Z := 88036.
Definition L_TABLE : Z := 87364.
Definition L_LENLENS : Z := 87652.
Definition L_CODELENS : Z := 87184.
Definition L_LEN_ : Z := 91800.
Definition L_LEN : Z := 91808.
Definition L_LENEXT : Z := 87112.
Definition L_DIST : Z := 92396.
Definition L_DISTEXT : Z := 87192.
Definition L_MATCH : Z := 92968.
Definition L_LIT : Z := 87084.
Definition L_CHECK : Z := 87576.
Definition L_LENGTH : Z := 87668.
Definition L_DONE : Z := 94180.
Definition L_UW : Z := 94212.
Definition L_UW_CALL : Z := 93900.
Definition L_UW_RET : Z := 93904.
Definition T_ZW : Z := 94288.
Definition L_ZB : Z := 94292.
Definition L_ITABLE : Z := 95716.
Definition L_IFAST : Z := 99212.

Definition s_fix (cx : ictx) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -224 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kA0 = c_u cx /\ zget_l Rb l kA1 = 0 /\
  zget_l Rb l kS6 = c_p cx + 168 /\ zget_l Rb l kT6 = -16180 /\ zget_l Rb l kT4 = 30 /\ zget_l Rb l kS9 = JTAB_ADDR /\
  zget_l Rb l kS4 = 16209.

Definition s_vars (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kS2 = c_n cx - t_cin st /\
  zget_l Rb l kS3 = c_ob cx + t_cout st /\ zget_l Rb l kRA = c_osz cx - t_cout st /\
  zget_l Rb l kS7 = t_hold st /\ zget_l Rb l kS8 = t_bits st.

Definition s_regs_disp (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS10 = c_q cx + t_cin st.
Definition s_regs_d10 (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st.
Definition s_regs_d0 (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st /\ zget_l Rb l kA2 = t_mode st.
Definition s_regs_arm (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = c_q cx + t_cin st.
Definition s_regs_leave (cx : ictx) (st : ist) (rv : Z) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -224 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kA0 = c_u cx /\ zget_l Rb l kA1 = 0 /\
  zget_l Rb l kS11 = c_q cx + t_cin st /\ zget_l Rb l kS2 = c_n cx - t_cin st /\
  zget_l Rb l kS3 = c_ob cx + t_cout st /\ zget_l Rb l kRA = c_osz cx - t_cout st /\
  zget_l Rb l kS7 = t_hold st /\ zget_l Rb l kS8 = t_bits st /\
  zget_l Rb l kS1 = rv.
Definition s_regs_leave_ld (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -224 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kA0 = c_u cx /\ zget_l Rb l kA1 = 0 /\
  zget_l Rb l kS11 = c_q cx + t_cin st /\ zget_l Rb l kS2 = c_n cx - t_cin st /\
  zget_l Rb l kS3 = c_ob cx + t_cout st /\ zget_l Rb l kRA = c_osz cx - t_cout st /\
  zget_l Rb l kS7 = t_hold st /\ zget_l Rb l kS8 = t_bits st.
Definition s_regs_ret (cx : ictx) (rc : Z) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -224 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS5 = rc.
Definition s_regs_entry (cx : ictx) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx /\ zget_l Rb l kA0 = c_u cx /\ zget_l Rb l kA1 = 0 /\
  zget_l Rb l kRA = c_K cx kRA /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_K cx kS0 /\ zget_l Rb l kS1 = c_K cx kS1 /\ zget_l Rb l kS2 = c_K cx kS2 /\
  zget_l Rb l kS3 = c_K cx kS3 /\ zget_l Rb l kS4 = c_K cx kS4 /\ zget_l Rb l kS5 = c_K cx kS5 /\
  zget_l Rb l kS6 = c_K cx kS6 /\ zget_l Rb l kS7 = c_K cx kS7 /\ zget_l Rb l kS8 = c_K cx kS8 /\
  zget_l Rb l kS9 = c_K cx kS9 /\ zget_l Rb l kS10 = c_K cx kS10 /\ zget_l Rb l kS11 = c_K cx kS11.

Definition i_frame (cx : ictx) (M : mem) : Prop :=
  let u := c_u cx in let p := c_p cx in let K := c_K cx in
  mem_u64 R_segs M (u + -8) (K kRA) /\ mem_u64 R_segs M (u + -16) (K kS0) /\ mem_u64 R_segs M (u + -24) (K kS1) /\
  mem_u64 R_segs M (u + -32) (K kS2) /\ mem_u64 R_segs M (u + -40) (K kS3) /\ mem_u64 R_segs M (u + -48) (K kS4) /\
  mem_u64 R_segs M (u + -56) (K kS5) /\ mem_u64 R_segs M (u + -64) (K kS6) /\ mem_u64 R_segs M (u + -72) (K kS7) /\
  mem_u64 R_segs M (u + -80) (K kS8) /\ mem_u64 R_segs M (u + -88) (K kS9) /\ mem_u64 R_segs M (u + -96) (K kS10) /\
  mem_u64 R_segs M (u + -104) (K kS11) /\
  mem_u64 R_segs M (u + -120) 0 /\
  mem_u64 R_segs M (u + -128) (u) /\
  mem_u64 R_segs M (u + -136) (-16180) /\
  mem_u64 R_segs M (u + -152) 16209 /\
  mem_u64 R_segs M (u + -168) (c_n cx - c_cin0 cx) /\
  mem_u64 R_segs M (u + -176) (p + 7160) /\
  mem_u64 R_segs M (u + -184) (-5) /\
  mem_u64 R_segs M (u + -192) (p + 160) /\
  mem_u64 R_segs M (u + -200) (p + 808) /\
  mem_u64 R_segs M (u + -208) (p + 1384) /\
  mem_u64 R_segs M (u + -216) (p + 136) /\
  mem_u64 R_segs M (u + -224) (p + 140).
Definition s_ret (cx : ictx) (st : ist) (M : mem) : Prop := mem_u64 R_segs M (c_u cx + -160) (t_ret st).
Definition s_out (cx : ictx) (st : ist) (M : mem) : Prop := mem_u64 R_segs M (c_u cx + -144) (t_out st).

Definition i_frame_ok (cx : ictx) (a k : Z) : Prop :=
  a + k <= c_u cx + -224 \/ c_u cx <= a \/
  (c_u cx + -160 <= a /\ a + k <= c_u cx + -152) \/ (c_u cx + -144 <= a /\ a + k <= c_u cx + -136) \/
  (c_u cx + -112 <= a /\ a + k <= c_u cx + -104).

Lemma i_frame_frame : forall cx M a bs,
  i_frame cx M -> 0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 -> 0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  i_frame_ok cx a (Z.of_nat (length bs)) ->
  i_frame cx (wbytes M (w64 a) bs).
Proof.
  intros cx M a bs H Hu1 Hu2 Ha Hl Ha2 D. unfold i_frame, i_frame_ok in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25).
  repeat split; (apply mem_u64_frame; [assumption | unfold zdisj; lia_std]).
Qed.

Lemma i_frame_magreeL : forall cx M0 M rs,
  magreeL M0 M rs -> i_frame cx M0 -> 0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  disj_all (c_u cx + -224) 64 rs -> disj_all (c_u cx + -152) 8 rs -> disj_all (c_u cx + -136) 24 rs -> disj_all (c_u cx + -104) 104 rs ->
  i_frame cx M.
Proof.
  intros cx M0 M rs HA H Hu1 Hu2 D1 D2 D3 D4. unfold i_frame in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25).
  repeat split;
    (eapply mem_u64_magreeL;
     [ exact HA | eassumption | lia_std | lia_std
     | first [ solve [eapply (disj_all_sub rs); [exact D1 | lia_std | lia_std]]
             | solve [eapply (disj_all_sub rs); [exact D2 | lia_std | lia_std]]
             | solve [eapply (disj_all_sub rs); [exact D3 | lia_std | lia_std]]
             | solve [eapply (disj_all_sub rs); [exact D4 | lia_std | lia_std]] ] ]).
Qed.

Definition i_hooks (cx : ictx) (M : mem) : Prop :=
  mem_u64 R_segs M (c_u cx + 64) A_ZCALLOC /\ mem_u64 R_segs M (c_u cx + 72) A_ZCFREE.
Lemma i_hooks_frame : forall cx M a bs,
  i_hooks cx M -> 0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  (a + Z.of_nat (length bs) <= c_u cx + 56 \/ c_u cx + 88 <= a) ->
  i_hooks cx (wbytes M (w64 a) bs).
Proof.
  intros cx M a bs [A B] Hu1 Hu2 Ha Hl Ha2 D. split; (apply mem_u64_frame; [assumption | unfold zdisj; lia_std]).
Qed.
Lemma i_hooks_magreeL : forall cx M0 M rs,
  magreeL M0 M rs -> i_hooks cx M0 -> 0 <= c_u cx -> c_u cx + 208 <= two64 -> disj_all (c_u cx + 56) 32 rs -> i_hooks cx M.
Proof.
  intros cx M0 M rs HA [A B] Hu1 Hu2 D.
  split; (eapply mem_u64_magreeL; [exact HA | eassumption | lia_std | lia_std | eapply (disj_all_sub rs); [exact D | lia_std | lia_std]]).
Qed.

Definition wb_bounds (u p a len : Z) : Prop :=
  0 <= u + -1024 /\ u + 208 <= two64 /\ 0 <= p /\ p + STATE_SIZE <= two64 /\ 0 <= a /\ 0 < len /\ a + len <= two64.
Lemma i_frame_frame1 : forall cx M a bs,
  i_frame cx M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) -> i_frame_ok cx a (Z.of_nat (length bs)) ->
  i_frame cx (wbytes M (w64 a) bs).
Proof. intros cx M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D. apply i_frame_frame; assumption. Qed.
Lemma i_hooks_frame1 : forall cx M a bs,
  i_hooks cx M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_u cx + 56 \/ c_u cx + 88 <= a) -> i_hooks cx (wbytes M (w64 a) bs).
Proof. intros cx M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D. apply i_hooks_frame; try assumption. lia_std. Qed.
Lemma i_cst_frame1 : forall cx M a bs,
  i_cst R_segs cx M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_u cx + 56 \/ c_u cx + 88 <= a) ->
  (a + Z.of_nat (length bs) <= c_p cx \/ (c_p cx + 8 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 16) \/
   (c_p cx + 24 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 56) \/ (c_p cx + 76 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 88) \/
   (c_p cx + 96 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 7160) \/ c_p cx + 7164 <= a) ->
  i_cst R_segs cx (wbytes M (w64 a) bs).
Proof. intros cx M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D1 D2. apply i_cst_frame; try assumption; [lia_std | split; assumption]. Qed.
Definition st_hole (p a k : Z) : Prop :=
  (p + 16 <= a /\ a + k <= p + 28) \/ (p + 32 <= a /\ a + k <= p + 76) \/ (p + 88 <= a /\ a + k <= p + 108) \/ p + 168 <= a.
Lemma st_rest_frameH : forall cx st M a bs,
  st_rest R_segs cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_p cx + 12 \/ st_hole (c_p cx) a (Z.of_nat (length bs))) ->
  st_rest R_segs cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D. unfold st_rest, st_hole, STATE_SIZE in *.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.
Lemma st_at_frameH : forall cx st M a bs,
  st_at R_segs cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_p cx + 8 \/ st_hole (c_p cx) a (Z.of_nat (length bs))) ->
  st_at R_segs cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs [Hm H] HB D. split.
  - dand HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold st_hole, STATE_SIZE in *.
    apply mem_u32_frame; [exact Hm | unfold zdisj; lia_std].
  - apply st_rest_frameH; [exact H | exact HB | unfold st_hole in *; lia_std].
Qed.
Lemma strm_at_frameH : forall cx st M a bs,
  strm_at R_segs cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_u cx \/ (c_u cx + 12 <= a /\ a + Z.of_nat (length bs) <= c_u cx + 24) \/ c_u cx + 36 <= a) ->
  (a + Z.of_nat (length bs) <= c_p cx + 96 \/ c_p cx + 108 <= a) -> strm_at R_segs cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D1 D2. unfold strm_at, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.
Lemma rom_ok_frame1 : forall M a bs,
  rom_ok M -> (0 <= a /\ a + Z.of_nat (length bs) <= two64) -> zdisj a (Z.of_nat (length bs)) ROM_LO (ROM_HI - ROM_LO) ->
  rom_ok (wbytes M (w64 a) bs).
Proof. intros M a bs H [B1 B2] D. apply rom_ok_frame; assumption. Qed.

Definition s_std (cx : ictx) (fin : Z -> Z) (M : mem) : Prop :=
  rom_ok M /\
  mem_wr R_segs M (c_u cx + -1024) 1232 /\
  mem_wr R_segs M (c_p cx) STATE_SIZE /\
  mem_wr R_segs M (c_ob cx) (c_osz cx) /\
  mem_wr R_segs M (c_w cx) (wsz cx) /\
  i_frame cx M /\ i_cst R_segs cx M /\ i_hooks cx M /\
  mem_arr 1 R_segs M (c_q cx) (c_n cx) fin.

End FXG.
Ltac open_std H :=
  dand H as (ROM & Wstk & Wp & Wob & Ww & FRM & CST & HK & Hin).
Ltac close_std := unfold s_std; icx_cbn; split_conj; assumption.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zwb_x a :=
  first [ lazymatch goal with |- ?G => match goal with W : G |- _ => exact W end end
        | unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia ].
Ltac zwb_pre M a bs :=
  try (let W := fresh "ZWBs" in
       lazymatch goal with
       | H : i_frame ?cx M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       | H : i_cst _ ?cx M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       | H : st_rest _ ?cx _ M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       | H : st_at _ ?cx _ M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       end).
Ltac zwb_post a := repeat match goal with W : wb_bounds _ _ a (Z.of_nat (length _)) |- _ => clear W end.
Ltac zmem_transport_loop_SBase M a bs :=
  repeat match goal with
  | H : i_frame ?cx M |- _ =>
      first [ apply (i_frame_frame1 cx M a bs) in H;
              [| zwb_x a | unfold i_frame_ok; icx_cbn; zlen_norm; zlia ]
            | idtac "WARNING: i_frame dropped at store" a; clear H ]
  | H : i_cst ?segs ?cx M |- _ =>
      first [ apply (i_cst_frame1 cx M a bs) in H;
              [| zwb_x a | icx_cbn; zlen_norm; zlia | icx_cbn; zlen_norm; zlia ]
            | idtac "WARNING: i_cst dropped at store" a; clear H ]
  | H : i_hooks ?cx M |- _ =>
      first [ apply (i_hooks_frame1 cx M a bs) in H;
              [| zwb_x a | icx_cbn; zlen_norm; zlia ]
            | idtac "WARNING: i_hooks dropped at store" a; clear H ]
  | H : st_at ?segs ?cx ?st M |- _ =>
      first [ apply (st_at_frameH cx st M a bs) in H;
              [| zwb_x a | unfold st_hole; icx_cbn; zlen_norm; zlia ]
            | idtac "NOTE: st_at dropped at store (open it before writing state fields)" a; clear H ]
  | H : st_rest ?segs ?cx ?st M |- _ =>
      first [ apply (st_rest_frameH cx st M a bs) in H;
              [| zwb_x a | unfold st_hole; icx_cbn; zlen_norm; zlia ]
            | idtac "NOTE: st_rest dropped at store (open it before writing state fields other than mode)" a; clear H ]
  | H : strm_at ?segs ?cx ?st M |- _ =>
      first [ apply (strm_at_frameH cx st M a bs) in H;
              [| zwb_x a | icx_cbn; zlen_norm; zlia | icx_cbn; zlen_norm; zlia ]
            | idtac "NOTE: strm_at dropped at store" a; clear H ]
  | H : s_ret ?cx ?st M |- _ =>
      first [ unfold s_ret in H; apply (mem_u64_frame _ M a bs) in H; [|icx_cbn; zdisj_tac]; change (s_ret cx st (wbytes M (w64 a) bs)) in H
            | idtac "NOTE: s_ret dropped at store" a; clear H ]
  | H : s_out ?cx ?st M |- _ =>
      first [ unfold s_out in H; apply (mem_u64_frame _ M a bs) in H; [|icx_cbn; zdisj_tac]; change (s_out cx st (wbytes M (w64 a) bs)) in H
            | idtac "NOTE: s_out dropped at store" a; clear H ]
  | H : mem_arr ?k ?segs M ?base ?n ?f |- _ =>
      first [ apply (mem_arr_frame segs k M base n f a bs) in H; [|unfold zdisj; zlen_norm; zlia]
            | idtac "WARNING: mem_arr fact dropped at store" a base; clear H ]
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 8;
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 4;
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 2;
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 1;
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      zrng_ensure a' (Z.of_nat (length bs'));
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_frame segs M a bs a' len) in H; [|zdisj_tac]
            | let H1 := fresh "Zl" in let H2 := fresh "Zh" in
              destruct (mem_zero_split_store segs M a bs a' len H ltac:(zlia) ltac:(zlen_norm; zlia) ltac:(zlia) ltac:(zlia) ltac:(zlen_norm; zlia)) as [H1 H2];
              clear H;
              rewrite ?length_app, ?repeat_length, ?length_map, ?length_Z_to_le_bytes', ?Nat2Z.inj_add in H2;
              cbn [length] in H1, H2; znat_lits_in H1; znat_lits_in H2; zfold_in H1; zfold_in H2;
              znorm_zero_len H1; znorm_zero_len H2;
              try (lazymatch type of H1 with mem_zero _ _ _ ?z => lazymatch z with 0 => clear H1 end end);
              try (lazymatch type of H2 with mem_zero _ _ _ ?z => lazymatch z with 0 => clear H2 end end)
            | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_frame1 M a bs) in H; [| zlen_norm; zlia | unfold ROM_LO, ROM_HI; zdisj_tac]
            | idtac "WARNING: rom_ok dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | idtac "WARNING: framed fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | idtac "WARNING: framed2 fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stableL ?Fr _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; in_some_tac]
            | idtac "WARNING: framedL fact dropped at store" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.
End FXG.
Ltac zmem_transport M a bs ::=
  zwb_pre M a bs; zxfer_pre a bs;
  zmem_transport_loop_SBase M a bs;
  zxfer_post a; zwb_post a.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zreattachL_extra HA Mo Mn ::=
  try match goal with
  | H : rom_ok Mo |- _ =>
      first [ let H' := fresh in
              pose proof (rom_ok_magreeL Mo Mn _ H HA ltac:(unfold ROM_LO, ROM_HI; disj_all_tac)) as H';
              clear H; rename H' into H
            | idtac "zreattachL: dropped rom_ok"; clear H ]
  end;
  try match goal with
  | H : i_frame ?cx Mo |- _ =>
      first [ apply (i_frame_magreeL cx Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped i_frame"; clear H ]
  end;
  try match goal with
  | H : i_cst ?segs ?cx Mo |- _ =>
      first [ apply (i_cst_magreeL segs cx Mo Mn _ HA) in H;
              [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia
               | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped i_cst"; clear H ]
  end;
  try match goal with
  | H : i_hooks ?cx Mo |- _ =>
      first [ apply (i_hooks_magreeL cx Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped i_hooks"; clear H ]
  end;
  try match goal with
  | H : st_at ?segs ?cx ?st Mo |- _ =>
      first [ apply (st_at_magreeL segs cx st Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped st_at"; clear H ]
  end;
  try match goal with
  | H : st_rest ?segs ?cx ?st Mo |- _ =>
      first [ apply (st_rest_magreeL segs cx st Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped st_rest"; clear H ]
  end;
  try match goal with
  | H : strm_at ?segs ?cx ?st Mo |- _ =>
      first [ apply (strm_at_magreeL segs cx st Mo Mn _ HA) in H;
              [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped strm_at"; clear H ]
  end;
  try match goal with
  | H : s_ret ?cx ?st Mo |- _ =>
      first [ unfold s_ret in H; apply (mem_u64_magreeL1 _ Mo Mn _ _ _ HA) in H; [|solve [icx_cbn; zsideL]]; change (s_ret cx st Mn) in H
            | idtac "zreattachL: dropped s_ret"; clear H ]
  end;
  try match goal with
  | H : s_out ?cx ?st Mo |- _ =>
      first [ unfold s_out in H; apply (mem_u64_magreeL1 _ Mo Mn _ _ _ HA) in H; [|solve [icx_cbn; zsideL]]; change (s_out cx st Mn) in H
            | idtac "zreattachL: dropped s_out"; clear H ]
  end;
  repeat match goal with
  | H : mem_arr ?k ?segs Mo ?base ?n ?f |- _ =>
      first [ apply (mem_arr_magreeL segs k Mo Mn _ base n f HA) in H; [| disj_all_tac ]
            | idtac "zreattachL: dropped mem_arr at" base; clear H ]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac open_cx CX :=
  let CXl := fresh "CXl" in
  dand CX as (CXl & AL & SEP);
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_S] in CXl; destr_conj CXl.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac disj_all_tac ::= solve [ cbv [N_LENS N_CODES N_WORK STATE_SIZE WIN_SIZE ZS_SIZE FRA]; zconj_norm; repeat split; first [ exact I | zlia ] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zkeysb := zkeys; cbv [ROMHI_S FR_INF FR_UW FR_IT FR_IF FR_AD] in *.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac zgetl_nil := repeat match goal with H : zget_l ?R [] ?k = _ |- _ => cbv beta iota delta [zget_l alookup] in H end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

End FXG.
Ltac fp_cbv_in H := unfold fp_loop, fp_win, fp_lib in H; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE] in H.
Ltac fp_frame_init fp M :=
  pose proof (mpostL_stable R_segs M fp ltac:(unfold fp_loop, fp_win, fp_lib; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE]; ranges_ok_tac)) as HST;
  assert (HAG : framed (fun X => mpostL R_segs M X fp) M) by (apply mpostL_refl);
  fp_cbv_in HST; fp_cbv_in HAG.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.
End FXG.
Ltac fp_frame_from HP0 :=
  lazymatch type of HP0 with mpostL ?segs ?M0 ?M ?fp =>
    let HST := fresh "HST" in let HAG := fresh "HAG" in
    pose proof (mpostL_stable segs M0 fp ltac:(unfold fp_loop, fp_win, fp_lib; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE]; ranges_ok_tac)) as HST;
    change (framed (fun X => mpostL segs M0 X fp) M) in HP0; rename HP0 into HAG;
    fp_cbv_in HST; fp_cbv_in HAG
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Section K.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).

Definition k_mem (st : ist) (lf cf : Z -> Z) (M : mem) : Prop :=
  s_std cx fin M /\ st_at R_segs cx st M /\ s_ret cx st M /\ s_out cx st M /\
  mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf /\ mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf /\
  mpostL R_segs M0 M (fp_loop cx).

Definition KDISP (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_disp cx st R [] -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_DISP (zupd R []) M MD) T.
Definition KDISP10 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_d10 cx st R [] -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_DISP10 (zupd R []) M MD) T.
Definition KD0 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_d0 cx st R [] -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_DISP0 (zupd R []) M MD) T.
Definition KSETMODE (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (m : Z) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_d0 cx st R [] ->
    s_std cx fin M -> mem_u32 R_segs M (c_p cx + 8) m -> st_rest R_segs cx st M -> s_ret cx st M -> s_out cx st M ->
    mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
    mpostL R_segs M0 M (fp_loop cx) ->
    realizes R_segs (zcfg R_segs L_SETMODE (zupd R []) M MD) T.
Definition s_regs_reload (st : ist) (R : tree Z) (wantA1 leftS0 : bool) : Prop :=
  zget R kSP = c_u cx + -224 /\ zget R kGP = c_K cx kGP /\ zget R kTP = c_K cx kTP /\
  zget R kS0 = c_p cx /\ zget R kA0 = c_u cx /\ (wantA1 = false -> zget R kA1 = 0) /\
  zget R kS4 = 16209 /\ zget R kS6 = c_p cx + 168 /\ zget R kS9 = JTAB_ADDR /\
  zget R kS10 = c_q cx + t_cin st /\ zget R kS2 = c_n cx - t_cin st /\
  zget R kS3 = c_ob cx + t_cout st /\
  (leftS0 = true -> zget R kS1 = c_osz cx - t_cout st) /\ (leftS0 = false -> zget R kRA = c_osz cx - t_cout st) /\
  zget R kS7 = t_hold st /\ zget R kS8 = t_bits st.
Definition KRELOAD_A1 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_reload st R true true -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_RELOAD_A1 (zupd R []) M MD) T.
Definition KRELOAD_RA (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_reload st R false true -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_RELOAD_RA (zupd R []) M MD) T.
Definition KRELOAD (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_reload st R false false -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_RELOAD (zupd R []) M MD) T.
Definition bad_of (st : ist) : ist :=
  IST BAD (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Definition KBADMSG_S11 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx (bad_of st) lf cf -> meas cx (bad_of st) < B -> s_regs_disp cx st R [] ->
    0 <= zget R kA2 < two64 -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_BADMSG_S11 (zupd R []) M MD) T.
Definition KBADMSG_S10 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx (bad_of st) lf cf -> meas cx (bad_of st) < B -> s_regs_d10 cx st R [] ->
    0 <= zget R kA2 < two64 -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_BADMSG_S10 (zupd R []) M MD) T.
Definition KBADMSG_A3 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx (bad_of st) lf cf -> meas cx (bad_of st) < B ->
    s_fix cx R [] -> zget R kS10 = c_q cx + t_cin st -> zget R kA2 = c_n cx - t_cin st ->
    zget R kS3 = c_ob cx + t_cout st -> zget R kRA = c_osz cx - t_cout st ->
    zget R kS7 = t_hold st -> zget R kS8 = t_bits st ->
    0 <= zget R kA3 < two64 -> k_mem st lf cf M ->
    realizes R_segs (zcfg R_segs L_BADMSG_A3 (zupd R []) M MD) T.

Definition KLEAVE : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (rv : Z) (lf cf : Z -> Z),
    sinv cx st lf cf -> s_regs_leave cx st rv R [] ->
    s_std cx fin M -> st_at R_segs cx st M -> s_out cx st M ->
    mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
    mpostL R_segs M0 M (fp_loop cx) ->
    realizes R_segs (zcfg R_segs L_LEAVE (zupd R []) M MD) T.
Definition KLEAVE_LD : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> s_regs_leave_ld cx st R [] ->
    s_std cx fin M -> st_at R_segs cx st M -> s_ret cx st M -> s_out cx st M ->
    mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
    mpostL R_segs M0 M (fp_loop cx) ->
    realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R []) M MD) T.
Definition KRET : Prop :=
  forall (R : tree Z) (M : mem) (rc m : Z),
    rc mod two64 <> 0 -> s_regs_ret cx rc R [] -> s_std cx fin M ->
    mem_u32 R_segs M (c_p cx + 8) m -> reach m ->
    mpostL R_segs M0 M (fp_loop cx) ->
    realizes R_segs (zcfg R_segs L_RET (zupd R []) M MD) T.
End K.

End FXG.
Ltac open_kmem H := dand H as (STD & SAT & SRET & SOUT & Hlens & Hcodes & HP0).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition KALL (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem) (B : Z) : Prop :=
  KDISP cx fin MD T M0 B /\ KDISP10 cx fin MD T M0 B /\ KD0 cx fin MD T M0 B /\ KSETMODE cx fin MD T M0 B /\
  KRELOAD_A1 cx fin MD T M0 B /\ KRELOAD_RA cx fin MD T M0 B /\ KRELOAD cx fin MD T M0 B /\
  KBADMSG_S11 cx fin MD T M0 B /\ KBADMSG_S10 cx fin MD T M0 B /\ KBADMSG_A3 cx fin MD T M0 B /\
  KLEAVE cx fin MD T M0 /\ KLEAVE_LD cx fin MD T M0 /\ KRET cx fin MD T M0.
End FXG.
Ltac open_K H := dand H as (KD & KD10 & KD00 & KSM & KRA1 & KRRA & KRL & KB11 & KB10 & KBA3 & KL & KLL & KRT).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma KALL_mono : forall cx fin MD T M0 B B', B' <= B -> KALL cx fin MD T M0 B -> KALL cx fin MD T M0 B'.
Proof.
  intros cx fin MD T M0 B B' HB K. open_K K.
  unfold KALL, KDISP, KDISP10, KD0, KSETMODE, KRELOAD_A1, KRELOAD_RA, KRELOAD, KBADMSG_S11, KBADMSG_S10, KBADMSG_A3 in *.
  split_conj; try assumption; intros; first [eapply KD | eapply KD10 | eapply KD00 | eapply KSM | eapply KRA1 | eapply KRRA | eapply KRL
                                             | eapply KB11 | eapply KB10 | eapply KBA3]; try eassumption; lia_std.
Qed.

Definition arm_stmt (L X : Z) : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = X -> sinv cx st lf cf ->
    s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes R_segs (zcfg R_segs L (zupd Rb l) M MD) T.

Definition arm_stmt_ob (L X : Z) : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_S cx -> c_ob cx + c_osz cx <= c_u cx - FRA ->
    m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = X -> sinv cx st lf cf ->
    s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes R_segs (zcfg R_segs L (zupd Rb l) M MD) T.

Definition memcpy_spec_s : Prop := memcpy_spec_at R_segs A_MEMCPY.
Definition itable_spec_s : Prop := itable_spec_at R_segs L_ITABLE FR_IT.
Definition ifast_spec_s : Prop := ifast_spec_at R_segs L_IFAST FR_IF.
Definition adler32_spec_s : Prop := adler32_spec_at R_segs A_ADLER32 FR_AD rom_ok.
Definition adler32_null_spec_s : Prop := adler32_null0_spec_at R_segs A_ADLER32.
End FXG.
