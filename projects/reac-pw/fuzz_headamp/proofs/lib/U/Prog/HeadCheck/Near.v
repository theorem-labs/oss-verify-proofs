(** The inlined pod_nearest(f, 0, 255) of the UBSan LLVMFuzzerTestOneInput (0x145ec -> 0x146f4 / 0x144f4,
    cell_value at fuzz_headamp.c:105, pod.h:152-171): proof of [near_stmt] (U/Prog/HeadCheck/Cut.v) from the
    contracts of its soft-float callees (__extendsftf2, __getf2 = __gttf2, __floatditf, __subtf3 with __addtf3,
    __lttf2 = __cmptf2).

    The code computes the plain build's values in the plain build's order (the machine model [hn_bin] of
    Prog/HeadCheck/NearVal.v, which [hn_bin_nearest] turns into [nearest]) and adds four sanitizer checks, each a
    branch to `unimp` at 0x148a0: the float-cast checks f < 2^63 (`flt.s fs0, fs3`, 0x14624) and
    __gttf2(d, -2^63 - 1) > 0 (0x1463c), and the overflow checks on t + 1 (0x146c0) and t - 1 (0x14694). [hn_traps]
    shows each one is not taken once the range test -1.0f <= f <= 256.0f has passed: f < 2^63, d > -2^63 - 1
    (CJ/Spec/NearSF.v [near_sf_c2]) and -1 <= t <= 256. The walk [body] reaches the callees through the bridges of
    Prog/HeadCheck/Near.v ([br_ext], [br_ge], [br_fd], [br_sub], [br_le]) at the UBSan image's addresses. The piece
    has no frame of its own: param, d and frac live in main's cells sp + 0x28, sp + 0x38 / 0x30 (frac's high word
    in s10), and __subtf3 / __addtf3 use the 48 bytes below sp. fuzz_role's UBSan pod_nearest walk
    (U/Prog/pod_nearest.v) is the form; its trap facts are restated with headamp's bounds. *)
From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat NearSF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_letf2 G_getf2 G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require IImgU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts NearVal Near.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadCheck Require Import Cut.
Import ListNotations.
Open Scope Z_scope.

(** ** The sanitizer checks are not taken *)
(** 2^63 as binary32 (fs3, 0x141ec / 0x14208). *)
Lemma D5f : fp_decode fmt_single 0x5f000000 = S754_finite false 8388608 40.
Proof. vm_compute. reflexivity. Qed.

(** flt.s f < 2^63 for a finite f <= 256. *)
Lemma flt_2p63 : forall b N D, f32_ratio b = Some (N, D) -> N <= 256 * D ->
  fst (fp_lt fmt_single b 0x5f000000) = true.
Proof.
  intros b N D. unfold fp_lt, fp_compare, f32_ratio. cbn [fst]. rewrite D5f. cbv zeta.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Hd; intros HR HN; try discriminate HR.
  - reflexivity.
  - clear Hd. destruct s; [reflexivity|].
    rewrite sfc_ff. pose proof (Pos2Z.pos_is_pos m) as Hm.
    destruct (Z.compare_spec e 40) as [E|E|E]; cbv iota; [exfalso | reflexivity | exfalso];
      revert HR HN; destruct (Z.leb_spec 0 e) as [He0|He0]; cbv iota; intros HR HN;
      injection HR as HN' HD'; subst N D; try lia;
      assert (P : 1099511627776 <= 2^e) by (change 1099511627776 with (2^40); apply Z.pow_le_mono_r; lia);
      assert (P2 : 1 * 2^e <= Zpos m * 2^e) by (apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia | lia]);
      lia.
Qed.

(** After the NaN test and the range test -1.0f <= f <= 256.0f: f < 2^63 (check 0x14624), __gttf2(d, C2) = 1
    (check 0x1463c), and t = trunc(f) in [-2^31 - 1, 2^31], so t + 1 and t - 1 do not overflow (checks 0x146c0,
    0x14694). *)
Theorem hn_traps : forall b, 0 <= b < 2^32 ->
  fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
  fst (fp_lt fmt_single 0x43800000 b) = false ->
  fst (fp_lt fmt_single b 0x5f000000) = true /\ SF.f128_ge (pn_d b) NearSF.C2_128 = 1 /\
  - 2^31 - 1 <= bv_swrap 64 (pn_t b) <= 2^31.
Proof.
  intros b Hb Heq Hl1 Hl2. rewrite (pn_d_eq b Hb).
  destruct (f32_ratio b) as [[N D]|] eqn:HR.
  - rewrite (flt_m1 b N D HR) in Hl1. rewrite (flt_256 b N D HR) in Hl2.
    apply Z.ltb_ge in Hl1. apply Z.ltb_ge in Hl2.
    pose proof (proj2 (near_f32_ratio b) N D HR) as HD.
    assert (HB : (INT32_MIN - 1) * D <= N <= (INT32_MAX + 1) * D) by (unfold INT32_MIN, INT32_MAX; lia).
    split; [|split].
    + exact (flt_2p63 b N D HR Hl2).
    + exact (NearSF.near_sf_c2 b N D Hb HR (proj1 HB)).
    + rewrite (toint_ratio b N D HR HB). pose proof (quot_rng N D HD HB) as Hq.
      rewrite swrap_iw0 by lia. exact Hq.
  - exfalso. destruct (ratio_none b HR) as [Hd|[Hd|Hd]].
    + rewrite (feq_nan b Hd) in Heq. discriminate Heq.
    + rewrite (flt_minf_m1 b Hd) in Hl1. discriminate Hl1.
    + rewrite (flt_pinf_256 b Hd) in Hl2. discriminate Hl2.
Qed.

(** The overflow checks on t + 1 and t - 1 (`addi a0,s7,+-1`; `blt a0,s7`, resp. `bge a0,s7`). *)
Lemma lts_inc : forall t, -2^31 - 1 <= bv_swrap 64 t <= 2^31 ->
  bv_lts (Z_to_bv 64 (t + 1)) (Z_to_bv 64 t) = false.
Proof.
  intros t Ht. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2^63) in Ht.
  change (bv_modulus 64) with (2^64) in Ht.
  apply Z.ltb_ge.
  destruct (Z.ltb_spec ((t + 1) mod 2^64) (2^63)); destruct (Z.ltb_spec (t mod 2^64) (2^63)); cbv iota;
    revert Ht; Z.div_mod_to_equations; lia.
Qed.

Lemma lts_dec : forall t, -2^31 - 1 <= bv_swrap 64 t <= 2^31 ->
  bv_lts (Z_to_bv 64 (t + -1)) (Z_to_bv 64 t) = true.
Proof.
  intros t Ht. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap in Ht. change (bv_half_modulus 64) with (2^63) in Ht.
  change (bv_modulus 64) with (2^64) in Ht.
  apply Z.ltb_lt.
  destruct (Z.ltb_spec ((t + -1) mod 2^64) (2^63)); destruct (Z.ltb_spec (t mod 2^64) (2^63)); cbv iota;
    revert Ht; Z.div_mod_to_equations; lia.
Qed.

(** A 4-byte run read back. *)
Lemma read_bytes4 : forall segs m a l, bytes_at segs m a l -> length l = 4%nat ->
  ov_read_bytes segs m (wa a) 4 = Some l.
Proof.
  intros segs m a l H L. pose proof (bytes_at_ov_read segs m a l 0 4 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal. cbn [skipn]. apply firstn_all2. lia.
Qed.

Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib.Step.exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | _ => idtac
    end
  end;
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(** ** The walk *)
Section Walk.
Variables (Q : machine_state -> Prop) (gp tp s0 s1 s2 s3 s4 s5 s6 s8 s9 s11 a4 : word) (F : bvmap 5 word)
  (m0 : word -> option byte) (b Sp lo : Z) (w68 w98 wa0 wa8 wb0 : word).
Hypothesis HEX : @C_extendsftf2.extendsftf2_contract IImgU.N_img.
Hypothesis HFD : @C_floatditf.floatditf_contract IImgU.N_img.
Hypothesis HSB : @G_subtf3.subtf3_contract IImgU.N_img.
Hypothesis HGE : @G_getf2.getf2_contract IImgU.N_img.
Hypothesis HLE : @G_letf2.letf2_contract IImgU.N_img.
Hypothesis Hb : 0 <= b < 2^32.
(** fs0 = f after 0x145f4 `flw fs0,0(s7)`; fs1 = -1.0f, fs2 = 256.0f, fs3 = 2^63. *)
Hypothesis HF8 : Sem.reg_get F (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b).
Hypothesis HF9 : Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1).
Hypothesis HF18 : Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256).
Hypothesis HF19 : Sem.reg_get F (Z_to_bv 5 19) = Sem.nan_box (Z_to_bv 32 F32_2P63).
Hypothesis Hlo : 0 <= lo.
Hypothesis HLO : lo + 48 <= Sp.
Hypothesis HSpT : Sp + 0x1d8 <= 2^64.

(** The exits, with the machine model [hn_bin b] in place of [nearest]; m0 is the memory after the param store
    0x145ec. *)
Hypothesis K : forall (t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : word -> option byte),
  frm0 fc' ->
  (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  munch (NEAR_W Sp) m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> U.MemNorm.task_mem rsegs m' ->
  stk rsegs m' lo (Sp + FRAME_LOCALS) ->
  match hn_bin b with
  | Some n =>
      evt rsegs Q
        (MS (mkR wa8 (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 255) a1' w68 (Z_to_bv 64 9) a4
                 (Z_to_bv 64 5) w98 wa0 s2 s3 s4 s5 s6 (Z_to_bv 64 n) s8 s9 s10' s11 t3' t4' (Z_to_bv 64 8) wb0)
            F' (Z_to_bv 64 0x146f4) fc' None m' (seg_rom rsegs))
  | None =>
      evt rsegs Q
        (MS (mkR wa8 (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 5) w98 wa0
                 s2 s3 s4 s5 s6 s7' s8 s9 s10' s11 t3' t4' (Z_to_bv 64 8) wb0)
            F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs))
  end.

(** The memory the walk carries: changed only in [NEAR_W], the stack region present and writable. The frame
    cells the walk reads are hypotheses beside it. *)
Definition MemN (m : word -> option byte) : Prop :=
  munch (NEAR_W Sp) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ U.MemNorm.task_mem rsegs m /\
  stk rsegs m lo (Sp + FRAME_LOCALS).

Lemma MN_mi : forall m, MemN m -> mem_inv rsegs m.
Proof. intros m (_ & _ & H & _). exact H. Qed.
Lemma MN_tm : forall m, MemN m -> U.MemNorm.task_mem rsegs m.
Proof. intros m (_ & _ & _ & H & _). exact H. Qed.

Lemma MN_stk48 : forall m, MemN m -> stk rsegs m (Sp - 48) Sp.
Proof.
  intros m (_ & _ & _ & _ & ST). unfold FRAME_LOCALS in ST.
  destruct (stk_split rsegs m lo (Sp - 48) (Sp + 0x1d8) ST ltac:(lia)) as [_ ST2].
  exact (proj1 (stk_split rsegs m (Sp - 48) Sp (Sp + 0x1d8) ST2 ltac:(lia))).
Qed.

(** A leaf callee writes nothing. *)
Lemma MN_call : forall m m', MemN m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  U.MemNorm.task_mem rsegs m' -> MemN m'.
Proof.
  intros m m' (MU & WM & MI & TM & ST) MU' WM' MI' TM'.
  split; [|split; [|split; [|split]]].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]. intros x _. exact I.
  - exact (wmono_trans rsegs _ _ _ WM WM').
  - exact MI'.
  - exact TM'.
  - exact (stk_transport_disjoint rsegs [] m m' lo _ ST MU' WM' I).
Qed.

(** __subtf3 / __addtf3 write the 48 bytes below sp. *)
Lemma MN_sub : forall m m', MemN m -> munch [(Sp - 48, Sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  U.MemNorm.task_mem rsegs m' -> stk rsegs m' (Sp - 48) Sp -> MemN m'.
Proof.
  intros m m' (MU & WM & MI & TM & ST) MU' WM' MI' TM' ST'.
  split; [|split; [|split; [|split]]].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']].
    unfold sub_fp, NEAR_W, NEAR_STACK. cbn [outside]. intros x (O1 & _ & _). split; [exact O1 | exact I].
  - exact (wmono_trans rsegs _ _ _ WM WM').
  - exact MI'.
  - exact TM'.
  - unfold FRAME_LOCALS in *.
    destruct (stk_split rsegs m lo (Sp - 48) (Sp + 0x1d8) ST ltac:(lia)) as [STa STb].
    destruct (stk_split rsegs m (Sp - 48) Sp (Sp + 0x1d8) STb ltac:(lia)) as [_ STc].
    pose proof (stk_transport_disjoint rsegs _ m m' lo (Sp - 48) STa MU' WM'
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STa'.
    pose proof (stk_transport_disjoint rsegs _ m m' Sp (Sp + 0x1d8) STc MU' WM'
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STc'.
    apply (stk_merge rsegs m' lo (Sp - 48)); [exact STa' | | lia].
    apply (stk_merge rsegs m' (Sp - 48) Sp); [exact ST' | exact STc' | lia].
Qed.

(** A store of 8 bytes into the frame cells [sp + 0x28, sp + 0x40). *)
Lemma MN_store_ok : forall m a, MemN m -> Sp + 0x28 <= a -> a + 8 <= Sp + 0x40 -> store_ok rsegs m (wa a) 8 = true.
Proof.
  intros m a (_ & _ & _ & _ & ST) H1 H2.
  apply (stk_store_ok rsegs m lo (Sp + FRAME_LOCALS) a 8 ST); unfold FRAME_LOCALS; lia.
Qed.

Lemma MN_store : forall m a (v : word), MemN m -> Sp + 0x28 <= a -> a + 8 <= Sp + 0x40 ->
  MemN (write_to_mem m (wa a) (le8 v)) /\ bytes_at rsegs (write_to_mem m (wa a) (le8 v)) a (le8 v).
Proof.
  intros m a v MN H1 H2. pose proof (MN_store_ok m a MN H1 H2) as HS.
  destruct MN as (MU & WM & MI & TM & ST). unfold FRAME_LOCALS in *.
  assert (HS' : store_ok rsegs m (wa a) (length (le8 v)) = true) by (rewrite length_le8; exact HS).
  split; [split; [|split; [|split; [|split]]] |].
  - apply munch_write; [exact MU | lia | rewrite length_le8; lia |].
    unfold NEAR_W. cbn [inside]. rewrite length_le8. right; left; lia.
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS'].
  - exact (task_mem_write rsegs m (wa a) (le8 v) TM HS').
  - apply stk_write; [exact ST | lia | rewrite length_le8; lia].
  - apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(** A frame cell outside a store, a leaf callee or __subtf3's stack keeps its bytes. *)
Lemma D_store : forall m a (v w : word) c, bytes_at rsegs m c (le8 w) -> Sp + 0x28 <= a -> a + 8 <= Sp + 0x40 ->
  c + 8 <= a \/ a + 8 <= c -> bytes_at rsegs (write_to_mem m (wa a) (le8 v)) c (le8 w).
Proof.
  intros m a v w c H H1 H2 H3.
  apply bytes_at_write_other; [exact H | lia | rewrite length_le8; lia | rewrite !length_le8; lia].
Qed.

Lemma D_nil : forall m m' c bs, bytes_at rsegs m c bs -> munch [] m m' -> bytes_at rsegs m' c bs.
Proof. intros m m' c bs H MU. exact (bytes_at_transport rsegs [] m m' c bs H MU I). Qed.

Lemma D_sub : forall m m' c bs, bytes_at rsegs m c bs -> munch [(Sp - 48, Sp)] m m' -> Sp <= c ->
  bytes_at rsegs m' c bs.
Proof.
  intros m m' c bs H MU Hc. apply (bytes_at_transport rsegs _ m m' c bs H MU). cbn [disjoint_from].
  split; [lia | exact I].
Qed.

(** ** The exits 0x144f4 (None) and 0x146f4 (Some n, n in s7) *)
Lemma exit_none : forall (t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : word -> option byte),
  frm0 fc' -> (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  MemN m' -> hn_bin b = None ->
  evt rsegs Q
    (MS (mkR wa8 (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' w68 a3' a4' (Z_to_bv 64 5) w98 wa0
             s2 s3 s4 s5 s6 s7' s8 s9 s10' s11 t3' t4' (Z_to_bv 64 8) wb0)
        F' (Z_to_bv 64 0x144f4) fc' None m' (seg_rom rsegs)).
Proof.
  intros t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' F' fc' m' FRM HF (MU & WM & MI & TM & ST) HN.
  pose proof (K t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' F' fc' m' FRM HF MU WM MI TM ST) as KK.
  rewrite HN in KK. exact KK.
Qed.

Lemma exit_some : forall (t0' t1' t2' a1' s10' t3' t4' : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : word -> option byte) (n : Z),
  frm0 fc' -> (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  MemN m' -> hn_bin b = Some n ->
  evt rsegs Q
    (MS (mkR wa8 (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 255) a1' w68 (Z_to_bv 64 9) a4
             (Z_to_bv 64 5) w98 wa0 s2 s3 s4 s5 s6 (Z_to_bv 64 n) s8 s9 s10' s11 t3' t4' (Z_to_bv 64 8) wb0)
        F' (Z_to_bv 64 0x146f4) fc' None m' (seg_rom rsegs)).
Proof.
  intros t0' t1' t2' a1' s10' t3' t4' F' fc' m' n FRM HF (MU & WM & MI & TM & ST) HN.
  pose proof (K t0' t1' t2' t0' a1' t0' t0' t0' s10' t3' t4' F' fc' m' FRM HF MU WM MI TM ST) as KK.
  rewrite HN in KK. exact KK.
Qed.

(** The memory and the hypotheses of the state in the goal. *)
Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => m end.
Ltac cur_mn m := lazymatch goal with H : MemN m |- _ => H end.

(** `sd` of a 64-bit word at the frame cell [A]: step, carry [MemN] and the other cells over, name the new memory;
    a cell the store overwrites is dropped. *)
Ltac nstore A :=
  let m := cur_mem in let MN := cur_mn m in
  let HS := fresh "HS" in
  pose proof (MN_store_ok m A MN ltac:(lia) ltac:(lia)) as HS; step; clear HS;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?AA (le8 ?V)) _) =>
    change (write_to_mem m AA (le8 V)) with (write_to_mem m (wa A) (le8 V));
    let MN' := fresh "MN" in let DD := fresh "D" in
    destruct (MN_store m A V MN ltac:(lia) ltac:(lia)) as [MN' DD];
    repeat match goal with
    | H : bytes_at rsegs m ?c (le8 ?w) |- _ =>
        let H' := fresh "D" in
        pose proof (D_store m A V w c H ltac:(lia) ltac:(lia) ltac:(lia)) as H'; clear H
    end;
    let m' := fresh "m" in
    set (m' := write_to_mem m (wa A) (le8 V)) in *; clearbody m'; first [clear dependent m | clear MN]
  end.

(** `ld` of the frame cell [A]. *)
Ltac nload A :=
  let m := cur_mem in
  match goal with
  | H : bytes_at rsegs m A (le8 ?w) |- _ =>
      let HR := fresh "HR" in pose proof (read_le8 rsegs m A w H) as HR; step; clear HR
  end.

(** After a leaf callee from memory [m] to [m']: carry [MemN] and the frame cells over. *)
Ltac npost m m' MU WM MI TM :=
  let MN := cur_mn m in
  let MN' := fresh "MN" in
  pose proof (MN_call m m' MN MU WM MI TM) as MN';
  repeat match goal with
  | H : bytes_at rsegs m ?c ?bs |- _ =>
      let H' := fresh "D" in pose proof (D_nil m m' c bs H MU) as H'; clear H
  end;
  first [clear dependent m | clear MN MU WM];
  rewrite ret_pc_even by (try lia; reflexivity).

(** ** 0x1469c (NaN, f < -1.0f or 256.0f < f): the reloads, a5 = OUT_OF_RANGE, `j 0x144f4` *)
Lemma none_tail : forall (ra t0 t1 t2 a0 a1 a2 a3 a4x a5 a6 a7 s7x s10x t3 t4 t5 t6 : word) (F' : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  frm0 fc -> (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  MemN m ->
  bytes_at rsegs m (Sp + 0x68) (le8 w68) -> bytes_at rsegs m (Sp + 0x98) (le8 w98) ->
  bytes_at rsegs m (Sp + 0xa0) (le8 wa0) -> bytes_at rsegs m (Sp + 0xa8) (le8 wa8) ->
  bytes_at rsegs m (Sp + 0xb0) (le8 wb0) ->
  hn_bin b = None ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4x a5 a6 a7 s2 s3 s4 s5 s6 s7x s8 s9 s10x s11
             t3 t4 t5 t6)
        F' (Z_to_bv 64 0x1469c) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4x a5 a6 a7 s7x s10x t3 t4 t5 t6 F' fc m FRM HF MN C68 C98 Ca0 Ca8 Cb0 HN.
  (* ld a2,0x68(sp); addi t5,zero,8; ld t6,0xb0(sp); ld a6,0x98(sp); ld a7,0xa0(sp); ld ra,0xa8(sp);
     addi a5,zero,5; j 0x144f4 *)
  nload (Sp + 0x68). step. nload (Sp + 0xb0). nload (Sp + 0x98). nload (Sp + 0xa0). nload (Sp + 0xa8).
  step. step.
  eapply exit_none; [exact FRM | exact HF | exact MN | exact HN].
Qed.

(** ** 0x146c8: the reloads (a4 = param from sp + 0x28); 255 < r unsigned goes to 0x144f4, else 0x146f4 *)
Lemma tail : forall (X : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4x a5 a6 a7 s10x t3 t4 t5 t6 : word) (F' : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte),
  frm0 fc -> (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  MemN m ->
  bytes_at rsegs m (Sp + 0x28) (le8 a4) ->
  bytes_at rsegs m (Sp + 0x68) (le8 w68) -> bytes_at rsegs m (Sp + 0x98) (le8 w98) ->
  bytes_at rsegs m (Sp + 0xa0) (le8 wa0) -> bytes_at rsegs m (Sp + 0xa8) (le8 wa8) ->
  bytes_at rsegs m (Sp + 0xb0) (le8 wb0) ->
  hn_bin b = (if 255 <? X mod 2^64 then None else Some (X mod 2^64)) ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4x a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 X) s8 s9
             s10x s11 t3 t4 t5 t6)
        F' (Z_to_bv 64 0x146c8) fc None m (seg_rom rsegs)).
Proof.
  intros X ra t0 t1 t2 a0 a1 a2 a3 a4x a5 a6 a7 s10x t3 t4 t5 t6 F' fc m FRM HF MN C28 C68 C98 Ca0 Ca8 Cb0 HN.
  (* ld a2,0x68(sp); addi t5,zero,8; addi a3,zero,9; ld t6,0xb0(sp); addi a0,zero,0xff; ld a6,0x98(sp);
     ld a7,0xa0(sp); ld ra,0xa8(sp); addi a5,zero,5; ld a4,0x28(sp); bltu a0,s7 *)
  nload (Sp + 0x68). step. step. nload (Sp + 0xb0). step. nload (Sp + 0x98). nload (Sp + 0xa0).
  nload (Sp + 0xa8). step. nload (Sp + 0x28). step.
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with (255 <? X mod 2^64) by (unfold bv_ltu; rewrite ?unsigned_lit_wrap; reflexivity) end.
  destruct (255 <? X mod 2^64) eqn:BT; cbv iota.
  - eapply exit_none; [exact FRM | exact HF | exact MN | rewrite HN; try rewrite BT; reflexivity].
  - rewrite <- (bv_mod_lit X).
    eapply exit_some; [exact FRM | exact HF | exact MN | rewrite HN; try rewrite BT; reflexivity].
Qed.

(** ** 0x145f8 .. 0x146c8 *)
Lemma body : forall (ra t0 t1 t2 a0 a1 a2 a3 a4x a5 a6 a7 s7x s10 t3 t4 t5 t6 : word) (fc : bv 32),
  frm0 fc -> MemN m0 ->
  bytes_at rsegs m0 (Sp + 0x28) (le8 a4) ->
  bytes_at rsegs m0 (Sp + 0x48) (le8 (Z_to_bv 64 MHALF_HI)) ->
  bytes_at rsegs m0 (Sp + 0x50) (le8 (Z_to_bv 64 HALF_HI)) ->
  bytes_at rsegs m0 (Sp + 0x58) (le8 (Z_to_bv 64 C2_HI)) ->
  bytes_at rsegs m0 (Sp + 0x60) (le8 (Z_to_bv 64 C2_LO)) ->
  bytes_at rsegs m0 (Sp + 0x68) (le8 w68) -> bytes_at rsegs m0 (Sp + 0x98) (le8 w98) ->
  bytes_at rsegs m0 (Sp + 0xa0) (le8 wa0) -> bytes_at rsegs m0 (Sp + 0xa8) (le8 wa8) ->
  bytes_at rsegs m0 (Sp + 0xb0) (le8 wb0) ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4x a5 a6 a7 s2 s3 s4 s5 s6 s7x s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x145f8) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4x a5 a6 a7 s7x s10 t3 t4 t5 t6 fc FRM MN C28 C48 C50 C58 C60 C68 C98 Ca0 Ca8
    Cb0.
  (* 0x145f8 feq.s a0,fs0,fs0; beqz a0 *)
  step. fix_reg F HF8 8%Z. unfold feq_s. rewrite unbox_nan_box, (u32_lit b Hb).
  destruct (fst (fp_eq fmt_single b b)) eqn:FE; unfold bword; step.
  2:{ (* a NaN *)
      if_true. eapply none_tail; try eassumption; [intros k _ _; reflexivity |].
      unfold hn_bin. rewrite FE. reflexivity. }
  if_false.
  (* 0x14600 fmv.s fa0,fs0; jal __extendsftf2 *)
  step. fix_reg F HF8 8%Z. rewrite unbox_nan_box, sgnj_self32.
  step.
  eapply evt_cut.
  { eapply (br_ext IImgU.N_img rsegs 0x152f8 eq_refl eq_refl HEX b);
      [ apply freg_get_same; reflexivity | exact (MN_mi _ MN) | exact (MN_tm _ MN) ]. }
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
              & MI2 & TM2).
  npost m0 m2 MU2 WM2 MI2 TM2.
  (* 0x14608 sd a0,0x38(sp); flt.s a0,fs0,fs1; sd a1,0x30(sp); bnez a0 *)
  nstore (Sp + 56).
  step. fix_reg F HF8 8%Z. fix_reg F HF9 9%Z. unfold flt_s.
  rewrite !unbox_nan_box, (u32_lit b Hb), (u32_lit F32_M1) by (unfold F32_M1; lia). unfold F32_M1.
  nstore (Sp + 48).
  destruct (fst (fp_lt fmt_single b 0xbf800000)) eqn:LT1; unfold bword; step.
  { (* f < -1.0f *)
    if_true. eapply none_tail; try eassumption; [hfc |].
    unfold hn_bin. rewrite FE, LT1. reflexivity. }
  if_false.
  (* 0x14618 flt.s a0,fs2,fs0; bnez a0 *)
  step. fix_reg F HF8 8%Z. fix_reg F HF18 18%Z. unfold flt_s.
  rewrite !unbox_nan_box, (u32_lit b Hb), (u32_lit F32_256) by (unfold F32_256; lia). unfold F32_256.
  destruct (fst (fp_lt fmt_single 0x43800000 b)) eqn:LT2; unfold bword; step.
  { (* 256.0f < f *)
    if_true. eapply none_tail; try eassumption; [hfc |].
    unfold hn_bin. rewrite FE, LT1, LT2. reflexivity. }
  if_false.
  destruct (hn_traps b Hb FE LT1 LT2) as (T1 & T2 & T3).
  (* 0x14620 flt.s a0,fs0,fs3; beqz a0 -> trap (not taken: f < 2^63) *)
  step. fix_reg F HF8 8%Z. fix_reg F HF19 19%Z. unfold flt_s.
  rewrite !unbox_nan_box, (u32_lit b Hb), (u32_lit F32_2P63) by (unfold F32_2P63; lia). unfold F32_2P63.
  rewrite T1. unfold bword. step. if_false.
  (* 0x14628 ld a0,0x38(sp); ld a1,0x30(sp); ld a2,0x60(sp); ld a3,0x58(sp); jal __gttf2 *)
  nload (Sp + 56). nload (Sp + 48). nload (Sp + 0x60). nload (Sp + 0x58). step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_ge IImgU.N_img rsegs 0x1523c eq_refl eq_refl HGE); [exact (MN_mi _ MN) | exact (MN_tm _ MN)]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MU3 & WM3 & MI3 & TM3);
    npost m m3 MU3 WM3 MI3 TM3 ].
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def. fold_c128 NearSF.C2_128. rewrite T2.
  (* 0x1463c blez a0 -> trap (not taken: __gttf2(d, C2) = 1) *)
  step. if_false.
  (* 0x14640 fcvt.l.s s7,fs0,rtz *)
  step. fix_reg F HF8 8%Z. rewrite unbox_nan_box, (u32_lit b Hb), pn_t_def.
  (* 0x14644 mv a0,s7; jal __floatditf *)
  step. step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_fd IImgU.N_img rsegs 0x15454 eq_refl eq_refl HFD (pn_t b));
      [ rewrite unsigned_lit_wrap, SF.wrap64_mod; first [reflexivity | f_equal; lia]
      | exact (MN_mi _ MN) | exact (MN_tm _ MN) ]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & TM4);
    npost m m4 MU4 WM4 MI4 TM4 ].
  (* 0x1464c mv a2,a0; mv a3,a1; ld a0,0x38(sp); ld a1,0x30(sp); jal __subtf3 *)
  step. step. nload (Sp + 56). nload (Sp + 48). step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_sub IImgU.N_img rsegs 0x15578 eq_refl eq_refl HSB);
      [ lia | exact (MN_stk48 _ MN) | exact (MN_mi _ MN) | exact (MN_tm _ MN) | eassumption ]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fc5 & m5 & -> & MU5 & WM5 & MI5 & TM5 & FRM5
                & ST5);
    pose proof (MN_sub m m5 MN MU5 WM5 MI5 TM5 ST5) as MN5;
    repeat match goal with
    | H : bytes_at rsegs m ?c ?bs |- _ =>
        let H' := fresh "D" in pose proof (D_sub m m5 c bs H MU5 ltac:(lia)) as H'; clear H
    end;
    first [clear dependent m | clear MN MU5 WM5] ].
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def.
  (* 0x14660 sd a0,0x38(sp); mv s10,a1; mv a2,zero; ld a3,0x50(sp); jal __getf2 *)
  nstore (Sp + 56). step. step. nload (Sp + 0x50). step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_ge IImgU.N_img rsegs 0x1523c eq_refl eq_refl HGE); [exact (MN_mi _ MN) | exact (MN_tm _ MN)]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MU6 & WM6 & MI6 & TM6);
    npost m m6 MU6 WM6 MI6 TM6 ].
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 HALF_128.
  (* 0x14674 bgez a0 -> 0x146bc *)
  step. rewrite lts0 by apply f128_ge_range. rewrite Z.ltb_antisym, Bool.negb_involutive.
  destruct (0 <=? SF.f128_ge (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) HALF_128) eqn:GE;
    cbv iota.
  { (* frac >= 1/2: 0x146bc addi a0,s7,1; blt a0,s7 -> trap (not taken); mv s7,a0 *)
    step. step. rewrite (lts_inc (pn_t b) T3). cbv iota. step.
    eapply tail; try eassumption; [hfc |].
    apply hn_eq; [exact FE | exact LT1 | exact LT2 |]. unfold pn_r. cbv zeta. rewrite GE. lia. }
  (* 0x14678 ld a0,0x38(sp); mv a1,s10; mv a2,zero; ld a3,0x48(sp); jal __lttf2 *)
  nload (Sp + 56). step. step. nload (Sp + 0x48). step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_le IImgU.N_img rsegs 0x15174 eq_refl eq_refl HLE); [exact (MN_mi _ MN) | exact (MN_tm _ MN)]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MU7 & WM7 & MI7 & TM7);
    npost m m7 MU7 WM7 MI7 TM7 ].
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 MHALF_128.
  (* 0x1468c bgez a0 -> 0x146c8 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) MHALF_128 <? 0) eqn:LM;
    cbn [negb]; cbv iota.
  - (* frac < -1/2: 0x14690 addi a0,s7,-1; bge a0,s7 -> trap (not taken); j 0x146c4; mv s7,a0 *)
    step. step. rewrite (lts_dec (pn_t b) T3). cbn [negb]. cbv iota. step. step.
    eapply tail; try eassumption; [hfc |].
    apply hn_eq; [exact FE | exact LT1 | exact LT2 |]. unfold pn_r. cbv zeta. rewrite GE, LM. lia.
  - (* r = t *)
    eapply tail; try eassumption; [hfc |].
    apply hn_eq; [exact FE | exact LT1 | exact LT2 |]. unfold pn_r. cbv zeta. rewrite GE, LM. lia.
Qed.

End Walk.

(** ** [near_stmt], from the five callee contracts *)
Theorem near_holds : @C_extendsftf2.extendsftf2_contract IImgU.N_img -> @C_floatditf.floatditf_contract IImgU.N_img ->
  @G_subtf3.subtf3_contract IImgU.N_img -> @G_getf2.getf2_contract IImgU.N_img -> @G_letf2.letf2_contract IImgU.N_img ->
  near_stmt.
Proof.
  intros HEX HFD HSB HGE HLE. unfold near_stmt.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp
    v e w68 w98 wa0 wa8 wb0 Ha7 Hs7 Hv Hpp HPL HE HB4 HF9 HF18 HF19 H48 H50 H58 H60 H68 H98 Ha0 Ha8 Hb0 ST HLO HAL
    HROM FRM MI TM K.
  subst a7 s7.
  pose proof (Z_to_bv_lit_self sp) as Esp. set (Sp := bv_unsigned sp) in *. clearbody Sp. subst sp.
  pose proof ST as (Hlo & HSpT & _). unfold NEAR_STACK in HLO. unfold FRAME_LOCALS in HSpT.
  unfold POD_PROPS, OFF_ENT, ENT_SIZE in *.
  (* the body's first word, below lo *)
  assert (HW : bytes_at rsegs m (pp + 16404 + 104 * Z.of_nat v + 8) (firstn 4 (e_body e))).
  { pose proof (bytes_at_ent_body rsegs m _ e HE) as H8.
    pose proof (bytes_at_sub rsegs m _ _ 0 4 H8 ltac:(rewrite length_app; lia)) as H4.
    rewrite Z.add_0_r in H4.
    match type of H4 with bytes_at _ _ _ ?l => replace l with (firstn 4 (e_body e)) in H4 end; [exact H4|].
    change (skipn 0 ?l) with l. rewrite List.firstn_app.
    replace (4 - length (e_body e))%nat with 0%nat by lia. cbn [firstn]. symmetry. apply List.app_nil_r. }
  clear HE.
  (* 0x145ec sd a4,0x28(sp) *)
  assert (HS : store_ok rsegs m (wa (Sp + 40)) 8 = true)
    by (apply (stk_store_ok rsegs m lo (Sp + FRAME_LOCALS) (Sp + 40) 8 ST); unfold FRAME_LOCALS; lia).
  assert (HS' : store_ok rsegs m (wa (Sp + 40)) (length (le8 a4)) = true) by (rewrite length_le8; exact HS).
  step. clear HS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?AA (le8 ?V)) _) =>
    change (write_to_mem m AA (le8 V)) with (write_to_mem m (wa (Sp + 40)) (le8 V)) end.
  assert (MU1 : munch (NEAR_W Sp) m (write_to_mem m (wa (Sp + 40)) (le8 a4))).
  { apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
    unfold NEAR_W. cbn [inside]. rewrite length_le8. right; left; lia. }
  pose proof (wmono_write rsegs m m (wa (Sp + 40)) (le8 a4) (wmono_refl rsegs m)) as WM1.
  pose proof (mem_inv_store rsegs m (wa (Sp + 40)) (le8 a4) MI HS') as MI1.
  pose proof (task_mem_write rsegs m (wa (Sp + 40)) (le8 a4) TM HS') as TM1.
  pose proof (stk_write rsegs m lo (Sp + FRAME_LOCALS) (Sp + 40) (le8 a4) ST ltac:(lia)
                ltac:(rewrite length_le8; lia)) as ST1.
  pose proof (bytes_at_write_same rsegs m (Sp + 40) (le8 a4) ltac:(lia) ltac:(rewrite length_le8; lia)) as C28.
  repeat match goal with
  | H : bytes_at rsegs m ?c ?cs |- _ =>
      apply (bytes_at_write_other rsegs m (Sp + 40) (le8 a4) c cs) in H;
      [ | lia | rewrite length_le8; lia | rewrite ?length_le8, ?List.length_firstn; lia ]
  end.
  set (m1 := write_to_mem m (wa (Sp + 40)) (le8 a4)) in *. clearbody m1. clear HS'.
  (* 0x145f0 add s7,a7,s7; 0x145f4 flw fs0,0(s7) *)
  step.
  pose proof (read_bytes4 rsegs m1 _ _ HW ltac:(rewrite List.length_firstn; lia)) as HR. step. clear HR.
  rewrite extract_rd32 by (rewrite List.length_firstn; lia). rewrite rd32_firstn.
  pose proof (rd32_range (e_body e)) as Hb.
  eapply body with (b := rd32 (e_body e)) (lo := lo) (a4 := a4) (w68 := w68) (w98 := w98) (wa0 := wa0)
    (wa8 := wa8) (wb0 := wb0).
  all: lazymatch goal with
       | |- Sem.reg_get (bvmap_set _ _ _) (Z_to_bv 5 8) = _ => apply freg_get_same; reflexivity
       | |- Sem.reg_get (bvmap_set _ _ _) _ = _ => rewrite freg_get_other by reflexivity; assumption
       | |- MemN _ _ _ _ =>
           unfold MemN; refine (conj (munch_refl _ _) (conj (wmono_refl _ _) (conj MI1 (conj TM1 ST1))))
       | |- forall _, _ => idtac
       | |- _ => first [assumption | lia]
       end.
  intros t0' t1' t2' a0' a1' a3' a4' s7' s10' t3' t4' F' fc' m' FRM' HF' MU' WM' MI' TM' ST'.
  rewrite (hn_bin_nearest _ Hb).
  apply K; try assumption.
  - intros k H8 H10. rewrite (HF' k H8 H10). apply freg_get_other.
    unfold bv_eqb. apply Z.eqb_neq. intro E. apply H8. rewrite <- E. reflexivity.
  - exact (munch_trans _ _ _ _ MU1 MU').
  - exact (wmono_trans rsegs _ _ _ WM1 WM').
Qed.
