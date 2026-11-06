(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c): the memory kit of its inner
   walk (U/Prog/Seg/M02D.v; the plain twin is lib/Prog/Seg/M02K.v). The pieces carry one fact about memory from call
   to call, M02_inv S m0 m (written only inside M02_W S since m0, writability kept, mem_inv, MemNorm.task_mem); these
   lemmas step it across a callee's post (m02_inv_step) and read every fact of M02_mem back at m: the two blocks'
   states (c and m lie below the window), the stack-protector cells and main's cells cap, c, m (outside M02_W), the
   stack window (present: it lies above Tac_slot.SL_TOP, where a writable byte is present), the callee stack regions
   (stack_ok), free cells of main's frame (rw_cells) and the .rodata string "nosuch0" piece D passes (piece C reads
   "%sx" itself, M02_C.c_fmt_ro).
   Part of the proof of LLVMFuzzerTestOneInput: a kit of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment lemma). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP
  Image Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env printf_facts_c reac_segconf_find_c
  m_find_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot M02D.
Import ListNotations.
Open Scope Z_scope.

Lemma m02_TASK_SIZE : TASK_SIZE = 2 ^ 47.
Proof. reflexivity. Qed.

(* Words: s2 = ~m as a literal word, signed reads of small values, 4-byte loads. *)
Lemma m02_not_lit : forall z, 0 <= z < 2 ^ 64 -> bv_not (Z_to_bv 64 z) = Z_to_bv 64 (18446744073709551615 - z).
Proof.
  intros z Hz. apply bv_eq. rewrite bv_not_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small z) by lia. rewrite Z.lnot_eq_pred_opp.
  rewrite (Z.mod_small (18446744073709551615 - z)) by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma m02_signed_lit : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite ZBridge.zb_signed. rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec0 z (2 ^ 63)); lia.
Qed.

Lemma m02_ld4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le4 v) 0 4 H) by (rewrite length_le4; lia).
  unfold le4. reflexivity.
Qed.

(* M02_inv from its three memory facts: task_mem comes back from m0's, as M02_W lies below 2^47. *)
Lemma m02_inv_of : forall S m0 m, MemNorm.task_mem rsegs m0 -> S <= 2 ^ 47 ->
  munch (M02_W S) m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> M02_inv S m0 m.
Proof.
  intros S m0 m HTM H47 MU WM HMI. split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  intros a b E.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra.
  destruct (sl_outside_dec (M02_W S) (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (HTM a b E).
  - right. rewrite m02_TASK_SIZE. unfold M02_W, M02_FRAME in O. cbn [outside] in O. lia.
Qed.

Lemma m02_inv_refl : forall S c mm cap rc mc m0, M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m0.
Proof.
  intros S c mm cap rc mc m0 (HMI & HTM & _).
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HMI | exact HTM].
Qed.

(* A callee's post: it wrote only inside W, which lies inside M02_W S and below TASK_SIZE. *)
Lemma m02_inv_step : forall S m0 m m' W, M02_inv S m0 m -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  sub_fp W (M02_W S) -> (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < 2 ^ 47) -> M02_inv S m0 m'.
Proof.
  intros S m0 m m' W (MU & WM & _ & HTM) MU' WM' HMI' Hsub Hlow.
  split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ Hsub MU'))|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact HMI'|].
  intros a b E.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra.
  destruct (sl_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU' a O) in E. exact (HTM a b E).
  - right. rewrite m02_TASK_SIZE. exact (Hlow _ Ra O).
Qed.

(* The same, for a post that gives MemNorm.task_mem itself (snprintf's printf_post). *)
Lemma m02_inv_step_tm : forall S m0 m m' W, M02_inv S m0 m -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  MemNorm.task_mem rsegs m' -> sub_fp W (M02_W S) -> M02_inv S m0 m'.
Proof.
  intros S m0 m m' W (MU & WM & _ & _) MU' WM' HMI' HTM' Hsub.
  split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ Hsub MU'))|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact HMI' | exact HTM'].
Qed.

(* "nosuch0" of .rodata, read from the image (mem_inv: no byte of the memory is read-only). *)
Lemma m02_nosuch : forall m, mem_inv rsegs m -> bytes_at rsegs m STR_NOSUCH (zb S_nosuch ++ [ZERO]).
Proof.
  intros m H.
  assert (E : zb S_nosuch ++ [ZERO] = zb (S_nosuch ++ [0])) by (vm_compute; reflexivity). rewrite E.
  destruct (ro_cells_image rsegs m STR_NOSUCH (zb (S_nosuch ++ [0])) H ltac:(vm_compute; reflexivity)
              ltac:(unfold STR_NOSUCH; lia) ltac:(vm_compute; intros Hc; discriminate Hc)) as [_ R].
  cbn [cells_bytes cbytes] in R. rewrite app_nil_r in R. exact R.
Qed.

Lemma m02_nosuch_z : forall m, mem_inv rsegs m -> cstrz_at rsegs m STR_NOSUCH S_nosuch.
Proof.
  intros m H. exists (zb S_nosuch). split; [exact (m02_nosuch m H)|].
  split; [vm_compute; reflexivity|]. intros Hin. vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [discriminate Hin|]). exact Hin.
Qed.

Section K.
Variables (S c mm cap : Z) (rc : rconf) (mc : mconf) (m0 m : word -> option byte).
Hypothesis HM : M02_mem S c mm cap rc mc m0.
Hypothesis HI : M02_inv S m0 m.

Lemma m02_mem_inv : mem_inv rsegs m.
Proof. exact (proj1 (proj2 (proj2 HI))). Qed.

Lemma m02_task_mem : MemNorm.task_mem rsegs m.
Proof. exact (proj2 (proj2 (proj2 HI))). Qed.

Lemma m02_bnds : S mod 16 = 0 /\ 0x60000 <= S - 65536 /\ S <= 2 ^ 47 /\
  0 < c /\ c mod 16 = 0 /\ c + SEG_C_SIZE <= S - 65536 /\ 0 < mm /\ mm mod 16 = 0 /\ mm + SEG_M_SIZE <= S - 65536.
Proof.
  destruct HM as (_ & _ & _ & H16 & HT & H47 & _ & _ & _ & _ & _ & _ & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm & _).
  repeat split; assumption.
Qed.

Lemma m02_rom : forall a, S - 65536 <= a < S -> seg_rom rsegs (wa a) = None.
Proof. destruct HM as (_ & _ & _ & _ & _ & _ & _ & HR & _). exact HR. Qed.

(* A fact of m0 on bytes outside M02_W S holds at m. *)
Lemma m02_keep : forall a bs, bytes_at rsegs m0 a bs -> disjoint_from (M02_W S) a (Z.of_nat (length bs)) ->
  bytes_at rsegs m a bs.
Proof. intros a bs H Hd. exact (bytes_at_transport rsegs _ _ _ _ _ H (proj1 HI) Hd). Qed.

Lemma m02_rconf : rconf_at rsegs m c rc.
Proof.
  pose proof m02_bnds as (_ & _ & _ & Hc0 & _ & Hc & _).
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (bs & HB & HE) & _).
  exists bs. split; [|exact HE]. apply m02_keep; [exact HB|].
  rewrite (proj1 HE). unfold M02_W, M02_FRAME, SEG_C_SIZE in *. cbn [disjoint_from]. repeat split; lia.
Qed.

Lemma m02_mconf : mconf_at rsegs m mm mc.
Proof.
  pose proof m02_bnds as (_ & _ & _ & _ & _ & _ & Hm0 & _ & Hm).
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (bs & HB & HE)).
  exists bs. split; [|exact HE]. apply m02_keep; [exact HB|].
  rewrite (proj1 HE). unfold M02_W, M02_FRAME, SEG_M_SIZE in *. cbn [disjoint_from]. repeat split; lia.
Qed.

Lemma m02_ssp : ssp_ok m.
Proof.
  pose proof m02_bnds as (_ & HT & _).
  destruct HM as (_ & _ & (HG & g & HGd) & _).
  split; [|exists g]; apply m02_keep; try assumption; rewrite length_le8; unfold M02_W, M02_FRAME;
    cbn [disjoint_from sa_got_guard sa_guard SA SEG_UBSAN]; repeat split; lia.
Qed.

(* main's cells cap (sp + 0x20), c (sp + 0x48), m (sp + 0x50): outside M02_W. *)
Lemma m02_cap : bytes_at rsegs m (S - M02_FRAME + 0x20) (le8 (Z_to_bv 64 cap)).
Proof.
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & HC & _).
  apply m02_keep; [exact HC|]. rewrite length_le8. unfold M02_W, M02_FRAME. cbn [disjoint_from]. repeat split; lia.
Qed.

Lemma m02_cellc : bytes_at rsegs m (S - M02_FRAME + 0x48) (le8 (Z_to_bv 64 c)).
Proof.
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HC & _).
  apply m02_keep; [exact HC|]. rewrite length_le8. unfold M02_W, M02_FRAME. cbn [disjoint_from]. repeat split; lia.
Qed.

Lemma m02_cellm : bytes_at rsegs m (S - M02_FRAME + 0x50) (le8 (Z_to_bv 64 mm)).
Proof.
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HC & _).
  apply m02_keep; [exact HC|]. rewrite length_le8. unfold M02_W, M02_FRAME. cbn [disjoint_from]. repeat split; lia.
Qed.

(* The stack window stays present: it lies above SL_TOP, where every writable byte is present. *)
Lemma m02_stk : stk rsegs m (S - 65536) S.
Proof.
  pose proof m02_bnds as (_ & HT & H47 & _).
  destruct HM as (_ & _ & _ & _ & _ & _ & (_ & _ & HST) & _).
  apply sl_stk_of_writable; [unfold SL_TOP; lia | lia |].
  intros a Ha. unfold writable_at. apply (proj1 (proj2 HI)). exact (proj1 (HST a Ha)).
Qed.

(* The stack region a callee of main (sp = S - 240) uses. *)
Lemma m02_stack_ok : forall depth, 0 <= depth <= 65536 - M02_FRAME ->
  stack_ok rsegs m (S - 65536) (S - M02_FRAME) depth.
Proof.
  intros depth Hd. pose proof m02_bnds as (H16 & _).
  split; [exact (proj1 (stk_split rsegs m _ (S - M02_FRAME) _ m02_stk ltac:(unfold M02_FRAME; lia)))|].
  split; [unfold M02_FRAME in *; lia|]. split; [unfold M02_FRAME; Z.div_mod_to_equations; lia|].
  intros a Ha. apply m02_rom. unfold M02_FRAME in *. lia.
Qed.

(* Cells of main's own frame (or of the window) the walk stores to or reads. *)
Lemma m02_cells : forall a n, S - 65536 <= a -> a + Z.of_nat n <= S -> exists bs, rw_cells rsegs m a [CB n bs].
Proof. intros a n H1 H2. exact (sl_rw_of_stk m _ _ a n m02_stk H1 H2). Qed.

Lemma m02_bytes : forall a n, S - 65536 <= a -> a + Z.of_nat n <= S ->
  exists bs, length bs = n /\ bytes_at rsegs m a bs.
Proof.
  intros a n H1 H2. destruct (m02_cells a n H1 H2) as (bs & HC).
  pose proof HC as [[Hwf _] _]. cbn [cells_wf] in Hwf.
  exists bs. split; [exact (proj1 Hwf) | exact (sl_rw_bytes m a n bs HC)].
Qed.

(* The window's bytes are writable at m. *)
Lemma m02_wr : forall a n, S - 65536 <= a -> a + n <= S -> 0 <= n -> wr_at rsegs m a n.
Proof.
  intros a n H1 H2 H3. pose proof m02_stk as (_ & _ & HST). pose proof m02_bnds as (_ & HT & H47 & _).
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (HST (a + i) ltac:(lia))).
Qed.

(* A reader query of main (c, a C string name outside the callee region) at main's sp. *)
Lemma m02_qp : forall depth name nm, 0 <= depth <= 65536 - M02_FRAME -> name <> 0 ->
  cstrz_at rsegs m name nm -> apart name (Z.of_nat (length nm) + 1) (S - 65536) (S - M02_FRAME) ->
  query_pre depth m (S - M02_FRAME) (S - 65536) c name rc nm.
Proof.
  intros depth name nm Hd Hn Hz Ha. pose proof m02_bnds as (_ & _ & _ & Hc0 & Hc16 & Hc & _).
  unfold query_pre. split; [lia|]. split; [exact Hc16|]. split; [exact m02_rconf|].
  split; [unfold apart, M02_FRAME; left; lia|]. split; [exact Hn|]. split; [exact Hz|]. split; [exact Ha|].
  split; [apply m02_stack_ok; exact Hd | exact m02_mem_inv].
Qed.

(* m_find(m, name, n) at main's sp, the n bytes l at name outside the callee region. *)
Lemma m02_mfp : forall name l, bytes_at rsegs m name l ->
  apart name (Z.of_nat (length l)) (S - 65536) (S - M02_FRAME) ->
  m_find_pre m (S - M02_FRAME) (S - 65536) mm name (Z.of_nat (length l)) mc l.
Proof.
  intros name l Hb Ha. pose proof m02_bnds as (_ & _ & _ & _ & _ & _ & Hm0 & Hm16 & Hm).
  unfold m_find_pre. split; [lia|]. split; [exact Hm16|]. split; [exact m02_mconf|].
  split; [unfold apart, M02_FRAME; left; lia|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact Ha|].
  split; [apply m02_stack_ok; unfold M_FIND_STACK, M02_FRAME; lia | exact m02_mem_inv].
Qed.

End K.

(* sub_fp of a callee's write set inside M02_W S, and its addresses below 2^47: unfold and lia. *)
Ltac m02_subfp :=
  unfold sub_fp, M02_W, M02_FRAME; intros ?x ?Hx; cbn [outside] in *; repeat split; lia.
Ltac m02_low :=
  intros ?x ?Hx ?O; cbn [outside] in O; unfold M02_FRAME in *; first [ exfalso; apply O; exact I | lia ].

(* Debugging aid: run tac, or fail showing the goal. *)
Ltac m02_show tac := first [ tac | match goal with |- ?G => fail 100 "GOAL:" G end ].

(* A branch the facts refute: zify its condition, read the literal words, lia. *)
Ltac m02_kill K :=
  exfalso; zify_cond K;
  first [ rewrite ?m02_signed_lit in K by (unfold mseg_addr, MSEG_SIZE in *; lia);
          rewrite ?unsigned_lit in K by (unfold mseg_addr, MSEG_SIZE in *; lia);
          unfold mseg_addr, MSEG_SIZE in *;
          try (rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt in K);
          lia
        | (* the condition was split (andb / orb) into several hypotheses *)
          repeat match goal with
          | H : context [bv_signed (Z_to_bv 64 ?z)] |- _ =>
              rewrite (m02_signed_lit z) in H by (unfold mseg_addr, MSEG_SIZE in *; lia)
          | H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
              rewrite (unsigned_lit z) in H by (unfold mseg_addr, MSEG_SIZE in *; lia)
          end;
          unfold mseg_addr, MSEG_SIZE in *; lia ].
Ltac m02_br tac := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => m02_show tac
  | _ => idtac end.
Ltac m02_ntk := let K := fresh "K" in m02_br ltac:(if_cases K; [m02_kill K | clear K]).
Ltac m02_tkn := let K := fresh "K" in m02_br ltac:(if_cases K; [clear K | m02_kill K]).
