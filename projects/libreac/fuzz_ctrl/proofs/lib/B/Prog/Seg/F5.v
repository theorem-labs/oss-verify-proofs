(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1665 of its 1776 lines of code are new or changed and 900 lines of the source are left out. *)
(* Segment F5 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan build of libreac v1.9.0, image B), frame-loop turn
   j, and the reac_ctrl_parse call block 0x8214c-0x82158 that F5 and F6 share. rule 24: no function proved (a slot
   segment).

   F5 is the short-frame arm (the record is below 50 bytes). Its entry 0x82048 is the return point of the parse
   call 0x82044 (F2 / F3), its exit 0x8215c the return point of the second parse call 0x82158:
     0x82048 bnez a0,82fa4     a0 = t_k j = 0 (a short frame has no header, so the first parse gave kind 0):
                               not taken (0x82fa4 is the abort pair)
     0x8204c sd   zero,184(s1) [A+184] = 0 = b2z (t_tfill j)
     0x82050 sd   zero,272(s1) [A+272] = 0 = b2z (t_8819 j)
     0x82054 sd   zero,312(s1) [A+312] = 0 (t_big j is false)
     0x82058 li   s8,0         s8 = 0 = t_k j
     0x8205c li   s9,0         s9 = 0 = b2z (t_sum_ok j)
     0x82060 li   a0,1 ; 0x82064 j 82148
     0x82148 sd   a0,248(s1)   [A+248] = 1 = 1 - b2z (t_sum_ok j)   (shared with F6)
   v1.9.0 against the patched image: the fill flag is the spill [A+184] (was s5), the sum flag s9 = b2z sum_ok
   (was [A+288]) and its complement the spill [A+248] (was s9); the join moves from 0x820d8 to 0x8214c (after the
   shared store at 0x82148); the abort pair is 0x82fa4 (was 0x82f40).
   The range has no instrumented check and no UBSan trap. The four stores write the spill words [A+184, A+192),
   [A+272, A+280), [A+312, A+320) and [A+248, A+256) of the save area: FRA and ENT move across them by c_fra_spill
   (Tac_slot's sl_stk_run and ent_store), the frame-loop bundles by c_spill_keep / c_lk_keep.

   The parse call block (F5's and F6's common tail):
     0x8214c mv a0,s2 ; 0x82150 mv a1,s4 ; 0x82154 li a2,0 ; 0x82158 jal reac_ctrl_parse
   seg_c proves it from the join cut Inv_B8214c_join (Inv_B8215c_at without the parse result) to the official
   Inv_B8215c_at. The callee runs on its lib/B contract (reac_ctrl_parse_c.v, the Section Hypothesis PARSE) with
   f = Phi, n = len and o = 0; the contract needs mem_inv, so the call runs on MemNorm.normalize of the memory
   (c_evt, after image A's F6 f6_ebc_evt). The side-stack package is Tac_fsfree's fra_fp, the window facts are
   fra_callee_fp. The write set c_PW is the callee window [sp - 8800, sp), the class-1 side-stack bytes and their
   shadow, and the shadow of the window; FRA moves across it by c_fra_run (R4's r4_fra) and c_fra_call (image A's
   f6_fra_call), ENT by ent_munch and ent_mat. Every cut fact is a spill at
   or above sp, a frame byte, a heap byte of the live block below stklo, an image byte or the shadow byte of one of
   those, so it is outside c_PW (c_PW_outs). The exit's v is t_k j: the contract returns fst (ctrlparse len (t_g
   j)) = t_k j, s8 = t_k j is FM's and the first word at fr + 176 ([A+280], FLI) is the parse struct's kind byte
   (pBb, ctrlparse_kind_bytes).

   CUTS. seg_F5 is S_F5 of a Theorem Labs lane's forms-asan-ubsan-v190.md (a working note, not in this delivery) over the official cuts of SlotInv.v (
   217aa9d4cd9): Inv_B82048_at carries a0 = t_k j and flen g j < 50 (0x82048 is reached only from 0x81f64 beqz s4
   and 0x81f7c bltu s4,50), and LK's FLI carries KNT (the KIND_NAME table bytes and their addressability), from
   which seg_c gives the exit's explicit KIND_NAME pair. Inv_B8214c_join is internal to this unit (the join of F5
   and F6). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
(* The fragment-record model (the record lengths c_FG_length / c_ID_length), imported before the main imports as
   lib/B/Prog/Seg/F8.v does, so those keep their names. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ================= register, byte and word helpers ================= *)

Lemma c_mkR_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried value, from H : rg regs r v. *)
Ltac c_slot H := let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* An rg fact moved to a register-equal state (through conversion, F8's f8_rg_move). *)
Lemma c_rg_move : forall (regs regs' : bvmap 5 word) (r : bv 5) (v : Z),
  rg regs r v -> getr regs' r = getr regs r -> rg regs' r v.
Proof. intros regs regs' r v H E. unfold rg in H |- *. exact (eq_trans E H). Qed.

Lemma c_id : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

Lemma c_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

(* A machine state with no pending syscall is the MS of its own fields. *)
Lemma c_ms_eta : forall ms, ms_svc_pending ms = None ->
  ms = MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros ms H. destruct ms. cbn in H. subst. reflexivity. Qed.

(* An 8-byte cell survives a write whose footprint misses it. *)
Lemma c_q64_keep : forall W m m' a v, q64 m a v -> munch W m m' ->
  (forall x, a <= x < a + 8 -> outside W x) -> q64 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold q64 in *.
  apply (fl_bytes W m m' a (le8 (Z_to_bv 64 v)) H MU).
  rewrite length_le8. exact HW.
Qed.

(* The spill base named by a spill conjunct is the A of register 9 (R4's r4_spill_A). *)
Lemma c_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* A spill word as a q64 at the spill base A of register 9. *)
Lemma c_spill_q64 : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A1 & H1 & Hq) H9 HA0 HA1 Hoff.
  rewrite (c_spill_A regs m off v A A1 H1 Hq H9 HA0 ltac:(lia) ltac:(lia)) in Hq. exact Hq.
Qed.

(* A frame-loop spill word survives a run that misses its eight bytes and keeps register 9. *)
Lemma c_spill_keep : forall regs regs' A off v m m' W,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  getr regs' 9 = getr regs 9 -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' A off v m m' W HS H9 HA0 HA1 Hoff E9 MU HW.
  pose proof (c_spill_q64 regs m off v A HS H9 HA0 HA1 Hoff) as Hq.
  exists A. split; [exact (c_rg_move regs regs' _ _ H9 E9)|].
  exact (c_q64_keep W m m' (A + off) v Hq MU HW).
Qed.

(* addressable survives a run whose writes miss the shadow bytes of the range (R4's r4_addr_keep). *)
Lemma c_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

(* stk across a run whose written bytes read back afterwards (R4's r4_stk_tr). *)
Lemma c_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma c_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* A present byte of a carried byte list reads back (R4's r4_ba_rd). *)
Lemma c_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

(* A prefix of a carried byte list is carried. *)
Lemma c_bytes_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H). pose proof (length_firstn n bs) as HL.
  split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite (H i ltac:(lia)).
  rewrite <- (firstn_skipn n bs) at 1. apply nth_error_app1. lia.
Qed.

Lemma c_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

(* ================= the turn records' lengths (Tac_ro.v's tr_* proofs) ================= *)

Lemma c_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold fg_first, fg_body.
  rewrite !length_app, length_skipn, (rf_bsl_length g 6 6), (rf_bsl_length g 27 (fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma c_fr_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma c_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.

Lemma c_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply c_first_length; [exact HL | exact HG | apply (c_fr_fg_n len); exact FR].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply rf_clear_length, rf_fg_join_length;
      solve [exact HL | exact HG | apply (c_fr_fg_n len); exact FR | apply c_keep_T; exact KEEP].
Qed.

Lemma c_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (c_next_length 1 1 1 1 1); solve [exact IH | unfold t_g; apply fr50_length].
Qed.

Lemma c_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn.
    assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact IH | exact IH]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; unfold fg_id;
      (match goal with |- context [if ?c then _ else _] => destruct c end;
       [apply RcIdentModel.ING_length; exact Hr | exact Hr]).
Qed.

Lemma c_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

(* ================= the frame-loop bundles across a run ================= *)

(* FLI / LK across a run that keeps s11 and register 9 and moves the FLI spills (Tac_ro.v's fli_keep / lk_keep;
   adopt 11 adds KNT, the KIND_NAME table bytes and their addressability).  The spill premise excludes the four
   words the frame-loop segments F4-F6 store in v1.9.0 ([A+184], [A+248], [A+272], [A+312]), none of which is an
   FLI spill.  RAD (the records' and the local `first`'s addressable bytes) is kept whole. *)
Lemma c_fli_keep : forall g fr (regs regs' : bvmap 5 word) (m m' : word -> option byte),
  FLI g fr regs m -> rg regs' 27 (-8) ->
  addressable m' (fr + 2624) 6 -> stk rsegs m' fr (fr + FRAME_BYTES) -> RAD fr m' -> KNT m' ->
  (forall off v, 0 <= off <= 336 -> off mod 8 = 0 -> off <> 184 -> off <> 248 -> off <> 272 -> off <> 312 ->
     spill regs m off v -> spill regs' m' off v) ->
  FLI g fr regs' m'.
Proof.
  intros g fr regs regs' m m' H H27 Had Hstk HRAD HKN K. unfold FLI in H |- *.
  destruct H as (_ & H168a & H96 & H112 & H120 & H128 & H136 & H144 & H152 & H280 & H160 & H176 & H192 & H200 &
    H216 & H208 & H104 & H256 & H264 & H288 & H296 & H304 & _ & _ & _ & _ & H168 & H88).
  repeat match goal with |- _ /\ _ => split end;
    solve [ exact H27 | exact Had | exact Hstk | exact HRAD | exact HKN
          | apply K; [lia | reflexivity | lia | lia | lia | lia | assumption] ].
Qed.

Lemma c_fli_mem : forall g fr (regs : bvmap 5 word) (m : word -> option byte),
  FLI g fr regs m -> rg regs 27 (-8) /\ addressable m (fr + 2624) 6 /\ stk rsegs m fr (fr + FRAME_BYTES) /\
    RAD fr m /\ KNT m.
Proof.
  intros g fr regs m H. unfold FLI in H.
  destruct H as (H27 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Had &
    Hstk & HRAD & HKN & _ & _).
  split; [exact H27|]. split; [exact Had|]. split; [exact Hstk|]. split; [exact HRAD | exact HKN].
Qed.

(* KNT across a run that misses the image and its shadow. *)
Lemma c_knt_keep : forall W m m', KNT m -> munch W m m' ->
  (forall x, 0 <= x < AC.GT -> outside W x /\ outside W (shadow_addr x)) -> KNT m'.
Proof.
  intros W m m' (HKb & HKa) MU Olo.
  assert (HKl : length KNC.kind_name_bytes = 112%nat) by reflexivity.
  assert (HKv : KNC.KIND_NAME = 0x9f580) by reflexivity.
  assert (HGT : AC.GT = 6283264) by reflexivity.
  split.
  - apply (fl_bytes W m m' KNC.KIND_NAME _ HKb MU). rewrite HKl. intros x Hx.
    change (Z.of_nat 112) with 112 in Hx. exact (proj1 (Olo x ltac:(lia))).
  - apply (c_addr_keep W m m' KNC.KIND_NAME 112 HKa MU). intros i Hi.
    exact (proj2 (Olo (KNC.KIND_NAME + i) ltac:(lia))).
Qed.

(* LK across a run whose write set misses the save area offsets 0 .. 344 but for the four store words, the frame
   (stk, our[], the records and `first`) and its shadow, and the image and its shadow, and that keeps registers 9
   and 27. *)
Lemma c_lk_keep : forall g fr j A (regs regs' : bvmap 5 word) (m m' : word -> option byte) W,
  LK g fr j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + 344 -> ~ (A + 184 <= x < A + 192) -> ~ (A + 248 <= x < A + 256) ->
     ~ (A + 272 <= x < A + 280) -> ~ (A + 312 <= x < A + 320) -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x)) ->
  (forall x, 0 <= x < AC.GT -> outside W x /\ outside W (shadow_addr x)) ->
  LK g fr j regs' m'.
Proof.
  intros g fr j A regs regs' m m' W (Hj & H240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 MU WM OA Ofr Olo.
  pose proof FRAME_BYTES_val as HFBv.
  destruct (c_fli_mem g fr regs m HFLI) as (H27 & Had & Hstk & HRAD & HKN).
  assert (K : forall off v, 0 <= off <= 336 -> off mod 8 = 0 -> off <> 184 -> off <> 248 -> off <> 272 ->
            off <> 312 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hm8 H1 H2 H3 H4 HS.
    apply (c_spill_keep regs regs' A off v m m' W HS H9 HA0 HA1 ltac:(lia) E9 MU).
    intros x Hx. apply OA; Z.div_mod_to_equations; lia. }
  assert (KA : forall p n, fr <= p -> p + n <= fr + FRAME_BYTES -> addressable m p n -> addressable m' p n).
  { intros p n Hp Hn Had0. apply (c_addr_keep W m m' p n Had0 MU).
    intros i Hi. exact (proj2 (Ofr (p + i) ltac:(lia))). }
  split; [exact Hj|]. split; [apply K; [lia | reflexivity | lia | lia | lia | lia | exact H240]|].
  split.
  { unfold OURb in *. apply (fl_bytes W m m' (fr + 2624) (OUR (g_in g)) HOUR MU).
    rewrite OUR_length. intros x Hx. change (Z.of_nat 6) with 6 in Hx. exact (proj1 (Ofr x ltac:(lia))). }
  apply (c_fli_keep g fr regs regs' m m' HFLI (c_rg_move regs regs' _ _ H27 E27)).
  - apply KA; [lia | lia | exact Had].
  - apply (c_stk_tr W m m' fr (fr + FRAME_BYTES) Hstk MU WM). intros x Hx. left. exact (proj1 (Ofr x Hx)).
  - unfold RAD in HRAD |- *. destruct HRAD as (Hid & Hfg & Hfs). unfold fragb in *.
    split; [apply KA; [lia | lia | exact Hid]|]. split; [apply KA; [lia | lia | exact Hfg]|].
    apply KA; [lia | lia | exact Hfs].
  - exact (c_knt_keep W m m' HKN MU Olo).
  - exact K.
Qed.

(* REC0 (the identity record at fr + 2688 and the fragment record at fr + 2768) across a run that misses the
   frame. *)
Lemma c_rec0_keep : forall g fr j W m m', REC0 g fr j m -> munch W m m' ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x) -> REC0 g fr j m'.
Proof.
  intros g fr j W m m' H MU HO. pose proof FRAME_BYTES_val as HFBv. unfold REC0, FREC, IDb, FGb, IDBe, FGBe in *.
  destruct H as ((HID & Hidok) & (HFG & Hfgok)).
  split; split; try assumption.
  - apply (fl_bytes W m m' (fr + 2688) _ HID MU). rewrite c_ID_length.
    intros x Hx. change (Z.of_nat 38) with 38 in Hx. apply HO. lia.
  - apply (fl_bytes W m m' (fr + 2768) _ HFG MU). rewrite c_FG_length.
    intros x Hx. change (Z.of_nat 72) with 72 in Hx. apply HO. lia.
Qed.

(* FPS (the parse struct's 36 bytes at fr + 176 and their addressability) across a run that misses the frame and
   its shadow. *)
Lemma c_fps_keep : forall g fr j W m m', FPS g fr j m -> munch W m m' ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x)) -> FPS g fr j m'.
Proof.
  intros g fr j W m m' (HpB & HadB) MU HO. pose proof FRAME_BYTES_val as HFBv. split.
  - unfold pBb in *. apply (fl_bytes W m m' (fr + 176) (t_B (g_in g) j) HpB MU).
    assert (Lb : length (t_B (g_in g) j) = 36%nat) by apply ctrlparse_length.
    rewrite Lb. intros x Hx. change (Z.of_nat 36) with 36 in Hx. exact (proj1 (HO x ltac:(lia))).
  - apply (c_addr_keep W m m' (fr + 176) 36 HadB MU). intros i Hi. exact (proj2 (HO (fr + 176 + i) ltac:(lia))).
Qed.

(* The body of the first-fragment state is at most 23 bytes (firstn of the last 23 of the 50 frame bytes). *)
Lemma c_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens _ _); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* FSj (v1.9.0: the frame local `first`: have at fr + 2880, n at fr + 2884, the body from fr + 2885, its 40
   addressable bytes; FI reads the ghost only) across a run that misses the frame and its shadow. *)
Lemma c_fsj_keep : forall g fr j (regs regs' : bvmap 5 word) m m' W,
  FSj g fr j regs m -> munch W m m' ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x)) -> FSj g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W HF MU HO. pose proof FRAME_BYTES_val as HFBv.
  unfold FSj, FSb in HF |- *. destruct HF as (Hhave & Hn & Hbody & Had & HFI).
  pose proof (c_body_len (g_in g) j) as HL.
  split; [unfold u32 in *; apply (fl_bytes W m m' _ _ Hhave MU); rewrite length_le4;
          intros x Hx; change (Z.of_nat 4) with 4 in Hx; exact (proj1 (HO x ltac:(lia)))|].
  split; [unfold b8 in *; apply (fl_bytes W m m' _ _ Hn MU); cbn [length];
          intros x Hx; change (Z.of_nat 1) with 1 in Hx; exact (proj1 (HO x ltac:(lia)))|].
  split; [apply (fl_bytes W m m' _ _ Hbody MU); intros x Hx; exact (proj1 (HO x ltac:(lia)))|].
  split; [apply (c_addr_keep W m m' (fr + 2880) 40 Had MU); intros i Hi;
          exact (proj2 (HO (fr + 2880 + i) ltac:(lia)))|].
  exact HFI.
Qed.

(* FTURN (v1.9.0: the cursor spills [A+224] / [A+232] and the frame bytes at Phi, at most len of them). *)
Lemma c_fturn_keep : forall g j phi A (regs regs' : bvmap 5 word) m m' W,
  FTURN g j phi regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  munch W m m' -> (forall x, A + 224 <= x < A + 240 -> outside W x) ->
  (forall x, phi <= x < phi + t_len (g_in g) j -> outside W x) -> FTURN g j phi regs' m'.
Proof.
  intros g j phi A regs regs' m m' W (H224 & H232 & HPB & HPL) H9 HA0 HA1 E9 MU OA OP.
  split; [apply (c_spill_keep regs regs' A 224 _ m m' W H224 H9 HA0 HA1 ltac:(lia) E9 MU);
          intros x Hx; apply OA; lia|].
  split; [apply (c_spill_keep regs regs' A 232 _ m m' W H232 H9 HA0 HA1 ltac:(lia) E9 MU);
          intros x Hx; apply OA; lia|].
  split; [|exact HPL].
  apply (fl_bytes W m m' phi _ HPB MU). intros x Hx. apply OP. lia.
Qed.

(* The kind byte of the parse struct: the first word at fr + 176 is t_k j (ctrlparse_kind_bytes, 0 <= t_k <= 13). *)
Lemma c_le4_kind : forall k, 0 <= k <= 13 -> le4 (Z_to_bv 64 k) = [Z_to_bv 8 k; cp_z; cp_z; cp_z].
Proof.
  intros k Hk.
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
              k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia.
  repeat (destruct E as [E|E]; [subst k; reflexivity|]). subst k. reflexivity.
Qed.

Lemma c_u32_kind : forall g fr j m, pBb g fr j m -> u32 m (fr + 176) (t_k (g_in g) j).
Proof.
  intros g fr j m H. unfold pBb, u32, t_k, t_B in *.
  pose proof (ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)) as R.
  rewrite (c_le4_kind _ R). rewrite <- ctrlparse_kind_bytes. exact (c_bytes_firstn m _ _ 4 H).
Qed.

(* ================= the normalized memory (MemNorm) ================= *)

Definition c_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma c_tops_gt : c_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c_find_below : forall segs top x n s,
  c_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold c_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma c_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (c_find_below sg 0x5fe000 x n s c_tops_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma c_stk_iff : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb);
    pose proof (wview_rel_rw rsegs m m0 (wa a) HR (c_ro_hi a ltac:(lia))) as EW;
    pose proof (mrd_rel rsegs m m0 (wa a) HR) as ER.
  - split; [rewrite EW; exact Hw | exists b; rewrite <- ER; exact Hb].
  - split; [rewrite <- EW; exact Hw | exists b; rewrite ER; exact Hb].
Qed.

Lemma c_sw_iff : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR.
  split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    pose proof Ha as Ha'; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha';
    destruct (H a Ha) as (Hw & b & Hb);
    pose proof (wview_rel_rw rsegs m m0 (wa a) HR (c_ro_hi a ltac:(lia))) as EW;
    pose proof (mrd_rel rsegs m m0 (wa a) HR) as ER.
  - split; [rewrite EW; exact Hw | exists b; rewrite <- ER; exact Hb].
  - split; [rewrite <- EW; exact Hw | exists b; rewrite ER; exact Hb].
Qed.

Lemma c_addr_iff : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR.
  split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]); (split; [exact H2|]);
    intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); (split; [exact Hap|]); exists b;
    pose proof (mrd_rel rsegs m m0 (wa (shadow_addr (p + i))) HR) as ER.
  - rewrite <- ER. split; [exact Hb | exact Hok].
  - rewrite ER. split; [exact Hb | exact Hok].
Qed.

Lemma c_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (proj1 (bytes_at_rel rsegs m m0 a bs R) ltac:(assumption)) end.
Qed.

Lemma c_tls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k R H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19).
  unfold asan_tls_cells.
  split; [exact (R _ _ H1)|]. split; [exact (R _ _ H2)|]. split; [exact (R _ _ H3)|].
  split; [exact (R _ _ H4)|]. split; [exact (R _ _ H5)|]. split; [exact Hk|].
  split; [exact (R _ _ H7)|]. split; [exact (R _ _ H8)|]. split; [exact (R _ _ H9)|].
  split; [exact (R _ _ H10)|]. split; [exists tb, te; exact (R _ _ H11)|].
  split; [exact (R _ _ H12)|]. split; [exact (R _ _ H13)|]. split; [exact (R _ _ H14)|].
  split; [exact (R _ _ H15)|]. split; [exact (R _ _ H16)|]. split; [exact (R _ _ H17)|].
  split; [exact HDB|]. exact (R _ _ H19).
Qed.

Lemma c_fp_tr : forall cs m m0 TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (forall lo' hi', 0x5fe000 <= lo' -> hi' <= 2 ^ 64 -> stk rsegs m lo' hi' -> stk rsegs m0 lo' hi') ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D Hba Hstk
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact (c_tls_tr m m0 _ _ _ _ _ _ _ Hba HT)|].
  split; [exact (Hba _ _ HTP)|].
  split.
  { destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. pose proof P5 as P5'. destruct P5' as (_ & P5b & _).
    apply Hstk; [unfold ASAN_GT in P3; lia | exact P5b | exact P5]. }
  split; [exact (Hba _ _ H88)|].
  split; [exact (Hba _ _ H96)|].
  split.
  { eapply Forall_impl; [|exact HCL]. intros c (Hc & h & fl & Hh & Hfl & Hfll & Hflb).
    split; [exact Hc|]. exists h, fl. split; [exact (Hba _ _ Hh)|]. split; [exact (Hba _ _ Hfl)|].
    split; [exact Hfll | exact Hflb]. }
  split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HDd].
Qed.

Lemma c_fp_iff : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D HR. split; apply c_fp_tr.
  - intros a bs H. exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) H).
  - intros lo' hi' H1 H2 H. exact (proj1 (c_stk_iff m m0 lo' hi' HR H1 H2) H).
  - intros a bs H. exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) H).
  - intros lo' hi' H1 H2 H. exact (proj2 (c_stk_iff m m0 lo' hi' HR H1 H2) H).
Qed.

Lemma c_tls_iff : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k HR. split; apply c_tls_tr; intros a bs H.
  - exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) H).
  - exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) H).
Qed.

(* ================= the parse call's write set (o = 0) ================= *)

Lemma c_M1 : fs_M 1%nat = 8192.
Proof. reflexivity. Qed.

Lemma c_hint1 : forall FS, fs_hint FS 1%nat = FS + 8.
Proof. intros FS. unfold fs_hint. cbn [Z.of_nat]. lia. Qed.

Lemma c_flag1 : forall FS, fs_flag FS 1%nat 0 = FS + 20480.
Proof.
  intros FS. unfold fs_flag.
  replace (2 ^ 15) with 32768 by reflexivity.
  replace (2 ^ (15 - Z.of_nat 1)) with 16384 by reflexivity. lia.
Qed.

Lemma c_frame1_0 : forall FS, fs_frame FS 1%nat 0 = FS + 1085440.
Proof. intros FS. unfold fs_frame. replace (2 ^ 20) with 1048576 by reflexivity. cbn [Z.of_nat]. lia. Qed.

Lemma c_frame1_M : forall FS, fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016.
Proof.
  intros FS. unfold fs_frame, fs_B. rewrite c_M1.
  replace (2 ^ 20) with 1048576 by reflexivity. cbn [Z.of_nat]. lia.
Qed.

Definition c_PW (S FS : Z) : list ivl :=
  reac_ctrl_parse_fp 0 S ++ fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)].

Lemma c_PW_eq : forall S FS, c_PW S FS =
  [(S - 8800, S); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (S - 8800), shadow_addr S)].
Proof.
  intros S FS. unfold c_PW, reac_ctrl_parse_fp, fp_w, fp_w1. cbn [flat_map app Z.eqb].
  rewrite c_hint1, c_flag1, c_frame1_M, c_frame1_0, c_M1. unfold REAC_CTRL_PARSE_K.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia. replace (FS + 8 + 8) with (FS + 16) by lia. reflexivity.
Qed.

(* A contiguous app range lies wholly in the low or wholly in the high app memory. *)
Lemma c_app_split : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> app_mem a) ->
  hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
Proof.
  intros lo hi Hlt H. destruct (Z_le_gt_dec hi LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec HIGHMEM_BEG lo) as [L2|L2]; [exact L2|exfalso].
  destruct (Z_le_gt_dec lo LOWMEM_END) as [L3|L3].
  - pose proof (H LOWMEM_END ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - pose proof (H lo ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* The shadow bytes of a contiguous app range are shadow memory. *)
Lemma c_shadow_ivl : forall lo hi x, (forall a, lo <= a < hi -> app_mem a) -> lo < hi ->
  shadow_addr lo <= x < shadow_addr hi -> in_shadow x.
Proof.
  intros lo hi x Happ Hlt Hx.
  assert (Hlo : 0 <= lo)
    by (pose proof (Happ lo ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hhi : hi <= APPMEM_END)
    by (pose proof (Happ (hi - 1) ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
  unfold in_shadow. unfold shadow_addr in Hx. destruct (c_app_split lo hi Hlt Happ) as [HL|HH].
  - left. unfold ASAN_K, LOWMEM_END, LOWSHADOW_END in *. Z.div_mod_to_equations. lia.
  - right. unfold ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

(* An app byte outside the window and the three class-1 side-stack ranges is outside the parse writes. *)
Lemma c_out_PW : forall S FS x,
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - REAC_CTRL_PARSE_K <= a < S -> app_mem a) ->
  REAC_CTRL_PARSE_K <= S -> app_mem x ->
  ~ (S - REAC_CTRL_PARSE_K <= x < S) ->
  ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
  ~ (FS + 1085440 <= x < FS + 2134016) ->
  outside (c_PW S FS) x.
Proof.
  intros S FS x HFS HW HSK Hx H1 H2 H3 H4. rewrite c_PW_eq. cbn [outside].
  unfold REAC_CTRL_PARSE_K in H1, HSK.
  split; [intros HC; lia|]. split; [intros HC; lia|]. split; [intros HC; lia|]. split; [intros HC; lia|].
  split.
  { intros HC. apply (app_not_shadow x Hx).
    apply (c_shadow_ivl (FS + 1085440) (FS + 2134016) x);
      [intros a Ha; apply HFS; unfold FS_SIZE; lia | lia | lia]. }
  split; [|exact I].
  intros HC. apply (app_not_shadow x Hx).
  apply (c_shadow_ivl (S - 8800) S x);
    [intros a Ha; apply HW; unfold REAC_CTRL_PARSE_K; lia | lia | lia].
Qed.

(* The shadow byte of an app byte apart from the window and from the class-1 frames is outside the parse writes. *)
Lemma c_sh_out : forall S FS p n i,
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) ->
  (forall a, S - REAC_CTRL_PARSE_K <= a < S -> app_mem a) ->
  REAC_CTRL_PARSE_K <= S -> S mod 8 = 0 -> FS mod 8 = 0 ->
  0 <= i < n -> app_mem (p + i) ->
  (p + n <= S - REAC_CTRL_PARSE_K \/ S <= p) ->
  (p + n <= FS + 1085440 \/ FS + 2134016 <= p) ->
  outside (c_PW S FS) (shadow_addr (p + i)).
Proof.
  intros S FS p n i HFS HW HSK HS8 HFS8 Hi Hap Hdw Hdf.
  pose proof (shadow_of_app (p + i) Hap) as Hsh.
  rewrite c_PW_eq. cbn [outside].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HW (shadow_addr (p + i)) ltac:(unfold REAC_CTRL_PARSE_K; lia)) Hsh)|].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HFS (shadow_addr (p + i)) ltac:(unfold FS_SIZE; lia)) Hsh)|].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HFS (shadow_addr (p + i)) ltac:(unfold FS_SIZE; lia)) Hsh)|].
  split; [intros HC; exact (app_not_shadow (shadow_addr (p + i))
            (HFS (shadow_addr (p + i)) ltac:(unfold FS_SIZE; lia)) Hsh)|].
  split.
  { intros HC. unfold shadow_addr, ASAN_K in *. destruct Hdf as [Hd|Hd]; Z.div_mod_to_equations; lia. }
  split; [|exact I].
  intros HC. unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_K in *. destruct Hdw as [Hd|Hd];
    Z.div_mod_to_equations; lia.
Qed.

(* The side stack after the call: a_fs_ok rebuilt from the contract's fp post (R9's r9_fs_ok). *)
Lemma c_fs_ok : forall m m' TP FS lo hi W D W',
  AC.a_fs_ok m FS ->
  fp [1%nat] m' TP FS lo hi W D ->
  munch W' m m' ->
  (forall x, FS <= x < FS + 8 -> outside W' x) ->
  (forall x, FS + 16 <= x < FS + 88 -> outside W' x) ->
  (forall x, FS + 4096 <= x < FS + 20480 -> outside W' x) ->
  (forall x, FS + 28672 <= x < FS + 36864 -> outside W' x) ->
  AC.a_fs_ok m' FS.
Proof.
  intros m m' TP FS lo hi W D W' (K1 & K2 & K3 & K4 & K5)
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFSlo & HA & HWd & HDd) MU O1 O2 O3 O4.
  assert (HSZ' : FS_SIZE = 11571200) by reflexivity.
  pose proof HP as HP'. destruct HP' as (P1 & P2 & P3 & P4 & P5).
  assert (HFS64 : FS + 11571200 <= 2 ^ 64).
  { pose proof (P4 (FS + FS_SIZE - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. lia. }
  assert (HM1 : AC.a_fs_M 1%nat = 8192) by reflexivity.
  inversion HCL as [|c0 l0 Hc1 Hrest Heq]; subst.
  destruct Hc1 as (_ & h & flags & HH & HF & HFl & HFb).
  rewrite c_M1 in HFl.
  split.
  { intros a Ha. destruct P5 as (_ & _ & Hs). destruct (Hs a ltac:(unfold AC.FS_SIZE in Ha; lia)) as (Hw & Hb).
    split; [exact Hw | exact Hb]. }
  split.
  { replace 20 with (bv_unsigned (Z_to_bv 64 20)) by reflexivity.
    exact (KindBGlue.bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88). }
  split.
  { destruct H96 as (_ & _ & Hb). pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as E.
    replace (FS + 96 + Z.of_nat 0) with (FS + 96) in E by lia. exact E. }
  split.
  { intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hne].
    - exists (bv_unsigned h).
      replace (AC.a_fs_hint FS 1) with (fs_hint FS 1%nat) by (unfold AC.a_fs_hint, fs_hint; reflexivity).
      exact (KindBGlue.bytes_at_le8_word rsegs m' _ h HH).
    - destruct (K4 c Hc) as (h' & Hh). exists h'.
      apply (KindBGlue.kb_word_munch rsegs m m' W' _ h' Hh MU).
      intros j Hj. unfold AC.a_fs_hint.
      assert (Hcn : Z.of_nat c <> 1) by (intros Hcc; apply Hne; lia).
      split; [lia|].
      destruct (Z.eq_dec (Z.of_nat c) 0) as [E0|E0].
      + apply O1. lia.
      + apply O2. lia. }
  { intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hne].
    - rewrite HM1 in Hj.
      assert (Hlen : (Z.to_nat j < length flags)%nat) by lia.
      destruct HF as (_ & _ & Hb).
      destruct (nth_error flags (Z.to_nat j)) as [bb|] eqn:En;
        [|exfalso; apply nth_error_None in En; lia].
      pose proof (Hb (Z.to_nat j) Hlen) as E. rewrite En in E.
      replace (fs_flag FS 1%nat 0 + Z.of_nat (Z.to_nat j)) with (AC.a_fs_flag FS 1%nat j) in E
        by (unfold fs_flag, AC.a_fs_flag; lia).
      pose proof (proj1 (Forall_forall _ _) HFb bb (nth_error_In _ _ En)) as Hb01.
      destruct Hb01 as [Eb|Eb]; subst bb; [left | right]; exact E.
    - assert (Hcn : Z.of_nat c <> 1) by (intros Hcc; apply Hne; lia).
      assert (Hc10 : Z.of_nat c <= 10) by lia.
      assert (Hp : 2 ^ (15 - Z.of_nat c) = 2 * 2 ^ (14 - Z.of_nat c)).
      { replace (15 - Z.of_nat c) with (Z.succ (14 - Z.of_nat c)) by lia. rewrite Z.pow_succ_r by lia. lia. }
      assert (Hq0 : 0 < 2 ^ (14 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
      unfold AC.a_fs_M in Hj.
      assert (Hrange : FS + 4096 <= AC.a_fs_flag FS c j < FS + 20480 \/
                       FS + 28672 <= AC.a_fs_flag FS c j < FS + 36864).
      { unfold AC.a_fs_flag. replace (2 ^ 15) with 32768 by reflexivity.
        destruct (Z.eq_dec (Z.of_nat c) 0) as [E0|E0].
        - left. rewrite E0 in Hp, Hj |- *. replace (2 ^ (14 - 0)) with 16384 in Hj by reflexivity.
          replace (2 ^ (15 - 0)) with 32768 by reflexivity. lia.
        - right. assert (Hq2 : 2 ^ (14 - Z.of_nat c) <= 4096).
          { replace 4096 with (2 ^ 12) by reflexivity. apply Z.pow_le_mono_r; lia. }
          lia. }
      assert (Hb64 : 0 <= AC.a_fs_flag FS c j < 2 ^ 64) by lia.
      assert (Hout : outside W' (AC.a_fs_flag FS c j)) by (destruct Hrange; [apply O3 | apply O4]; lia).
      rewrite (KindBGlue.mbyte_munch rsegs W' m m' _ MU Hb64 Hout).
      exact (K5 c j Hc Hj). }
Qed.

(* The runtime cells the bcmp wrapper of reac_ctrl_parse reads, from FRA's AsanRTInv.RT alone. *)
Lemma c_byte1 : forall m a bs (i : nat) b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. destruct k as [|k]; [|lia].
  cbn [nth_error]. replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by lia.
  rewrite H by exact Hi. exact Hn.
Qed.

Lemma c_rt_cells : forall sp m md, AsanRTInv.RT sp m md ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_real_cells sp m md HRT) as HR.
  pose proof (AsanRTInv.RT_cf_cells sp m md HRT) as (Hg & _ & _ & _ & _ & _ & H240 & _).
  split; [exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact Hg|].
  split.
  - pose proof (c_byte1 m (RT_CF + 240) _ 14 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in HH by (unfold RT_CF, CF; lia). exact HH.
  - pose proof (c_byte1 m (RT_CF + 240) _ 15 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in HH by (unfold RT_CF, CF; lia). exact HH.
Qed.

(* The six BC bytes the bcmp wrapper compares with are the registered global (0x21200, 7). *)
Lemma c_bc_addr : forall m, (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  addressable m REAC_CTRL_PARSE_BC 6.
Proof.
  intros m HAG. unfold REAC_CTRL_PARSE_BC.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi.
  assert (Hg : in_globals AF.frame_AG (0x21200 + i)).
  { exists 0x21200, 7. split; [|lia]. unfold AF.frame_AG. do 4 apply in_cons. apply in_eq. }
  destruct (HAG _ Hg) as (_ & _ & _ & H). specialize (H 0 ltac:(lia)). rewrite Z.add_0_r in H. exact H.
Qed.

(* Every index reac_ctrl_parse reads of its 50-byte header lies in that header; none of a short record. *)
Lemma c_cp_rd_lt : forall n fr i, In i (cp_rd n fr) -> (i < 50)%nat.
Proof. intros n fr i H. pose proof (cp_rd_lt39 n fr i H). lia. Qed.

Lemma c_cp_rd_short : forall n fr, n < 50 -> cp_rd n fr = [].
Proof.
  intros n fr H. unfold cp_rd. replace (50 <=? n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

(* ================= the parse call run 0x8214c -> 0x8215c ================= *)

(* mv a0,s2 ; mv a1,s4 ; li a2,0 ; jal reac_ctrl_parse, over explicit registers, with the call taken on its
   contract (o = 0) on MemNorm.normalize m; the post comes back to m by evt_normalize (image A's f6_ebc_evt). *)
Lemma c_evt : reac_ctrl_parse_contract ->
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n S FS : Z) (bs : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    asan_cells m -> shadow_rw m ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S) (reac_ctrl_parse_D f n 0) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8215c) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1v
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 f) s3 (Z_to_bv 64 n) s5 s6 s7 s8v s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x8215c) fc None m' (seg_rom rsegs) /\
         munch (c_PW S FS) m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W 0 S)
           (reac_ctrl_parse_D f n 0))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 f) s3 (Z_to_bv 64 n) s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8214c) fc None m (seg_rom rsegs)).
Proof.
  intros HPARSE ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m f n S FS bs Hf Hn HS HS16 HHI HAPP HST HRO Hlen Hbig HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HSKl : 0x5fe000 <= S - REAC_CTRL_PARSE_K) by (unfold HIGHMEM_BEG in HHI; lia).
  pose proof (proj1 (c_stk_iff m (normalize rsegs m) (S - REAC_CTRL_PARSE_K) S REL HSKl ltac:(lia)) HST)
    as HSTn.
  pose proof (mem_inv_normalize rsegs m) as HMIn.
  assert (HRDn : forall i, In i (cp_rd n bs) ->
            mrd rsegs (normalize rsegs m) (wa (f + Z.of_nat i)) = nth_error bs i).
  { intros i Hi. rewrite <- (mrd_rel rsegs m _ _ REL). exact (HRD i Hi). }
  pose proof (c_cells_rel m _ REL HAC) as HACn.
  pose proof (proj1 (c_sw_iff m _ REL) HSW) as HSWn.
  pose proof (proj1 (c_addr_iff m _ _ _ REL) HWA) as HWAn.
  assert (HFAn : 50 <= n -> addressable (normalize rsegs m) f 50)
    by (intros Hb; exact (proj1 (c_addr_iff m _ _ _ REL) (HFA Hb))).
  pose proof (proj1 (c_addr_iff m _ _ _ REL) HBC) as HBCn.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H1) as H1n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H2) as H2n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H3) as H3n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H4) as H4n.
  pose proof (proj1 (bytes_at_rel rsegs m _ _ _ REL) H5) as H5n.
  pose proof (proj1 (c_fp_iff _ m _ _ _ _ _ _ _ REL) HFP) as HFPn.
  assert (HTLSn : reac_ctrl_parse_tls (normalize rsegs m) (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S).
  { intros DT TS C T DB k HT. apply HTLS. exact (proj2 (c_tls_iff m _ _ _ _ _ _ _ _ REL) HT). }
  clear HST HRD HAC HSW HWA HFA HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* 0x8214c mv a0,s2 ; 0x82150 mv a1,s4 ; 0x82154 li a2,0 ; 0x82158 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply LE.evt_cut.
  { eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact HRO |].
    eapply HP with (f := f) (n := n) (o := 0) (S := S) (FS := FS) (fr := bs) (junk := []).
    all: try reflexivity.
    all: try assumption.
    all: try lia.
    all: try (intros Ho; exfalso; apply Ho; reflexivity). }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    E & MU & WM & MI & ST & _ & ACm & SR & AD & FP & _) & HREL & HROs).
  subst s0'.
  destruct HREL as (Er & Ef & Epc & Esvc & Erv & Efc & Erom & Hrel).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in Er, Ef, Epc, Esvc, Erv,
    Efc, Erom, Hrel.
  set (mm' := ms_mem ms') in Hrel, HROs.
  rewrite (c_ms_eta ms' Esvc), Er, Ef, Epc, Erv, Efc, Erom.
  apply LE.evt_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mm'.
  split.
  { replace (ret_pc (Z_to_bv 64 0x8215c)) with (Z_to_bv 64 0x8215c)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  split; [exact (munch_rel rsegs (c_PW S FS) m (normalize rsegs m) mm' m0' REL Hrel HROs MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mm' m0' REL Hrel HROs WM)|].
  split; [exact (ro_agree_same rsegs m mm' HRO HROs)|].
  split; [exact (proj2 (c_stk_iff mm' m0' (S - REAC_CTRL_PARSE_K) S Hrel HSKl ltac:(lia)) ST)|].
  split; [exact (proj2 (c_sw_iff mm' m0' Hrel) SR)|].
  split; [exact (proj2 (c_addr_iff mm' m0' _ _ Hrel) AD)|].
  exact (proj2 (c_fp_iff _ mm' m0' _ _ _ _ _ _ Hrel) FP).
Qed.

(* The lazy-model run of a Lib-engine evt (F8's f8_run_lib). *)
Section Run.
Context {fx : FPState}.

Lemma c_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

End Run.

(* ================= small model and memory facts ================= *)

Lemma c_big : forall inp j, t_len inp j < 50 -> t_big inp j = false.
Proof. intros inp j H. unfold t_big. apply Z.leb_gt. lia. Qed.

Lemma c_sum : forall inp j, t_len inp j < 50 -> t_sum_ok inp j = false.
Proof. intros inp j H. unfold t_sum_ok. rewrite (c_big inp j H). reflexivity. Qed.

Lemma c_8819 : forall inp j, t_len inp j < 50 -> t_8819 inp j = false.
Proof. intros inp j H. unfold t_8819. rewrite (c_big inp j H). reflexivity. Qed.

Lemma c_tfill : forall inp j, t_len inp j < 50 -> t_tfill inp j = false.
Proof. intros inp j H. unfold t_tfill. rewrite (c_big inp j H). reflexivity. Qed.

Lemma c_k0 : forall inp j, t_len inp j < 50 -> t_k inp j = 0.
Proof.
  intros inp j H.
  assert (Hh : cp_hdr (t_len inp j) (t_g inp j) = false).
  { unfold cp_hdr. replace (50 <=? t_len inp j) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  unfold t_k, ctrlparse. rewrite Hh. reflexivity.
Qed.

Lemma c_tlen_nn : forall inp j, 0 <= t_len inp j.
Proof.
  intros inp j. pose proof (fc_range inp j) as R.
  assert (HL : 0 <= f_L inp (fc inp j)).
  { unfold f_L. pose proof (inb_range inp (fc inp j)). pose proof (inb_range inp (fc inp j + 1)).
    destruct (2 <=? f_left inp (fc inp j)); lia. }
  unfold t_len, f_len, f_h, f_left, nlen in *. lia.
Qed.

(* store_ok from a writable window (image A's f6_store_ok). *)
Lemma c_store_ok : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* A carried byte list survives a write that misses it. *)
Lemma c_ba_write : forall m a bs a' bs', bytes_at rsegs m a bs ->
  0 <= a' -> a' + Z.of_nat (length bs') <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> x < a' \/ a' + Z.of_nat (length bs') <= x) ->
  bytes_at rsegs (write_to_mem m (wa a') bs') a bs.
Proof.
  intros m a bs a' bs' H Ha1 Ha2 Hd.
  apply (fl_bytes [(a', a' + Z.of_nat (length bs'))] m _ a bs H).
  - apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia].
  - intros x Hx. cbn [outside]. split; [destruct (Hd x Hx); lia | exact I].
Qed.

(* An address the write set covers lies in one of its ranges (R9's r9_not_out). *)
Lemma c_not_out : forall W x, ~ outside W x -> exists r, In r W /\ fst r <= x < snd r.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exfalso; apply H; exact I|].
  cbn [outside] in H.
  destruct (Z_le_gt_dec lo x) as [H1|H1].
  - destruct (Z_lt_ge_dec x hi) as [H2|H2].
    + exists (lo, hi). split; [left; reflexivity | cbn [fst snd]; lia].
    + assert (HA : ~ (lo <= x < hi)) by lia.
      destruct (IH x ltac:(tauto)) as (r & Hin & Hr). exists r. split; [right; exact Hin | exact Hr].
  - assert (HA : ~ (lo <= x < hi)) by lia.
    destruct (IH x ltac:(tauto)) as (r & Hin & Hr). exists r. split; [right; exact Hin | exact Hr].
Qed.

(* The image's RELRO globals lie in [0x90000, 0x100000) (checked by computation on FrameAPI.v's list, so the proofs
   follow whatever blocks the v1.9.0 FrameAPI.v states). *)
Lemma c_relro_ok : forallb (fun p => (0x90000 <=? fst p) && (fst p + snd p <=? 0x100000)) AF.frame_RELRO = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c_relro_range : forall a, in_globals AF.frame_RELRO a -> 0x90000 <= a < 0x100000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) c_relro_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_true_iff in H as (H1 & H2). apply Z.leb_le in H1, H2. lia.
Qed.

(* ---- local views of the generated allocator laws (v1.9.0 Contract.v, a working branch 48004cf7bfc) ----
   a Theorem Labs lane's rule (15:18Z / 15:32Z): a law's conjunct list is taken apart once per file, here, by a position-free
   proof, and every site of F4-F6 uses these views (F1.v has the same views for F1-F3). *)
Ltac c_conj := repeat (match goal with |- _ /\ _ => split end).

Section Laws.
Context {fx : FPState}.
Variable API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Local Notation AH := (AC.aa_AH AC.ASYMS AsanRTInv.RT API).
Local Notation OWN := (AC.aa_owned AC.ASYMS AsanRTInv.RT API).
Local Notation STKLO := (AC.aa_stklo AC.ASYMS AsanRTInv.RT API).
Local Notation STKHI := (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API).
Local Notation LAWS := (AC.aa_laws AC.ASYMS AsanRTInv.RT API).

(* a_laws_blocks *)
Lemma c_lw_blocks : forall H mem md p n, AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= STKLO mem md /\ end_in_app p n /\
  forall a, p <= a < p + n ->
    app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\ ~ AC.a_on_img_page a /\ ~ AC.a_in_fs AC.ASYMS mem a.
Proof.
  intros H mem md p n HAH Hin.
  pose proof (AC.a_laws_blocks _ _ _ _ _ LAWS H mem md p n HAH Hin) as P. decompose [and] P.
  c_conj; try assumption.
  all: match goal with
       | |- forall x, ?lo <= x < ?hi -> _ =>
           let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
           match goal with Hc : forall y, lo <= y < hi -> _ |- _ => pose proof (Hc a Ha) as Q end;
           decompose [and] Q; c_conj; assumption
       end.
Qed.

(* a_laws_store *)
Lemma c_lw_store : forall H mem mem' md, AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (STKLO mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AH H mem' md /\ (forall a, OWN H mem' md a <-> OWN H mem md a) /\ STKLO mem' md = STKLO mem md /\
  STKHI mem' md = STKHI mem md.
Proof.
  intros H mem mem' md HAH Hk Hw.
  pose proof (AC.a_laws_store _ _ _ _ _ LAWS H mem mem' md HAH Hk Hw) as P. decompose [and] P.
  c_conj; assumption.
Qed.

(* a_laws_fs_place *)
Lemma c_lw_fs_place : forall H mem md b, AH H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b ->
  0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= STKLO mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + AC.FS_SIZE -> app_mem a.
Proof.
  intros H mem md b HAH Hw Hb.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ LAWS H mem md b HAH Hw Hb) as P. decompose [and] P.
  c_conj; assumption.
Qed.

(* a_laws_fs_state, its first part *)
Lemma c_lw_fs_state_ok : forall H mem md FS, AH H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw HFS.
  pose proof (AC.a_laws_fs_state _ _ _ _ _ LAWS H mem md FS HAH Hw HFS) as P. decompose [and] P. assumption.
Qed.

(* a_laws_fs_store *)
Lemma c_lw_fs_store : forall H mem mem' md FS, AH H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (STKLO mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) -> AC.a_fs_ok mem' FS ->
  AH H mem' md /\ (forall a, OWN H mem' md a <-> OWN H mem md a) /\ STKLO mem' md = STKLO mem md /\
  STKHI mem' md = STKHI mem md.
Proof.
  intros H mem mem' md FS HAH Hw HFS Hk Hwr Hok.
  pose proof (AC.a_laws_fs_store _ _ _ _ _ LAWS H mem mem' md FS HAH Hw HFS Hk Hwr Hok) as P. decompose [and] P.
  c_conj; assumption.
Qed.

End Laws.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee of F5 and F6, reac_ctrl_parse (PARSE@0x82158), taken on its lib/B contract
   (lib/B/Prog/reac_ctrl_parse_c.v), never on its code. A normal callee premise, discharged at the top through
   callee_contracts_holds by the v1.9 image-B proof reac_ctrl_parse_holds (lib/B/Prog/reac_ctrl_parse.v, not in this
   delivery). *)
Hypothesis PARSE : reac_ctrl_parse_contract.

(* ================= FRA across a run that may write shadow bytes (R4's r4_fra) ================= *)
(* v1.9.0: the frame is FRAME_BYTES (3136) bytes with FRAME_SHADOW (392) shadow bytes, and the fr reload / selector
   spills are [A + 40, A + 56). *)
Lemma c_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HFSR HIN1' HIN2' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - pose proof (c_relro_range a Hin). lia.
    - pose proof (c_relro_range a Hin). lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [exact (c_rg_move regs regs' _ _ Hr8 E8)|].
  split; [exact (c_rg_move regs regs' _ _ Hr9 E9)|].
  split; [rewrite E3; exact Hr3|].
  split; [exact (c_rg_move regs regs' _ _ Hr19 E19)|].
  split; [exact (c_rg_move regs regs' _ _ Hr26 E26)|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA448|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hfsrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HFSR Hfsrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (c_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. split; [exact HIN1' | exact HIN2'].
Qed.

(* ================= the cells the parse call does not write (image A's f6_PW_outs) ================= *)
Lemma c_PW_outs : forall g fr hb regs mem md S FS,
  FRA B APIf ra g fr hb regs mem md -> AC.aspZ regs = S ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall x, S <= x -> outside (c_PW S FS) x) /\
  (forall x, S <= x < APPMEM_END -> outside (c_PW S FS) (shadow_addr x)) /\
  (forall x, 0 <= x < AC.GT -> outside (c_PW S FS) x /\ outside (c_PW S FS) (shadow_addr x)) /\
  (forall x, fr <= x < fr + FRAME_BYTES -> outside (c_PW S FS) x /\ outside (c_PW S FS) (shadow_addr x)) /\
  (forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (FS <= x < FS + AC.FS_SIZE) -> outside (c_PW S FS) x /\ outside (c_PW S FS) (shadow_addr x)) /\
  (forall x, g_S g - AF.SLOT_STACK <= x < S - REAC_CTRL_PARSE_K ->
     outside (c_PW S FS) x /\ outside (c_PW S FS) (shadow_addr x)).
Proof.
  intros g fr hb regs mem md S FS HFRA HS Htp HFS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  rewrite Haspz in HS. subst S.
  rewrite Haspz in Hapart.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhigh.
  destruct (c_lw_fs_place (APIf rc) _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSm & HFSapp).
  pose proof (HFSfr FS Htp HFS) as HFSfr'.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HKf : FS_SIZE = 11571200) by reflexivity.
  assert (HKF : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HKn : FN_STACK = 1044480) by reflexivity.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(lia)) as Hfrw.
  assert (HspH : HIGHMEM_BEG + 1044480 <= sp) by lia.
  assert (HSK : REAC_CTRL_PARSE_K <= sp) by lia.
  assert (HS8 : sp mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFSm; Z.div_mod_to_equations; lia).
  assert (HWapp : forall a, sp - REAC_CTRL_PARSE_K <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; lia).
  assert (HFSapp' : forall a, FS <= a < FS + FS_SIZE -> app_mem a) by (intros a Ha; apply HFSapp; lia).
  assert (Osh1 : forall x, app_mem x -> (x + 1 <= sp - REAC_CTRL_PARSE_K \/ sp <= x) ->
            (x + 1 <= FS + 1085440 \/ FS + 2134016 <= x) -> outside (c_PW sp FS) (shadow_addr x)).
  { intros x Hx H1 H2.
    pose proof (c_sh_out sp FS x 1 0 HFSapp' HWapp HSK HS8 HFS8 ltac:(lia)
                  ltac:(rewrite Z.add_0_r; exact Hx) H1 H2) as Ho.
    rewrite Z.add_0_r in Ho. exact Ho. }
  split.
  { intros x Hx. rewrite c_PW_eq. cbn [outside].
    assert (Q1 : (FS + 2134016) / 8 <= sp / 8) by (apply Z.div_le_mono; lia).
    assert (Q4 : sp / 8 + ASAN_K <= sp) by (rewrite HKk; clear - HspH HKh; Z.div_mod_to_equations; lia).
    unfold shadow_addr.
    assert (Q2 : (sp - 8800) / 8 <= sp / 8) by (apply Z.div_le_mono; lia).
    repeat split; try exact I; intros HC; lia. }
  split.
  { intros x Hx. apply Osh1; [unfold app_mem; right; lia | right; lia | right; lia]. }
  split.
  { intros x Hx. split.
    - apply (c_out_PW sp FS x HFSapp' HWapp HSK); [unfold app_mem; left; lia | lia | lia | lia | lia].
    - apply Osh1; [unfold app_mem; left; lia | left; lia | left; lia]. }
  split.
  { intros x Hx. split.
    - apply (c_out_PW sp FS x HFSapp' HWapp HSK (Happ x Hx)); lia.
    - apply Osh1; [exact (Happ x Hx) | lia | lia]. }
  split.
  { intros x Hx Hlt Hnf. split.
    - apply (c_out_PW sp FS x HFSapp' HWapp HSK Hx); lia.
    - apply Osh1; [exact Hx | left; lia | lia]. }
  { intros x Hx. split.
    - apply (c_out_PW sp FS x HFSapp' HWapp HSK); [unfold app_mem; right; lia | lia | lia | lia | lia].
    - apply Osh1; [unfold app_mem; right; lia | left; lia | right; lia]. }
Qed.

(* ================= FRA and ENT across the parse call (image A's f6_fra_call) ================= *)
Lemma c_fra_call : forall g fr hb regs regs' mem mem' md md' S FS Wx Dx,
  FRA B APIf ra g fr hb regs mem md -> AC.aspZ regs = S ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  munch (c_PW S FS) mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> shadow_rw mem' ->
  stk rsegs mem' (S - REAC_CTRL_PARSE_K) S ->
  addressable mem' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (S - REAC_CTRL_PARSE_K) S Wx Dx ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ (ENT APIf g hb mem md -> ENT APIf g hb mem' md').
Proof.
  intros g fr hb regs regs' mem mem' md md' S FS Wx Dx HFRA HS Htp HFS MU WM HRO HSW Hstkw HADw HFP
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (c_PW_outs g fr hb regs mem md S FS HFRA HS Htp HFS) as (Ohi & Ohis & Olo & Ofr & Oblk & Owin).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (_ & _ & HFSfr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  rewrite Haspz in HS. subst S.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhigh.
  destruct (c_lw_fs_place (APIf rc) _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSm & HFSapp).
  pose proof (c_lw_fs_state_ok (APIf rc) _ _ _ FS HAH Htp HFS) as Hok.
  pose proof (HFSfr FS Htp HFS) as HFSfr'.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HKf : FS_SIZE = 11571200) by reflexivity.
  assert (HKF : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  assert (HspH : HIGHMEM_BEG + 1044480 <= sp) by lia.
  assert (HSK : REAC_CTRL_PARSE_K <= sp) by lia.
  assert (HS8 : sp mod 8 = 0) by (clear - Hspm; Z.div_mod_to_equations; lia).
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HWapp : forall a, sp - REAC_CTRL_PARSE_K <= a < sp -> app_mem a)
    by (intros a Ha; unfold app_mem; right; lia).
  assert (HFSapp' : forall a, FS <= a < FS + FS_SIZE -> app_mem a) by (intros a Ha; apply HFSapp; lia).
  (* the side-stack cells outside the class-1 ranges are outside the write set *)
  assert (OFS : forall x, FS <= x < FS + FS_SIZE -> ~ (FS + 8 <= x < FS + 16) ->
            ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
            outside (c_PW sp FS) x).
  { intros x Hx G1 G2 G3. apply (c_out_PW sp FS x HFSapp' HWapp HSK (HFSapp' x Hx)); [lia | exact G1 | exact G2 | exact G3]. }
  (* the stores agree with mem off a_store_ok, the FakeStack and its shadow *)
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
    rewrite c_PW_eq. cbn [outside].
    split.
    { intros HC. apply Hns. unfold AC.a_store_ok. right; left. lia. }
    split; [intros HC; apply Hnfs; lia|].
    split; [intros HC; apply Hnfs; lia|].
    split; [intros HC; apply Hnfs; lia|].
    split.
    { intros HC. apply Hnsh. exists (8 * (a - ASAN_K)). split.
      - clear - HC HKk HKF. unfold shadow_addr in HC. Z.div_mod_to_equations. lia.
      - unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    split; [|exact I].
    intros HC. apply Hns. unfold AC.a_store_ok. right; right; right. exists (8 * (a - ASAN_K)). split.
    - unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - right; left. unfold shadow_addr in HC.
      clear - HC Hstklo HS4 HS8 Hspa HAS HAPP HKk HKs HKa HKp. Z.div_mod_to_equations. lia. }
  assert (Hokp : AC.a_fs_ok mem' FS).
  { apply (c_fs_ok mem mem' (AC.as_tp AC.ASYMS) FS (sp - REAC_CTRL_PARSE_K) sp Wx Dx (c_PW sp FS) Hok HFP MU).
    - intros x Hx. apply OFS; lia.
    - intros x Hx. apply OFS; lia.
    - intros x Hx. apply OFS; lia.
    - intros x Hx. apply OFS; lia. }
  assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (c_lw_fs_store (APIf rc) (hb ++ g_H g) mem mem' md FS HAH Htp HFS Hagree Hwm Hokp)
    as (HAH' & Hown & HSTKeq & HSTKhi).
  (* the input block: a live entry block, so app memory below stklo, outside the frame and the side stack *)
  assert (HINo : forall x, g_p g <= x < g_p g + g_n g ->
            outside (c_PW sp FS) x /\ outside (c_PW sp FS) (shadow_addr x)).
  { intros x Hx. destruct (Hinblk ltac:(lia)) as (Hin & _).
    destruct (c_lw_blocks (APIf rc) (hb ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hst2 & _ & Hall).
    destruct (Hall x Hx) as (Happq & _ & _ & _ & Hnfs).
    apply (Oblk x Happq); [lia|].
    intros HC. apply Hnfs. exists FS. split; [exact HFS|]. split; [exact Htp | exact HC]. }
  destruct (fra_in_keep_sh g mem mem' (c_PW sp FS) Hinb Hinblk MU HINo) as (HIN1' & HIN2').
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (c_fra_run g fr hb regs regs' mem mem' md (c_PW sp FS) HFRA MU WM HRO).
    - (* rt_disjoint *)
      rewrite c_PW_eq. unfold shadow_addr.
      unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      assert (D1 : 0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia).
      assert (D2 : 0 <= (sp - 8800) / 8) by (apply Z.div_pos; lia).
      cbn [disjoint_from]. repeat split; first [exact I | left; lia].
    - exact HAH'.
    - exact HSTKeq.
    - intros a Ha. destruct (HSW a Ha) as (_ & b & Hb). exists b. exact Hb.
    - destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
      eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, Z2Nat.id by lia. intros x Hx.
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr)))
        by (rewrite c_sh8; lia).
      exact (proj2 (Ofr (fr + 8 * (x - Sfr fr)) ltac:(lia))).
    - intros x Hx. exact (proj1 (Olo x ltac:(lia))).
    - intros x Hx. exact (proj1 (Ofr x ltac:(lia))).
    - intros x Hx. rewrite HbvA in Hx. apply Ohi. lia.
    - intros x Hx. rewrite HbvA in Hx. apply Ohi. lia.
    - intros x Hx. apply Ohi. lia.
    - (* the entry-anchored window after the call *)
      intros x Hx.
      destruct (Z_lt_le_dec x (sp - REAC_CTRL_PARSE_K)) as [Hl|Hl].
      + left. exact (proj1 (Owin x ltac:(lia))).
      + destruct (Z_lt_le_dec x sp) as [Hl2|Hl2].
        * right. destruct Hstkw as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
        * left. apply Ohi. exact Hl2.
    - (* the registered globals stay addressable: their shadow bytes are not written *)
      intros a Ha.
      assert (Hab : 0 <= a < AC.GT).
      { destruct Ha as (lo & len & Hil & Hr).
        assert (Hok2 : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG = true)
          by (vm_compute; reflexivity).
        pose proof (proj1 (forallb_forall _ _) Hok2 (lo, len) Hil) as Hq. cbn [fst snd] in Hq.
        apply andb_prop in Hq as [Hq1 Hq2]. apply Z.leb_le in Hq1, Hq2. lia. }
      apply (c_addr_keep (c_PW sp FS) mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia. exact (proj2 (Olo a Hab)).
    - (* the slot window outside the frame stays addressable *)
      intros a Ha Hnf.
      destruct (Z_le_gt_dec (sp - REAC_CTRL_PARSE_K) a) as [Hw1|Hw1];
        [destruct (Z_lt_ge_dec a sp) as [Hw2|Hw2]|].
      + replace a with (sp - REAC_CTRL_PARSE_K + (a - (sp - REAC_CTRL_PARSE_K))) by lia.
        apply (addressable_sub mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K); [exact HADw | lia | lia | lia].
      + apply (c_addr_keep (c_PW sp FS) mem mem' a 1 (HWA a Ha Hnf) MU).
        intros i Hi. replace (a + i) with a by lia. exact (Ohis a ltac:(lia)).
      + apply (c_addr_keep (c_PW sp FS) mem mem' a 1 (HWA a Ha Hnf) MU).
        intros i Hi. replace (a + i) with a by lia. exact (proj2 (Owin a ltac:(lia))).
    - (* the FakeStack frame record: its flag byte and slot word are class-6 cells, its tp word in the image *)
      intros (FS' & jj & Htp' & HFS'r & Hj & Hfrj & Hflag & Htail).
      assert (EFS : FS' = FS).
      { apply (fsf_wm_uniq mem (AC.as_tp AC.ASYMS) FS' FS Htp' Htp HFS'r HFS);
          unfold AC.as_tp, AC.ASYMS; cbn; lia. }
      subst FS'.
      assert (HB6 : asan_stack_malloc_c.fs_B 6 = 4096) by reflexivity.
      assert (HM6 : asan_stack_malloc_c.fs_M 6 = 256) by reflexivity.
      assert (Hfl : asan_stack_malloc_c.fs_flag FS 6 jj = FS + 36352 + jj)
        by (unfold asan_stack_malloc_c.fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + jj * 4096)
        by (rewrite Hfrj; unfold asan_stack_malloc_c.fs_frame, asan_stack_malloc_c.fs_B; cbn; lia).
      rewrite HM6 in Hj.
      exists FS, jj.
      split.
      { apply (KindBGlue.kb_word_munch rsegs mem mem' (c_PW sp FS) _ FS Htp MU).
        intros k Hk. split; [unfold AC.as_tp, AC.ASYMS; cbn; lia|].
        apply (proj1 (Olo (AC.as_tp AC.ASYMS + k) ltac:(unfold AC.as_tp, AC.ASYMS; cbn; lia))). }
      split; [exact HFS|].
      split; [rewrite HM6; exact Hj|].
      split; [exact Hfrj|].
      split.
      { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx.
        rewrite Hfl in Hx. apply OFS; lia. }
      { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx.
        rewrite HB6 in Hx. apply OFS; lia. }
    - exact HIN1'.
    - exact HIN2'.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  { apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat. }
  intros HENT.
  eapply ent_mat; [|exact Hmat].
  eapply ent_munch with (W := c_PW sp FS); [exact HENT | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU
    | | exact HSTKeq | exact HSTKhi |].
  - intros x Hk. apply (proj2 (fr_outside_lib _ _)).
    destruct Hk as [Hblk | [Himg | [Habv | [(b & Hor & ->) | (q & k & i & Hin & Hni & Hi & ->)]]]].
    + destruct Hblk as (q & k & i & Hin & Hni & Hi & ->).
      destruct (c_lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
        as (_ & Hq4 & Hend & _ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      exact (proj1 (Oblk (q + i) Happq ltac:(lia)
               ltac:(intro HC; apply Hnfs; exists FS; split; [exact HFS | split; [exact Htp | exact HC]]))).
    + pose proof (img_below_GT x Himg) as Hxg. exact (proj1 (Olo x Hxg)).
    + exact (Ohi x ltac:(lia)).
    + destruct Hor as [Hi|Hr].
      * pose proof (img_below_GT b Hi) as Hbg. exact (proj2 (Olo b Hbg)).
      * exact (Ohis b ltac:(lia)).
    + (* ENT append #1: the shadow of an entry block (app memory below stklo, off the side stack) *)
      destruct (c_lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
        as (_ & Hq4 & Hend & _ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
      exact (proj2 (Oblk (q + i) Happq ltac:(lia)
               ltac:(intro HC; apply Hnfs; exists FS; split; [exact HFS | split; [exact Htp | exact HC]]))).
  - intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ================= FRA and ENT across spill stores (image A's f5_fra_spill) ================= *)
(* A write set W inside the save area [A + 72, A + 336) (the spills below the frame-base spill [A + 336] and
   above the v1.9.0 fr reload / selector spills [A + 40, A + 56)): app memory above stklo and below the entry sp,
   inside the S-anchored slot window, so sl_stk_run moves FRA and ent_store moves ENT. *)
Lemma c_fra_spill : forall g fr hb regs regs' mem mem' md md' Asp W,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 Asp -> 0 <= Asp < 2 ^ 64 ->
  munch W mem mem' -> wmono rsegs mem mem' -> all_app W -> rt_disjoint W ->
  (forall x, ~ outside W x -> Asp + 72 <= x < Asp + 336) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' Asp W HFRA HENT H9 HA MU WM HAW HD HWloc HWIN' Hmat
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HA0e : Asp = A0).
  { apply c_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (HOUT : forall x, (x < Asp + 72 \/ Asp + 336 <= x) -> outside W x).
  { intros x Hx. destruct (c_out_dec W x) as [Ho|Ho]; [exact Ho|]. apply HWloc in Ho. lia. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x,
            (A' + 336 <= x < A' + 344 \/ A' + 40 <= x < A' + 56) -> outside W x).
  { intros A' HA' x Hx. apply HOUT.
    assert (Hm : A' mod 2 ^ 64 = Asp).
    { unfold rg in H9. rewrite HA' in H9. apply (f_equal (@bv_unsigned 64)) in H9.
      rewrite MState.unsigned_lit_wrap, (MState.unsigned_lit Asp) in H9 by lia. exact H9. }
    change (2 ^ 64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. apply HOUT. unfold AC.GT in Hx. lia. }
  assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    destruct (c_out_dec W a) as [Ho|Ho]; [exact Ho|]. apply HWloc in Ho. exfalso. apply Hns.
    unfold AC.a_store_ok. right; left. lia. }
  destruct (c_lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH Hmc Hwrit)
    as (HAH' & Hown & HSTKeq & HSTKhi).
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Hap.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md W
             HFRA MU WM HRO HAW HD HAH' HSTKeq HWIN').
    - intros x Hx. apply HOUT. lia.
    - intros x Hx. apply HOUT. lia.
    - intros A' HA' x Hx. apply (HA9 A' HA'). lia.
    - intros A' HA' x Hx. apply (HA9 A' HA'). lia.
    - intros x Hx. apply HOUT. lia.
    - intros x Hx. apply HOUT. left.
      assert (Hsf : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
        by (unfold Sfr, shadow_addr; rewrite HKk, HKh; unfold APPMEM_END in Hfrhi; Z.div_mod_to_equations; lia).
      lia.
    - intros Hrec. eapply fsrec_stklo; [exact HAH | exact MU | | exact Hrec]. intros x Hx _. apply HOUT. lia.
    - intros x Hx. apply HOUT. destruct (Hinap x Hx) as (_ & Hlt & _). lia.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
  - eapply ent_mat; [| exact Hmat].
    eapply ent_store with (W := W); [exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKhi |].
    + intros x Hx. destruct (c_out_dec W x) as [Ho|Ho]; [left; exact Ho|].
      apply HWloc in Ho. right; left. lia.
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ================= the join cut 0x8214c and the parse call ================= *)

(* The join 0x8214c of F5 (0x82064 j 82148 ; 0x82148 sd a0,248(s1)) and F6 (0x82144 snez a0,a0 ; 0x82148 sd
   a0,248(s1)): Inv_B8215c_at without the parse result (a0 = v, the record word v at fr + 176 and the FLVsp spills)
   and without its explicit KIND_NAME pair (LK's FLI carries it, adopt 11); the call block 0x8214c-0x82158
   produces both.  An internal cut of this unit (F5 and F6 compose through it), not a slot cut.  v1.9.0 against the
   patched image: the join moves from 0x820d8 to 0x8214c, past the shared store [A+248] = 1 - b2z sum_ok (the
   patched image kept that flag in s9). *)
Definition Inv_B8214c_join (g : ghost) (j : nat) (c : config) : Prop :=
  exists phi, CUTST B APIf ra g 0x8214c (hb1 phi (AC.a_size (flen g j)))
    (fun fr regs m =>
       g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
       rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ FM g j phi fr regs m /\ FSj g fr j regs m /\
       spill regs m 248 (1 - b2z (t_sum_ok (g_in g) j)) /\
       (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
       FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m)
    c.

(* FLI's spills that the exit Inv_B8215c_at names (FLVsp's four words and [A+280] = fr + 176), FLI taken apart
   here once for seg_c. *)
Lemma c_fli_flv : forall g fr (regs : bvmap 5 word) (m : word -> option byte),
  FLI g fr regs m ->
  spill regs m 120 (fragb fr + 15) /\ spill regs m 128 (fragb fr + 19) /\ spill regs m 256 (fragb fr + 8) /\
  spill regs m 304 (fr + 272) /\ spill regs m 296 (fr + 304) /\ spill regs m 280 (fr + 176).
Proof.
  intros g fr regs m H. unfold FLI in H. decompose [and] H.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* 0x8214c -> 0x8215c: the three argument moves and the parse call, on the contract (o = 0). *)
Lemma seg_c : forall j, Hat B APIf ra (Inv_B8215c_at B APIf ra) j -> Hat B APIf ra Inv_B8214c_join j.
Proof.
  intros j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hs2 & Hs4 & HFM & HFS &
    H248 & Hrec & HFT & HREC & HFPS & H272).
  subst c. rewrite SEGS.
  pose proof HFM as (H184 & Hs8 & Hs6 & Hs9 & H312).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & HST0).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  rewrite Haspz in Hwlo, HST0.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by reflexivity.
  assert (HKn : FN_STACK = 1044480) by reflexivity.
  assert (HKf : FS_SIZE = 11571200) by reflexivity.
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  (* the live block (phi, a_size len): below stklo, app memory, off the side stack *)
  destruct (c_lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH ltac:(apply in_or_app; left; left; reflexivity))
    as (_ & Hp4096 & Hpstk & _ & Hpall).
  pose proof (c_tlen_nn (g_in g) j) as Hlen0. unfold flen in *.
  assert (Hasz : t_len (g_in g) j <= AC.a_size (t_len (g_in g) j) /\ 1 <= AC.a_size (t_len (g_in g) j))
    by (unfold AC.a_size; lia).
  (* the call's class-1 side-stack package (Tac_fsfree's fra_fp) *)
  destruct (fra_fp B APIf ra g fr (hb1 phi (AC.a_size (t_len (g_in g) j))) regs mem md [1%nat] REAC_CTRL_PARSE_K
              (reac_ctrl_parse_W 0 (AC.aspZ regs)) (reac_ctrl_parse_D phi (t_len (g_in g) j) 0) HFRA)
    as (FS & FPp & TLSp & _ & _).
  { intros cc Hc. cbn [In] in Hc. destruct Hc as [<-|[]]; lia. }
  { lia. }
  { intros w Hw. unfold reac_ctrl_parse_W in Hw. cbn [In Z.eqb] in Hw.
    destruct Hw as [<-|[]]. cbn [fst snd]. left. rewrite Haspz. lia. }
  { intros d Hd. unfold reac_ctrl_parse_D in Hd.
    destruct (t_len (g_in g) j <? 50) eqn:E; cbn [In app Z.eqb] in Hd; [destruct Hd|].
    destruct Hd as [<-|[]]. cbn [fst snd]. right; right. split; [lia|].
    exists phi, (AC.a_size (t_len (g_in g) j)). split; [unfold hb1; cbn [app In]; left; reflexivity|].
    apply Z.ltb_ge in E. lia. }
  pose proof FPp as FPp0.
  destruct FPp0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HTc & HTPw & HPl & _).
  destruct HPl as (HFS0 & HFSmod & HFSgt & HFSapp & HFSstk).
  assert (HFS64 : FS + FS_SIZE <= 2 ^ 64).
  { pose proof (HFSapp (FS + FS_SIZE - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. lia. }
  assert (HFSr : 0 <= FS < 2 ^ 64) by lia.
  assert (EFS : bv_unsigned (Z_to_bv 64 FS) = FS) by (apply MState.unsigned_lit; lia).
  assert (HFSw : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS)
    by (rewrite <- EFS; exact (KindBGlue.bytes_at_le8_word rsegs mem _ (Z_to_bv 64 FS) HTPw)).
  destruct (fra_callee_fp B APIf ra g fr _ regs mem md REAC_CTRL_PARSE_K [1%nat] FS _ _ _ _ HFRA
              ltac:(lia) FPp TLSp ltac:(lia) ltac:(lia))
    as (HWhi & HWtop & HWm16 & HWstk & HWapp & HWaddr & _ & _).
  rewrite Haspz in FPp, TLSp, HWhi, HWtop, HWm16, HWstk, HWapp, HWaddr.
  assert (HTPu : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS)
    by (rewrite Hr4; apply MState.unsigned_lit; unfold AC.as_tp, AC.ASYMS; cbn; lia).
  destruct (c_rt_cells sp mem md HRT) as (HB1 & HB2 & HB3 & HB4 & HB5).
  apply (c_run_lib regs (Z_to_bv 64 0x8214c) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x8215c /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 10 = Z_to_bv 64 (t_k (g_in g) j) /\
       munch (c_PW sp FS) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (sp - REAC_CTRL_PARSE_K) sp /\ shadow_rw mem' /\
       addressable mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
       fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (sp - REAC_CTRL_PARSE_K) sp (reac_ctrl_parse_W 0 sp)
         (reac_ctrl_parse_D phi (t_len (g_in g) j) 0))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { rewrite c_mkR_expand. rewrite Hr2. c_slot Hs2. c_slot Hs4.
      eapply (c_evt PARSE) with (f := phi) (n := t_len (g_in g) j) (S := sp) (FS := FS) (bs := t_g (g_in g) j).
      - lia.
      - lia.
      - lia.
      - exact Hspm.
      - exact HWhi.
      - exact HWtop.
      - exact HWstk.
      - exact Hro.
      - exact (c_tg_len (g_in g) j).
      - intros Hbig. split; [lia|]. split; [lia|]. left. lia.
      - intros i Hi. destruct (Z_lt_le_dec (t_len (g_in g) j) 50) as [Hlt|Hge].
        + rewrite (c_cp_rd_short _ _ Hlt) in Hi. destruct Hi.
        + destruct (Hrec Hge) as (_ & _ & HB3'). pose proof (c_cp_rd_lt _ _ i Hi) as Hilt.
          apply HB3'. rewrite (c_tg_len (g_in g) j). exact Hilt.
      - exact (AsanRTInv.RT_cells sp mem md HRT).
      - exact (AsanRTInv.RT_shadow_rw sp mem md HRT).
      - exact HWaddr.
      - intros Hbig. rewrite <- (Z.add_0_r phi).
        apply (addressable_sub mem phi (AC.a_size (t_len (g_in g) j)) 0 50 (proj2 HHB)); lia.
      - exact (c_bc_addr mem HAG).
      - exact HB1.
      - exact HB2.
      - exact HB3.
      - exact HB4.
      - exact HB5.
      - rewrite HTPu. exact FPp.
      - rewrite HTPu. exact TLSp. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
        E & MU & WM & RO & ST & SR & AD & FPq).
      eexists _, (Z_to_bv 64 0x8215c), m'. split; [exact E|].
      split; [reflexivity|].
      split; [symmetry; exact Hr2|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [symmetry; exact Hs2|].
      split; [reflexivity|]. split; [symmetry; exact Hs4|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|].
      split; [exact SR|]. split; [exact AD|]. rewrite HTPu in FPq; exact FPq. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 & Er23 &
      Er24 & Er25 & Er26 & Er27 & Er10 & MU & WM & RO' & ST' & SR' & AD' & FPq) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (t_k (g_in g) j)) by (rewrite Hreg; exact Er10).
    destruct (c_fra_call g fr _ regs regs' mem mem' md md' sp FS _ _
                HFRA Haspz HFSw HFSr MU WM RO' SR' ST' AD' FPq Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat)
      as (HFRA'' & HENTf).
    pose proof (HENTf HENT) as HENT''.
    destruct (c_PW_outs g fr _ regs mem md sp FS HFRA Haspz HFSw HFSr) as (Ohi & Ohis & Olo & Ofr & Oblk & Owin).
    assert (Oph : forall x, phi <= x < phi + AC.a_size (t_len (g_in g) j) ->
              outside (c_PW sp FS) x /\ outside (c_PW sp FS) (shadow_addr x)).
    { intros x Hx. destruct (Hpall x Hx) as (Happx & _ & _ & _ & Hnfs).
      apply (Oblk x Happx); [lia|].
      intro HCb. apply Hnfs. exists FS. split; [exact HFSr | split; [exact HFSw | exact HCb]]. }
    assert (HA448' : A + 448 <= 2 ^ 64) by lia.
    assert (OA : forall x, A <= x -> outside (c_PW sp FS) x) by (intros x Hx; apply Ohi; lia).
    assert (HLK' : LK g fr j regs' mem').
    { apply (c_lk_keep g fr j A regs regs' mem mem' (c_PW sp FS) HLK Hr9 ltac:(lia) HA448' Fr9 Fr27 MU WM).
      - intros x Hx _ _ _ _. apply OA. lia.
      - exact Ofr.
      - exact Olo. }
    pose proof HLK' as (_ & _ & _ & HFLI').
    destruct (c_fli_mem g fr regs' mem' HFLI') as (_ & _ & _ & _ & (HKNB' & HKNA')).
    pose proof HLK as (_ & _ & _ & HFLI).
    destruct (c_fli_flv g fr regs mem HFLI) as (H120 & H128 & H256 & H304 & H296 & H280).
    assert (Kq : forall off v, 0 <= off <= 336 -> spill regs mem off v -> q64 mem' (A + off) v).
    { intros off v Hoff HS. pose proof (c_spill_q64 regs mem off v A HS Hr9 ltac:(lia) HA448' ltac:(lia)) as Hq.
      apply (c_q64_keep _ mem mem' _ _ Hq MU). intros x Hx. apply OA. lia. }
    assert (Ks : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff HS. apply (c_spill_keep regs regs' A off v mem mem' _ HS Hr9 ltac:(lia) HA448' ltac:(lia)
        Fr9 MU). intros x Hx. apply OA. lia. }
    assert (HFPS' : FPS g fr j mem') by exact (c_fps_keep g fr j _ mem mem' HFPS MU Ofr).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr. unfold flen.
    split; [reflexivity|]. split; [exact HFRA''|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      apply (c_addr_keep _ mem mem' phi _ Hphiad MU). intros i Hi. exact (proj2 (Oph (phi + i) ltac:(lia))). }
    split; [exact HLK'|].
    split; [exact (c_rg_move regs regs' _ _ Hs2 Fr18)|].
    split; [exact (c_rg_move regs regs' _ _ Hs4 Fr20)|].
    split.
    { split; [exact (Ks 184 _ ltac:(lia) H184)|].
      split; [exact (c_rg_move regs regs' _ _ Hs8 Fr24)|].
      split; [exact (c_rg_move regs regs' _ _ Hs6 Fr22)|].
      split; [exact (c_rg_move regs regs' _ _ Hs9 Fr25) | exact (Ks 312 _ ltac:(lia) H312)]. }
    split.
    { apply (c_fsj_keep g fr j regs regs' mem mem' _ HFS MU Ofr). }
    split; [exact HKNB'|].
    split; [exact HKNA'|].
    split; [exact (Ks 248 _ ltac:(lia) H248)|].
    split.
    { intros H50. apply (fl_bytes _ mem mem' phi _ (Hrec H50) MU). rewrite c_tg_len.
      intros x Hx. change (Z.of_nat 50) with 50 in Hx. exact (proj1 (Oph x ltac:(lia))). }
    split.
    { apply (c_fturn_keep g j phi A regs regs' mem mem' _ HFT Hr9 ltac:(lia) HA448' Fr9 MU).
      - intros x Hx. apply OA. lia.
      - intros x Hx. exact (proj1 (Oph x ltac:(lia))). }
    split; [exact (c_rec0_keep g fr j _ mem mem' HREC MU (fun x Hx => proj1 (Ofr x Hx)))|].
    split; [exact HFPS'|].
    split; [unfold F272 in *; exact (Ks 272 _ ltac:(lia) H272)|].
    exists A, (t_k (g_in g) j).
    split.
    { split; [exact (c_rg_move regs regs' _ _ Hr9 Fr9)|].
      split; [exact (Kq 120 _ ltac:(lia) H120)|].
      split; [exact (Kq 128 _ ltac:(lia) H128)|].
      split; [exact (Kq 256 _ ltac:(lia) H256)|].
      split; [exact (Kq 304 _ ltac:(lia) H304) | exact (Kq 296 _ ltac:(lia) H296)]. }
    split; [unfold rg; exact Fr10|].
    split; [exact (c_rg_move regs regs' _ _ Hs8 Fr24)|].
    split; [pose proof (ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)); unfold t_k; lia|].
    split; [exact (Kq 280 _ ltac:(lia) H280)|].
    exact (c_u32_kind g fr j mem' (proj1 HFPS')).
Qed.

(* ================= segment F5: 0x82048 -> 0x8214c, then the call ================= *)

Lemma seg_F5_run : forall j, Hat B APIf ra Inv_B8214c_join j -> Hat B APIf ra (Inv_B82048_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & Hs2 & Hs4 & HFT &
    HLK & H22 & HFS & HREC & HFPS & Ha0 & Hlen).
  subst c. rewrite SEGS.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhigh.
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  unfold flen in Hlen.
  assert (Hk0 : t_k (g_in g) j = 0) by exact (c_k0 (g_in g) j Hlen).
  rewrite Hk0 in Ha0.
  (* the four spill words are byte-backed and writable: they lie inside the S-anchored slot window *)
  assert (HSO : forall m' off, wmono rsegs mem m' -> 0 <= off -> off + 8 <= 448 ->
            store_ok rsegs m' (wa (A + off)) 8 = true).
  { intros m' off HW Ho1 Ho2. apply (c_store_ok mem m' (A + off) 8); [| exact HW | lia | lia].
    intros i Hi. destruct Hwin as (_ & _ & Hs). change (Z.of_nat 8) with 8 in Hi.
    exact (proj1 (Hs (A + off + i) ltac:(lia))). }
  set (m1 := write_to_mem mem (wa (A + 184)) (le8 (Z_to_bv 64 0))).
  set (m2 := write_to_mem m1 (wa (A + 272)) (le8 (Z_to_bv 64 0))).
  set (m3 := write_to_mem m2 (wa (A + 312)) (le8 (Z_to_bv 64 0))).
  set (m4 := write_to_mem m3 (wa (A + 248)) (le8 (Z_to_bv 64 1))).
  apply (c_run_lib regs (Z_to_bv 64 0x82048) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x8214c /\ mem' = m4 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 22 = getr regs 22 /\
       getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 24 = Z_to_bv 64 0 /\ getr R0 25 = Z_to_bv 64 0)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite c_mkR_expand. unfold a0v in Ha0. c_slot Ha0. c_slot Hr9.
    (* 0x82048 bnez a0 : a0 = t_k j = 0, not taken (0x82fa4 is the abort pair) *)
    step. try rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    (* 0x8204c sd zero,184(s1) *)
    pose proof (HSO mem 184 (wmono_refl rsegs mem) ltac:(lia) ltac:(lia)) as HS1.
    step.
    (* 0x82050 sd zero,272(s1) *)
    lazymatch goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (HSO mm 272 ltac:(apply wmono_write; apply wmono_refl) ltac:(lia) ltac:(lia)) as HS2 end.
    step.
    (* 0x82054 sd zero,312(s1) *)
    lazymatch goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (HSO mm 312 ltac:(apply wmono_write; apply wmono_write; apply wmono_refl) ltac:(lia) ltac:(lia))
        as HS3 end.
    step.
    (* 0x82058 li s8,0 ; 0x8205c li s9,0 ; 0x82060 li a0,1 ; 0x82064 j 82148 *)
    step. step. step. step.
    (* 0x82148 sd a0,248(s1) *)
    lazymatch goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (HSO mm 248 ltac:(apply wmono_write; apply wmono_write; apply wmono_write; apply wmono_refl)
                    ltac:(lia) ltac:(lia)) as HS4' end.
    step.
    finish.
    all: try reflexivity.
    all: try (symmetry; exact Hr9).
    all: try (apply bv_eq; vm_compute; reflexivity).
  - intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er22 &
      Er26 & Er27 & Er24 & Er25) Hreg Hmat.
    subst pc' mem'.
    set (W := [(A + 184, A + 192); (A + 272, A + 280); (A + 312, A + 320); (A + 248, A + 256)]).
    assert (MU : munch W mem m4).
    { subst m4 m3 m2 m1 W.
      apply munch_write;
        [apply munch_write;
           [apply munch_write;
              [apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia
                 | rewrite length_le8; cbn [inside]; left; lia]
              | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]
           | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; right; left; lia]
        | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; right; right; left; lia]. }
    assert (WM : wmono rsegs mem m4)
      by (subst m4 m3 m2 m1; apply wmono_write; apply wmono_write; apply wmono_write; apply wmono_write;
          apply wmono_refl).
    assert (HWIN' : stk rsegs m4 (g_S g - AF.SLOT_STACK) (g_S g)).
    { subst m4 m3 m2 m1.
      apply stk_write; [apply stk_write; [apply stk_write; [apply stk_write; [exact Hwin | lia
        | rewrite length_le8; lia] | lia | rewrite length_le8; lia] | lia | rewrite length_le8; lia]
        | lia | rewrite length_le8; lia]. }
    assert (HAW : all_app W).
    { subst W. cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
    assert (HD : rt_disjoint W).
    { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [exact I | left; lia]. }
    assert (HWloc : forall x, ~ outside W x -> A + 72 <= x < A + 336).
    { intros x Hx. destruct (c_not_out W x Hx) as (r & Hin & Hr). subst W. cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia. }
    assert (OW : forall x, ~ (A + 184 <= x < A + 192) -> ~ (A + 272 <= x < A + 280) ->
              ~ (A + 312 <= x < A + 320) -> ~ (A + 248 <= x < A + 256) -> outside W x).
    { intros x H1 H2 H3 H4. subst W. cbn [outside]. repeat split; assumption. }
    assert (OWlo : forall x, x < A + 184 -> outside W x /\ outside W (shadow_addr x)).
    { intros x Hx. split; [apply OW; lia|].
      destruct (Z_lt_le_dec x 0) as [Hn|Hp].
      - apply OW; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
      - assert (Hsx : shadow_addr x <= x / 8 + ASAN_K) by (unfold shadow_addr; lia).
        assert (Hx8 : x / 8 <= A / 8 + 34) by (Z.div_mod_to_equations; lia).
        assert (HA8 : A / 8 + ASAN_K + 34 < A) by (unfold ASAN_K; Z.div_mod_to_equations; lia).
        apply OW; lia. }
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr24 : getr regs' 24 = Z_to_bv 64 0) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = Z_to_bv 64 0) by (rewrite Hreg; exact Er25).
    destruct (c_fra_spill g fr _ regs regs' mem m4 md md' A W HFRA HENT Hr9 HA64 MU WM HAW HD HWloc HWIN' Hmat
                Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26) as (HFRA'' & HENT'').
    (* the four stored words (each later store is at another word) *)
    assert (Q248 : q64 m4 (A + 248) 1).
    { subst m4. unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (Q312 : q64 m4 (A + 312) 0).
    { subst m4. unfold q64. apply c_ba_write; [| lia | rewrite length_le8; lia | rewrite !length_le8; intros x Hx; lia].
      subst m3. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (Q272 : q64 m4 (A + 272) 0).
    { subst m4. unfold q64. apply c_ba_write; [| lia | rewrite length_le8; lia | rewrite !length_le8; intros x Hx; lia].
      subst m3. apply c_ba_write; [| lia | rewrite length_le8; lia | rewrite !length_le8; intros x Hx; lia].
      subst m2. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (Q184 : q64 m4 (A + 184) 0).
    { subst m4. unfold q64. apply c_ba_write; [| lia | rewrite length_le8; lia | rewrite !length_le8; intros x Hx; lia].
      subst m3. apply c_ba_write; [| lia | rewrite length_le8; lia | rewrite !length_le8; intros x Hx; lia].
      subst m2. apply c_ba_write; [| lia | rewrite length_le8; lia | rewrite !length_le8; intros x Hx; lia].
      subst m1. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (HA448' : A + 448 <= 2 ^ 64) by lia.
    assert (H9' : rg regs' 9 A) by exact (c_rg_move regs regs' _ _ Hr9 Fr9).
    (* the live block and the frame lie below A *)
    destruct (c_lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
                (AC.a_size (flen g j)) HAH ltac:(apply in_or_app; left; left; reflexivity))
      as (_ & Hp4096 & Hpstk & _ & Hpall).
    pose proof (c_tlen_nn (g_in g) j) as Hlen0. unfold flen in *.
    assert (Hasz : t_len (g_in g) j <= AC.a_size (t_len (g_in g) j)) by (unfold AC.a_size; lia).
    assert (Ofr : forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x))
      by (intros x Hx; apply OWlo; lia).
    assert (Olo : forall x, 0 <= x < AC.GT -> outside W x /\ outside W (shadow_addr x))
      by (intros x Hx; apply OWlo; lia).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', m4, md', fr. unfold flen.
    split; [reflexivity|]. split; [exact HFRA''|]. split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      apply (c_addr_keep W mem m4 phi _ Hphiad MU). intros i Hi. apply OWlo. lia. }
    split.
    { apply (c_lk_keep g fr j A regs regs' mem m4 W HLK Hr9 ltac:(lia) HA448' Fr9 Fr27 MU WM).
      - intros x _ H1 H2 H3 H4. exact (OW x H1 H3 H4 H2).
      - exact Ofr.
      - exact Olo. }
    split; [exact (c_rg_move regs regs' _ _ Hs2 Fr18)|].
    split; [exact (c_rg_move regs regs' _ _ Hs4 Fr20)|].
    split.
    { (* FM: [A+184] = b2z tfill = 0, s8 = t_k = 0, s6 = 1, s9 = b2z sum_ok = 0, [A+312] = 0 (t_big false) *)
      unfold FM. rewrite (c_tfill (g_in g) j Hlen), Hk0, (c_sum (g_in g) j Hlen), (c_big (g_in g) j Hlen).
      split; [exists A; split; [exact H9' | exact Q184]|].
      split; [unfold rg; exact Fr24|].
      split; [exact (c_rg_move regs regs' _ _ H22 Fr22)|].
      split; [unfold rg; exact Fr25 | exists A; split; [exact H9' | exact Q312]]. }
    split; [exact (c_fsj_keep g fr j regs regs' mem m4 W HFS MU Ofr)|].
    split.
    { (* [A+248] = 1 - b2z sum_ok = 1 *)
      rewrite (c_sum (g_in g) j Hlen). exists A. split; [exact H9' | exact Q248]. }
    split; [intros H50; lia|].
    split.
    { apply (c_fturn_keep g j phi A regs regs' mem m4 W HFT Hr9 ltac:(lia) HA448' Fr9 MU).
      - intros x Hx. apply OW; lia.
      - intros x Hx. apply OWlo. lia. }
    split; [exact (c_rec0_keep g fr j W mem m4 HREC MU (fun x Hx => proj1 (Ofr x Hx)))|].
    split; [exact (c_fps_keep g fr j W mem m4 HFPS MU Ofr)|].
    unfold F272. rewrite (c_8819 (g_in g) j Hlen). exists A. split; [exact H9' | exact Q272].
Qed.

(* seg_F5 (S_F5): the short-frame run to the join, then the parse call block. *)
Lemma seg_F5 : forall j : nat,
  Hat B APIf ra (Inv_B8215c_at B APIf ra) j -> Hat B APIf ra (Inv_B82048_at B APIf ra) j.
Proof. intros j Hexit. exact (seg_F5_run j (seg_c j Hexit)). Qed.

End S.
