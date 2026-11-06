(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_add (op 0) of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput over the
   GENERIC allocator relation ARx: the ARx conversion of lib/A/W_LLVMFuzzerTestOneInput_add.v's lf_arm_add (Qed on
   a working branch 44de651f71b), in the form of W1Verify's converted check_bounded (a working branch,
   lib/A/W_check_bounded.v).  lf_arm_add_x's statement is the text of the Section hypothesis ARM_add of
   lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section w (:302), checked at the end (lf_arm_add_x_check, and
   lf_arm_add_x_cut_x, which feeds it to cut_x's own lf_arm_x).
   The arm and the proof are _add.v's (see its header): one run to op_add's entry, op_add through W2's oa_spec_g_x
   (lib/A/W_op_add.v:2936) at op_add's OWN globals ad_G, its journal lifted to G_fr and composed into the cut's, one
   run to the latch.  The conversion: AR -> ARx with the ghost lists (Hpe at the entry, Hp3 at the cut, Hp' after the
   call), al_* -> alx_*, the journal lemmas -> W_journal_x / YCbqG / W_frame_x's _x twins, op_add's keep lemmas ->
   W_op_add.v's _x ones (oa_call_keep takes HPST), paj_run_to_tok -> paj_run_to_tok_x.
   NOT CITED, RESTATED: _add.v no longer compiles after the merge of a working branch b87fa52d984 (W2's W_op_add.v
   keeps only the _x oa_call_keep / _blk / _hi), so this file does not Require it.  Its AR-free helpers (ad_set_nth ..
   ad_none_nwr, Section kit's ad_wr_offimg .. ad_aout_rebuild, ad_at_op / ad_none / ad_open and their lemmas,
   ad_romb, ae_* / ar_*, ad_awr / ad_nowr / ad_meq) are restated here with IDENTICAL names, statements and proofs
   (W8Entry-2's ruling).  The AR-stated helpers of _add.v and of _latch.v (which this file does Require, for its
   AR-free lemmas) are restated over ARx with the suffix _x: lt_blk_x .. lt_ainput_kept_x, ad_nodup_x, ad_fp_avoid_x,
   ad_call_keep_frm_x, lt_afn_pre_at_x, ad_gxp_x, ad_carry_x, ad_flag_kept_x.
   Section hypotheses beyond cut_x's Section w header (B .. RINV, verbatim):
     OA     - op_add: oa_spec_g_x exactly as W_op_add.v:2936 defines it, at PI := PB_fr, the walk's PST / ARx;
     HEV / HZS / HGOBJ / ROMPIN - _add.v's instance facts, verbatim;
     ERRL   - cut_x's errno_law_x (the _x form of _add.v's ERRL : errno_law B);
     GSHV   - _add.v's GSHV over ARx (gx_prog_x's last conjunct at ad_G);
     HPST   - the image is off PST (W_op_add.v Section x's HPST text; oa_call_keep's premise; trivial at PST = []);
     BLKN   - a live block's size is non-negative (W_kit_x.v Section g's BLKN text, the generic counterpart of the
              size bound of AR's al_blocks, which AR_laws_x's alx_blocks does not carry; the cf instance has it as
              AR_blocks_law_cf's last conjunct);
     RI_add_* / LS_add_* - _add.v's model rules, verbatim (_cut's LS is cut_x's LSx).
   The fake frame's bytes are off the image by YCbqG.frm_img_x (alx_client_img), not by W_frame_x's frm_off_imgP_x, so
   no IMGC hypothesis is taken.
   ROUTE R (a Theorem Labs lane, 2026-10-31; RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the nested Section addR at the end states lf_arm_add_xR, the
   text of cut_x's Section wR hypothesis ARM_add_R (:456), over R R_refl R_trans WLE_R and op_add at R (OA_R :=
   oa_spec_g_xR, W_op_add.v) in place of OA; its proof is lf_arm_add_x's over the R journal (see the Section's
   comment).  ad_call_keep_frm_x / lt_afn_pre_at_x are their _xR twins (R implicit) at wle. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the arm's addresses (offsets from fr_B0) *)
Definition A_ad_ret : Z := AF_arm_add + 12.        (* 0x8442c  j 0x84490 *)
Definition AD_N : Z := 144.                        (* the in.n cell F+144 *)

(* ------------------------------------------------------------------ list and range helpers *)
Fixpoint ad_set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: l' => x :: l'
  | S n', y :: l' => y :: ad_set_nth n' x l'
  | _, [] => []
  end.
Lemma ad_set_nth_length : forall (A : Type) n (x : A) l, length (ad_set_nth n x l) = length l.
Proof.
  intros A n x l. revert n. induction l as [|y l IH]; intros [|n]; cbn [ad_set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma ad_set_nth_same : forall (A : Type) n (x : A) l d, (n < length l)%nat -> nth n (ad_set_nth n x l) d = x.
Proof.
  intros A n x l d. revert n. induction l as [|y l IH]; intros [|n] Hn; cbn [ad_set_nth length nth] in *;
    try lia; [reflexivity | apply IH; lia].
Qed.
Lemma ad_set_nth_other : forall (A : Type) n p (x : A) l d, n <> p -> nth p (ad_set_nth n x l) d = nth p l d.
Proof.
  intros A n. induction n as [|n IH]; intros [|p] x l d Hnp; destruct l as [|y l];
    cbn [ad_set_nth nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.
Lemma ad_nd_app : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros A l1. induction l1 as [|y l1 IH]; intros l2 x Hnd Hx Hx2; [destruct Hx|].
  cbn [app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct Hx as [<- | Hx]; [apply Hni; apply in_or_app; right; exact Hx2 | exact (IH l2 x Hnd' Hx Hx2)].
Qed.
Lemma ad_nd_appr : forall (A : Type) (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  intros A l1. induction l1 as [|y l1 IH]; intros l2 Hnd; [exact Hnd|].
  cbn [app] in Hnd. apply NoDup_cons_iff in Hnd as [_ Hnd]. exact (IH l2 Hnd).
Qed.
(* no range of G meets [lo, lo + n) *)
Definition ad_apart (lo n : Z) (G : list (Z * Z)) : bool :=
  forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) G.
Lemma ad_apart_ok : forall lo n G, ad_apart lo n G = true -> forall a, inG G a -> ~ (lo <= a < lo + n).
Proof.
  intros lo n G H a Ha Hr. unfold ad_apart in H. rewrite forallb_forall in H.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hin & Hz). specialize (H r Hin).
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; unfold in_zr in Hz; lia.
Qed.
(* every range of G1 lies inside one of G2 *)
Lemma ad_sub_of_b : forall G1 G2, forallb (fun r => rng_inb (fst r) (snd r) G2) G1 = true ->
  forall a, inG G1 a -> inG G2 a.
Proof.
  intros G1 G2 H a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in H. destruct r as [lo n]. exact (rng_cover_zr lo n G2 (H _ Hr) a Hz).
Qed.
Lemma ad_inG_rng : forall G lo n a, In (lo, n) G -> lo <= a < lo + n -> inG G a.
Proof. intros G lo n a Hin Ha. unfold inG. apply Exists_exists. exists (lo, n). split; [exact Hin | exact Ha]. Qed.

(* ------------------------------------------------------------------ op_add's globals *)
(* op_add's own G (the brief's ruling; W_op_add.v's comment at oa_spec): g_s, g_nfd and relay_add's RA_G *)
Definition ad_G : list (Z * Z) := [(rg_s fr_globals, 4 * ASRC); (A_NFD, 4)] ++ RA_G fr_globals.
Lemma ad_G_eq : ad_G = [(0x5d88e0, 384); (0x5d8820, 4); (0x5d8ac0, 12); (0x5d87a0, 4); (0x5d8800, 4); (0x5d87c0, 8)].
Proof. reflexivity. Qed.
Lemma ad_G_obj : forall a, inG ad_G a -> inG G_fr_obj a.
Proof. apply ad_sub_of_b. vm_compute. reflexivity. Qed.
(* the globals of the output flags that aout_at reads, but errno *)
Definition ad_aout_glob : list (Z * Z) :=
  [(rg_send_max fr_globals, 8); (rg_nout fr_globals, 8); (rg_capout fr_globals, 8); (rg_out fr_globals, 8);
   (rg_client fr_globals, 4); (rg_client_broken fr_globals, 1); (rg_send_dead fr_globals, 1);
   (rg_send_eintr fr_globals, 1)].
(* the other globals amodel_at reads: g_gone, g_wake[1], g_thread_up, g_listen *)
Definition ad_misc_glob : list (Z * Z) :=
  [(rg_gone fr_globals, 1); (rg_wake fr_globals + 4, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)].
Ltac ad_in := cbv [In ad_aout_glob ad_misc_glob ad_G app RA_G]; repeat (first [left; reflexivity | right]).
(* a concrete register is callee-saved *)
Ltac ad_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Lemma ad_keep_obj : forall a, inG (ad_aout_glob ++ ad_misc_glob) a -> inG G_fr_obj a /\ ~ inG ad_G a.
Proof.
  intros a Ha. split.
  - revert a Ha. apply ad_sub_of_b. vm_compute. reflexivity.
  - intros HG. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
    assert (Hb : forallb (fun r => ad_apart (fst r) (snd r) ad_G) (ad_aout_glob ++ ad_misc_glob) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. exact (ad_apart_ok _ _ _ (Hb r Hr) a HG Hz).
Qed.

(* ------------------------------------------------------------------ the model after the operation *)
Definition ad_os (hs : list (option hsrc)) : list Z :=
  map (fun o : option hsrc => match o with Some _ => 1 | None => 0 end) hs.
Lemma ad_os_nth : forall hs i, nth i (ad_os hs) 0 = match nth i hs None with Some _ => 1 | None => 0 end.
Proof.
  unfold ad_os. intros hs i. revert hs. induction i as [|i IH]; intros [|o hs]; cbn [map nth];
    try reflexivity; apply IH.
Qed.
Lemma ad_first_lt : forall os i, oa_first os = Some i -> (i < 4)%nat.
Proof.
  intros os i H. unfold oa_first in H.
  repeat match type of H with context [if ?c then _ else _] => destruct c end;
    first [injection H as <-; lia | discriminate H].
Qed.
Lemma ad_first_zero : forall os i, oa_first os = Some i -> nth i os 0 = 0.
Proof.
  intros os i H. unfold oa_first in H.
  destruct (nth 0 os 0 =? 0) eqn:E0; [injection H as <-; apply Z.eqb_eq; exact E0|].
  destruct (nth 1 os 0 =? 0) eqn:E1; [injection H as <-; apply Z.eqb_eq; exact E1|].
  destruct (nth 2 os 0 =? 0) eqn:E2; [injection H as <-; apply Z.eqb_eq; exact E2|].
  destruct (nth 3 os 0 =? 0) eqn:E3; [injection H as <-; apply Z.eqb_eq; exact E3 | discriminate H].
Qed.
(* errno's value in the output flags after a call that may set it *)
Definition ad_set_ev (c : ctl) (v : Z) : ctl := CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) v.
Lemma ad_set_ev_same : forall c, ad_set_ev c (ct_ev c) = c.
Proof. intros [a b c d e]. reflexivity. Qed.
(* the bytes slot i of g_s stays outside what op_add writes when slot j <> i is the one it opens *)
Lemma ad_slot_nwr : forall os i j a, oa_first os = Some i -> j <> i -> (j < 4)%nat ->
  rg_s fr_globals + ASRC * Z.of_nat j <= a < rg_s fr_globals + ASRC * Z.of_nat j + ASRC -> ~ oa_wr os a.
Proof.
  intros os i j a Hf Hji Hj Ha. pose proof (ad_first_lt os i Hf) as Hi. unfold oa_wr. rewrite Hf.
  unfold oa_HA, A_NFD, ASRC in *. cbn [fr_globals rg_s] in *.
  intros [Hs | [Hn | Hr]]; [nia | lia|].
  unfold RA_G in Hr. cbn [fr_globals rg_lock rg_nsrc rg_capsrc rg_src] in Hr.
  repeat (apply inG_cons in Hr as [Hr | Hr]; [unfold in_zr in Hr; cbn [fst snd] in Hr; lia|]).
  exact (inG_nil a Hr).
Qed.
(* g_s and the other program globals are none of op_add's writes when no slot is free *)
Lemma ad_none_nwr : forall os a, oa_first os = None -> ~ oa_wr os a.
Proof. intros os a Hf. unfold oa_wr. rewrite Hf. tauto. Qed.

Section kit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.

(* off the image, a byte that is writable is present, so its view carries its writability *)
Lemma ad_wr_offimg : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> writable_at segs (mrestrict H m) a -> apresent H m a.
Proof.
  intros H m a Ha Hni Hw.
  assert (Hseg : wview segs (fun _ => None) (Z_to_bv 64 a) = None).
  { unfold wview. cbv beta iota.
    destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Ef; [|reflexivity].
    exfalso. apply Hni. exists seg. pose proof (find_segment_in _ _ _ _ Ef) as Hin.
    pose proof (find_segment_range _ _ _ _ Ef) as Hr. rewrite unsigned_lit_small in Hr by lia.
    split; [exact Hin | lia]. }
  unfold writable_at, mrestrict in Hw. unfold apresent.
  destruct (H (Z_to_bv 64 a)) eqn:Eh.
  - exfalso. apply Hw. unfold wview in Hseg |- *. rewrite ?Eh. exact Hseg.
  - destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [split; [reflexivity | exists b; reflexivity]|].
    exfalso. apply Hw. unfold wview in Hseg |- *. rewrite ?Eh, ?Em. exact Hseg.
Qed.
Lemma ad_offimg_kept : forall (W W' : world segs) mem mem' a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a ->
  abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Ha Hni Hv. split; [exact Hv|]. intros Hw.
  apply apresent_writable. apply (apresent_transfer segs (w_H W) (w_H W') mem mem' a Ha Hni Hv).
  exact (ad_wr_offimg (w_H W) mem a Ha Hni Hw).
Qed.
Lemma ad_sv8_view : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8, arm in *.
  apply (val_mem_moved segs (w_H W) (w_H W') mem mem' a a 8 v); [|exact Hv].
  intros j Hj. apply HK. cbn in Hj. lia.
Qed.
Lemma ad_vm_view : forall (W W' : world segs) mem mem' a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HK Hv. unfold arm in *.
  apply (val_mem_moved segs (w_H W) (w_H W') mem mem' a a n v); [|exact Hv].
  intros j Hj. apply HK. lia.
Qed.
(* the frame and the fake frame, across a stretch that keeps the frame's view (but the in.n cell), its
   writability, and the fake frame's bytes *)
Lemma ad_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, lf_F cx <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W' mem') a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  0 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    HV HW HKF HKS HF0 HF1 HF2.
  unfold AD_N in HV.
  assert (KV : forall a v, lf_F cx <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lf_F cx + 144 \/ lf_F cx + 152 <= a) ->
             sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 Hv. apply (ad_sv8_view W W' mem mem'); [|exact Hv]. intros x Hx. apply HV; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [intros i Hi; apply HW; lia|].
  do 9 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | lia | assumption]|]).
    apply KV; [lia | lia | lia | assumption]. }
  do 3 (split; [apply (lt_sv8_kept W W' mem mem'); [intros x Hx; apply HKF; lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply HKF; lia | exact A16]|].
  split; [|apply (akept_awr W mem); [intros x Hx; apply HKS; lia | exact (proj2 A17)]].
  apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply HKS. lia.
Qed.
(* what a list's / a source's footprint is made of: its global head, or the bytes of one of its blocks *)
Lemma ad_alist_cov : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines ->
  forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  (LA <= a < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= a < fst b + snd b.
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) r Hr a Ha.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
    destruct Hr as [<- | []]. right. exists (hl_v l, AREC * hl_cap l).
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    split.
    + unfold alist_blks. apply in_or_app. left.
      destruct (Z.eqb_spec (hl_cap l) 0); [lia | left; reflexivity].
    + cbn [gfp fst snd] in Ha |- *. rewrite lt_bzs_len, length_app, lt_concat_len in Ha.
      unfold hl_n in *. unfold AREC in *. lia.
  - apply in_map_iff in Hr as (x & <- & Hx). right. exists (fst x, Z.of_nat (length (snd x)) + 1). split.
    + unfold alist_blks. apply in_or_app. right.
      apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx.
    + cbn [gfp fst snd] in Ha |- *. rewrite lt_bzs_len, length_app in Ha. cbn [length] in Ha. lia.
Qed.
Lemma ad_asrc_cov : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h ->
  forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r ->
  (HA <= a < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= a < fst b + snd b.
Proof.
  intros ly S W mem HA h HS r Hr a Ha.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  - left. cbn [fst snd] in Ha. exact Ha.
  - right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|].
    cbn [gfp fst snd] in Ha |- *. rewrite lt_bzs_len, Hpj in Ha. exact Ha.
  - apply in_app_or in Hr as [Hr | Hr].
    { destruct (ad_alist_cov ly S W mem (HA + 16) _ _ Hpend r Hr a Ha) as [Hs | (b & Hb & Hab)];
        [left; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; left; exact Hb | exact Hab]. }
    apply in_app_or in Hr as [Hr | Hr].
    { destruct (ad_alist_cov ly S W mem (HA + 64) _ _ Hexp r Hr a Ha) as [Hs | (b & Hb & Hab)];
        [left; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hab]. }
    { destruct (ad_alist_cov ly S W mem (HA + 80) _ _ Hheld r Hr a Ha) as [Hs | (b & Hb & Hab)];
        [left; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hab]. }
Qed.
(* one slot of g_s, across a stretch that keeps the slot's 96 bytes and its blocks (live, bytes kept) *)
Lemma ad_slot_kept : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' j o,
  aslot B ly S W mem j o ->
  (forall a, rg_s fr_RG + ASRC * Z.of_nat j <= a < rg_s fr_RG + ASRC * Z.of_nat j + ASRC -> abyte_kept W mem W' mem' a) ->
  (forall b, In b (slot_blks o) -> In b (ablocks B ly' S') /\
     (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  aslot B ly' S' W' mem' j o.
Proof.
  intros ly S W mem ly' S' W' mem' j o HS KS KB. unfold aslot in *. destruct o as [h|].
  - cbn [slot_blks] in KB. apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ h HS).
    + intros r Hr a Ha. destruct (ad_asrc_cov ly S W mem _ h HS r Hr a Ha) as [Hs | (b & Hb & Hab)].
      * exact (KS a Hs).
      * exact (proj2 (KB b Hb) a Hab).
    + intros b Hb. exact (proj1 (KB b Hb)).
  - destruct HS as [G1 G2]. split.
    + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx. apply KS. unfold ASRC in *. lia.
    + apply (akept_awr W mem); [|exact G2]. intros x Hx. apply KS. lia.
Qed.
(* the output flags, across a stretch that keeps their globals and buffer; errno takes the value v *)
Lemma ad_aout_rebuild : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' c O mx no cap out v,
  aout_at B fr_globals ly S W mem c O mx no cap out ->
  (forall a, inG ad_aout_glob a -> abyte_kept W mem W' mem' a) ->
  (cap <> 0 -> In (out, cap) (ablocks B ly' S') /\ forall a, out <= a < out + cap -> abyte_kept W mem W' mem' a) ->
  val_mem segs (arm W' mem') (as_errno B) 4 v -> awr W' mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
  aout_at B fr_globals ly' S' W' mem' (ad_set_ev c v) O mx no cap out.
Proof.
  intros ly S W mem ly' S' W' mem' c O mx no cap out v
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) KG KB Hev Hew Hv.
  assert (KC : forall lo n, In (lo, n) ad_aout_glob -> forall x, lo <= x < lo + n -> abyte_kept W mem W' mem' x)
    by (intros lo n Hin x Hx; apply KG; exact (ad_inG_rng _ lo n x Hin Hx)).
  assert (KV : forall lo n (w : nat) z, In (lo, n) ad_aout_glob -> Z.of_nat w <= n ->
      val_mem segs (arm W mem) lo w z -> val_mem segs (arm W' mem') lo w z)
    by (intros lo n w z Hin Hw Hz; apply (akept_vm W mem); [intros x Hx; apply (KC lo n Hin); lia | exact Hz]).
  assert (KA : forall lo n, In (lo, n) ad_aout_glob -> awr W mem lo n -> awr W' mem' lo n)
    by (intros lo n Hin Hw; apply (akept_awr W mem); [exact (KC lo n Hin) | exact Hw]).
  unfold ad_set_ev. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (KV _ 8); [ad_in | cbn; lia | exact H1]|]. split; [apply KA; [ad_in | exact H2]|].
  split; [apply (KV _ 8); [ad_in | cbn; lia | exact H3]|]. split; [apply KA; [ad_in | exact H4]|].
  split; [apply (KV _ 8); [ad_in | cbn; lia | exact H5]|]. split; [apply KA; [ad_in | exact H6]|].
  split; [apply (KV _ 8); [ad_in | cbn; lia | exact H7]|]. split; [apply KA; [ad_in | exact H8]|].
  split; [apply (KV _ 4); [ad_in | cbn; lia | exact H9]|]. split; [apply KA; [ad_in | exact H10]|].
  split; [apply (KV _ 1); [ad_in | cbn; lia | exact H11]|]. split; [apply KA; [ad_in | exact H12]|].
  split; [apply (KV _ 1); [ad_in | cbn; lia | exact H13]|]. split; [apply KA; [ad_in | exact H14]|].
  split; [apply (KV _ 1); [ad_in | cbn; lia | exact H15]|]. split; [apply KA; [ad_in | exact H16]|].
  split; [exact Hev|]. split; [exact Hew|]. split; [exact Hv|].
  do 6 (split; [assumption|]).
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  destruct (KB ltac:(lia)) as [Hin' KO].
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin'|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx. apply KO. lia.
Qed.
End kit.

(* ------------------------------------------------------------------ the AR-stated helpers, over ARx *)
(* _latch.v's Section kit lemmas lt_blk .. lt_aout and Section w lemmas lt_amodel_kept / lt_ainput_kept, and _add.v's
   Section kit lemmas ad_nodup / ad_fp_avoid: the same texts over ARx (the ghost list Hp after S), al_* -> alx_*, the
   size bound of a block from BLKN *)
Section kitx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* _latch.v:60 lt_low, a Section-local Ltac of that file (dropped at its End kit), restated *)
Ltac lt_low :=
  cbn [fst snd gfp]; unfold CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lt_ceil_lo; lia.
(* _latch.v:83 lt_blk *)
Lemma lt_blk_x : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S Hp W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _).
  pose proof (BLKN ly S Hp W mem md p n HAR Hin) as H3.
  pose proof (req_size_pos n H3) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
(* ---- struct list ---- *)
Lemma lt_alist_x : forall ly S Hp (W : world segs) mem md LA l lines,
  ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= CEIL8 ->
  lt_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lt_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lt_blk_x ly S Hp W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; lia|]. apply lt_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
    cbn [gfp fst snd]. rewrite lt_bzs_len, length_app, lt_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
Lemma lt_asrc_x : forall ly S Hp (W : world segs) mem md HA h,
  ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= CEIL8 ->
  lt_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lt_alist_x ly S Hp W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lt_alist_x ly S Hp W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lt_alist_x ly S Hp W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply lt_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite lt_bzs_len, Hpj. unfold APARTIAL, CEIL8 in *. lia.
    + apply lt_fp_low_app; [exact A1|]. apply lt_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
Lemma lt_aentry_x : forall ly S Hp (W : world segs) mem md e,
  ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  lt_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lt_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                                (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                                                   Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (lt_blk_x ly S Hp W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lt_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
      cbn [gfp snd]. rewrite lt_bzs_len, length_app. unfold CEIL8 in *. lia.
    + apply lt_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lt_bzs_len, lt_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold CEIL8. pose proof lt_ceil_lo. lia. }
        destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan's globals ---- *)
Lemma lt_arelay_x : forall ly S Hp (W : world segs) mem md G es,
  ARx ly S Hp W mem md -> arelay_at B fr_globals ly S W mem G es ->
  lt_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : lt_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry_x ly S Hp W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lt_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry_x ly S Hp W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
Lemma lt_aout_x : forall ly S Hp (W : world segs) mem md c O mx no cap out,
  ARx ly S Hp W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  lt_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lt_fp_low_cons; [lt_low | lt_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | cbn; unfold CEIL8 in *; lia | apply lt_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
(* _latch.v:329 lt_amodel_kept *)
Lemma lt_amodel_kept_x : forall ly S Hp (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S Hp W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= CEIL8)
      by (unfold fr_RG, CEIL8; cbn; unfold ASRC; pose proof lt_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (lt_asrc_x ly S Hp W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lt_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lt_arelay_x ly S Hp W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lt_aout_x ly S Hp W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. lia.
Qed.
(* _latch.v:445 lt_ainput_kept *)
Lemma lt_ainput_kept_x : forall cx ly S Hp (W : world segs) mem md (W' : world segs) mem',
  ARx ly S Hp W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S Hp W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hpz) | (Hn & Hin)]; [lia|].
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold CEIL8. lia.
Qed.
(* W_gesture_end.v ablocks_nodup: the live blocks are pairwise distinct *)
(* _add.v:276 ad_nodup *)
Lemma ad_nodup_x : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S Hp W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
    cbn [snd]. apply req_size_pos. lia. }
  destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
  revert Hpos Hpw. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hpw; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. constructor; [|exact (IH Hl Hpw)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* a byte of a live block other than the relay table is outside a footprint inside that table *)
(* _add.v:290 ad_fp_avoid *)
Lemma ad_fp_avoid_x : forall ly S Hp (W : world segs) mem md p n T FP j,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (T, ATABLE) (ablocks B ly S) -> (p, n) <> (T, ATABLE) ->
  (forall a, inFP FP a -> T <= a < T + ATABLE) -> 0 <= j < req_size n -> ~ inFP FP (p + j).
Proof.
  intros ly S Hp W mem md p n T FP j HAR Hpn HT Hne HFP Hj Hf. apply HFP in Hf.
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md p n T ATABLE HAR Hpn HT Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. unfold ATABLE in Hf. lia.
Qed.
End kitx.

(* ------------------------------------------------------------------ the walk, over ARx *)
Section add.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- cut_x's Section w (W_LLVMFuzzerTestOneInput_cut_x.v:191-235), verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) 0.2): the allocator rules' room record RP, whose room invariant is the
   cut's NP (the walk's RM := fun S _ => NP S; at top_x rp_RM RP := fun S _ => room_live_cf S = NP) ---- *)
Variable RP : roomp.
Hypothesis RP_NP : forall S k, rp_RM RP S k <-> NP S.
(* ---- op_add: oa_spec_g_x, exactly as lib/A/W_op_add.v defines it, at PI := PB_fr and the room record RP ---- *)
Hypothesis OA : oa_spec_g_x (PI := PB_fr) B PST ARx MT RP (BASE + AF_fr_op_add).
(* ---- instance facts (W_LLVMFuzzerTestOneInput_top.v's HEV and HZS), verbatim ---- *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_A.
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* ---- the program's 20 objects are in G_fr (_G.v obj_c), verbatim ---- *)
Hypothesis HGOBJ : forall a, inG G_fr_obj a -> inG G_fr a.
(* ---- cut_x's errno_law_x (_add.v's ERRL : errno_law B, over ARx) ---- *)
Hypothesis ERRL : errno_law_x B ARx.
(* ---- the two instance facts of gx_prog_x B ARx ad_G (_add.v's ROMPIN verbatim; GSHV over ARx) ---- *)
Hypothesis ROMPIN : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
Hypothesis GSHV : forall ly S Hp (W : world segs) mem md a n, ARx ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG ad_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ---- the image is off PST (W_op_add.v Section x's HPST; oa_call_keep's premise): a callee's journal keeps every
   image byte outside the callee's own G.  At the instance's PST := [] it holds trivially. ---- *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* ---- a live block's size is non-negative (W_kit_x.v Section g's BLKN; AR's al_blocks carries it, AR_laws_x's
   alx_blocks does not; the cf instance has it as AR_blocks_law_cf's last conjunct) ---- *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* ---- the arm's model obligations (pure, over lmod; RINV / LS are _cut's Variables) ---- *)
(* the operation this arm runs: op = 0 at the cursor, nothing read yet in it *)
Definition ad_at_op (cx : lfcx) (m : lmod) : Prop :=
  0 <= lm_k m < c_n cx /\ lm_O m = [] /\ in_byte cx (lm_k m) mod 10 = 0.
(* the model after op_add found no closed slot: one input byte consumed *)
Definition ad_none (m : lmod) : lmod :=
  LM (lm_k m + 1) (lm_hs m) (lm_G m) (lm_es m) (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m)
     (lm_nfd m).
(* the model after op_add opened slot i: the new source (descriptor 100 + g_nfd, buffer q holding pj), the relay's
   new entry, g_nfd + 1, and errno as the call left it *)
Definition ad_open (m : lmod) (i : nat) (q : Z) (pj : list byte) (ev : Z) : lmod :=
  LM (lm_k m + 1) (ad_set_nth i (Some (oa_new_src (100 + lm_nfd m) q pj)) (lm_hs m)) (lm_G m)
     (lm_es m ++ [ra_new (100 + lm_nfd m)]) (ad_set_ev (lm_c m) ev) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m)
     (lm_gn m) (lm_nfd m + 1).
(* the blocks of the sources after slot i (closed) takes a source *)
Lemma ad_concat_set : forall hs i x, nth i hs None = None -> (i < length hs)%nat ->
  Permutation (concat (map slot_blks (ad_set_nth i x hs))) (slot_blks x ++ concat (map slot_blks hs)).
Proof.
  induction hs as [|o hs IH]; intros [|i] x Hn Hi; cbn [length] in Hi; try lia.
  - cbn [ad_set_nth map concat nth] in *. subst o. cbn [slot_blks app]. apply Permutation_refl.
  - cbn [ad_set_nth map concat nth] in *.
    eapply Permutation_trans; [apply Permutation_app_head; exact (IH i x Hn ltac:(lia))|].
    apply Permutation_app_swap_app.
Qed.
(* the model's blocks after op_add opened slot i: the new 6000-byte buffer, and the relay's entry names none *)
Lemma ad_model_blks_open : forall m i q pj ev, nth i (lm_hs m) None = None -> (i < length (lm_hs m))%nat ->
  Permutation (model_blks (ad_open m i q pj ev)) ((q, APARTIAL) :: model_blks m).
Proof.
  intros m i q pj ev Hn Hi. unfold model_blks, ad_open. cbn [lm_G lm_es lm_hs lm_cap lm_out].
  rewrite map_app, concat_app. cbn [map concat].
  change (aentry_blks (ra_new (100 + lm_nfd m))) with (@nil (Z * Z)). rewrite !app_nil_r.
  pose proof (ad_concat_set (lm_hs m) i (Some (oa_new_src (100 + lm_nfd m) q pj)) Hn Hi) as Hc.
  change (slot_blks (Some (oa_new_src (100 + lm_nfd m) q pj))) with [(q, APARTIAL)] in Hc.
  eapply Permutation_trans; [apply perm_skip; apply Permutation_app_head; apply Permutation_app_tail; exact Hc|].
  cbn [app].
  eapply Permutation_trans; [apply perm_skip; apply Permutation_sym; apply Permutation_middle|].
  apply perm_swap.
Qed.
(* what op_add's contract takes of the model when a slot is free: room for relay_add's entry, a fresh descriptor,
   and g_nfd + 1 within amodel_at's bound (the plain model's nfd <= t + 1 does not give it at t = 511) *)
Hypothesis RI_add_pre : forall cx t m,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Hypothesis RI_add_open : forall cx t m i q pj ev,
  RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (ad_open m i q pj ev).
Hypothesis RI_add_none : forall cx t m,
  RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None -> RINV cx (t + 1) (ad_none m).
(* the allocator-state facts op_add's contract takes (whether or not a slot is free), read off LS *)
Hypothesis LS_add_room : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S (oa_cost MT).
Hypothesis LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  LSx cx (t + 1) (ad_open m i q pj ev) ly' S'.
Hypothesis LS_add_none : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSx cx (t + 1) (ad_none m) ly S.
(* the room round's count row (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c); lib/A/ReplyLScnt.v fr_LS3cp_cnt_add at
   commit ba8e99b5bd2): at the cut, the live counts plus op_add's premise peak oa_peak stay under RP's bounds.  The
   guards are the walk's facts at the cut (the model's sizes come from amodel_at) *)
Hypothesis LS_cnt : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> amodel_at B ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RP oa_peak (ablocks B ly S).

(* ROM is image, so off PST (W_op_add.v oa_pstr) *)
Lemma ad_pstr : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr]. Qed.

(* _add.v:301 ad_call_keep_frm: what a callee taken at its own G' keeps of a frame of the caller's state: the journal's frame clause, read
   through the overlay of ajournal_gx (an off-image byte is not one of G').  Route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): stated over
   the journal at a world relation R (the proof reads only the frame clause); ad_call_keep_frm_x is it at wle. *)
Lemma ad_call_keep_frm_xR {R : world segs -> world segs -> Prop} : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world segs) m0
    md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k cid pos a,
  gx_ok segs B G' ->
  ajournal_gx_xR segs B PST ARx R G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k cid pos a HGok HJx Hin Hr Hnf Ha Hni.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hnf).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa. exact (Hni (proj1 (HGok a HGa))).
Qed.
Lemma ad_call_keep_frm_x : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world segs) m0 md0 ly1 S1 Hp1 (W1 : world segs) m1 md1 k
    cid pos a,
  gx_ok segs B G' ->
  ajournal_gx_x segs B PST ARx G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
  In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof. exact (@ad_call_keep_frm_xR (@wle segs)). Qed.
(* _latch.v:632 lt_afn_pre_at over ARx: a callee's afn_pre_x at sp = F: the donor's afn_pre_at (Reusable/YCbq.v:1810),
   whose achain is the entry's chain with this frame pushed (the prologue saved ra at sp0-8 and s0 at sp0-16,
   `saved_regs` of aframe_at: achain_push, YCbq.v:295) -- or, when sp0 is within 16 bytes of the stack top, the empty
   chain.  Its proof is _latch.v's, under the zify flag _latch.v's proofs run with (true); _add.v's (false) after it.
   Route R: stated over the cut's journal at a world relation R (the proof reads only the inner journal's ARx, layout,
   view-frame and presence clauses, through ajournal_gx_inner_xR / aview_above_of_journal_xR / afn_pre_x_atR);
   lt_afn_pre_at_x is it at wle. *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma lt_afn_pre_at_xR {R : world segs -> world segs -> Prop} : forall cx Hp full ly3 S3 Hp3 fpos k (W : world segs) mem
    md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hp full ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
Lemma lt_afn_pre_at_x : forall cx Hp full ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof. exact (@lt_afn_pre_at_xR (@wle segs)). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* ------------------------------------------------------------------ gx_prog at ad_G *)
Definition ad_romb (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                     (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma ad_romb_ok : forall a, ad_romb a = true -> in_rom segs a.
Proof.
  intros a H. unfold ad_romb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
(* _add.v:527 ad_gxp, as gx_prog_x *)
Lemma ad_gxp_x : gx_prog_x B ARx ad_G.
Proof.
  split; [apply (gx_ok_sub segs B ad_G G_fr); [intros a Ha; exact (HGOBJ a (ad_G_obj a Ha)) | exact HG]|].
  split.
  { intros a Ha. rewrite HEV. split; [exact (ad_apart_ok TFIB_ERRNO_A 4 ad_G ltac:(vm_compute; reflexivity) a Ha)|].
    split; [exact (ad_apart_ok (VAL (A_OBJ 0)) 8 ad_G ltac:(vm_compute; reflexivity) a Ha)|].
    exact (ad_apart_ok (VAL (A_OBJ 32)) 8 ad_G ltac:(vm_compute; reflexivity) a Ha). }
  split.
  { intros a Hr. split; [exact (rom_apart_ok segs ad_G a ltac:(vm_compute; reflexivity) Hr)|].
    split; [exact (ROMPIN a Hr)|]. split.
    - rewrite HEV. intros He. apply (rom_apart_ok segs [(TFIB_ERRNO_A, 4)] a ltac:(vm_compute; reflexivity) Hr).
      exact (ad_inG_rng [(TFIB_ERRNO_A, 4)] TFIB_ERRNO_A 4 a (or_introl eq_refl) He).
    - intros He. change AOFL_HEAD with A_ofl_head in He.
      apply (rom_apart_ok segs [(A_ofl_head, 8)] a ltac:(vm_compute; reflexivity) Hr).
      exact (ad_inG_rng [(A_ofl_head, 8)] A_ofl_head 8 a (or_introl eq_refl) He). }
  split.
  { intros a Ha.
    pose proof (rng_all_in (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end)
                  ad_G a ltac:(vm_compute; reflexivity) Ha) as Hf.
    cbv beta in Hf. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate Hf]. }
  split.
  { intros a Ha m. pose proof (segwb_ok segs a (rng_all_in (segwb segs) ad_G a ltac:(vm_compute; reflexivity) Ha)) as Hs.
    unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact Hs]. }
  exact GSHV.
Qed.
Lemma ad_G_fr : forall a, inG ad_G a -> inG G_fr a.
Proof. intros a Ha. exact (HGOBJ a (ad_G_obj a Ha)). Qed.
(* ------------------------------------------------------------------ the store of in.n, carried *)
Lemma ad_carry_x : forall cx (W : world segs) mem mem' md ly3 S3 Hp3 fpos m,
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 Hp3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof lt_ceil_lo as HCL. pose proof (c_ERRNO_LOW B HEV) as (HE0 & HE1).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold AD_N, CEIL8 in *; lia. }
  pose proof HFR as (_ & HAW & _).
  split.
  { apply (ad_aframe_kept cx true _ W W mem mem' HFR).
    - intros a Ha Hna. exact (proj1 (KEEP a ltac:(lia) Hna)).
    - intros a Ha. apply WK. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAW. lia.
    - intros a Ha. apply KL. unfold CEIL8. lia.
    - intros a Ha. apply KL. unfold CEIL8, SB in *. lia.
    - lia.
    - lia.
    - lia. }
  split; [exact (lt_amodel_kept_x B ARx LAWS BLKN ly3 S3 Hp3 W mem md W mem' m HAR HMOD HE0 HE1 KL)|].
  split; [exact (lt_ainput_kept_x B ARx LAWS BLKN cx ly3 S3 Hp3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (lt_rom_kept W W mem mem' HRV KL)|].
  exact (lt_jt_kept W W mem mem' HJT KL).
Qed.
(* the fake frame's flag word (lcut's conjunct after aframe_at), across the same keep as ad_carry's *)
Lemma ad_flag_kept_x : forall cx (W : world segs) mem mem' md ly3 S3 Hp3 fpos,
  ARx ly3 S3 Hp3 W mem md -> In (1, fpos) (frames S3) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) -> abyte_kept W mem W mem' a) ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 Hp3 fpos HAR Hfin Hsp KEEP Hv.
  pose proof asan_consts as (HC1 & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. cbn in Hx. apply KEEP; unfold AD_N in *; lia.
Qed.

(* ------------------------------------------------------------------ the arm's two runs *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Definition ae_region : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 144 152 [].
Definition ae_facts : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (26%nat, mkAF SB SB 0) ] [] [].
Definition ss_ae : sstate := mkSS AF_arm_add sr_atoms [ae_region] None ae_facts.
Definition ae_Bx : sv := SOff 26 0.
Definition ae_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* 0x84420: the in.n cell F+144 is the run's only writable window *)
Lemma ae_entry : forall (W : world segs) regs mem F,
  getr regs 9 = w64 F -> getr regs 26 = w64 SB -> 2 ^ 46 <= F <= 2 ^ 47 - 152 ->
  (forall o, 144 <= o < 152 -> writable_at segs (arm W mem) (F + o)) ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) ss_ae
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_add)) mem (seg_rom segs)))
  /\ sh_ok segs ae_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F R9 R26 HF HW. rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  split.
  - unfold ss_ae. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|constructor]. unfold region_ok, ae_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. exact (HW o Ho).
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [ae_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E26, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Definition ar_facts : facts := mkFacts [ (26%nat, mkAF SB SB 0) ] [] [].
Definition ss_ar : sstate := mkSS A_ad_ret sr_atoms [] None ar_facts.
(* 0x8442c, back from op_add: `j 0x84490` reads nothing *)
Lemma ar_entry : forall (W : world segs) regs mem,
  getr regs 26 = w64 SB ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) ss_ar
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_ad_ret)) mem (seg_rom segs)))
  /\ sh_ok segs ae_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem R26. rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  split.
  - unfold ss_ar. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + constructor.
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [ar_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* the registers the pre-call run does not write: all but ra (the jal) and s6 (mv s6,t3) *)
Definition ae_kept : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* the registers `j 0x84490` keeps: all *)
Definition ar_kept : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* the pre-call run's write obligation: the in.n cell is in the function's own stack window *)
Ltac ad_awr U9 :=
  cbn [ss_mem add_cond ss_ae ae_region];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ae_region] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the in.n cell is outside the run's writable window *)
Ltac ad_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [In ss_mem add_cond ss_ae ae_region] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ae_region] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; unfold AD_N in Hna; lia | ]);
  destruct Hin.
Ltac ad_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* ------------------------------------------------------------------ the arm *)
(* the text of cut_x's Section w hypothesis ARM_add (W_LLVMFuzzerTestOneInput_cut_x.v:552) *)
Theorem lf_arm_add_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 0 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4) & R6 & R7 & R27 & Ht & Hk & HO
    & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL. pose proof (c_ERRNO_LOW B HEV) as (HE0 & HE1).
  (* the operation is 0: picks 0 is false, so s5 = 0 and t3 / t4 are the cursor after one byte *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 0).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 0) with false in HPK. cbv iota in HPK.
  destruct HPK as (R28 & R29 & R21).
  assert (HAT : ad_at_op cx m) by (split; [exact Hk | split; [exact HO | exact Hop]]).
  (* the contract's facts at entry: the stack, the input's length, the empty frame list *)
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _ & Hfrs0 & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (ajournal_gx_AR_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as HAR.
  assert (Hfrs3 : frames S3 = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hfrs0. reflexivity. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  pose proof HFR as (_ & HAWR & _).
  (* ---- run 1: 0x84420 to op_add's entry ---- *)
  assert (R9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  destruct (ae_entry W regs mem (lf_F cx) R9 R26 ltac:(lia) ltac:(intros o Ho; exact (HAWR o ltac:(lia))))
    as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + lm_k m + 1))
    by (rewrite (EEo 28%nat 28%bv eq_refl), (KR0 28%bv ltac:(cbv; tauto)); exact R28).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1))
    by (rewrite (EEo 29%nat 29%bv eq_refl), (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 0)) with (Z_to_bv 64 (BASE + AF_arm_add)).
  paj_run_to_tok_x RUNTO HS HJ SHOK ae_span AF_fr_op_add.
  { ad_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  (* the run's only store is the in.n cell: everything else is kept, and every present byte stays present *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); ad_nowr U9 Hna).
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (apresent_grows (w_H W) _ _ a HG1 Hp). }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      abyte_kept W mem W (ms_mem ms) a)
    by (intros a Ha Hna; split; [exact (K1 a Ha Hna) | apply WK]).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  destruct (ad_carry_x cx W mem (ms_mem ms) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HIN HRV HROM KEEP WK) as (HFR1 & HMOD1 & HIN1 & HRV1 & HROM1).
  pose proof (ad_flag_kept_x cx W mem (ms_mem ms) md ly3 S3 Hp3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL1.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : sv8 W (ms_mem ms) (lf_F cx + AD_N) (c_n cx - lm_k m - 1)).
  { unfold sv8, AD_N.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - lm_k m - 1) RG0) end.
    - rewrite ?ew_ewset_other by lia. exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zside.
    - zside. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs []) Ev)
      by (first [exact HAE | split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                                    | rewrite !ed_ewset; exact (proj2 HAE)]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] ae_kept HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (KK : forall rr, In rr ae_kept -> In rr jt_kept -> getr (ms_regs ms) rr = getr regsD rr)
    by (intros rr H1 H2; rewrite (KR rr H1); exact (KR0 rr H2)).
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (22%bv : bv 5) Q22.
  rewrite ?E28 in Q22.
  pmkst HS.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (m1 := ms_mem ms) in *. set (rc1 := ms_regs ms) in *.
  pose proof (ajournal_gx_AR_x segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W m1 mdc k HJ) as HAR1.
  assert (Hsp1 : spZ rc1 = lf_F cx).
  { unfold spZ. rewrite (KK 2%bv ltac:(cbv; tauto) ltac:(cbv; tauto)), C2. unfold w64. apply unsigned_lit_small. lia. }
  (* ---- the call: op_add's afn_pre at sp = F, and its premises at ad_G ---- *)
  destruct (lt_afn_pre_at_x cx Hpe true ly3 S3 Hp3 fpos k W m1 mdc rc1 OA_STK HB HJ HFR1 Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KK 3%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C3. }
  { rewrite (KK 4%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C4. }
  { rewrite (KK 8%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C8. }
  { unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK. lia. }
  { unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK, LLVMF_STK. lia. }
  pose proof HMOD1 as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDb & HTH & (lst & HLST) & HLSTw).
  set (hs := lm_hs m) in *. set (os := ad_os hs).
  assert (Hlos : length os = 4%nat) by (unfold os, ad_os; rewrite length_map; exact Hlen4).
  assert (Hrng : forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31)
    by (intros i Hi; unfold os; rewrite ad_os_nth; destruct (nth i hs None); lia).
  assert (Hcells : forall i, (i < 4)%nat -> val_mem segs (arm W m1) (oa_HA i + 4) 4 (nth i os 0)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|].
    - pose proof HSi as (_ & Hop1 & _ & _ & _ & _ & _ & Hopen & _). rewrite Hopen in Hop1. exact Hop1.
    - destruct HSi as [G1 _]. exact (oa_zero_vm _ _ _ 4 4 G1 ltac:(lia) ltac:(unfold ASRC; cbn; lia)). }
  assert (Hclosed : forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W m1 (oa_HA i)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|]; [discriminate | intros _; exact HSi]. }
  assert (HGgs : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) Ha)).
  assert (HGnfd : forall a, A_NFD <= a < A_NFD + 4 -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G A_NFD 4 a ltac:(ad_in) Ha)).
  assert (HGra : forall a, inG (RA_G fr_globals) a -> inG ad_G a)
    by (intros a Ha; unfold ad_G; apply inG_app; right; exact Ha).
  assert (Hfree : oa_first os <> None -> (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)))
    by (intros Hn; destruct (RI_add_pre cx t m HRI Ht HAT Hn) as (H1 & H2 & _); exact (conj H1 H2)).
  destruct (LS_add_room cx t m ly3 S3 HLS HRI HAT) as [Hlive Hmok].
  pose proof (OA ad_G ad_gxp_x) as OAS.
  eapply SRr_bind.
  { exact (OAS W ly3 S3 Hp3 rc1 m1 mdc ch os (lm_nfd m) (lm_G m) (lm_es m) HPREc ltac:(rewrite Hsp1; exact HF32)
      ltac:(rewrite Hfrs3; vm_compute; reflexivity) Hlos Hrng Hcells Hclosed HNFDv ltac:(unfold OPS_MAX in HNFDb; lia)
      HZS HGgs HGnfd HGra (or_intror HREL) HLOCK HWAKE HRV1 Hfree Hlive Hmok
      (* the room round: the room from the cut's NP (kr := 0), the counts from LS_cnt *)
      0%nat (proj2 (RP_NP S3 _) HNP) (LS_cnt cx t m ly3 S3 W mem HLS HRI HAT HMOD Ht)). }
  intros W2 c2 Hwle2 (ly' & S' & Hp' & regs' & mem' & md' & kk & -> & HJc & HP2 & HPK & HOK & Hfrs' & HRM2 & HCASE & HERRK).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S' 0%nat) HRM2) as HNP2.
  rewrite Hsp1 in HJc. rewrite Q1.
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  set (FP1 := oa_FP os (lm_G m) (lm_es m)) in *.
  assert (Hosd : oa_first (ad_os (lm_hs m)) = oa_first os) by reflexivity.
  pose proof (ajournal_gx_AR_x segs B PST ARx ad_G 0 [] OA_STK _ _ _ _ _ _ _ _ [] ly' S' Hp' W2 mem' md' kk HJc) as HAR2.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & HesL & HTin & _ & HEOK & _).
  destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 HTin) as (HT4096 & HTceil & _).
  pose proof (proj1 ad_gxp_x) as HGoa.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 ad_gxp_x))))) as HGW.
  (* op_add's footprint is relay_add's new entry, inside the relay table *)
  assert (HFPT : forall a, inFP FP1 a -> lm_G m <= a < lm_G m + ATABLE).
  { intros a Ha. unfold FP1, oa_FP in Ha. destruct (oa_first os) eqn:Hf; [|exact (False_ind _ (inFP_nil a Ha))].
    destruct (Hfree ltac:(first [discriminate | rewrite Hf; discriminate])) as [Hes4 _].
    unfold ra_FP in Ha. destruct (lm_G m =? 0); [exact (False_ind _ (inFP_nil a Ha))|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold AENT, ATABLE in *. lia. }
  assert (HFP0 : oa_first os = None -> forall a, ~ inFP FP1 a).
  { intros Hf a Ha. unfold FP1, oa_FP in Ha. rewrite Hf in Ha. exact (inFP_nil a Ha). }
  assert (HFPns : ~ YI16.sink_open_fp FP1).
  { intros (r & Hr & H0). pose proof (HFPT 0 (ex_intro _ r (conj Hr H0))) as H. lia. }
  pose proof HSEP as ((rest & HPS) & HSEP2).
  (* ---- the journal: op_add's, lifted to G_fr and composed into the cut's ---- *)
  assert (HFPsub : forall a, inFP FP1 a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Ha. pose proof (HFPT a Ha) as Hra. unfold ATABLE in Hra.
    destruct (HSEP2 (lm_G m, ATABLE) ltac:(left; reflexivity)) as [Hnot | Hall].
    - right. exists (lm_G m), ATABLE. split; [exact HTin|]. split; [exact Hnot|]. change (req_size ATABLE) with 896. lia.
    - left. split; [apply Hall; cbn [fst snd]; change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
      exists (lm_G m), ATABLE. split; [exact HTin|]. change (req_size ATABLE) with 896. lia. }
  assert (HJc' : ajournal_gx_x segs B PST ARx G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2 mem' md' kk)
    by exact (ajournal_gx_G_mono_x segs B PST ARx ad_G G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2
                mem' md' kk ad_G_fr HJc).
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W m1 mdc k
     OA_STK (lf_F cx) 0 [] FP1 [] ly' S' Hp' W2 mem' md' kk HJ HJc'
     ltac:(unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPsub) as HJ2.
  cbn [app] in HJ2.
  (* ---- what the call keeps, per category of byte ---- *)
  assert (HLIVE : forall b, In b (ablocks B ly3 S3) -> In b (ablocks B ly' S')).
  { intros b Hb. destruct (oa_first os) as [i|].
    - destruct HCASE as (q & T' & pj & _ & _ & _ & _ & [(HT0 & _) | (_ & _ & HP)] & _); [lia|].
      apply (Permutation_in _ (Permutation_sym HP)). right. exact Hb.
    - destruct HCASE as (-> & -> & _). exact Hb. }
  assert (EFF : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  (* the frame and everything above it: outside op_add's window *)
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem' a = aview segs (w_H W) m1 a).
  { intros a Ha. apply (oa_call_keep_hi B PST ARx ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HGoa HJc a);
      lia. }
  (* the function's own stack window is present after the call (the composed journal) *)
  assert (WF : forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W2 mem') a).
  { intros a Ha. pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
    pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply apresent_writable. apply Hpres2. lia. }
  (* the fake frame and its shadow: a frame of the call's state, off the image *)
  set (FF := frame_addr ly3 1 fpos) in *.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE HAR1 HTin) as (_ & _ & _ & HTapp & _).
  assert (KF : forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) -> abyte_kept W m1 W2 mem' a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 <= FF) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    assert (FF8' : FF / 8 * 8 <= FF) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in *; lia).
    (* a byte of the fake frame is a client byte, off the image (YCbqG.frm_img_x, from alx_client_img); its
       shadow is above the image *)
    assert (Hni : ~ in_img segs a).
    { destruct Ha as [Ha | Ha].
      - apply (frm_img_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc 1 fpos a HAR1 Hfin).
        replace (fs_frame_bytes 1) with 128 by reflexivity. unfold FF in *. lia.
      - intros Hi. pose proof (pa_img_range a Hi). unfold SB in Ha. lia. }
    apply (ad_offimg_kept W W2 m1 mem' a Ha64 Hni).
    apply (ad_call_keep_frm_x ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk 1 fpos a HGoa HJc Hfin);
      [| | exact Ha64 | exact Hni].
    - unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
      replace (fs_frame_bytes 1) with 128 by reflexivity. unfold FF in *. unfold SB in Ha.
      change (128 / 8) with 16.
      destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros Hf. apply HFPT in Hf.
      pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE 1 fpos HAR1 HTin Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
      replace (fs_frame_bytes 1) with 128 in Hd by reflexivity. unfold FF in *.
      change (req_size ATABLE) with 896 in HTapp.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp. unfold ATABLE, SB in *. lia. }
  (* op_add's own globals outside the bytes it writes: oa_kept, and writable in every memory (gx_prog) *)
  assert (KG : forall a, inG ad_G a -> ~ oa_wr os a -> abyte_kept W m1 W2 mem' a)
    by (intros a Ha Hnw; split; [exact (HOK a Ha Hnw) | intros _; exact (HGW a Ha (arm W2 mem'))]).
  (* the other program objects: the callee journal's image clause, and apres_kept *)
  assert (KO : forall a, inG G_fr_obj a -> ~ inG ad_G a -> abyte_kept W m1 W2 mem' a).
  { intros a Hobj HnG. destruct (HG a (HGOBJ a Hobj)) as (Himg & Hown & _).
    assert (Herr : ~ (as_errno B <= a < as_errno B + 4))
      by (rewrite HEV; exact (ad_apart_ok TFIB_ERRNO_A 4 G_fr_obj ltac:(vm_compute; reflexivity) a Hobj)).
    split.
    - exact (oa_call_keep B PST ARx HPST ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HJc HFPns a Himg HnG
               Hown Herr).
    - intros Hw. exact (oa_writable_img W W2 m1 mem' a Himg (HPK a Himg Hown Herr) Hw). }
  assert (KM : forall lo n, In (lo, n) (ad_aout_glob ++ ad_misc_glob) -> forall x, lo <= x < lo + n ->
      abyte_kept W m1 W2 mem' x).
  { intros lo n Hin x Hx. destruct (ad_keep_obj x (ad_inG_rng _ lo n x Hin Hx)) as [H1 H2]. exact (KO x H1 H2). }
  (* the bytes of a block live at the call: the journal's block clause, present after (AR) *)
  assert (KB : forall p n j, In (p, n) (ablocks B ly3 S3) -> 0 <= j < req_size n -> ~ inFP FP1 (p + j) ->
      abyte_kept W m1 W2 mem' (p + j)).
  { intros p n j Hp Hj Hnf. split.
    - exact (oa_call_keep_blk B PST ARx LAWS ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HGoa HJc p n j
               Hp (HLIVE _ Hp) Hj Hnf).
    - intros _. destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W2 mem' md' p n HAR2 (HLIVE _ Hp)) as (_ & _ & _ & _ & Hpr & _).
      exact (apresent_writable segs _ _ _ (proj1 (Hpr (p + j) ltac:(lia)))). }
  assert (KBt : forall p n x, In (p, n) (ablocks B ly3 S3) -> (p, n) <> (lm_G m, ATABLE) -> p <= x < p + req_size n ->
      abyte_kept W m1 W2 mem' x).
  { intros p n x Hp Hne Hx. replace x with (p + (x - p)) by lia. apply (KB p n); [exact Hp | lia |].
    exact (ad_fp_avoid_x B ARx LAWS ly3 S3 Hp3 W m1 mdc p n (lm_G m) FP1 (x - p) HAR1 Hp HTin Hne HFPT ltac:(lia)). }
  (* the model's blocks are distinct: the separation's Permutation and AR's disjoint blocks *)
  pose proof (Permutation_NoDup HPS (ad_nodup_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc HAR1)) as NDS.
  set (tailm := concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (Hmb : model_blks m = (lm_G m, ATABLE) :: tailm) by reflexivity.
  assert (Hmin : forall b, In b (model_blks m) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPS)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (Hdist : forall b, In b tailm -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. pose proof (ad_nd_appr _ _ _ NDS) as ND1. rewrite Hmb in ND1. cbn [app] in ND1.
    apply NoDup_cons_iff in ND1 as [Hni _]. apply Hni. apply in_or_app. left. exact Hb. }
  assert (Hdinp : forall b, In b (input_blks cx) -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. apply (ad_nd_app _ _ _ _ NDS Hb). apply in_or_app. left. rewrite Hmb. left. reflexivity. }
  (* ---- the parts of the model op_add does not write ---- *)
  assert (HSLOT : forall j, (j < 4)%nat -> oa_first os <> Some j -> aslot B ly' S' W2 mem' j (nth j hs None)).
  { intros j Hj Hnj. apply (ad_slot_kept B ly3 S3 W m1 ly' S' W2 mem' j _ (HSL j Hj)).
    - intros a Ha. unfold fr_RG in Ha. apply KG.
      + exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) ltac:(unfold ASRC in *; lia)).
      + destruct (oa_first os) as [i|] eqn:Hf;
          [exact (ad_slot_nwr os i j a Hf ltac:(congruence) Hj Ha) | exact (ad_none_nwr os a Hf)].
    - intros [p n] Hb.
      assert (Hbt : In (p, n) tailm).
      { unfold tailm. apply in_or_app. right. apply in_or_app. left. apply in_concat.
        exists (slot_blks (nth j hs None)). split; [apply in_map; apply nth_In; lia | exact Hb]. }
      assert (Hbin : In (p, n) (ablocks B ly3 S3)) by (apply Hmin; rewrite Hmb; right; exact Hbt).
      split; [exact (HLIVE _ Hbin)|]. intros a Ha. cbn [fst snd] in Ha.
      destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc p n HAR1 Hbin) as (_ & _ & Hreq).
      exact (KBt p n a Hbin (Hdist _ Hbt) ltac:(lia)). }
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV0 & _ & HEVr & _ & _ & _ & _ & _ & _ & HOB).
  assert (HOUT2 : forall v, val_mem segs (arm W2 mem') (as_errno B) 4 v -> awr W2 mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
      aout_at B fr_globals ly' S' W2 mem' (ad_set_ev (lm_c m) v) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
        (lm_cap m) (lm_out m)).
  { intros v Hev Hew Hv. apply (ad_aout_rebuild B ly3 S3 W m1 ly' S' W2 mem' _ _ _ _ _ _ v HOUT);
      [| | exact Hev | exact Hew | exact Hv].
    - intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as ((lo & n) & Hin & Hz).
      apply (KM lo n); [apply in_or_app; left; exact Hin | exact Hz].
    - intros Hc. destruct HOB as [(Hc0 & _) | (_ & _ & Hoin & _)]; [lia|].
      assert (Hbt : In (lm_out m, lm_cap m) tailm).
      { unfold tailm, aout_blks. apply in_or_app. right. apply in_or_app. right.
        destruct (Z.eqb_spec (lm_cap m) 0); [lia | left; reflexivity]. }
      split; [exact (HLIVE _ Hoin)|]. intros a Ha.
      destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hoin) as (_ & _ & Hreq).
      exact (KBt _ _ a Hoin (Hdist _ Hbt) ltac:(lia)). }
  assert (HGONE2 : agone_at fr_RG W2 mem' (lm_gn m)).
  { apply (agone_at_kept fr_globals W m1 W2 mem' _ HGONE). intros r [<- | []] x Hx.
    apply (KM (rg_gone fr_globals) 1); [ad_in | exact Hx]. }
  assert (HWAKE2 : awake_at fr_RG W2 mem').
  { apply (awake_at_kept fr_globals W m1 W2 mem' HWAKE). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply (KM (rg_wake fr_globals + 4) 4); [ad_in | lia]. }
  assert (HTH2 : val_mem segs (arm W2 mem') AG_THREAD_UP 1 0)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_THREAD_UP 1); [ad_in | exact Hx] | exact HTH]).
  assert (HLST2 : val_mem segs (arm W2 mem') AG_LISTEN 4 lst)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLST]).
  assert (HLSTw2 : awr W2 mem' AG_LISTEN 4)
    by (apply (akept_awr W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLSTw]).
  assert (HIN2 : ainput_at B cx ly' S' W2 mem').
  { destruct HIN1 as (I1 & I2). split.
    - destruct I1 as [I1 | (Hn & Hin)]; [left; exact I1 | right; split; [exact Hn | exact (HLIVE _ Hin)]].
    - apply (akept_garr8 W m1); [|exact I2]. intros x Hx. rewrite length_map in Hx. rewrite <- Hnlen in Hx.
      destruct I1 as [(Hz & _) | (Hn & Hin)]; [lia|].
      assert (Hbi : In (c_p cx, c_n cx) (input_blks cx))
        by (unfold input_blks; destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]).
      destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hin) as (_ & _ & Hreq).
      exact (KBt _ _ x Hin (Hdinp _ Hbi) ltac:(lia)). }
  assert (HFR2 : aframe_at cx true (frame_addr ly' 1 fpos) W2 mem').
  { rewrite EFF. apply (ad_aframe_kept cx true FF W W2 m1 mem' HFR1).
    - intros a Ha _. exact (KH a Ha).
    - intros a Ha. apply WF. unfold LLVMF_STK. lia.
    - intros a Ha. apply KF. left. exact Ha.
    - intros a Ha. apply KF. right. exact Ha.
    - lia.
    - lia.
    - lia. }
  (* the fake frame's flag word (lcut's conjunct after aframe_at): inside KF's 128 bytes *)
  assert (HFL2 : sv8 W2 mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { assert (EFL : flag_addr ly' 1 fpos = flag_addr ly3 1 fpos).
    { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
      unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    rewrite EFF, EFL. unfold sv8 in *. apply (akept_vm W m1); [|exact HFL1].
    intros x Hx. apply KF. left. cbn in Hx. lia. }
  assert (HRV2 : rom_view segs W2 mem')
    by exact (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low ad_G 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc []
                ly' S' Hp' W2 mem' md' kk HJc (proj1 (proj2 (proj2 ad_gxp_x))) ad_pstr HRV1).
  assert (HROM2 : jt_rom W2 mem').
  { intros i Hi. apply (ad_vm_view W W2 m1 mem'); [|exact (HROM1 i Hi)]. intros x Hx.
    assert (Hx' : fr_jtab <= x < fr_jtab + 36) by (change (Z.of_nat 4) with 4 in Hx; lia).
    assert (Hr : in_rom segs x).
    { apply ad_romb_ok. apply (rng_all_in ad_romb [(fr_jtab, 36)] x ltac:(vm_compute; reflexivity)).
      exact (ad_inG_rng [(fr_jtab, 36)] fr_jtab 36 x (or_introl eq_refl) Hx'). }
    rewrite (HRV2 x Hr), (HRV1 x Hr). reflexivity. }
  (* ---- run 2: 0x8442c to the latch, for any model the operation leaves ---- *)
  assert (R26b : getr regs' 26 = w64 SB).
  { rewrite (lt_pres rc1 regs' 26%bv HP2 ltac:(ad_cs)). rewrite (KK 26%bv ltac:(cbv; tauto) ltac:(cbv; tauto)).
    exact C26. }
  assert (FIN : forall m', amodel_at B ly' S' W2 mem' m' -> ablocks_sep B fr_FP cx m' ly' S' ->
      LSx cx (t + 1) m' ly' S' -> RINV cx (t + 1) m' -> lm_k m' = lm_k m + 1 ->
      SRr segs W2 {| cfg_ms := mkst regs' (Z_to_bv 64 (BASE + 8512)) mem' (seg_rom segs); cfg_model := md' |}
        (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hpe t)).
  { intros m' HMOD2 HSEP' HLS' HRI' Hk'.
    destruct (ar_entry W2 regs' mem' R26b) as [HSb SHOKb].
    change (Z_to_bv 64 (BASE + 8512)) with (Z_to_bv 64 (BASE + A_ad_ret)).
    remember (Eimg (Ereg regs' [])) as Eb eqn:HEb.
    assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
    assert (HAEb : env_agree 32 (Ereg regs' []) Eb)
      by (rewrite HEb; split; [intros q0 Hq0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    clear HEb.
    paj_run_to_tok_x RUNTO HSb HJ2 SHOKb ae_span AF_LLVM_latch.
    { apply awr_ok_x_nil. }
    ad_meq HF Em.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [] ar_kept HSb HAEb ltac:(vm_compute; reflexivity)) as KR3.
    cbn [ms_regs restrict] in KR3.
    pmkst HSb. rewrite Em in *.
    apply SRr_ret.
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly', S', Hp', (k + kk), m', fpos.
    split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP'|]. split; [exact HLS'|]. split; [exact HNP2|].
    split; [exact HRI'|].
    lazymatch goal with |- lregs_K _ _ _ _ _ ?rf _ _ =>
      assert (G1 : forall r : bv 5, In r ar_kept -> acallee_saved (bv_unsigned r) -> In r ae_kept -> In r jt_kept ->
                   getr rf r = getr regsD r)
        by (intros r H0 H1 H2 H3; rewrite (KR3 r H0), (lt_pres rc1 regs' r HP2 H1); exact (KK r H2 H3));
      assert (G22 : getr rf 22 = w64 (c_p cx + lm_k m + 1))
        by (rewrite (KR3 22%bv ltac:(cbv; tauto)), (lt_pres rc1 regs' 22%bv HP2 ltac:(ad_cs)); exact Q22) end.
    rewrite EFF. unfold lregs_K, lregs_common.
    split.
    { split; [rewrite (G1 2%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (G1 8%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (G1 9%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C9|].
      split; [rewrite (G1 18%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C18|].
      split; [rewrite (G1 19%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (G1 20%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C20|].
      split; [rewrite (G1 23%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C23|].
      split; [rewrite (G1 24%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (G1 25%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (G1 26%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (G1 3%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C3|].
      rewrite (G1 4%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C4. }
    split; [rewrite (G1 27%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite G22, Hk'; f_equal; lia|].
    split.
    { rewrite Hk'. apply (ad_sv8_view W W2 m1 mem'); [intros x Hx; apply KH; unfold AD_N in *; lia|].
      replace (c_n cx - (lm_k m + 1)) with (c_n cx - lm_k m - 1) by lia. exact SVN. }
    rewrite Hk'. lia. }
  (* ---- the two outcomes of op_add ---- *)
  destruct (oa_first os) as [i|] eqn:Hfirst.
  - (* a slot was free: op_add opened slot i *)
    destruct HCASE as (q & T' & pj & HNEW & HNFD2 & HREL2 & HLOCK2 & HPERM & HMO).
    destruct HPERM as [(HT0 & _) | (_ & -> & HPERM)]; [lia|].
    pose proof (ad_first_lt os i Hfirst) as Hi4.
    assert (Hnone : nth i hs None = None).
    { pose proof (ad_first_zero os i Hfirst) as Hz. unfold os in Hz. rewrite ad_os_nth in Hz.
      destruct (nth i hs None); [discriminate | reflexivity]. }
    destruct (RI_add_pre cx t m HRI Ht HAT ltac:(rewrite Hosd; discriminate)) as (Hes4 & Hfd & Hnfd512).
    destruct (ERRL ly' S' Hp' W2 mem' md' HAR2) as ((v & Hev & Hv) & Hew).
    pose proof (ad_nodup_x B ARx LAWS BLKN ly' S' Hp' W2 mem' md' HAR2) as ND2.
    apply (Permutation_NoDup HPERM) in ND2. apply NoDup_cons_iff in ND2 as [Hfresh _].
    pose proof HNEW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _).
    cbn [oa_new_src hs_pjunk] in Hpj.
    assert (HMOD2 : amodel_at B ly' S' W2 mem' (ad_open m i q pj v)).
    { unfold ad_open. split; [cbn [lm_hs]; rewrite ad_set_nth_length; exact Hlen4|].
      split.
      { intros j Hj. cbn [lm_hs]. unfold aslot.
        destruct (Nat.eq_dec j i) as [-> | Hji].
        - rewrite ad_set_nth_same by (fold hs; lia). exact HNEW.
        - rewrite ad_set_nth_other by congruence. pose proof (HSLOT j Hj ltac:(congruence)) as HSj.
          unfold aslot in HSj. exact HSj. }
      split; [exact HREL2|].
      split; [exact (HOUT2 v Hev Hew Hv)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [exact HNFD2|].
      split; [intros j Hj; exact (HGW (AG_NFD + j) (HGnfd (AG_NFD + j) ltac:(unfold AG_NFD, A_NFD; lia)) (arm W2 mem'))|].
      split; [cbn [lm_nfd]; unfold OPS_MAX in *; lia|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    assert (Hmb' : Permutation (model_blks (ad_open m i q pj v)) ((q, APARTIAL) :: model_blks m))
      by exact (ad_model_blks_open m i q pj v Hnone ltac:(fold hs; lia)).
    assert (HSEP' : ablocks_sep B fr_FP cx (ad_open m i q pj v) ly' S').
    { split.
      - exists rest. eapply Permutation_trans; [exact HPERM|]. eapply Permutation_trans; [apply perm_skip; exact HPS|].
        eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
        change ((q, APARTIAL) :: model_blks m ++ rest) with (((q, APARTIAL) :: model_blks m) ++ rest).
        apply Permutation_app_tail. exact (Permutation_sym Hmb').
      - intros b Hb. apply (Permutation_in _ Hmb') in Hb. destruct Hb as [<- | Hb]; [|exact (HSEP2 b Hb)].
        destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (q, APARTIAL)
                    (ablocks B (c_ly cx) (c_S cx))) as [Hin | Hnin]; [right | left; exact Hnin].
        intros a Ha. cbn [fst snd] in Ha.
        pose proof HJ as (_ & _ & (memS0 & HJ0i & _) & _).
        pose proof HJ0i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone0 & _).
        replace a with (q + (a - q)) by lia.
        apply (Hgone0 q APARTIAL (a - q) Hin Hfresh). change (req_size APARTIAL) with 6000 in Ha |- *. lia. }
    apply (FIN (ad_open m i q pj v) HMOD2 HSEP').
    + exact (LS_add_open cx t m i q pj v ly3 S3 ly' S' HLS HRI HAT Hosd HMO HPERM).
    + exact (RI_add_open cx t m i q pj v HRI Ht HAT Hosd Hpj Hv).
    + reflexivity.
  - (* no slot was free: op_add changed nothing outside its frame *)
    destruct HCASE as (-> & -> & -> & HAV). rewrite Hsp1 in HAV.
    assert (KGn : forall a, inG ad_G a -> abyte_kept W m1 W mem' a)
      by (intros a Ha; exact (KG a Ha (ad_none_nwr os a Hfirst))).
    assert (HREL2 : arelay_at B fr_globals ly3 S3 W mem' (lm_G m) (lm_es m)).
    { apply (arelay_at_kept B fr_globals ly3 S3 W m1 ly3 S3 W mem' _ _ HREL).
      - intros r Hr x Hx. unfold arelay_fp in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Hx.
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_src fr_globals) 8 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_nsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_capsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + replace x with (lm_G m + (x - lm_G m)) by lia.
          apply (KB (lm_G m) ATABLE); [exact HTin | change (req_size ATABLE) with 896; unfold ATABLE in Hx; lia
                                      | exact (HFP0 eq_refl _)].
        + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He). rewrite Forall_forall in HEOK.
          destruct (oa_efp_in B ly3 S3 W m1 e (HEOK e He) r Hr x Hx) as (b & n & Hb & Hbx).
          replace x with (b + (x - b)) by lia. apply (KB b n); [exact Hb | lia | exact (HFP0 eq_refl _)].
      - intros b Hb. exact (proj2 (lt_arelay_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 HREL) b Hb). }
    assert (HLOCK2 : alock_at fr_globals W mem' false).
    { apply (alock_at_kept fr_globals W m1 W mem' false HLOCK). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
      apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_lock fr_globals) 12 x ltac:(ad_in) Hx). }
    assert (KNFD : forall x, AG_NFD <= x < AG_NFD + 4 -> abyte_kept W m1 W mem' x)
      by (intros x Hx; apply KGn; apply HGnfd; unfold AG_NFD, A_NFD in *; lia).
    assert (Hev0 : val_mem segs (arm W mem') (as_errno B) 4 (ct_ev (lm_c m))).
    { apply (ad_vm_view W W m1 mem'); [|exact HEV0]. intros x Hx. change (Z.of_nat 4) with 4 in Hx.
      apply HAV; unfold CEIL8, OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK in *; lia. }
    destruct (ERRL ly3 S3 Hp' W mem' md' HAR2) as (_ & Hew0).
    assert (HMOD2 : amodel_at B ly3 S3 W mem' (ad_none m)).
    { unfold ad_none. split; [exact Hlen4|].
      split; [intros j Hj; exact (HSLOT j Hj ltac:(discriminate))|].
      split; [exact HREL2|].
      split; [rewrite <- (ad_set_ev_same (lm_c m)); exact (HOUT2 _ Hev0 Hew0 HEVr)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [apply (akept_vm W m1); [intros x Hx; apply KNFD; change (Z.of_nat 4) with 4 in Hx; lia | exact HNFDv]|].
      split; [apply (akept_awr W m1); [exact KNFD | exact HNFDw]|].
      split; [exact HNFDb|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    apply (FIN (ad_none m) HMOD2 HSEP).
    + exact (LS_add_none cx t m ly3 S3 HLS HRI HAT Hosd).
    + exact (RI_add_none cx t m HRI HAT Hosd).
    + reflexivity.
Qed.

(* CHECK (cut_x's scope): lf_arm_add_x's type is the Section w hypothesis ARM_add of W_LLVMFuzzerTestOneInput_cut_x.v:552,
   restated with the generic invariants at this Section's variables *)
Lemma lf_arm_add_x_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 0 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof. exact lf_arm_add_x. Qed.
(* and cut_x's own composition of the arms, lf_arm_x (cut_x.v:322), takes it as its ARM_add argument *)
Definition lf_arm_add_x_cut_x :=
  lf_arm_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LSx RINV lf_arm_add_x.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the arm at a world relation R.  lf_arm_add_xR's statement is the text of the
   Section wR hypothesis ARM_add_R of W_LLVMFuzzerTestOneInput_cut_x.v (:456), checked at the end (lf_arm_add_xR_check,
   and lf_arm_add_xR_cut_x, which feeds it to cut_x's own lf_arm_xR).  Against lf_arm_add_x: R and its laws, and op_add
   at R (OA_R := oa_spec_g_xR .. R .., W_op_add.v: relay_add's realloc may re-hide, so the call gives only R W W2) in
   place of OA.  The proof is lf_arm_add_x's with the cut's journal ajournal_gx_x -> ajournal_gx_xR .. R; run 1 (to
   op_add's entry) the G run paj_run_to_x_xG with paj_run_to_tok_xR (it ends in the call, so it concludes SRrG); the
   call bound by SRrG_bind (R_trans); run 2 (back from op_add to the latch) the strict run over the R journal
   (paj_run_to_x_xR) lifted by SRr_SRrG (WLE_R), as cut_x's lf_seg_jt_xR; and the journal lemmas their _xR twins
   (W_journal_x.v: ajournal_gx_AR_xR / _G_mono_xR / _sub_xR / _rom_view_xR; W_op_add.v Section wR: oa_call_keep_xR /
   _blk_xR / _hi_xR; this file: ad_call_keep_frm_xR / lt_afn_pre_at_xR).  Every other step is lf_arm_add_x's.
   The twins take all three laws (a Theorem Labs lane's one layout for top_x's bullets, 2026-10-31): this proof does not need
   R_refl, so its first step names it, and Coq abstracts it with the others. ---- *)
Section addR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* ---- op_add: oa_spec_g_xR, exactly as lib/A/W_op_add.v defines it, at PI := PB_fr, the room record RP and R ---- *)
Hypothesis OA_R : oa_spec_g_xR (PI := PB_fr) B PST ARx R MT RP (BASE + AF_fr_op_add).
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
(* the text of cut_x's Section wR hypothesis ARM_add_R (W_LLVMFuzzerTestOneInput_cut_x.v:456) *)
Theorem lf_arm_add_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 0 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  (* R_refl, named so that it is abstracted (the one layout of the R twins); nothing below uses it *)
  pose proof R_refl as HRrefl. clear HRrefl.
  intros cx Hpe t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4) & R6 & R7 & R27 & Ht & Hk & HO
    & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL. pose proof (c_ERRNO_LOW B HEV) as (HE0 & HE1).
  (* the operation is 0: picks 0 is false, so s5 = 0 and t3 / t4 are the cursor after one byte *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 0).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 0) with false in HPK. cbv iota in HPK.
  destruct HPK as (R28 & R29 & R21).
  assert (HAT : ad_at_op cx m) by (split; [exact Hk | split; [exact HO | exact Hop]]).
  (* the contract's facts at entry: the stack, the input's length, the empty frame list *)
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _ & Hfrs0 & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (ajournal_gx_AR_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as HAR.
  assert (Hfrs3 : frames S3 = [(1, fpos)]).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hfrs0. reflexivity. }
  assert (Hfin : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  pose proof HFR as (_ & HAWR & _).
  (* ---- run 1: 0x84420 to op_add's entry (the G run: it ends in the call) ---- *)
  assert (R9 : getr regs 9 = w64 (lf_F cx)) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R26 : getr regs 26 = w64 SB) by (rewrite (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  destruct (ae_entry W regs mem (lf_F cx) R9 R26 ltac:(lia) ltac:(intros o Ho; exact (HAWR o ltac:(lia))))
    as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + lm_k m + 1))
    by (rewrite (EEo 28%nat 28%bv eq_refl), (KR0 28%bv ltac:(cbv; tauto)); exact R28).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - lm_k m - 1))
    by (rewrite (EEo 29%nat 29%bv eq_refl), (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 0)) with (Z_to_bv 64 (BASE + AF_arm_add)).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK ae_span AF_fr_op_add.
  { ad_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  (* the run's only store is the in.n cell: everything else is kept, and every present byte stays present *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); ad_nowr U9 Hna).
  assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (apresent_grows (w_H W) _ _ a HG1 Hp). }
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + AD_N <= a < lf_F cx + AD_N + 8) ->
      abyte_kept W mem W (ms_mem ms) a)
    by (intros a Ha Hna; split; [exact (K1 a Ha Hna) | apply WK]).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  destruct (ad_carry_x cx W mem (ms_mem ms) md ly3 S3 Hp3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
              HFR HMOD HIN HRV HROM KEEP WK) as (HFR1 & HMOD1 & HIN1 & HRV1 & HROM1).
  pose proof (ad_flag_kept_x cx W mem (ms_mem ms) md ly3 S3 Hp3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL1.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : sv8 W (ms_mem ms) (lf_F cx + AD_N) (c_n cx - lm_k m - 1)).
  { unfold sv8, AD_N.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - lm_k m - 1) RG0) end.
    - rewrite ?ew_ewset_other by lia. exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zside.
    - zside. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs []) Ev)
      by (first [exact HAE | split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                                    | rewrite !ed_ewset; exact (proj2 HAE)]]) end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] ae_kept HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (KK : forall rr, In rr ae_kept -> In rr jt_kept -> getr (ms_regs ms) rr = getr regsD rr)
    by (intros rr H1 H2; rewrite (KR rr H1); exact (KR0 rr H2)).
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (22%bv : bv 5) Q22.
  rewrite ?E28 in Q22.
  pmkst HS.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (m1 := ms_mem ms) in *. set (rc1 := ms_regs ms) in *.
  pose proof (ajournal_gx_AR_xR segs B PST ARx G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ _ [(1, fpos)] ly3 S3 Hp3 W m1 mdc k HJ) as HAR1.
  assert (Hsp1 : spZ rc1 = lf_F cx).
  { unfold spZ. rewrite (KK 2%bv ltac:(cbv; tauto) ltac:(cbv; tauto)), C2. unfold w64. apply unsigned_lit_small. lia. }
  (* ---- the call: op_add's afn_pre at sp = F, and its premises at ad_G ---- *)
  destruct (lt_afn_pre_at_xR cx Hpe true ly3 S3 Hp3 fpos k W m1 mdc rc1 OA_STK HB HJ HFR1 Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KK 3%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C3. }
  { rewrite (KK 4%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C4. }
  { rewrite (KK 8%bv ltac:(cbv; tauto) ltac:(cbv; tauto)). exact C8. }
  { unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK. lia. }
  { unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK, LLVMF_STK. lia. }
  pose proof HMOD1 as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFDv & HNFDw & HNFDb & HTH & (lst & HLST) & HLSTw).
  set (hs := lm_hs m) in *. set (os := ad_os hs).
  assert (Hlos : length os = 4%nat) by (unfold os, ad_os; rewrite length_map; exact Hlen4).
  assert (Hrng : forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31)
    by (intros i Hi; unfold os; rewrite ad_os_nth; destruct (nth i hs None); lia).
  assert (Hcells : forall i, (i < 4)%nat -> val_mem segs (arm W m1) (oa_HA i + 4) 4 (nth i os 0)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|].
    - pose proof HSi as (_ & Hop1 & _ & _ & _ & _ & _ & Hopen & _). rewrite Hopen in Hop1. exact Hop1.
    - destruct HSi as [G1 _]. exact (oa_zero_vm _ _ _ 4 4 G1 ltac:(lia) ltac:(unfold ASRC; cbn; lia)). }
  assert (Hclosed : forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W m1 (oa_HA i)).
  { intros i Hi. unfold os. rewrite ad_os_nth. pose proof (HSL i Hi) as HSi. unfold aslot in HSi.
    destruct (nth i hs None) as [h|]; [discriminate | intros _; exact HSi]. }
  assert (HGgs : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) Ha)).
  assert (HGnfd : forall a, A_NFD <= a < A_NFD + 4 -> inG ad_G a)
    by (intros a Ha; exact (ad_inG_rng ad_G A_NFD 4 a ltac:(ad_in) Ha)).
  assert (HGra : forall a, inG (RA_G fr_globals) a -> inG ad_G a)
    by (intros a Ha; unfold ad_G; apply inG_app; right; exact Ha).
  assert (Hfree : oa_first os <> None -> (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)))
    by (intros Hn; destruct (RI_add_pre cx t m HRI Ht HAT Hn) as (H1 & H2 & _); exact (conj H1 H2)).
  destruct (LS_add_room cx t m ly3 S3 HLS HRI HAT) as [Hlive Hmok].
  (* op_add at R: its post holds in a world W2 with only R W W2 *)
  pose proof (OA_R ad_G ad_gxp_x) as OAS.
  eapply (YA0nH.SRrG_bind segs R R_trans).
  { exact (OAS W ly3 S3 Hp3 rc1 m1 mdc ch os (lm_nfd m) (lm_G m) (lm_es m) HPREc ltac:(rewrite Hsp1; exact HF32)
      ltac:(rewrite Hfrs3; vm_compute; reflexivity) Hlos Hrng Hcells Hclosed HNFDv ltac:(unfold OPS_MAX in HNFDb; lia)
      HZS HGgs HGnfd HGra (or_intror HREL) HLOCK HWAKE HRV1 Hfree Hlive Hmok
      (* the room round: the room from the cut's NP (kr := 0), the counts from LS_cnt *)
      0%nat (proj2 (RP_NP S3 _) HNP) (LS_cnt cx t m ly3 S3 W mem HLS HRI HAT HMOD Ht)). }
  intros W2 c2 HR2 (ly' & S' & Hp' & regs' & mem' & md' & kk & -> & HJc & HP2 & HPK & HOK & Hfrs' & HRM2 & HCASE & HERRK).
  (* the room after op_add: its post's rp_RM at kr = 0 is the cut's NP *)
  pose proof (proj1 (RP_NP S' 0%nat) HRM2) as HNP2.
  rewrite Hsp1 in HJc. rewrite Q1.
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  set (FP1 := oa_FP os (lm_G m) (lm_es m)) in *.
  assert (Hosd : oa_first (ad_os (lm_hs m)) = oa_first os) by reflexivity.
  pose proof (ajournal_gx_AR_xR segs B PST ARx ad_G 0 [] OA_STK _ _ _ _ _ _ _ _ [] ly' S' Hp' W2 mem' md' kk HJc) as HAR2.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & HesL & HTin & _ & HEOK & _).
  destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 HTin) as (HT4096 & HTceil & _).
  pose proof (proj1 ad_gxp_x) as HGoa.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 ad_gxp_x))))) as HGW.
  (* op_add's footprint is relay_add's new entry, inside the relay table *)
  assert (HFPT : forall a, inFP FP1 a -> lm_G m <= a < lm_G m + ATABLE).
  { intros a Ha. unfold FP1, oa_FP in Ha. destruct (oa_first os) eqn:Hf; [|exact (False_ind _ (inFP_nil a Ha))].
    destruct (Hfree ltac:(first [discriminate | rewrite Hf; discriminate])) as [Hes4 _].
    unfold ra_FP in Ha. destruct (lm_G m =? 0); [exact (False_ind _ (inFP_nil a Ha))|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold AENT, ATABLE in *. lia. }
  assert (HFP0 : oa_first os = None -> forall a, ~ inFP FP1 a).
  { intros Hf a Ha. unfold FP1, oa_FP in Ha. rewrite Hf in Ha. exact (inFP_nil a Ha). }
  assert (HFPns : ~ YI16.sink_open_fp FP1).
  { intros (r & Hr & H0). pose proof (HFPT 0 (ex_intro _ r (conj Hr H0))) as H. lia. }
  pose proof HSEP as ((rest & HPS) & HSEP2).
  (* ---- the journal: op_add's, lifted to G_fr and composed into the cut's (at R: R_trans) ---- *)
  assert (HFPsub : forall a, inFP FP1 a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Ha. pose proof (HFPT a Ha) as Hra. unfold ATABLE in Hra.
    destruct (HSEP2 (lm_G m, ATABLE) ltac:(left; reflexivity)) as [Hnot | Hall].
    - right. exists (lm_G m), ATABLE. split; [exact HTin|]. split; [exact Hnot|]. change (req_size ATABLE) with 896. lia.
    - left. split; [apply Hall; cbn [fst snd]; change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
      exists (lm_G m), ATABLE. split; [exact HTin|]. change (req_size ATABLE) with 896. lia. }
  assert (HJc' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2 mem'
      md' kk)
    by exact (ajournal_gx_G_mono_xR segs B PST ARx ad_G G_fr 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc [] ly' S' Hp' W2
                mem' md' kk ad_G_fr HJc).
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
     (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hpe (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W m1 mdc k
     OA_STK (lf_F cx) 0 [] FP1 [] ly' S' Hp' W2 mem' md' kk HJ HJc'
     ltac:(unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPsub) as HJ2.
  cbn [app] in HJ2.
  (* ---- what the call keeps, per category of byte ---- *)
  assert (HLIVE : forall b, In b (ablocks B ly3 S3) -> In b (ablocks B ly' S')).
  { intros b Hb. destruct (oa_first os) as [i|].
    - destruct HCASE as (q & T' & pj & _ & _ & _ & _ & [(HT0 & _) | (_ & _ & HP)] & _); [lia|].
      apply (Permutation_in _ (Permutation_sym HP)). right. exact Hb.
    - destruct HCASE as (-> & -> & _). exact Hb. }
  assert (EFF : frame_addr ly' 1 fpos = frame_addr ly3 1 fpos).
  { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
    unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  (* the frame and everything above it: outside op_add's window *)
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem' a = aview segs (w_H W) m1 a).
  { intros a Ha.
    apply (oa_call_keep_hi_xR B PST ARx R ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HGoa HJc a);
      lia. }
  (* the function's own stack window is present after the call (the composed journal) *)
  assert (WF : forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W2 mem') a).
  { intros a Ha. pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
    pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    apply apresent_writable. apply Hpres2. lia. }
  (* the fake frame and its shadow: a frame of the call's state, off the image *)
  set (FF := frame_addr ly3 1 fpos) in *.
  destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE HAR1 HTin) as (_ & _ & _ & HTapp & _).
  assert (KF : forall a, (FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16) -> abyte_kept W m1 W2 mem' a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 <= FF) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    assert (FF8' : FF / 8 * 8 <= FF) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in *; lia).
    (* a byte of the fake frame is a client byte, off the image (YCbqG.frm_img_x, from alx_client_img); its
       shadow is above the image *)
    assert (Hni : ~ in_img segs a).
    { destruct Ha as [Ha | Ha].
      - apply (frm_img_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc 1 fpos a HAR1 Hfin).
        replace (fs_frame_bytes 1) with 128 by reflexivity. unfold FF in *. lia.
      - intros Hi. pose proof (pa_img_range a Hi). unfold SB in Ha. lia. }
    apply (ad_offimg_kept W W2 m1 mem' a Ha64 Hni).
    apply (ad_call_keep_frm_xR ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk 1 fpos a HGoa HJc Hfin);
      [| | exact Ha64 | exact Hni].
    - unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
      replace (fs_frame_bytes 1) with 128 by reflexivity. unfold FF in *. unfold SB in Ha.
      change (128 / 8) with 16.
      destruct Ha as [Ha | Ha]; [left | right]; lia.
    - intros Hf. apply HFPT in Hf.
      pose proof (sep_block_frame_x segs B ARx LAWS ly3 S3 Hp3 W m1 mdc (lm_G m) ATABLE 1 fpos HAR1 HTin Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
      replace (fs_frame_bytes 1) with 128 in Hd by reflexivity. unfold FF in *.
      change (req_size ATABLE) with 896 in HTapp.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp. unfold ATABLE, SB in *. lia. }
  (* op_add's own globals outside the bytes it writes: oa_kept, and writable in every memory (gx_prog) *)
  assert (KG : forall a, inG ad_G a -> ~ oa_wr os a -> abyte_kept W m1 W2 mem' a)
    by (intros a Ha Hnw; split; [exact (HOK a Ha Hnw) | intros _; exact (HGW a Ha (arm W2 mem'))]).
  (* the other program objects: the callee journal's image clause, and apres_kept *)
  assert (KO : forall a, inG G_fr_obj a -> ~ inG ad_G a -> abyte_kept W m1 W2 mem' a).
  { intros a Hobj HnG. destruct (HG a (HGOBJ a Hobj)) as (Himg & Hown & _).
    assert (Herr : ~ (as_errno B <= a < as_errno B + 4))
      by (rewrite HEV; exact (ad_apart_ok TFIB_ERRNO_A 4 G_fr_obj ltac:(vm_compute; reflexivity) a Hobj)).
    split.
    - exact (oa_call_keep_xR B PST ARx HPST R ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk HJc
               HFPns a Himg HnG Hown Herr).
    - intros Hw. exact (oa_writable_img W W2 m1 mem' a Himg (HPK a Himg Hown Herr) Hw). }
  assert (KM : forall lo n, In (lo, n) (ad_aout_glob ++ ad_misc_glob) -> forall x, lo <= x < lo + n ->
      abyte_kept W m1 W2 mem' x).
  { intros lo n Hin x Hx. destruct (ad_keep_obj x (ad_inG_rng _ lo n x Hin Hx)) as [H1 H2]. exact (KO x H1 H2). }
  (* the bytes of a block live at the call: the journal's block clause, present after (AR) *)
  assert (KB : forall p n j, In (p, n) (ablocks B ly3 S3) -> 0 <= j < req_size n -> ~ inFP FP1 (p + j) ->
      abyte_kept W m1 W2 mem' (p + j)).
  { intros p n j Hp Hj Hnf. split.
    - exact (oa_call_keep_blk_xR B PST ARx LAWS R ad_G OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc ly' S' Hp' W2 mem' md' kk
               HGoa HJc p n j Hp (HLIVE _ Hp) Hj Hnf).
    - intros _. destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W2 mem' md' p n HAR2 (HLIVE _ Hp)) as (_ & _ & _ & _ & Hpr & _).
      exact (apresent_writable segs _ _ _ (proj1 (Hpr (p + j) ltac:(lia)))). }
  assert (KBt : forall p n x, In (p, n) (ablocks B ly3 S3) -> (p, n) <> (lm_G m, ATABLE) -> p <= x < p + req_size n ->
      abyte_kept W m1 W2 mem' x).
  { intros p n x Hp Hne Hx. replace x with (p + (x - p)) by lia. apply (KB p n); [exact Hp | lia |].
    exact (ad_fp_avoid_x B ARx LAWS ly3 S3 Hp3 W m1 mdc p n (lm_G m) FP1 (x - p) HAR1 Hp HTin Hne HFPT ltac:(lia)). }
  (* the model's blocks are distinct: the separation's Permutation and AR's disjoint blocks *)
  pose proof (Permutation_NoDup HPS (ad_nodup_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc HAR1)) as NDS.
  set (tailm := concat (map aentry_blks (lm_es m)) ++ concat (map slot_blks hs) ++ aout_blks (lm_cap m) (lm_out m)).
  assert (Hmb : model_blks m = (lm_G m, ATABLE) :: tailm) by reflexivity.
  assert (Hmin : forall b, In b (model_blks m) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPS)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (Hdist : forall b, In b tailm -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. pose proof (ad_nd_appr _ _ _ NDS) as ND1. rewrite Hmb in ND1. cbn [app] in ND1.
    apply NoDup_cons_iff in ND1 as [Hni _]. apply Hni. apply in_or_app. left. exact Hb. }
  assert (Hdinp : forall b, In b (input_blks cx) -> b <> (lm_G m, ATABLE)).
  { intros b Hb Heq. subst b. apply (ad_nd_app _ _ _ _ NDS Hb). apply in_or_app. left. rewrite Hmb. left. reflexivity. }
  (* ---- the parts of the model op_add does not write ---- *)
  assert (HSLOT : forall j, (j < 4)%nat -> oa_first os <> Some j -> aslot B ly' S' W2 mem' j (nth j hs None)).
  { intros j Hj Hnj. apply (ad_slot_kept B ly3 S3 W m1 ly' S' W2 mem' j _ (HSL j Hj)).
    - intros a Ha. unfold fr_RG in Ha. apply KG.
      + exact (ad_inG_rng ad_G (rg_s fr_globals) (4 * ASRC) a ltac:(ad_in) ltac:(unfold ASRC in *; lia)).
      + destruct (oa_first os) as [i|] eqn:Hf;
          [exact (ad_slot_nwr os i j a Hf ltac:(congruence) Hj Ha) | exact (ad_none_nwr os a Hf)].
    - intros [p n] Hb.
      assert (Hbt : In (p, n) tailm).
      { unfold tailm. apply in_or_app. right. apply in_or_app. left. apply in_concat.
        exists (slot_blks (nth j hs None)). split; [apply in_map; apply nth_In; lia | exact Hb]. }
      assert (Hbin : In (p, n) (ablocks B ly3 S3)) by (apply Hmin; rewrite Hmb; right; exact Hbt).
      split; [exact (HLIVE _ Hbin)|]. intros a Ha. cbn [fst snd] in Ha.
      destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc p n HAR1 Hbin) as (_ & _ & Hreq).
      exact (KBt p n a Hbin (Hdist _ Hbt) ltac:(lia)). }
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV0 & _ & HEVr & _ & _ & _ & _ & _ & _ & HOB).
  assert (HOUT2 : forall v, val_mem segs (arm W2 mem') (as_errno B) 4 v -> awr W2 mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
      aout_at B fr_globals ly' S' W2 mem' (ad_set_ev (lm_c m) v) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
        (lm_cap m) (lm_out m)).
  { intros v Hev Hew Hv. apply (ad_aout_rebuild B ly3 S3 W m1 ly' S' W2 mem' _ _ _ _ _ _ v HOUT);
      [| | exact Hev | exact Hew | exact Hv].
    - intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as ((lo & n) & Hin & Hz).
      apply (KM lo n); [apply in_or_app; left; exact Hin | exact Hz].
    - intros Hc. destruct HOB as [(Hc0 & _) | (_ & _ & Hoin & _)]; [lia|].
      assert (Hbt : In (lm_out m, lm_cap m) tailm).
      { unfold tailm, aout_blks. apply in_or_app. right. apply in_or_app. right.
        destruct (Z.eqb_spec (lm_cap m) 0); [lia | left; reflexivity]. }
      split; [exact (HLIVE _ Hoin)|]. intros a Ha.
      destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hoin) as (_ & _ & Hreq).
      exact (KBt _ _ a Hoin (Hdist _ Hbt) ltac:(lia)). }
  assert (HGONE2 : agone_at fr_RG W2 mem' (lm_gn m)).
  { apply (agone_at_kept fr_globals W m1 W2 mem' _ HGONE). intros r [<- | []] x Hx.
    apply (KM (rg_gone fr_globals) 1); [ad_in | exact Hx]. }
  assert (HWAKE2 : awake_at fr_RG W2 mem').
  { apply (awake_at_kept fr_globals W m1 W2 mem' HWAKE). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply (KM (rg_wake fr_globals + 4) 4); [ad_in | lia]. }
  assert (HTH2 : val_mem segs (arm W2 mem') AG_THREAD_UP 1 0)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_THREAD_UP 1); [ad_in | exact Hx] | exact HTH]).
  assert (HLST2 : val_mem segs (arm W2 mem') AG_LISTEN 4 lst)
    by (apply (akept_vm W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLST]).
  assert (HLSTw2 : awr W2 mem' AG_LISTEN 4)
    by (apply (akept_awr W m1); [intros x Hx; apply (KM AG_LISTEN 4); [ad_in | exact Hx] | exact HLSTw]).
  assert (HIN2 : ainput_at B cx ly' S' W2 mem').
  { destruct HIN1 as (I1 & I2). split.
    - destruct I1 as [I1 | (Hn & Hin)]; [left; exact I1 | right; split; [exact Hn | exact (HLIVE _ Hin)]].
    - apply (akept_garr8 W m1); [|exact I2]. intros x Hx. rewrite length_map in Hx. rewrite <- Hnlen in Hx.
      destruct I1 as [(Hz & _) | (Hn & Hin)]; [lia|].
      assert (Hbi : In (c_p cx, c_n cx) (input_blks cx))
        by (unfold input_blks; destruct (Z.eqb_spec (c_n cx) 0); [lia | left; reflexivity]).
      destruct (lt_blk_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 Hin) as (_ & _ & Hreq).
      exact (KBt _ _ x Hin (Hdinp _ Hbi) ltac:(lia)). }
  assert (HFR2 : aframe_at cx true (frame_addr ly' 1 fpos) W2 mem').
  { rewrite EFF. apply (ad_aframe_kept cx true FF W W2 m1 mem' HFR1).
    - intros a Ha _. exact (KH a Ha).
    - intros a Ha. apply WF. unfold LLVMF_STK. lia.
    - intros a Ha. apply KF. left. exact Ha.
    - intros a Ha. apply KF. right. exact Ha.
    - lia.
    - lia.
    - lia. }
  (* the fake frame's flag word (lcut's conjunct after aframe_at): inside KF's 128 bytes *)
  assert (HFL2 : sv8 W2 mem' (frame_addr ly' 1 fpos + 120) (flag_addr ly' 1 fpos)).
  { assert (EFL : flag_addr ly' 1 fpos = flag_addr ly3 1 fpos).
    { pose proof HJc as (_ & _ & (memSc & HJci & _) & _). pose proof HJci as (_ & Hly & _).
      unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
    rewrite EFF, EFL. unfold sv8 in *. apply (akept_vm W m1); [|exact HFL1].
    intros x Hx. apply KF. left. cbn in Hx. lia. }
  assert (HRV2 : rom_view segs W2 mem')
    by exact (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low ad_G 0 [] OA_STK (lf_F cx) FP1 ly3 S3 Hp3 W m1 mdc []
                ly' S' Hp' W2 mem' md' kk HJc (proj1 (proj2 (proj2 ad_gxp_x))) ad_pstr HRV1).
  assert (HROM2 : jt_rom W2 mem').
  { intros i Hi. apply (ad_vm_view W W2 m1 mem'); [|exact (HROM1 i Hi)]. intros x Hx.
    assert (Hx' : fr_jtab <= x < fr_jtab + 36) by (change (Z.of_nat 4) with 4 in Hx; lia).
    assert (Hr : in_rom segs x).
    { apply ad_romb_ok. apply (rng_all_in ad_romb [(fr_jtab, 36)] x ltac:(vm_compute; reflexivity)).
      exact (ad_inG_rng [(fr_jtab, 36)] fr_jtab 36 x (or_introl eq_refl) Hx'). }
    rewrite (HRV2 x Hr), (HRV1 x Hr). reflexivity. }
  (* ---- run 2: 0x8442c to the latch, for any model the operation leaves (no call: the strict run over the R
     journal, lifted to R by WLE_R) ---- *)
  assert (R26b : getr regs' 26 = w64 SB).
  { rewrite (lt_pres rc1 regs' 26%bv HP2 ltac:(ad_cs)). rewrite (KK 26%bv ltac:(cbv; tauto) ltac:(cbv; tauto)).
    exact C26. }
  assert (FIN : forall m', amodel_at B ly' S' W2 mem' m' -> ablocks_sep B fr_FP cx m' ly' S' ->
      LSx cx (t + 1) m' ly' S' -> RINV cx (t + 1) m' -> lm_k m' = lm_k m + 1 ->
      YA0nH.SRrG segs R W2 {| cfg_ms := mkst regs' (Z_to_bv 64 (BASE + 8512)) mem' (seg_rom segs); cfg_model := md' |}
        (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hpe t)).
  { intros m' HMOD2 HSEP' HLS' HRI' Hk'.
    apply (YA0nH.SRr_SRrG segs R WLE_R).
    destruct (ar_entry W2 regs' mem' R26b) as [HSb SHOKb].
    change (Z_to_bv 64 (BASE + 8512)) with (Z_to_bv 64 (BASE + A_ad_ret)).
    remember (Eimg (Ereg regs' [])) as Eb eqn:HEb.
    assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
    assert (HAEb : env_agree 32 (Ereg regs' []) Eb)
      by (rewrite HEb; split; [intros q0 Hq0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    clear HEb.
    paj_run_to_tok_x RUNTOR HSb HJ2 SHOKb ae_span AF_LLVM_latch.
    { apply awr_ok_x_nil. }
    ad_meq HF Em.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs' [] ar_kept HSb HAEb ltac:(vm_compute; reflexivity)) as KR3.
    cbn [ms_regs restrict] in KR3.
    pmkst HSb. rewrite Em in *.
    apply SRr_ret.
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly', S', Hp', (k + kk), m', fpos.
    split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP'|]. split; [exact HLS'|]. split; [exact HNP2|].
    split; [exact HRI'|].
    lazymatch goal with |- lregs_K _ _ _ _ _ ?rf _ _ =>
      assert (G1 : forall r : bv 5, In r ar_kept -> acallee_saved (bv_unsigned r) -> In r ae_kept -> In r jt_kept ->
                   getr rf r = getr regsD r)
        by (intros r H0 H1 H2 H3; rewrite (KR3 r H0), (lt_pres rc1 regs' r HP2 H1); exact (KK r H2 H3));
      assert (G22 : getr rf 22 = w64 (c_p cx + lm_k m + 1))
        by (rewrite (KR3 22%bv ltac:(cbv; tauto)), (lt_pres rc1 regs' 22%bv HP2 ltac:(ad_cs)); exact Q22) end.
    rewrite EFF. unfold lregs_K, lregs_common.
    split.
    { split; [rewrite (G1 2%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (G1 8%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (G1 9%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C9|].
      split; [rewrite (G1 18%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C18|].
      split; [rewrite (G1 19%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (G1 20%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C20|].
      split; [rewrite (G1 23%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C23|].
      split; [rewrite (G1 24%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (G1 25%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (G1 26%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (G1 3%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C3|].
      rewrite (G1 4%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact C4. }
    split; [rewrite (G1 27%bv ltac:(cbv; tauto) ltac:(ad_cs) ltac:(cbv; tauto) ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite G22, Hk'; f_equal; lia|].
    split.
    { rewrite Hk'. apply (ad_sv8_view W W2 m1 mem'); [intros x Hx; apply KH; unfold AD_N in *; lia|].
      replace (c_n cx - (lm_k m + 1)) with (c_n cx - lm_k m - 1) by lia. exact SVN. }
    rewrite Hk'. lia. }
  (* ---- the two outcomes of op_add ---- *)
  destruct (oa_first os) as [i|] eqn:Hfirst.
  - (* a slot was free: op_add opened slot i *)
    destruct HCASE as (q & T' & pj & HNEW & HNFD2 & HREL2 & HLOCK2 & HPERM & HMO).
    destruct HPERM as [(HT0 & _) | (_ & -> & HPERM)]; [lia|].
    pose proof (ad_first_lt os i Hfirst) as Hi4.
    assert (Hnone : nth i hs None = None).
    { pose proof (ad_first_zero os i Hfirst) as Hz. unfold os in Hz. rewrite ad_os_nth in Hz.
      destruct (nth i hs None); [discriminate | reflexivity]. }
    destruct (RI_add_pre cx t m HRI Ht HAT ltac:(rewrite Hosd; discriminate)) as (Hes4 & Hfd & Hnfd512).
    destruct (ERRL ly' S' Hp' W2 mem' md' HAR2) as ((v & Hev & Hv) & Hew).
    pose proof (ad_nodup_x B ARx LAWS BLKN ly' S' Hp' W2 mem' md' HAR2) as ND2.
    apply (Permutation_NoDup HPERM) in ND2. apply NoDup_cons_iff in ND2 as [Hfresh _].
    pose proof HNEW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpj & _).
    cbn [oa_new_src hs_pjunk] in Hpj.
    assert (HMOD2 : amodel_at B ly' S' W2 mem' (ad_open m i q pj v)).
    { unfold ad_open. split; [cbn [lm_hs]; rewrite ad_set_nth_length; exact Hlen4|].
      split.
      { intros j Hj. cbn [lm_hs]. unfold aslot.
        destruct (Nat.eq_dec j i) as [-> | Hji].
        - rewrite ad_set_nth_same by (fold hs; lia). exact HNEW.
        - rewrite ad_set_nth_other by congruence. pose proof (HSLOT j Hj ltac:(congruence)) as HSj.
          unfold aslot in HSj. exact HSj. }
      split; [exact HREL2|].
      split; [exact (HOUT2 v Hev Hew Hv)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [exact HNFD2|].
      split; [intros j Hj; exact (HGW (AG_NFD + j) (HGnfd (AG_NFD + j) ltac:(unfold AG_NFD, A_NFD; lia)) (arm W2 mem'))|].
      split; [cbn [lm_nfd]; unfold OPS_MAX in *; lia|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    assert (Hmb' : Permutation (model_blks (ad_open m i q pj v)) ((q, APARTIAL) :: model_blks m))
      by exact (ad_model_blks_open m i q pj v Hnone ltac:(fold hs; lia)).
    assert (HSEP' : ablocks_sep B fr_FP cx (ad_open m i q pj v) ly' S').
    { split.
      - exists rest. eapply Permutation_trans; [exact HPERM|]. eapply Permutation_trans; [apply perm_skip; exact HPS|].
        eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
        change ((q, APARTIAL) :: model_blks m ++ rest) with (((q, APARTIAL) :: model_blks m) ++ rest).
        apply Permutation_app_tail. exact (Permutation_sym Hmb').
      - intros b Hb. apply (Permutation_in _ Hmb') in Hb. destruct Hb as [<- | Hb]; [|exact (HSEP2 b Hb)].
        destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (q, APARTIAL)
                    (ablocks B (c_ly cx) (c_S cx))) as [Hin | Hnin]; [right | left; exact Hnin].
        intros a Ha. cbn [fst snd] in Ha.
        pose proof HJ as (_ & _ & (memS0 & HJ0i & _) & _).
        pose proof HJ0i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone0 & _).
        replace a with (q + (a - q)) by lia.
        apply (Hgone0 q APARTIAL (a - q) Hin Hfresh). change (req_size APARTIAL) with 6000 in Ha |- *. lia. }
    apply (FIN (ad_open m i q pj v) HMOD2 HSEP').
    + exact (LS_add_open cx t m i q pj v ly3 S3 ly' S' HLS HRI HAT Hosd HMO HPERM).
    + exact (RI_add_open cx t m i q pj v HRI Ht HAT Hosd Hpj Hv).
    + reflexivity.
  - (* no slot was free: op_add changed nothing outside its frame *)
    destruct HCASE as (-> & -> & -> & HAV). rewrite Hsp1 in HAV.
    assert (KGn : forall a, inG ad_G a -> abyte_kept W m1 W mem' a)
      by (intros a Ha; exact (KG a Ha (ad_none_nwr os a Hfirst))).
    assert (HREL2 : arelay_at B fr_globals ly3 S3 W mem' (lm_G m) (lm_es m)).
    { apply (arelay_at_kept B fr_globals ly3 S3 W m1 ly3 S3 W mem' _ _ HREL).
      - intros r Hr x Hx. unfold arelay_fp in Hr.
        destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Hx.
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_src fr_globals) 8 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_nsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_capsrc fr_globals) 4 x ltac:(ad_in) Hx).
        + replace x with (lm_G m + (x - lm_G m)) by lia.
          apply (KB (lm_G m) ATABLE); [exact HTin | change (req_size ATABLE) with 896; unfold ATABLE in Hx; lia
                                      | exact (HFP0 eq_refl _)].
        + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He). rewrite Forall_forall in HEOK.
          destruct (oa_efp_in B ly3 S3 W m1 e (HEOK e He) r Hr x Hx) as (b & n & Hb & Hbx).
          replace x with (b + (x - b)) by lia. apply (KB b n); [exact Hb | lia | exact (HFP0 eq_refl _)].
      - intros b Hb. exact (proj2 (lt_arelay_x B ARx LAWS BLKN ly3 S3 Hp3 W m1 mdc _ _ HAR1 HREL) b Hb). }
    assert (HLOCK2 : alock_at fr_globals W mem' false).
    { apply (alock_at_kept fr_globals W m1 W mem' false HLOCK). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
      apply KGn. apply HGra. exact (ad_inG_rng (RA_G fr_globals) (rg_lock fr_globals) 12 x ltac:(ad_in) Hx). }
    assert (KNFD : forall x, AG_NFD <= x < AG_NFD + 4 -> abyte_kept W m1 W mem' x)
      by (intros x Hx; apply KGn; apply HGnfd; unfold AG_NFD, A_NFD in *; lia).
    assert (Hev0 : val_mem segs (arm W mem') (as_errno B) 4 (ct_ev (lm_c m))).
    { apply (ad_vm_view W W m1 mem'); [|exact HEV0]. intros x Hx. change (Z.of_nat 4) with 4 in Hx.
      apply HAV; unfold CEIL8, OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK in *; lia. }
    destruct (ERRL ly3 S3 Hp' W mem' md' HAR2) as (_ & Hew0).
    assert (HMOD2 : amodel_at B ly3 S3 W mem' (ad_none m)).
    { unfold ad_none. split; [exact Hlen4|].
      split; [intros j Hj; exact (HSLOT j Hj ltac:(discriminate))|].
      split; [exact HREL2|].
      split; [rewrite <- (ad_set_ev_same (lm_c m)); exact (HOUT2 _ Hev0 Hew0 HEVr)|].
      split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
      split; [apply (akept_vm W m1); [intros x Hx; apply KNFD; change (Z.of_nat 4) with 4 in Hx; lia | exact HNFDv]|].
      split; [apply (akept_awr W m1); [exact KNFD | exact HNFDw]|].
      split; [exact HNFDb|].
      split; [exact HTH2|]. split; [exists lst; exact HLST2 | exact HLSTw2]. }
    apply (FIN (ad_none m) HMOD2 HSEP).
    + exact (LS_add_none cx t m ly3 S3 HLS HRI HAT Hosd).
    + exact (RI_add_none cx t m HRI HAT Hosd).
    + reflexivity.
Qed.

(* CHECK (cut_x's scope): lf_arm_add_xR's type is the Section wR hypothesis ARM_add_R of
   W_LLVMFuzzerTestOneInput_cut_x.v:456, restated with the generic invariants at this Section's variables *)
Lemma lf_arm_add_xR_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 0 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof. exact lf_arm_add_xR. Qed.
(* and cut_x's own composition of the arms at R, lf_arm_xR (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:476), takes it as its ARM_add_R argument *)
Definition lf_arm_add_xR_cut_x :=
  lf_arm_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LSx RINV R lf_arm_add_xR.
End addR.
End add.
