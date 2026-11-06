(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 354 of its 379 lines of code are new or changed and 493 lines of the source are left out. *)
(* The two refuse call sites of cross_check (image A fuzz_segconf.asan), as closed lemmas: at each site the
   loop invariant of cross_check_d.v supplies every premise of refuse_contract (rule 1j-bis), and the facts of
   a cut survive the call.

     refuse_site_ok_89350   jal 0x88da4 at 0x89350, return 0x89354: refuse(c, 0, F_xmodel, s->name, s->model)
     refuse_site_ok_8939c   jal 0x88da4 at 0x8939c, return 0x893a0: refuse(c, 0, F_xbox, s->name)

   Between the loop head 0x892ac and either call the code stores nothing (only loads, ALU and branches), so a
   site lemma is stated over the reader of the loop head itself.

   Also here: the side conditions a call of refuse needs beside refuse_pre (room for its class-0 frame, the
   event budget, the empty frame chain, refuse's footprint inside cross_check's), the shadow facts of the
   block read off AR at the call state, and the transport of a cut's facts across the call.

   No instruction is walked here: every lemma is about the predicates of cross_check_d.v, refuse_c.v and
   SegABase.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c cross_check_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import cross_check_d cross_check_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the offsets of struct reac_segconf as hypotheses lia can use (seg_spec.v:72-93) *)
Local Ltac cc_k :=
  pose proof (eq_refl : seg_spec.SEG_C_SIZE = 16616);
  pose proof (eq_refl : seg_spec.RSEG_SIZE = 356);
  pose proof (eq_refl : seg_spec.RC_REFUSAL = 0x2e88);
  pose proof (eq_refl : seg_spec.RC_REFUSAL_LEN = 200);
  pose proof (eq_refl : seg_spec.RC_NREF = 0x34c8);
  pose proof (eq_refl : seg_spec.RC_REFUSED = 0x34cc);
  pose proof (eq_refl : seg_spec.RC_OVERFLOW = 0x34d0);
  pose proof (eq_refl : seg_spec.RS_MODEL = 0x24).

(* ================= 0. small facts: the register value, the footprint of refuse ================= *)
Lemma cc_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof.
intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* sa_va_arg's length bound: the nat literal 65535 is above the abstraction threshold (abstract-large-number),
   so lia sees it as an atom; compare through a Z.to_nat bound and a closed computation *)
Lemma cc_len_65535 : forall (s : list Z), Z.of_nat (length s) <= 11384 -> (length s <= 65535)%nat.
Proof.
intros s Hs. assert (Hl : (length s <= Z.to_nat 11384)%nat) by lia.
apply (Nat.le_trans _ _ _ Hl). apply Nat.leb_le. vm_compute. reflexivity.
Qed.
(* every byte refuse writes lies in [c + RC_REFUSAL, c + RC_OVERFLOW): refusal[8], n_refusals, refused *)
Lemma refuse_W_in_block : forall c rcs a, inFP (refuse_W c rcs) a ->
  c + seg_spec.RC_REFUSAL <= a < c + seg_spec.RC_OVERFLOW.
Proof.
intros c rcs a (r & Hr & Ha). cc_k. unfold refuse_W in Hr. apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat eqn:E; intros Hr; [|destruct Hr].
  apply Nat.ltb_lt in E.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; [unfold seg_spec.refusal_addr in Ha|]; lia.
Qed.
(* refuse's footprint does not hold the sink token at 0 *)
Lemma refuse_W_pos : forall c rcs, 0 < c -> Forall (fun r => 0 < fst r) (refuse_W c rcs).
Proof.
intros c rcs Hc. cc_k. apply Forall_forall. intros r Hr. unfold refuse_W in Hr.
apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst]. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat; intros Hr; [|destruct Hr].
  destruct Hr as [<- | [<- | []]]; cbn [fst]; [unfold seg_spec.refusal_addr|]; lia.
Qed.
(* the three forbidden ranges of refuse_pre's sa_va_args all lie at or above the end of seg[32] *)
Lemma cc_Wl_ok : forall c (n : nat) lo sp, c + seg_spec.SEG_C_SIZE <= lo ->
  Forall (fun iv => c + 356 * 32 <= fst iv)
    [(lo, sp);
     (seg_spec.refusal_addr c n, seg_spec.refusal_addr c n + seg_spec.RC_REFUSAL_LEN);
     (c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4)].
Proof.
intros c n lo sp H. cc_k.
constructor; [cbn [fst]; lia|].
constructor; [cbn [fst]; unfold seg_spec.refusal_addr; lia|].
constructor; [cbn [fst]; lia|].
constructor.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ================= 1. the block, read off AR at the current state ================= *)
Lemma sa_heap_sub : forall (B : asyms) ly S (q n q' n' : Z),
  sa_heap B ly S q n -> q <= q' -> q' + n' <= q + n -> sa_heap B ly S q' n'.
Proof. intros B ly S q n q' n' (b & m & Hin & Hb & Hm) H1 H2. exists b, m. split; [exact Hin | lia]. Qed.
(* a live heap block lies in [4096, alloc_ceiling): with astk_ok's alloc_ceiling <= ly_stk_lo this is what
   keeps the block, and so every %s argument of a refusal, apart from the stack range of sa_va_args *)
Lemma cc_block_low : forall (B : asyms) ly S (W : world SEGS) mem md (q n : Z),
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n ->
  4096 <= q /\ q + n <= alloc_ceiling.
Proof.
intros B ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ (YG0q.AR_laws_ok SEGS B) ly S W mem md b m HAR Hin)
  as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
split; lia.
Qed.
(* the block's shadow at any state it is live: this is how cross_check_pre's sa_addr comes back after a refuse
   call, refuse's post having no keep clause *)
Lemma cc_block_addr : forall (B : asyms) ly S (W : world SEGS) mem md (q n : Z),
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n ->
  sa_addr (rdW W mem) q n.
Proof.
intros B ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
pose proof alloc_ceiling_lt as Hac.
unfold sa_addr.
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia) Hn0).
Qed.

(* ================= 2. the footprints ================= *)
Lemma cc_FP_in_block : forall (v : ccx) a, inFP (cc_FP v) a ->
  x_c v <= a < x_c v + seg_spec.SEG_C_SIZE.
Proof.
intros v a (r & Hr & Ha). cc_k. unfold cc_FP, cross_check_W in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; lia.
Qed.
(* refuse writes c->refused and, while n_refusals < 8, the slot refusal[n] and c->n_refusals: all inside
   cross_check's own footprint cross_check_W *)
Lemma cc_refuse_FP_sub : forall (v : ccx) (rcs : rconf) a, (length (rc_refusal rcs) <= 8)%nat ->
  inFP (refuse_W (x_c v) rcs) a -> inFP (cc_FP v) a.
Proof.
intros v rcs a _ Hf. apply refuse_W_in_block in Hf.
exists (x_c v + seg_spec.RC_REFUSAL, x_c v + seg_spec.RC_OVERFLOW). split.
- unfold cc_FP, cross_check_W. apply in_cons. apply in_eq.
- cbn [fst snd]. exact Hf.
Qed.

(* ================= 3. the side conditions of a call of refuse ================= *)
(* cross_check owns no side-stack frame, so the frame list at a cut is the entry's and refuse still has room *)
Lemma cc_call_room : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  ly3 S3 W3 regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 ->
  frames S3 = frames (x_S v) /\ sa_room S3 /\ st_nev S3 + EV_refuse <= EV_MAX.
Proof.
intros B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 HP Hfi.
pose proof HP as [_ _ _ _ _ _ _ _ _ _ _ _ Hroom Hnev].
pose proof Hfi as [HJ _ _ _ _ _].
pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev3 & _).
cbn [app] in Hfr.
split; [exact Hfr|]. split.
- unfold sa_room in *. rewrite Hfr. exact Hroom.
- unfold EV_refuse, EV_cross_check in *. lia.
Qed.
(* s0 holds c, a live block below alloc_ceiling, so the frame chain at the call is empty (YCbq.achain_low) *)
Lemma cc_call_chain : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  ly3 S3 W3 regs3 mem3 md3 (regs : bvmap 5 word),
  cc_pre B lit gotw guard STK_REF v ->
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 ->
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 ->
  getr regs 8 = w64 (x_c v) -> 0 <= x_c v < 2 ^ 64 ->
  achain ly3 (rdW W3 mem3) (cc_sp0 v - 128) (s0Z regs) [].
Proof.
intros B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 regs HP Hfi Hun H8 Hc. cc_k.
pose proof Hfi as [HJ _ _ _ _ _]. pose proof HJ as (HAR3 & _).
pose proof Hun as [_ _ _ Hheap3].
destruct (cc_block_low B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3 ltac:(lia)) as [_ Hceil].
apply achain_low. unfold s0Z. rewrite H8, (cc_w64_u (x_c v) Hc). lia.
Qed.

(* ================= 4. the two sites ================= *)
(* what INV_LOOP and cc_pre give a site: AR and the block at the cut, the record, the index bound, and the
   block below the stack *)
Lemma cc_site_facts : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  AR SEGS B ly3 S3 W3 mem3 md3 /\ sa_heap B ly3 S3 (x_c v) seg_spec.SEG_C_SIZE /\
  sa_rconf (rdW W3 mem3) (x_c v) (cc_at v i) /\ 0 <= i < 32 /\
  (Z.to_nat i < length (rc_seg (cc_at v i)))%nat /\
  4096 <= x_c v /\ x_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ alloc_ceiling <= ly_stk_lo ly3.
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI. cc_k.
pose proof HP as [HA _ _ _ _ _ Hrc _ _ _ _ _ _ _].
pose proof HI as (Hfi & Hun & Hi & Hrci & _).
pose proof Hfi as [HJ _ _ _ _ Hnoal].
pose proof Hun as [_ _ _ Hheap3].
pose proof HJ as (HAR3 & _).
destruct (sa_rconf_n _ _ _ Hrc) as (_ & Hn32 & _).
destruct (cc_block_low B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3 ltac:(lia))
  as [H4096 Hceil].
destruct Hnoal as (_ & Hly & _).
pose proof HA as (_ & _ & _ & _ & _ & (_ & _ & Hstk & _) & _).
unfold cc_n in Hi.
split; [exact HAR3|]. split; [exact Hheap3|]. split; [exact Hrci|]. split; [lia|].
split; [unfold cc_at; rewrite cc_fold_len by lia; lia|].
split; [exact H4096|]. split; [exact Hceil|].
rewrite Hly. exact Hstk.
Qed.
(* one %s argument of a refusal that is a C string of seg[0 .. 32): its sa_va_arg ... *)
Lemma cc_str_va : forall (B : asyms) ly S (W : world SEGS) mem md (c : Z) (rcs : rconf) (p : Z) (s : list Z)
  (Wl : list (Z * Z)),
  AR SEGS B ly S W mem md -> sa_heap B ly S c seg_spec.SEG_C_SIZE -> sa_rconf (rdW W mem) c rcs ->
  sa_strz (rdW W mem) p s -> c <= p -> p + Z.of_nat (length s) + 8 <= c + 356 * 32 ->
  Forall (fun iv => c + 356 * 32 <= fst iv) Wl ->
  sa_va_arg (rdW W mem) Wl (w64 p) (AS s).
Proof.
intros B ly S W mem md c rcs p s Wl HAR Hheap Hrc Hstr Hcp Hps HWl. cc_k.
destruct (cc_block_low B ly S W mem md c seg_spec.SEG_C_SIZE HAR Hheap ltac:(lia)) as [H4096 Hceil].
pose proof alloc_ceiling_lt as Hac.
cbn [sa_va_arg]. rewrite (cc_w64_u p) by lia.
split; [lia|].
split.
{ split; [exact Hstr|]. intros x Hx.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
  replace x with (c + (x - c)) by lia.
  apply (sa_rconf_mapped _ c rcs (x - c) Hrc). lia. }
split; [apply cc_len_65535; lia|].
split.
{ apply (cc_block_addr B ly S W mem md); [exact HAR | | lia].
  apply (sa_heap_sub B ly S c seg_spec.SEG_C_SIZE); [exact Hheap | lia | lia]. }
unfold sa_apart_all. eapply Forall_impl; [|exact HWl].
intros iv Hiv. cbv beta in Hiv |- *. left.
pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hm.
unfold seg_spec.cstr_span. lia.
Qed.
(* ... and where it lies (refuse_va_locs: inside the live block c) *)
Lemma cc_str_loc : forall (B : asyms) ly S (W : world SEGS) mem md (c p : Z) (s : list Z),
  AR SEGS B ly S W mem md -> sa_heap B ly S c seg_spec.SEG_C_SIZE -> c <= p ->
  p + Z.of_nat (length s) + 8 <= c + 356 * 32 ->
  sa_heap B ly S (bv_unsigned (w64 p)) (Z.of_nat (length s) + 1) \/
  sa_fframe ly S (bv_unsigned (w64 p)) (Z.of_nat (length s) + 1).
Proof.
intros B ly S W mem md c p s HAR Hheap Hcp Hps. cc_k.
destruct (cc_block_low B ly S W mem md c seg_spec.SEG_C_SIZE HAR Hheap ltac:(lia)) as [H4096 Hceil].
pose proof alloc_ceiling_lt as Hac.
rewrite (cc_w64_u p) by lia. left.
apply (sa_heap_sub B ly S c seg_spec.SEG_C_SIZE); [exact Hheap | lia | lia].
Qed.
(* refuse_pre at a site of pass i, for a format f of cross_check's and the arguments the site hands over *)
Lemma cc_refuse_pre_gen : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3 (regs : bvmap 5 word) (f : list Z) (args : list SegModel.arg) (va : list word),
  cc_pre B lit gotw guard STK_REF v ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  frm0 fx ->
  In f seg_spec.REFUSE_FORMATS -> seg_spec.conv_kinds f = map seg_spec.arg_is_s args ->
  In f CROSS_CHECK_LITS ->
  sa_va_args (rdW W3 mem3)
    [(ly_stk_lo ly3, spZ regs);
     (seg_spec.refusal_addr (x_c v) (length (rc_refusal (cc_at v i))),
      seg_spec.refusal_addr (x_c v) (length (rc_refusal (cc_at v i))) + seg_spec.RC_REFUSAL_LEN);
     (x_c v + seg_spec.RC_REFUSED, x_c v + seg_spec.RC_REFUSED + 4)] va args ->
  refuse_va_locs (fun q n => sa_heap B ly3 S3 q n \/ sa_fframe ly3 S3 q n) va args ->
  refuse_pre SEGS B lit gotw guard ly3 S3 regs (rdW W3 mem3) (x_c v) 0 (lit f) va (cc_at v i) 0 f args.
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs f args va HP HI Hfrm Hf Hk Hfl Hva Hloc.
cc_k.
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & Hheap3 & Hrci & Hi & Hlen & H4096 & Hceil & Hstk).
pose proof HP as [_ _ _ _ Hc0 Hc16 _ _ _ Href _ _ _ _].
pose proof HI as (_ & Hun & _).
pose proof Hun as [_ Hlit Hssp3 _].
pose proof (Hlit f Hfl) as Hlf.
pose proof Hlf as (Hpos & _).
unfold refuse_pre.
split; [exact Hc0|]. split; [exact Hc16|]. split; [exact Hrci|]. split; [exact Hheap3|].
split; [exact (cc_block_addr B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR3 Hheap3 ltac:(lia))|].
split; [unfold cc_at; pose proof (cc_fold_refused (x_rcs v) i ltac:(lia)) as [_ Hr]; lia|].
split; [lia|]. split; [reflexivity|]. split; [exact Hf|]. split; [exact Hk|].
split; [lia|]. split; [reflexivity|]. split; [exact Hlf|]. split; [exact Hva|]. split; [exact Hloc|].
split; [exact Hfrm|]. split; [exact Hssp3|].
intros x Hx. apply Hlit. unfold CROSS_CHECK_LITS. apply in_or_app. right. exact Hx.
Qed.
(* 0x89350, the model-drop arm: a0 = c (s0), a1 = 0, a2 = s2 = F_xmodel, a3 = s4 = &seg[i] = s->name,
   a4 = s6 = s4 + 0x24 = s->model *)
Lemma refuse_site_ok_89350 : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3 (regs : bvmap 5 word),
  cc_pre B lit gotw guard STK_REF v ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  frm0 fx ->
  rs_model_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) = true ->
  rs_role_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) &&
    (rs_role (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) =? 4) = false ->
  getr regs 10 = w64 (x_c v) -> getr regs 11 = w64 0 -> getr regs 12 = w64 (lit F_xmodel) ->
  getr regs 13 = w64 (x_c v + 356 * i) ->
  getr regs 14 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL) ->
  spZ regs = cc_sp0 v - 128 ->
  refuse_pre SEGS B lit gotw guard ly3 S3 regs (rdW W3 mem3) (x_c v) 0 (lit F_xmodel)
    [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17]
    (cc_at v i) 0 F_xmodel
    [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d));
     AS (rs_model (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))].
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs HP HI Hfrm _ _ _ _ _ H13 H14 _. cc_k.
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & Hheap3 & Hrci & Hi & Hlen & H4096 & Hceil & Hstk).
destruct (sa_rconf_fields _ _ _ _ Hrci Hlen) as (Hname & Hnl & Hmodel & Hml & _).
rewrite Z2Nat.id in Hname, Hmodel by lia.
apply (cc_refuse_pre_gen B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs F_xmodel);
  [exact HP | exact HI | exact Hfrm | | | | |].
- unfold seg_spec.REFUSE_FORMATS. do 15 apply in_cons. apply in_eq.
- cbn [map seg_spec.arg_is_s]. vm_compute. reflexivity.
- unfold CROSS_CHECK_LITS. apply in_or_app. left. apply in_eq.
- cbn [sa_va_args]. rewrite H13, H14. split; [|split; [|exact I]].
  + apply (cc_str_va B ly3 S3 W3 mem3 md3 (x_c v) (cc_at v i));
      [exact HAR3 | exact Hheap3 | exact Hrci | exact Hname | lia | lia | apply cc_Wl_ok; lia].
  + apply (cc_str_va B ly3 S3 W3 mem3 md3 (x_c v) (cc_at v i));
      [exact HAR3 | exact Hheap3 | exact Hrci | exact Hmodel | lia | lia | apply cc_Wl_ok; lia].
- cbn [refuse_va_locs]. rewrite H13, H14. split; [|split; [|exact I]].
  + apply (cc_str_loc B ly3 S3 W3 mem3 md3 (x_c v)); [exact HAR3 | exact Hheap3 | lia | lia].
  + apply (cc_str_loc B ly3 S3 W3 mem3 md3 (x_c v)); [exact HAR3 | exact Hheap3 | lia | lia].
Qed.
(* 0x8939c, the box arm: a0 = c, a1 = 0, a2 = [sp + 0x10] = F_xbox, a3 = s4 = s->name; a4 is left over and the
   format reads one %s, so refuse_pre's argument list has one entry *)
Lemma refuse_site_ok_8939c : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx) (i : Z)
  ly3 S3 W3 regs3 mem3 md3 (regs : bvmap 5 word),
  cc_pre B lit gotw guard STK_REF v ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  frm0 fx ->
  rs_model_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) = false ->
  rs_role_set (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) &&
    (rs_role (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d) =? 4) = true ->
  getr regs 10 = w64 (x_c v) -> getr regs 11 = w64 0 -> getr regs 12 = w64 (lit F_xbox) ->
  getr regs 13 = w64 (x_c v + 356 * i) ->
  spZ regs = cc_sp0 v - 128 ->
  refuse_pre SEGS B lit gotw guard ly3 S3 regs (rdW W3 mem3) (x_c v) 0 (lit F_xbox)
    [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17]
    (cc_at v i) 0 F_xbox
    [AS (rs_name (nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d))].
Proof.
intros B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs HP HI Hfrm _ _ _ _ _ H13 _. cc_k.
destruct (cc_site_facts B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 HP HI)
  as (HAR3 & Hheap3 & Hrci & Hi & Hlen & H4096 & Hceil & Hstk).
destruct (sa_rconf_fields _ _ _ _ Hrci Hlen) as (Hname & Hnl & _).
rewrite Z2Nat.id in Hname by lia.
apply (cc_refuse_pre_gen B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs F_xbox);
  [exact HP | exact HI | exact Hfrm | | | | |].
- unfold seg_spec.REFUSE_FORMATS. do 16 apply in_cons. apply in_eq.
- cbn [map seg_spec.arg_is_s]. vm_compute. reflexivity.
- unfold CROSS_CHECK_LITS. apply in_or_app. left. apply in_cons. apply in_eq.
- cbn [sa_va_args]. rewrite H13. split; [|exact I].
  apply (cc_str_va B ly3 S3 W3 mem3 md3 (x_c v) (cc_at v i));
    [exact HAR3 | exact Hheap3 | exact Hrci | exact Hname | lia | lia | apply cc_Wl_ok; lia].
- cbn [refuse_va_locs]. rewrite H13. split; [|exact I].
  apply (cc_str_loc B ly3 S3 W3 mem3 md3 (x_c v)); [exact HAR3 | exact Hheap3 | lia | lia].
Qed.

(* ================= 5. what survives the call ================= *)
(* cross_check's own 128-byte frame lies above refuse's entry sp, so the 13 saved slots and the two spills
   come back unchanged *)
Lemma cc_own_frame_kept : forall (B : asyms) (STK_REF : Z) (v : ccx) ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4
  (rcs : rconf) k,
  0 <= STK_REF ->
  ajournal SEGS B STK_REF (cc_sp0 v - 128) (refuse_W (x_c v) rcs) ly3 S3 W3 mem3 md3 []
    ly4 S4 W4 mem4 md4 k ->
  (forall a, inFP (refuse_W (x_c v) rcs) a -> x_c v <= a < x_c v + seg_spec.SEG_C_SIZE) ->
  (forall a, x_c v <= a < x_c v + seg_spec.SEG_C_SIZE -> ~ (cc_sp0 v - 128 <= a < cc_sp0 v)) ->
  forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W4 mem4 a = rdW W3 mem3 a.
Proof.
intros B STK_REF v ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 rcs k HSTK HJ HFP HNO a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hlo & Hhi & H47 & _).
apply F1.
- lia.
- lia.
- intros Hf. exact (HNO a (HFP a Hf) Ha).
Qed.
(* the facts of a cut (read-only bytes, literals, the stack-protector cells, the block live) after the call.
   Two image facts no premise of the cut carries: the read-only window [SEG_RLO, SEG_RHI) lies in the image (the
   journal keeps an image byte, and nothing else of that window), and the stack-protector cells hold at every
   AR state (the record pins them; the journal does not keep a byte refuse may write, and gotw and guard are
   free here). Image A gives both from its per-binary facts (SegRecBase cif_relro_img, SegRecCells
   seg_rec_cells), as fuzz_command's walk does (chain_words_d.v cw_ro_imgP, CmdRecCells cmd_rec_cells). *)
Lemma cc_un_after : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z) (v : ccx)
  ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 (rcs : rconf) k,
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotw guard) ->
  cc_pre B lit gotw guard STK_REF v ->
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 ->
  (length (rc_refusal rcs) <= 8)%nat ->
  ajournal SEGS B STK_REF (cc_sp0 v - 128) (refuse_W (x_c v) rcs) ly3 S3 W3 mem3 md3 []
    ly4 S4 W4 mem4 md4 k ->
  cc_un B lit gotw guard STK_REF v ly4 S4 W4 mem4.
Proof.
intros B lit gotw guard STK_REF v ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 rcs k HRO HSSP _ Hun _ HJ. cc_k.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof Hun as [Hrod Hlit _ Hheap3].
pose proof HJ as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & F5 & _).
destruct Hheap3 as (b & m & Hin3 & Hb & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
(* the block is still live: else every byte of it, c among them, would be in refuse's footprint *)
assert (Hin4 : In (b, m) (ablocks B ly4 S4)).
{ destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (b, m) (ablocks B ly4 S4))
    as [Hy4|Hn4]; [exact Hy4|].
  exfalso. pose proof (F5 b m (x_c v - b) Hin3 Hn4 ltac:(lia)) as Hf.
  replace (b + (x_c v - b)) with (x_c v) in Hf by lia.
  apply refuse_W_in_block in Hf. lia. }
assert (Hheap4 : sa_heap B ly4 S4 (x_c v) seg_spec.SEG_C_SIZE) by (exists b, m; split; [exact Hin4 | lia]).
destruct (cc_block_low B ly4 S4 W4 mem4 md4 (x_c v) seg_spec.SEG_C_SIZE HAR4 Hheap4 ltac:(lia)) as [H4096 _].
(* an image byte the runtime does not own and that is not errno keeps its value: refuse's footprint is inside
   the block, whose bytes are no image bytes *)
assert (KI : forall y, in_img SEGS y -> ~ Exists (in_zr y) (as_owned_static B) ->
  ~ (as_errno B <= y < as_errno B + 4) -> rdW W4 mem4 y = rdW W3 mem3 y).
{ intros y Hi Ho He. apply (F3 y Hi Ho He). apply fp_spares_closed.
  - apply sink_closed_pos. apply refuse_W_pos. lia.
  - intros Hf. apply refuse_W_in_block in Hf.
    exact (blk_img SEGS B LAWS ly4 S4 W4 mem4 md4 b m y HAR4 Hin4 ltac:(lia) Hi). }
constructor.
- intros a Hro Ho He.
  assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (HRO a Hr)]. }
  rewrite (KI a Hi Ho He). exact (Hrod a Hro Ho He).
- intros x Hx. destruct (Hlit x Hx) as (Hpos & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
  split; [exact Hpos|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
  split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W4) mem4 _ Hrom)].
  intros j Hj. rewrite <- (Hzs j Hj).
  rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Himg (lit x + Z.of_nat j) ltac:(lia)) as (Hi & Ho & He).
  exact (KI _ Hi Ho He).
- exact (HSSP ly4 S4 W4 mem4 md4 HAR4).
- exact Hheap4.
Qed.
End f.
End d.
