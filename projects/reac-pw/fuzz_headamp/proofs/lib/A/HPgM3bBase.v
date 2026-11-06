(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95be for
   reac-pw/fuzz_rate's image A: role's pcs (C3 0x820c4, the memcpy return 0x820e4, the parse return 0x8210c, E
   0x8212c, MAL 0x823fc, T 0x82408) become rate's (0x828b8, 0x828dc, 0x8290c, E 0x82930, MAL 0x82c9c, A 0x82ca8);
   the registers are renamed as rate's code has them (pod s2 -> s6, &cell s6 -> s5 = &hz, flags & 1 s4 -> s3, the
   frame's shadow base s3 -> s4, the shadow offset s7 -> s2, len s8 -> s10, pp + 0x4d18 s10 -> s9); F is read from
   the cell R+0x78 (blocks A and C: a read-only region at R), the hz cell takes the 4-byte 0x5a5a5a5a, block B also
   stores pod into R+0x138 (a writable window of the region at R) and reloads the flags byte into s10; the memcpy call
   is lib/A/RtPgSteps.v rts_intrin_at (role's hd_memcpy dropped), the .rodata zone is [0x10000, 0x22000), the cut file
   is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_, the role cell -> rs_hz_at, the frame pattern at the exits rs_PZ), the
   entry-state and list lemmas come from lib/A/RtPgScanKit.v and the memory facts from lib/A/RtPgMem.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgScanHead.v, with its module paths and module names changed; 189 of its 245 lines of code are new or changed and 975 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanF.v (rk_skipn_cons, rk_pairs_skip,
   rk_pairs_run, rk_pairs_last) and proofs/reac-pw/fuzz_role/lib/A/RPgScanOuter.v and RPgScanInner.v
   (ro_post, ro_post_intro, ro_at_get, ro_at_sub, ro_at_keep, ro_chk_base, ro_denot0, ro_bge and the run tactics) at
   e39c26ea588; module paths fuzz_role -> fuzz_headamp, the rk_ / ro_ / si_ prefixes -> hb_, the cut lists and the
   cut base restated over headamp's lib/A/HPgSeg.v and HPgSegM.v (hs_at, hq_base3), the record facts restated over
   headamp's fold (Pod/Headamp.v ha_fold) instead of role's role_of_pairs. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): THE SHARED STEPS of the
   four pair-loop pieces of segment M03 of LLVMFuzzerTestOneInput (lib/A/HPgSegM.v hq_piece_M3b_pair_stmt,
   hq_piece_M3b_scan_stmt, hq_piece_M3b_latch_stmt, hq_piece_M3b_refuse_stmt). Proves no function (kind: segment
   lemma): the facts of the shared model the pair loop moves its invariant by, the reading and keeping of a cut's
   (location, value) list, the cut base at a state that differs from a cut's only in its registers and its
   I/O-equal model, and the block post every no-store block of the four pieces ends in.

   THE MODEL. pod_next_pair (pod.h:124-145) is Pod/Accessors.v pairs_by key_of: an entry that is not a String key
   is skipped, a key takes the slot, and the entry after a key is its value. The pair loop keeps
   HPgSegM.hq_fold_inv (the fold of the pairs from index j over what x holds is expect_of's answer). An entry that
   is not a key moves the scan's start without changing the pairs (hb_pairs_run); with no entry left, or with the
   last entry reached, no pair is left and the fold is the identity (hb_fold_end, hb_fold_last); a refused pair
   counts its key and keeps the first refusal (hb_fold_refuse). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ the pairs of the record's entries ================================ *)
Lemma hb_skipn_cons : forall {A : Type} (l : list A) (j : nat) (d : A), (j < length l)%nat ->
skipn j l = nth j l d :: skipn (S j) l.
Proof.
intros A l. induction l as [|x l IH]; intros j d Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hj. lia.
Qed.

Lemma hb_pairs_skip : forall (es : list ent) (m : nat), (m < length es)%nat ->
key_of (nth m es (Ent 0 0 [])) = None ->
pairs_by key_of (skipn m es) None = pairs_by key_of (skipn (S m) es) None.
Proof.
intros es m Hm Hk. rewrite (hb_skipn_cons es m (Ent 0 0 []) Hm). cbn [pairs_by]. rewrite Hk. reflexivity.
Qed.

Lemma hb_pairs_run : forall (es : list ent) (a m : nat), (a <= m)%nat -> (m <= length es)%nat ->
(forall q, (a <= q < m)%nat -> key_of (nth q es (Ent 0 0 [])) = None) ->
pairs_by key_of (skipn a es) None = pairs_by key_of (skipn m es) None.
Proof.
intros es a m. remember (m - a)%nat as n eqn:Hn. revert a m Hn.
induction n as [|n IH]; intros a m Hn Ham Hml Hq.
- assert (a = m) as -> by lia. reflexivity.
- rewrite (hb_pairs_skip es a ltac:(lia) (Hq a ltac:(lia))).
  apply (IH (S a) m); [lia | lia | lia |]. intros q Hqq. apply Hq. lia.
Qed.

Lemma hb_pairs_last : forall (es : list ent) (m : nat), (m < length es)%nat -> (length es <= S m)%nat ->
pairs_by key_of (skipn m es) None = [].
Proof.
intros es m H1 H2. rewrite (hb_skipn_cons es m (Ent 0 0 []) H1). cbn [pairs_by].
rewrite skipn_all2 by exact H2. destruct (key_of (nth m es (Ent 0 0 []))); reflexivity.
Qed.

(* one refused pair: its key is counted and the first refusal is kept (Pod/Headamp.v ha_fold) *)
Lemma hb_ha_fold_bad : forall cap k v rest cs keys rf bad, ha_prefix k = true -> expect_cell k v = inl bad ->
ha_fold expect_cell cap ((k, v) :: rest) cs keys rf =
ha_fold expect_cell cap rest cs (keys + 1) (if rf =? REFUSE_NONE then bad else rf).
Proof. intros cap k v rest cs keys rf bad Hp He. cbn [ha_fold]. rewrite Hp, He. reflexivity. Qed.

(* ================================ the pair loop's invariant (HPgSegM.hq_fold_inv) ================================ *)
(* the loop runs only on a live record, where expect_of's rc is the number of cells *)
Lemma hb_exp_rc : forall (cx : hs_scx rsegs) r, hq_live rsegs cx r ->
ans_rc (hq_exp rsegs cx r) = Z.of_nat (length (ans_cells (hq_exp rsegs cx r))).
Proof.
intros cx r (Hn & _ & Hp & Hs).
assert (E1 : (e_null (x_e cx) =? 1) = false) by (rewrite Hn; reflexivity).
unfold hq_exp, expect_model. rewrite E1, Hp, Hs. cbn [orb negb].
destruct (ha_fold _ _ _ _ _ _) as [[c k] f]. reflexivity.
Qed.

(* no entry is left: x holds expect_of's answer *)
Lemma hb_fold_end : forall (cx : hs_scx rsegs) r j cs keys rf,
hq_fold_inv rsegs cx r j cs keys rf -> (length (ents r) <= j)%nat ->
cs = ans_cells (hq_exp rsegs cx r) /\ keys = ans_keys (hq_exp rsegs cx r) /\ rf = ans_rf (hq_exp rsegs cx r).
Proof.
intros cx r j cs keys rf H Hj. unfold hq_fold_inv in H. rewrite skipn_all2 in H by exact Hj.
cbn [pairs_by ha_fold] in H. unfold hq_fin in H. injection H as E1 E2 E3. auto.
Qed.

(* the scan reached the last entry, with no key since its start: no pair is left either *)
Lemma hb_fold_last : forall (cx : hs_scx rsegs) r at0 m cs keys rf,
hq_fold_inv rsegs cx r at0 cs keys rf -> (at0 <= m)%nat ->
(m < length (ents r))%nat -> (length (ents r) <= S m)%nat ->
(forall q, (at0 <= q < m)%nat -> key_of (nth q (ents r) (Ent 0 0 [])) = None) ->
cs = ans_cells (hq_exp rsegs cx r) /\ keys = ans_keys (hq_exp rsegs cx r) /\ rf = ans_rf (hq_exp rsegs cx r).
Proof.
intros cx r at0 m cs keys rf H Ham Hm Hs Hq. unfold hq_fold_inv in H.
rewrite (hb_pairs_run (ents r) at0 m Ham ltac:(lia) Hq), (hb_pairs_last (ents r) m Hm Hs) in H.
cbn [ha_fold] in H. unfold hq_fin in H. injection H as E1 E2 E3. auto.
Qed.

(* a refused pair moves the invariant past its value *)
Lemma hb_fold_refuse : forall (cx : hs_scx rsegs) r m k v bad cs keys rf,
hq_pair_inv rsegs cx r m k v cs keys rf -> expect_cell k v = inl bad ->
hq_fold_inv rsegs cx r (S (S m)) cs (keys + 1) (if rf =? REFUSE_NONE then bad else rf).
Proof.
intros cx r m k v bad cs keys rf (_ & Hp & _ & Hf) He. unfold hq_fold_inv.
rewrite <- (hb_ha_fold_bad _ k v _ cs keys rf bad Hp He). exact Hf.
Qed.

(* ================================ the cut lists ================================ *)
(* a register fact of a list *)
Lemma hb_at_get : forall H mem regs e L r v, hs_at rsegs H mem regs e L -> In (LReg r, v) L ->
getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. unfold hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
(* a cell fact of a list *)
Lemma hb_at_cell : forall H mem regs e L b o v, hs_at rsegs H mem regs e L -> In (LCell b o, v) L ->
val_mem rsegs (mrestrict H mem) (hd_xv e b + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L b o v HL Hin. unfold hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
(* a sub-list of a list of facts *)
Lemma hb_at_sub : forall H mem regs e L L', hs_at rsegs H mem regs e L -> (forall x, In x L' -> In x L) ->
hs_at rsegs H mem regs e L'.
Proof.
intros H mem regs e L L' HL Hs. unfold hs_at in *. rewrite Forall_forall in *. intros x Hx. exact (HL x (Hs x Hx)).
Qed.
(* a list whose registers all lie in kept holds at a register file that agrees on kept (the list comes first, so
   that a caller's `ltac:(vm_compute; reflexivity)` for the forallb sees it) *)
Definition hb_locb (kept : list (bv 5)) (f : hd_loc * Z) : bool :=
match fst f with LReg r => existsb (fun c => bv_eqb c (Z_to_bv 5 r)) kept | LCell _ _ => true end.
Lemma hb_at_keep : forall H mem regs e L, hs_at rsegs H mem regs e L ->
forall regs' (kept : list (bv 5)),
(forall r, In r kept -> getr regs' r = getr regs r) -> forallb (hb_locb kept) L = true ->
hs_at rsegs H mem regs' e L.
Proof.
intros H mem regs e L HL regs' kept Hk Hb. unfold hs_at in *. rewrite Forall_forall in *.
intros [[r|b o] v] Hx. 2:{ exact (HL _ Hx). }
pose proof (HL _ Hx) as Hv. cbn [hd_at fst snd] in Hv |- *.
pose proof (proj1 (forallb_forall _ _) Hb _ Hx) as Hl. unfold hb_locb in Hl. cbn [fst] in Hl.
apply existsb_exists in Hl as (c & Hc & Hcb). apply bv_eqb_eq in Hcb. subst c.
rewrite (Hk _ Hc). exact Hv.
Qed.
Lemma hb_at_app : forall H mem regs e L1 L2,
hs_at rsegs H mem regs e (L1 ++ L2) <-> hs_at rsegs H mem regs e L1 /\ hs_at rsegs H mem regs e L2.
Proof. intros H mem regs e L1 L2. unfold hs_at. apply Forall_app. Qed.

(* membership in M03's concrete lists of facts *)
Ltac hb_unf := unfold hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_loopr, hq_L_scan, hq_L_body.
Ltac hb_in := hb_unf; cbv zeta; cbn [In app]; repeat (first [left; reflexivity | right]).
(* a list of facts that is a sub-list of a hypothesis' *)
Ltac hb_sub HL :=
apply (hb_at_sub _ _ _ _ _ _ HL);
let y := fresh "y" in let Hy := fresh "Hy" in
intros y Hy; hb_unf; cbv zeta in Hy |- *; cbn [In app] in Hy |- *;
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.
(* membership in a kept-register list map (Z_to_bv 5) [...] *)
Ltac hb_kin := apply in_map; cbn [In]; lia.

(* ================================ the cut base ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* what the pieces read of the segment's start *)
Lemma hb_start_wf : forall (cx : hs_scx rsegs) r ev, @hq_start_M03 fx rc SK rsegs B cx r ev -> pod_rec_wf r.
Proof. intros cx r ev HS. pose proof HS as (_ & _ & Hw & _). exact Hw. Qed.
Lemma hb_start_pre : forall (cx : hs_scx rsegs) r ev, @hq_start_M03 fx rc SK rsegs B cx r ev ->
hs_pre rsegs B cx (hi_shA headamp_himg_A).
Proof. intros cx r ev HS. exact (proj1 HS). Qed.
(* the real frame lies in the stack, below 2^47 *)
Lemma hb_start_R : forall (cx : hs_scx rsegs) r ev, @hq_start_M03 fx rc SK rsegs B cx r ev ->
0 < e_R (x_e cx) /\ e_R (x_e cx) + 0x1e0 <= 2 ^ 47 /\ e_R (x_e cx) mod 32 = 0.
Proof.
intros cx r ev HS. pose proof (hb_start_pre cx r ev HS) as Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & HeS & HRal & HRS & HstkR & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof (@alloc_ceiling_val rc) as [[Hc0 _] _].
pose proof hq_pcs_himg as (_ & _ & _ & _ & _ & _ & Hrsz). rewrite Hrsz in HRS. unfold HQ_RSZ in HRS.
unfold T_SEG_STK, ASTACK in *. lia.
Qed.
(* the pp block, live at the segment's start: 16-aligned, above the first page, below the allocation ceiling *)
Lemma hb_start_pp : forall (cx : hs_scx rsegs) r ev, @hq_start_M03 fx rc SK rsegs B cx r ev ->
In (e_pp (x_e cx), PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
e_pp (x_e cx) mod 16 = 0 /\ 4096 <= e_pp (x_e cx) /\ e_pp (x_e cx) + PP_SIZE <= alloc_ceiling /\
alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
intros cx r ev HS. pose proof (hb_start_pre cx r ev HS) as Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfresh).
destruct Hfresh as (_ & Hin & _). destruct HJ as (HAR & _).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) _ _ HAR Hin)
  as (Hal & Hp4k & Hpc & _).
assert (Hrq : req_size PP_SIZE = PP_SIZE) by reflexivity. rewrite Hrq in Hpc.
pose proof (@alloc_ceiling_val rc) as [[_ Hc1] _].
split; [exact Hin|]. split; [exact Hal|]. split; [exact Hp4k|]. split; [exact Hpc|]. lia.
Qed.

(* the checks' base at a state that differs from a cut's only in its registers and its I/O-equal model *)
Lemma hb_base3_regs : forall (cx : hs_scx rsegs) (fx2 : YK11.FPState) r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem2 md3 (x_k cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 md3 (Hcore & Hrest) HJ3 Hio3 H234'.
split; [|exact Hrest].
unfold hs_core, hs_mid in Hcore |- *.
destruct Hcore as (_ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
split; [exact HJ3|].
split; [intros q Hq; rewrite (H234' q Hq); exact (H234 q Hq)|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo | exact Hkeep].
Qed.

(* ================================ the block post ================================ *)
(* the state at a block's end pc, for a block that stores nothing: the world, the journal and the memory as at the
   block's start, the I/O state, the kept registers, and R *)
Definition hb_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (kept : list (bv 5))
(R : bvmap 5 word -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r, In r kept -> getr regs2 r = getr regs r) /\ R regs2.

Lemma hb_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept
(R : bvmap 5 word -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc -> ms_mem ms = memc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md' k -> same_io mdc md' ->
(forall r, In r kept -> getr (ms_regs ms) r = getr regs r) -> R (ms_regs ms) ->
hb_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept R W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc kept R E' ss' ms md' HS Hrv Hpc Hm HJ Hio Hk HR.
split; [reflexivity|]. exists (ms_regs ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc, Hm; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk | exact HR].
Qed.
End b.

(* ================================ arithmetic ================================ *)
Lemma hb_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma hb_blt : forall j n, 0 <= j < 2 ^ 63 -> 0 <= n < 2 ^ 63 ->
branch_taken BC_LT (Z_to_bv 64 j) (Z_to_bv 64 n) = (j <? n).
Proof.
intros j n Hj Hn. rewrite YO0c.branch_lt, !unsigned_lit_small by lia.
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
(* an 8-byte real-frame cell as a region chunk over an extra atom *)
Lemma hb_slot_chunk : forall {fx : YK11.FPState} E H mem R o v (n : nat), ew E n = Z_to_bv 64 v ->
val_mem rsegs (mrestrict H mem) (R + o) 8 (v mod 2 ^ 64) ->
YP09.chunk_ok rsegs E (mrestrict H mem) R (YP09.mkChunk o (CVal 8 (SOff n 0))).
Proof.
intros fx E H mem R o v n Hn Hv.
apply (chunk_ok_val rsegs E _ R o 8 (SOff n 0) (v mod 2 ^ 64)); [| | lia | exact Hv].
- rewrite hb_denot0, Hn. symmetry. apply HPgSteps.Z_to_bv_mod64.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
Qed.

(* ================================ the run tactics (role's si_ tactics) ================================ *)
(* the memory after a run over read-only regions is the memory at the block's start *)
Ltac hb_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hb_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply HPgSteps.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac hb_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
(* the registers of a kept list keep their value *)
Ltac hb_kept kept :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict _ ms) rg ex0 kept HS HAE
    ltac:(vm_compute; reflexivity) r Hr) end.
(* the post of a block's arm, after hb_mem *)
Ltac hb_post_intro B kept :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HM : ms_mem ?ms = _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rewrite HM in HJ;
  eapply (hb_post_intro B); [exact HS | reflexivity | reflexivity | exact HM | exact HJ | hb_io | hb_kept kept | ] end.
