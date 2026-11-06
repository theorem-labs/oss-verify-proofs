(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SCAN and SCANS segments of the ASan walk of fuzz_reply's relay_remove
   (lib/A/W_relay_remove_cx.v: rr_scan_stmt, rr_scans_stmt): the scan loop 0x83f14 -> {0x83f48 | 0x83fc4}.

   Where each part comes from (the retired lane form: commit 2ad36763b22, lib/A/Prog/relay_remove_*.v):
   - rrs_nth_le_bytes, rrs_garr8_le: copied from lib/A/W_gestures_end.v gse_nth_le_bytes / gse_garr8_le.
   - rrs_concat_split: the lane's rrA_concat_split (relay_remove_stg.v:172-180), verbatim.
   - rrs_eb_len, rrs_concat_len: the lane's rrA_entry_len (relay_remove_stg.v:182-186) and the length step of
     rrA_entry_cell (:197-199).
   - rrs_fd_cell: the lane's rrA_fd_cell (relay_remove_stg.v:221-241), restated over atable_at's garr8.
   - rr_scan (one step of the loop): the lane's rrA_iter / rrA_iter_tail / rrA_idisp (relay_remove_seg.v:477-581).
     Ported: the shadow pointer arithmetic (AD3, seg.v:557-559: (G0 + 56 k) / 8 = G0 / 8 + 7 k) and the three
     ends of one iteration with their registers.  New: the symbolic state at 0x83f14 (the form of
     W_check_bounded.v cb_loopX; the slot address made one atom by the alias fact of W_gestures_end.v gl_facts), so
     the shadow check takes the fast path and the report arm 0x83f38 .. 0x83f44 is never reached; the cut
     predicates' bookkeeping (RRL / RRM / RRU of W_relay_remove_cx.v) is new.
   - rr_scans: the lane's rrA_scan_fuel (relay_remove_stg.v:77-124), induction on |es| - k; with the
     continuations of rr_scan_stmt the lane's first-match / none-in-[k,n) merge is not needed.
   - the no-match exit's `forall e, In e es -> re_fd e <> FD`: the lane's argument by In_nth
     (relay_remove_p_bc.v:1586-1589). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (a Theorem Labs lane, lane RR_x): SCAN / SCANS over ARx (Section c is
   W_relay_remove_cx.v's generic block); the scan writes nothing and calls nothing, so RHELD (with its room budget and
   count fact) passes through unchanged.  The four helpers RIG cites (regs_ok_same, rrs_concat_len, rrs_concat_split,
   rrs_garr8_le) keep their statements. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ byte lists *)
Lemma rrs_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma rrs_concat_split : forall {X : Type} (f : X -> list byte) (l : list X) (d : X) (i : nat),
  (i < length l)%nat ->
  concat (map f l) = concat (map f (firstn i l)) ++ f (nth i l d) ++ concat (map f (skipn (S i) l)).
Proof.
  intros X f l d. induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [firstn skipn nth map concat].
  - reflexivity.
  - rewrite (IH i ltac:(cbn [length] in Hi; lia)) at 1. cbn [map concat]. rewrite app_assoc. reflexivity.
Qed.
Lemma rrs_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
intros e P1 P2. unfold entry_bytes.
rewrite !length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, P1, P2. reflexivity.
Qed.
Lemma rrs_concat_len : forall l, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
induction l as [|e l IH]; intros HF; [reflexivity|].
apply Forall_cons_iff in HF as [[P1 P2] HF]. cbn [map concat length]. rewrite length_app, (rrs_eb_len e P1 P2), (IH HF). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Lemma rrs_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, rrs_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.

(* entry k's fd field: the first 4 bytes of its 56 at G + 56 k *)
Lemma rrs_fd_cell : forall M G es tail k,
  garr8 SEGS M G (bzs (concat (map entry_bytes es) ++ tail)) ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (k < length es)%nat -> 0 <= re_fd (nth k es relay_remove_b_c.no_entry) < 2 ^ 31 ->
  val_mem SEGS M (G + AENT * Z.of_nat k) 4 (re_fd (nth k es relay_remove_b_c.no_entry)).
Proof.
intros M G es tail k Hg HF Hk Hfd.
rewrite (rrs_concat_split entry_bytes es relay_remove_b_c.no_entry k Hk) in Hg.
unfold bzs in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [Hg _]. apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
assert (HF1 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (firstn k es)).
{ rewrite <- (firstn_skipn k es) in HF. apply Forall_app in HF as [HF1 _]. exact HF1. }
rewrite length_map, (rrs_concat_len _ HF1), length_firstn in Hg.
replace (Nat.min k (length es)) with k in Hg by lia.
unfold entry_bytes in Hg. rewrite map_app in Hg. apply garr8_app in Hg as [Hg _].
unfold AENT. replace (G + 56 * Z.of_nat k) with (G + Z.of_nat (56 * k)) by lia.
apply rrs_garr8_le; [|lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

(* ------------------------------------------------------------------ the loop head 0x83f14 *)
(* a1 = G0 (atom 11), a2 = 56 |es| (12), a3 = SB + (X >> 3) (13), s3 = fd (19), s6 = SB (22), s8 = 56 k (24);
   atom 32 = X = G0 + 56 k (entry k), atom 33 = entry k's fd; the alias a1 + s8 = X makes the address of the fd
   load one atom, and the shadow entry over X's first 8 bytes takes the check's fast path. *)
Definition RRS_PHI : Z := 140737479966720.
Definition BxS : sv := SOff 22 0.
Definition rrs_sr : list sv := sr_set sr_atoms 13 (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3))).
Definition rrs_regions : smem := [ YP09.mkRegion (Some 32%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))] ].
Definition rrs_facts : facts :=
mkFacts [ (22%nat, mkAF SB SB 0); (32%nat, mkAF 4096 RRS_PHI 3); (33%nat, mkAF 0 (2 ^ 31 - 1) 0) ] []
  [ (SAlu ALU_ADD (SOff 11 0) (SOff 24 0), SOff 32 0) ].
Definition ss_rrs : sstate := mkSS A_rr_scan rrs_sr rrs_regions None rrs_facts.
Definition rrs_SH : list shent := [ mkSHE 32 0 8 ].
Definition rrs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rrs_extra (x fd : Z) : list word := map (Z_to_bv 64) [x; fd].
Definition RRS_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 11; 12; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.

(* a run over the read-only slot region leaves the memory as it was (W_LLVMFuzzerTestOneInput_cut.v jt_mem) *)
Ltac rrs_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL): K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x, blk_off_imgP_x), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x83ee8 (s7, listing A_HI 59) and 0x83ef8 (s9, A_HI 60).
   The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges both by
   vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH59 : VAL (A_HI 59) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH60 : VAL (A_HI 60) = rg_src RG + RR_HI_SRC.
(* g_wake[1], read at 0x83fe0 by PLdHi (A_OBJ 4) (W5's HV4, verbatim) *)
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal.v ajournal_gx_rom_view) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the live-state meter does not see the fake frame: its seat and its release are set_fs steps (W8's ruling, the
   lead's KF-COUNT #4: the ablocks form is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v / W_journal.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls (W7's drain, W4's gestures_end), by their published _x specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x83f94 with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (W_relay_finish_h.v's PSTR / PSTC form). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* SCANS: the loop by induction on |es| - k (the lane's rrA_scan_fuel). *)
Theorem rr_scans : rr_scans_stmt B PST ARx MT RP MMAX RG.
Proof.
unfold rr_scans_stmt. intros SCAN cx k W1 c1 HB HL KM KU.
remember (length (rxes cx) - k)%nat as d eqn:Hd. revert k W1 c1 Hd HL.
induction d as [|d IH]; intros k W1 c1 Hd HL.
- exfalso. destruct HL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
- apply (SCAN cx k W1 c1 HB HL).
  + intros W2 c2 HL2. apply (IH (S k) W2 c2); [lia | exact HL2].
  + intros W2 c2 HM. exact (KM k W2 c2 HM).
  + exact KU.
Qed.

Theorem rr_scan : rr_scan_stmt B PST ARx MT RP MMAX RG.
Proof.
unfold rr_scan_stmt. intros cx k W1 c1 HB HL KL KM KU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & _ & _ & HFDr & _).
destruct HL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & -> & HRH & H25 & H11 & H12 & H13 & H24 & HFD0 & Hk & Hpre & HH).
pose proof HH as (HLV & HREL & _).
pose proof HLV as (fpos & HJ & HLVr).
pose proof HREL as (_ & _ & _ & _ & _ & _ & Rlen & RIn & (tail & _ & _ & Rtab) & Rok & _).
pose proof HRH as ((Hsp & H3 & H4 & H8 & H9 & H18 & H20 & H21 & H22 & H26 & H27) & H19 & H23).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR RIn) as (HP16 & HP4096 & HPceil & HPh_ia & _ & _).
pose proof (proj1 HPh_ia) as HPh.
change (req_size ATABLE) with 896 in HPceil, HPh_ia, HPh.
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
assert (Hfdk : 0 <= re_fd (rnth cx k) < 2 ^ 31).
{ rewrite Forall_forall in Rok. destruct (Rok _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hk)) as (_ & _ & _ & _ & Hr & _).
  exact Hr. }
pose proof (rrs_fd_cell (arm W1 m1) (rxG0 cx) (rxes cx) tail k Rtab Hok Hk Hfdk) as Mfd.
assert (G8 : rxG0 cx = 8 * (rxG0 cx / 8)).
{ pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (rxG0 cx / 16)) with ((2 * (rxG0 cx / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
assert (XQ : (rxG0 cx + AENT * Z.of_nat k) / 8 = rxG0 cx / 8 + 7 * Z.of_nat k).
{ unfold AENT. rewrite G8 at 1. replace (8 * (rxG0 cx / 8) + 56 * Z.of_nat k) with ((rxG0 cx / 8 + 7 * Z.of_nat k) * 8) by ring.
  apply Z.div_mul. lia. }
assert (GB : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= 0x7fffff800000) by (unfold ASAN_CEIL in *; lia).
remember (Eimg (Ereg regs1 (rrs_extra (rxG0 cx + AENT * Z.of_nat k) (re_fd (rnth cx k))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rrs_extra (rxG0 cx + AENT * Z.of_nat k) (re_fd (rnth cx k)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E11 : ew E 11 = Z_to_bv 64 (rxG0 cx)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (AENT * rN cx)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E19 : ew E 19 = Z_to_bv 64 (rxFD cx)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 (AENT * Z.of_nat k)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat k))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_fd (rnth cx k)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (HS : st_ok_pi SEGS VAL E ss_rrs (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_scan)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rrs. apply pa_entry_st_ok_full.
- unfold rrs_sr. apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H13. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3)))).
  rewrite !U_SAlu, (U_atom E 22 SHADOW_OFF E22), (U_atom E 32 _ E32), U_lit by (unfold SHADOW_OFF, AENT in *; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by (unfold AENT; lia). change (2 ^ 3) with 8.
  unfold zcanon, M64. rewrite XQ.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite (Z.mod_small (rxG0 cx / 8 + 7 * Z.of_nat k)) by lia. rewrite Z.mod_small by (unfold SHADOW_OFF; lia).
  lia.
- vm_compute. reflexivity.
- unfold rrs_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E32, unsigned_lit_small by (unfold AENT; lia).
  split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (rxG0 cx + AENT * Z.of_nat k) 0 4 (SOff 33 0) (re_fd (rnth cx k)));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact Mfd.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
  + cbn [rrs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF, AENT in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((rxG0 cx + AENT * Z.of_nat k) mod 8 = 0).
    { unfold AENT. rewrite G8. replace (8 * (rxG0 cx / 8) + 56 * Z.of_nat k) with ((rxG0 cx / 8 + 7 * Z.of_nat k) * 8) by ring.
      apply Z_mod_mult. }
    unfold RRS_PHI, SB, SHADOW_OFF, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rrs_facts f_alias alias_ok]. split; [|exact I].
    apply bv_eq. change (U E (SAlu ALU_ADD (SOff 11 0) (SOff 24 0)) = U E (SOff 32 0)).
    rewrite U_SAlu, (U_atom E 11 _ E11), (U_atom E 24 _ E24), (U_atom E 32 _ E32) by (unfold AENT; lia).
    cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). reflexivity. }
clear HE.
assert (HBx : U E BxS = SHADOW_OFF) by (unfold BxS; rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxS rrs_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE (rxG0 cx + AENT * Z.of_nat k) 8 HAR RIn);
    [unfold AENT; lia | change (req_size ATABLE) with 896; unfold AENT; lia].
  + exact HBx.
  + rewrite (U_atom E 32 _ E32) by (unfold AENT; lia). reflexivity.
  + lia.
  + unfold AENT; lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rr_scan)) with (Z_to_bv 64 (BASE + A_rr_scan)).
(* the shadow check (fast path), the fd load, to the match test 0x83f24 *)
paj_run_tok_x RUN HS HJ SHOK rrs_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rrs_mem Em1.
psrr_branch_tok RUN BR HS SHOK rrs_Bspan.
- (* entry k has fd: to 0x83f48, RRM k *)
  rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 19 _ E19) in Hc by lia.
  apply Z.eqb_eq in Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x164).
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrs_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    prreg HS (10%bv : bv 5) N10; prreg HS (24%bv : bv 5) N24;
    pmkst HS; rewrite Em2, Em1 in HJ |- *; apply KM; unfold RRM;
    eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1, F, FL end.
  split; [reflexivity|].
  split; [unfold rregs_held, rregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
  split; [rewrite (HK 25%bv) by (cbv; tauto); exact H25|].
  split; [rewrite N10, E32; reflexivity|].
  split; [rewrite N24, E24; reflexivity|].
  split; [exact HFD0|]. split; [exact Hk|]. split; [exact Hc|].
  split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)].
- (* entry k has not fd: the step s8 += 56, a3 += 7 and the bound test 0x83f30 *)
  rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 19 _ E19) in Hc by lia.
  apply Z.eqb_neq in Hc.
  paj_run_tok_x RUN HS HJ SHOK rrs_Bspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrs_mem Em2.
  psrr_branch_tok RUN BR HS SHOK rrs_Bspan.
  + (* s8 = 56 |es|: entry k was the last; to the unlock tail 0x83fc4, RRU None *)
    rewrite branch_eq_U, (U_atom E 12 _ E12), (U_atom_off E 24 _ 56 E24) in Hc0 by (unfold rN, AENT; lia).
    apply Z.eqb_eq in Hc0.
    assert (Hlast : S k = length (rxes cx)) by (unfold rN, AENT in Hc0; lia).
    paj_run_to_tok_x RUNTO HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x1e0).
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rrs_mem Em3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
      cbn [ms_regs restrict] in HK;
      pmkst HS; rewrite Em3, Em2, Em1 in HJ |- *; apply KU; unfold RRU;
      eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1, F, FL end.
    split; [reflexivity|].
    split; [unfold rregs_base, spZ; rewrite !HK by (cbv; tauto); exact (proj1 HRH)|].
    split; [exact HFD0|].
    split; [split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)]|].
    (* no entry has fd (the lane's In_nth argument, relay_remove_p_bc.v:1586-1589) *)
    intros e He. destruct (In_nth (rxes cx) e relay_remove_b_c.no_entry He) as (i & Hi & <-).
    destruct (Nat.lt_ge_cases i k) as [L|L]; [exact (Hpre i L)|].
    replace i with k by lia. exact Hc.
  + (* entries left: back to the loop head 0x83f14, RRL (S k) *)
    rewrite branch_eq_U, (U_atom E 12 _ E12), (U_atom_off E 24 _ 56 E24) in Hc0 by (unfold rN, AENT; lia).
    apply Z.eqb_neq in Hc0.
    assert (Hk1 : (S k < length (rxes cx))%nat) by (unfold rN, AENT in Hc0; lia).
    paj_run_to_tok_x RUNTO HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x130).
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rrs_mem Em3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
      cbn [ms_regs restrict] in HK;
      prreg HS (13%bv : bv 5) N13; prreg HS (24%bv : bv 5) N24;
      pmkst HS; rewrite Em3, Em2, Em1 in HJ |- *; apply KL; unfold RRL;
      eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1, F, FL end.
    (* the shadow pointer of entry S k (the lane's AD3, relay_remove_seg.v:557-559) *)
    assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat k)) (Z_to_bv 64 3) =
                 Z_to_bv 64 (rxG0 cx / 8 + 7 * Z.of_nat k)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by (unfold AENT; lia).
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by (unfold AENT; lia). change (2 ^ 3) with 8. rewrite XQ.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    rewrite E22, E32, Q3, !YI08.alu64_add_lit in N13.
    rewrite E24, unsigned_lit_small in N24 by (unfold AENT; lia).
    split; [reflexivity|].
    split; [unfold rregs_held, rregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
    split; [rewrite (HK 25%bv) by (cbv; tauto); exact H25|].
    split; [rewrite (HK 11%bv) by (cbv; tauto); exact H11|].
    split; [rewrite (HK 12%bv) by (cbv; tauto); exact H12|].
    split; [rewrite N13; unfold w64; f_equal; lia|].
    split; [rewrite N24; unfold w64, AENT; f_equal; lia|].
    split; [exact HFD0|]. split; [exact Hk1|].
    split; [intros i Hi; destruct (Nat.eq_dec i k) as [->|Hne]; [exact Hc | apply Hpre; lia]|].
    split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)].
Qed.

(* ---- route R (a Theorem Labs lane crew, G8-A; a Theorem Labs lane): SCANS / SCAN at a world relation R, over a Theorem Labs lane 1's R
   statements (W_relay_remove_cx.v Section wR: rr_scans_stmt_xR / rr_scan_stmt_xR, RRL_xR / RRM_xR / RRU_xR).  The scan
   writes nothing and calls nothing, so it moves no world: its step is the strict walk over the R journal
   (CORE inside rr_scan_xR: SRr to the disjunction of the three exits, paj_run_x_xR), lifted to R and bound
   to the continuations.  The strict proofs above are unchanged; this replay changes only the names listed in
   a Theorem Labs lane's routeR/g8/mkscan.py. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNR := paj_run_x_xR B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xR B PST ARx LAWS R (G_RR B RG) HG 0 [].
Theorem rr_scans_xR : rr_scans_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold rr_scans_stmt_xR. intros SCAN cx k W1 c1 HB HL KM KU.
remember (length (rxes cx) - k)%nat as d eqn:Hd. revert k W1 c1 Hd HL.
induction d as [|d IH]; intros k W1 c1 Hd HL.
- exfalso. destruct HL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
- apply (SCAN cx k W1 c1 HB HL).
  + intros W2 c2 HL2. apply (IH (S k) W2 c2); [lia | exact HL2].
  + intros W2 c2 HM. exact (KM k W2 c2 HM).
  + exact KU.
Qed.

Theorem rr_scan_xR : rr_scan_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold rr_scan_stmt_xR. intros cx k W1 c1 HB HL KL KM KU.
(* the step, strict over the R journal, to the disjunction of its exits; then lifted and bound *)
enough (CORE : SRr SEGS W1 c1 (fun W2 c2 => RRL_xR B PST ARx MT RP RG R cx (S k) W2 c2 \/ RRM_xR B PST ARx MT RP RG R cx k W2 c2 \/ RRU_xR B PST ARx MT RP RG R cx None W2 c2)).
{ eapply (YA0nH.SRrG_bind SEGS R R_trans); [apply (YA0nH.SRr_SRrG SEGS R WLE_R); exact CORE|].
  intros W2 c2 _ [H2 | [H2 | H2]]; [exact (KL W2 c2 H2) | exact (KM W2 c2 H2) | exact (KU W2 c2 H2)]. }
clear KL KM KU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & _ & _ & HFDr & _).
destruct HL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & -> & HRH & H25 & H11 & H12 & H13 & H24 & HFD0 & Hk & Hpre & HH).
pose proof HH as (HLV & HREL & _).
pose proof HLV as (fpos & HJ & HLVr).
pose proof HREL as (_ & _ & _ & _ & _ & _ & Rlen & RIn & (tail & _ & _ & Rtab) & Rok & _).
pose proof HRH as ((Hsp & H3 & H4 & H8 & H9 & H18 & H20 & H21 & H22 & H26 & H27) & H19 & H23).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR RIn) as (HP16 & HP4096 & HPceil & HPh_ia & _ & _).
pose proof (proj1 HPh_ia) as HPh.
change (req_size ATABLE) with 896 in HPceil, HPh_ia, HPh.
assert (Hok : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx)).
{ eapply Forall_impl; [|exact Rok]. intros e (_ & _ & P1 & P2 & _). split; assumption. }
assert (Hfdk : 0 <= re_fd (rnth cx k) < 2 ^ 31).
{ rewrite Forall_forall in Rok. destruct (Rok _ (nth_In (rxes cx) relay_remove_b_c.no_entry Hk)) as (_ & _ & _ & _ & Hr & _).
  exact Hr. }
pose proof (rrs_fd_cell (arm W1 m1) (rxG0 cx) (rxes cx) tail k Rtab Hok Hk Hfdk) as Mfd.
assert (G8 : rxG0 cx = 8 * (rxG0 cx / 8)).
{ pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (rxG0 cx / 16)) with ((2 * (rxG0 cx / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
assert (XQ : (rxG0 cx + AENT * Z.of_nat k) / 8 = rxG0 cx / 8 + 7 * Z.of_nat k).
{ unfold AENT. rewrite G8 at 1. replace (8 * (rxG0 cx / 8) + 56 * Z.of_nat k) with ((rxG0 cx / 8 + 7 * Z.of_nat k) * 8) by ring.
  apply Z.div_mul. lia. }
assert (GB : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= 0x7fffff800000) by (unfold ASAN_CEIL in *; lia).
remember (Eimg (Ereg regs1 (rrs_extra (rxG0 cx + AENT * Z.of_nat k) (re_fd (rnth cx k))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rrs_extra (rxG0 cx + AENT * Z.of_nat k) (re_fd (rnth cx k)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E11 : ew E 11 = Z_to_bv 64 (rxG0 cx)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (AENT * rN cx)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E19 : ew E 19 = Z_to_bv 64 (rxFD cx)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 (AENT * Z.of_nat k)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat k))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_fd (rnth cx k)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (HS : st_ok_pi SEGS VAL E ss_rrs (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_scan)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rrs. apply pa_entry_st_ok_full.
- unfold rrs_sr. apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H13. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3)))).
  rewrite !U_SAlu, (U_atom E 22 SHADOW_OFF E22), (U_atom E 32 _ E32), U_lit by (unfold SHADOW_OFF, AENT in *; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by (unfold AENT; lia). change (2 ^ 3) with 8.
  unfold zcanon, M64. rewrite XQ.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite (Z.mod_small (rxG0 cx / 8 + 7 * Z.of_nat k)) by lia. rewrite Z.mod_small by (unfold SHADOW_OFF; lia).
  lia.
- vm_compute. reflexivity.
- unfold rrs_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E32, unsigned_lit_small by (unfold AENT; lia).
  split; [unfold AENT; lia|]. split; [unfold AENT; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (rxG0 cx + AENT * Z.of_nat k) 0 4 (SOff 33 0) (re_fd (rnth cx k)));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact Mfd.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
  + cbn [rrs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF, AENT in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((rxG0 cx + AENT * Z.of_nat k) mod 8 = 0).
    { unfold AENT. rewrite G8. replace (8 * (rxG0 cx / 8) + 56 * Z.of_nat k) with ((rxG0 cx / 8 + 7 * Z.of_nat k) * 8) by ring.
      apply Z_mod_mult. }
    unfold RRS_PHI, SB, SHADOW_OFF, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rrs_facts f_alias alias_ok]. split; [|exact I].
    apply bv_eq. change (U E (SAlu ALU_ADD (SOff 11 0) (SOff 24 0)) = U E (SOff 32 0)).
    rewrite U_SAlu, (U_atom E 11 _ E11), (U_atom E 24 _ E24), (U_atom E 32 _ E32) by (unfold AENT; lia).
    cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). reflexivity. }
clear HE.
assert (HBx : U E BxS = SHADOW_OFF) by (unfold BxS; rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxS rrs_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE (rxG0 cx + AENT * Z.of_nat k) 8 HAR RIn);
    [unfold AENT; lia | change (req_size ATABLE) with 896; unfold AENT; lia].
  + exact HBx.
  + rewrite (U_atom E 32 _ E32) by (unfold AENT; lia). reflexivity.
  + lia.
  + unfold AENT; lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rr_scan)) with (Z_to_bv 64 (BASE + A_rr_scan)).
(* the shadow check (fast path), the fd load, to the match test 0x83f24 *)
paj_run_tok_xR RUNR HS HJ SHOK rrs_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rrs_mem Em1.
psrr_branch_tok RUNR BR HS SHOK rrs_Bspan.
- (* entry k has fd: to 0x83f48, RRM k *)
  rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 19 _ E19) in Hc by lia.
  apply Z.eqb_eq in Hc.
  paj_run_to_tok_xR RUNTOR HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x164).
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrs_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    prreg HS (10%bv : bv 5) N10; prreg HS (24%bv : bv 5) N24;
    pmkst HS; rewrite Em2, Em1 in HJ |- *; apply SRr_ret; right; left; unfold RRM_xR;
    eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1, F, FL end.
  split; [reflexivity|].
  split; [unfold rregs_held, rregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
  split; [rewrite (HK 25%bv) by (cbv; tauto); exact H25|].
  split; [rewrite N10, E32; reflexivity|].
  split; [rewrite N24, E24; reflexivity|].
  split; [exact HFD0|]. split; [exact Hk|]. split; [exact Hc|].
  split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)].
- (* entry k has not fd: the step s8 += 56, a3 += 7 and the bound test 0x83f30 *)
  rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 19 _ E19) in Hc by lia.
  apply Z.eqb_neq in Hc.
  paj_run_tok_xR RUNR HS HJ SHOK rrs_Bspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrs_mem Em2.
  psrr_branch_tok RUNR BR HS SHOK rrs_Bspan.
  + (* s8 = 56 |es|: entry k was the last; to the unlock tail 0x83fc4, RRU None *)
    rewrite branch_eq_U, (U_atom E 12 _ E12), (U_atom_off E 24 _ 56 E24) in Hc0 by (unfold rN, AENT; lia).
    apply Z.eqb_eq in Hc0.
    assert (Hlast : S k = length (rxes cx)) by (unfold rN, AENT in Hc0; lia).
    paj_run_to_tok_xR RUNTOR HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x1e0).
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rrs_mem Em3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
      cbn [ms_regs restrict] in HK;
      pmkst HS; rewrite Em3, Em2, Em1 in HJ |- *; apply SRr_ret; right; right; unfold RRU_xR;
      eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1, F, FL end.
    split; [reflexivity|].
    split; [unfold rregs_base, spZ; rewrite !HK by (cbv; tauto); exact (proj1 HRH)|].
    split; [exact HFD0|].
    split; [split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)]|].
    (* no entry has fd (the lane's In_nth argument, relay_remove_p_bc.v:1586-1589) *)
    intros e He. destruct (In_nth (rxes cx) e relay_remove_b_c.no_entry He) as (i & Hi & <-).
    destruct (Nat.lt_ge_cases i k) as [L|L]; [exact (Hpre i L)|].
    replace i with k by lia. exact Hc.
  + (* entries left: back to the loop head 0x83f14, RRL (S k) *)
    rewrite branch_eq_U, (U_atom E 12 _ E12), (U_atom_off E 24 _ 56 E24) in Hc0 by (unfold rN, AENT; lia).
    apply Z.eqb_neq in Hc0.
    assert (Hk1 : (S k < length (rxes cx))%nat) by (unfold rN, AENT in Hc0; lia).
    paj_run_to_tok_xR RUNTOR HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x130).
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rrs_mem Em3.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
      cbn [ms_regs restrict] in HK;
      prreg HS (13%bv : bv 5) N13; prreg HS (24%bv : bv 5) N24;
      pmkst HS; rewrite Em3, Em2, Em1 in HJ |- *; apply SRr_ret; left; unfold RRL_xR;
      eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1, F, FL end.
    (* the shadow pointer of entry S k (the lane's AD3, relay_remove_seg.v:557-559) *)
    assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat k)) (Z_to_bv 64 3) =
                 Z_to_bv 64 (rxG0 cx / 8 + 7 * Z.of_nat k)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by (unfold AENT; lia).
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by (unfold AENT; lia). change (2 ^ 3) with 8. rewrite XQ.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    rewrite E22, E32, Q3, !YI08.alu64_add_lit in N13.
    rewrite E24, unsigned_lit_small in N24 by (unfold AENT; lia).
    split; [reflexivity|].
    split; [unfold rregs_held, rregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
    split; [rewrite (HK 25%bv) by (cbv; tauto); exact H25|].
    split; [rewrite (HK 11%bv) by (cbv; tauto); exact H11|].
    split; [rewrite (HK 12%bv) by (cbv; tauto); exact H12|].
    split; [rewrite N13; unfold w64; f_equal; lia|].
    split; [rewrite N24; unfold w64, AENT; f_equal; lia|].
    split; [exact HFD0|]. split; [exact Hk1|].
    split; [intros i Hi; destruct (Nat.eq_dec i k) as [->|Hne]; [exact Hc | apply Hpre; lia]|].
    split; [exists fpos; split; [exact HJ | exact HLVr] | exact (proj2 HH)].
Qed.

End wR.

End c.
End b.
End a.
