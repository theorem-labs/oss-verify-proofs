(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SCAN and SCANS segments of the image-B walk of fuzz_reply's relay_remove
   over W6's frozen cut file lib/B/W_relay_remove_cx.v (rr_scan_stmt, rr_scans_stmt): the scan loop
   0x8426c -> {0x842d8 | 0x843c0} of fuzz_reply.asan-ubsan.  Ported from lib/A/W_rr_scan.v
   (a working branch 57901ca62d8), which ports the retired lane form (commit 2ad36763b22,
   lib/A/Prog/relay_remove_*.v); this file's first B text was 8f74202634d (over a draft cut file).

   Where each part comes from:
   - rrs_nth_le_bytes, rrs_concat_split, rrs_eb_len, rrs_concat_len, rrs_garr8_le, rrs_fd_cell: lib/A/W_rr_scan.v,
     verbatim (pure list / byte lemmas over Prog/RelayRep.v and the kit's garr8; the lane's rrA_concat_split,
     rrA_entry_len, rrA_fd_cell).
   - rr_scans: lib/A/W_rr_scan.v rr_scans, verbatim (the lane's rrA_scan_fuel, induction on |es| - k).
   - rr_scan (one step of the loop): the form of lib/A/W_rr_scan.v rr_scan over B's loop: the loop state at 0x8426c
     seated by lib/B/W_traps.v's recipe (R1: the slot pointer's atom mkAF 4096 140737479966720 3; R2: the slot
     address a1 + s3 its own atom, both sum orders aliased; R3: the one-time flags a3 = a4 = 1 as mkAF 1 1 0 atoms),
     the shadow pointer computed inside the loop (0x84284-0x84288), the slot-address alias making it one atom so the
     shadow entry over the slot's first 8 bytes takes the check's fast path (the report call 0x842b4 is not taken).

   UBSAN TRAP EDGES: THREE PER ITERATION, all to `unimp` 0x843ec, none taken (lib/B/W_traps.v):
     0x84270  bltu a0,a1           WRAP: cited trap_ptr_wrap_atom (a0 = atom 32 = G0 + 56 k, a1 = atom 11 = G0,
                                   G0 + 56 k < 2^64 from G0 + 896 <= alloc_ceiling);
     0x8427c  beqz (a3 xor seqz a0)
                                   NULL-CONS xor: the runner folds seqz a0 to 0 (R1), the branch stops on
                                   a3 xor 0; cited trap_null_xor_folded (a3 = atom 13 = 1, R3);
     0x84280  beqz a4              BASE ALIGNED+NON-NULL flag: the runner decides it from a4's seat fact
                                   mkAF 1 1 0 (R3), no branch case. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (lane RRX, the image-A twin a Theorem Labs lane f4cd818e98d
   lib/A/W_rr_scan.v): SCAN / SCANS over the generic relation ARx, IN PLACE (the AR proofs are replaced; Section c is
   W_relay_remove_cx.v's generic block, verbatim); the cut predicates carry the head set Hp1 after S1.  The scan writes
   nothing and calls nothing, so RHELD (with its room budget rp_RM and its count fact cnt_ok_pk) passes through
   unchanged.  al_blocks -> alx_blocks, ajournal_gx_AR -> ajournal_gx_AR_x, the table block's shadow fact
   range_addressable_of_block -> range_addressable_of_block_hp0_x (under HP0), RUN / RUNTO over paj_run_x_x /
   paj_run_to_x_x with paj_run_tok_x / paj_run_to_tok_x.  The rrs_* helpers keep their statements. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
(* route R (the Section wR below): SRrG, and the R contract texts of drain / gestures_end (a Theorem Labs lane) and of
   relay_remove (a Theorem Labs lane) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps W_relay_remove_cx.
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

(* ------------------------------------------------------------------ the loop head 0x8426c *)
(* s0 = fd (atom 8), a1 = G0 (11), a2 = 56 |es| (12), a3 = (G0 <> 0) = 1 (13), a4 = (G0 <> 0 and 8-aligned) = 1
   (14), s2 = SB (18), s3 = 56 k (19); atom 32 = X = G0 + 56 k (entry k), atom 33 = entry k's fd.  The alias
   a1 + s3 = X (both orders) makes the slot address one atom: the shadow address (X >> 3) + s2 the loop computes
   matches the shadow pattern over Bx = s2's atom, and the shadow entry over X's first 8 bytes takes the check's
   fast path. *)
Definition RRS_PHI : Z := 140737479966720.
Definition BxS : sv := SOff 18 0.
Definition rrs_regions : smem := [ YP09.mkRegion (Some 32%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))] ].
Definition rrs_facts : facts :=
mkFacts [ (13%nat, mkAF 1 1 0); (14%nat, mkAF 1 1 0); (18%nat, mkAF SB SB 0); (32%nat, mkAF 4096 RRS_PHI 3);
  (33%nat, mkAF 0 (2 ^ 31 - 1) 0) ] []
  [ (SAlu ALU_ADD (SOff 11 0) (SOff 19 0), SOff 32 0); (SAlu ALU_ADD (SOff 19 0) (SOff 11 0), SOff 32 0) ].
Definition ss_rrs : sstate := mkSS A_rr_scan sr_atoms rrs_regions None rrs_facts.
Definition rrs_SH : list shent := [ mkSHE 32 0 8 ].
Definition rrs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rrs_extra (x fd : Z) : list word := map (Z_to_bv 64) [x; fd].
(* the registers the loop body does not write (it writes a0, a5 and s3) *)
Definition RRS_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 11; 12; 13; 14; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* a run over the read-only slot region leaves the memory as it was (W_LLVMFuzzerTestOneInput_cut.v jt_mem) *)
Ltac rrs_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.
(* rregs_base's s5 .. s11 clause at a cut the loop reaches: the registers 21 .. 27 are in RRS_KEPT *)
Lemma rrs_hi_kept : forall r : bv 5, 21 <= bv_unsigned r <= 27 -> In r RRS_KEPT.
Proof.
intros r Hr. apply In_bv_eq.
assert (Hm : map bv_unsigned RRS_KEPT = [2; 3; 4; 8; 9; 11; 12; 13; 14; 18; 20; 21; 22; 23; 24; 25; 26; 27])
by (vm_compute; reflexivity).
rewrite Hm. cbn [In]. lia.
Qed.
(* rregs_base / rregs_held at a cut the loop reaches, from the kept registers *)
Ltac rrs_base HK HQ Hsp H3 H4 :=
unfold rregs_base;
split; [unfold spZ; rewrite (HK 2%bv) by (cbv; tauto); exact Hsp|];
split; [rewrite (HK 3%bv) by (cbv; tauto); exact H3|];
split; [rewrite (HK 4%bv) by (cbv; tauto); exact H4|];
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; rewrite (HK r (rrs_hi_kept r Hr)); exact (HQ r Hr).
Ltac rrs_held HK HQ Hsp H3 H4 H8 H9 H18 H20 :=
unfold rregs_held;
split; [rrs_base HK HQ Hsp H3 H4|];
split; [rewrite (HK 8%bv) by (cbv; tauto); exact H8|];
split; [rewrite (HK 9%bv) by (cbv; tauto); exact H9|];
split; [rewrite (HK 18%bv) by (cbv; tauto); exact H18|];
rewrite (HK 20%bv) by (cbv; tauto); exact H20.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the allocator rules on the _c form (W_journal.v Section hc; a Theorem Labs lane 21:24Z): one table CTX_AFREE for free and
   free(NULL), which enter the same interceptor pc0.  Image B's relay_remove keeps NO frame pointer: at its free
   (0x8435c, ra 0x84360 = entry + 0x164) s0 holds fd, an integer below alloc_ceiling, so chain_pre's chain is cut by
   the register and the trace is the CLOSED singleton [0x84360] (a Theorem Labs lane 21:32Z; K0's B CTX_AFREE row, lib/B/YCk0.v:19).  The
   kit's B rr_spec_x takes it as its LAST premise `In [pc + 356] CTX_AFREE` (W4's b_facts, a Theorem Labs lane 21:5xZ); RCTX
   below carries it to MATCH's free (no ly_top conjunct: the chain is []). *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (image B's top, W_wake_x.v's form), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC); ASMP / ASF / FFL are the class-0
   fake frame's laws (image B's relay_remove takes none: wake does, W_wake_x.v) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
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
(* the register images of g_nsrc / g_src (the abstract placement does not fix them against the objects; PB_fr on
   AsanUbsan discharges both by vm_compute, as the image-A twin's HH59 / HH60) *)
Hypothesis HH53 : VAL (A_HI 53) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH54 : VAL (A_HI 54) = rg_src RG + RR_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are unowned image bytes (the image-A twin's HRGP / HRGI, verbatim) *)
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
(* no read-only image byte is owned by the runtime: rom_view survives the calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs;
   image B meets it at wake's return (W_wake_c_x.v wk_post_x's seat fact S' = set_fs f S) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (image B calls free's interceptor directly, WS_free) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) and wake (W_wake_c_x.v) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* B only: wake, tail-called at 0x843e8 (image A inlines it); W_relay_remove.v builds it by W_wake_x.v pb_wake_x *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (the image-A twin's PSTR / PSTG, verbatim). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ---- ROUTE R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form, lib/B/W_bx_reset_x.v): SCAN and SCANS
   at a world relation R, W_relay_remove_cx.v's Section wR statements rr_scan_stmt_xR / rr_scans_stmt_xR.  Against
   the strict texts only these change: the statements and the cut predicates RRL / RRM / RRU -> their _xR twins (the
   journal ajournal_gx_xR .. R, the walk SRrG SEGS R), the runs and the branch -> their SRrG forms (W_journal_x.v
   paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR), ajournal_gx_AR_x -> ajournal_gx_AR_xR.  The scan writes
   nothing and calls nothing (RHELD passes through), so each run stays at the world W1 and the continuations KL / KM
   / KU are used as SRrG facts; no law of R is read.  At R := wle each twin is its strict text: rr_scans and rr_scan
   after the Section are these at wle (moved below the Section; their statements are unchanged).
   Census rows (a Theorem Labs lane's G8b-relayrm-B.tsv (sha256 4c7c7e01243b; internal record)) -> twins: :263 AFREE -> AFREE_R, :267 DRAIN -> DRAIN_R,
   :268 GSE -> GSE_R, :270 AFREEN -> AFREEN_R (W_relay_remove_cx.v's texts; unused, the scan calls nothing),
   :289 rr_scans -> rr_scans_xR, :301 rr_scan -> rr_scan_xR.  The rrs_* helpers carry no journal: no twins. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
(* :263 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :267 DRAIN, :268 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :270 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* :289 rr_scans at R: the loop by induction on |es| - k (the lane's rrA_scan_fuel); the IH is SCAN's SRrG
   continuation *)
Theorem rr_scans_xR : rr_scans_stmt_xR B PST ARx R MT RP MMAX RG.
Proof.
unfold rr_scans_stmt_xR. intros SCAN cx k W1 c1 HB HL KM KU.
remember (length (rxes cx) - k)%nat as d eqn:Hd. revert k W1 c1 Hd HL.
induction d as [|d IH]; intros k W1 c1 Hd HL.
- exfalso. destruct HL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _). lia.
- apply (SCAN cx k W1 c1 HB HL).
  + intros W2 c2 HL2. apply (IH (S k) W2 c2); [lia | exact HL2].
  + intros W2 c2 HM. exact (KM k W2 c2 HM).
  + exact KU.
Qed.

(* :301 rr_scan at R *)
Theorem rr_scan_xR : rr_scan_stmt_xR B PST ARx R MT RP MMAX RG.
Proof.
unfold rr_scan_stmt_xR. intros cx k W1 c1 HB HL KL KM KU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & _ & _ & HFDr & _).
destruct HL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & -> & HRH & H11 & H12 & H13 & H14 & H19 & HFD0 & Hk & Hpre & HH).
pose proof HH as (HLV & HREL & _).
pose proof HLV as (HJ & HLVr).
pose proof HREL as (_ & _ & _ & _ & _ & _ & Rlen & RIn & (tail & _ & _ & Rtab) & Rok & _).
pose proof HRH as (HRB & H8 & H9 & H18 & H20).
pose proof HRB as (Hsp & H3 & H4 & HRBq).
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
assert (GB : 4096 <= rxG0 cx /\ rxG0 cx + 896 <= 0x7fffff800000) by (unfold ASAN_CEIL in *; lia).
remember (Eimg (Ereg regs1 (rrs_extra (rxG0 cx + AENT * Z.of_nat k) (re_fd (rnth cx k))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rrs_extra (rxG0 cx + AENT * Z.of_nat k) (re_fd (rnth cx k)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E8 : ew E 8 = Z_to_bv 64 (rxFD cx)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact H8).
assert (E11 : ew E 11 = Z_to_bv 64 (rxG0 cx)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (AENT * rN cx)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 1) by (rewrite (EEo 13%nat 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 1) by (rewrite (EEo 14%nat 14%bv eq_refl); exact H14).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 (AENT * Z.of_nat k)) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E32 : ew E 32 = Z_to_bv 64 (rxG0 cx + AENT * Z.of_nat k))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_fd (rnth cx k)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (HS : st_ok_pi SEGS VAL E ss_rrs (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_scan)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rrs. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
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
    rewrite E13, E14, E18, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF, AENT in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert ((rxG0 cx + AENT * Z.of_nat k) mod 8 = 0).
    { unfold AENT. rewrite G8. replace (8 * (rxG0 cx / 8) + 56 * Z.of_nat k) with ((rxG0 cx / 8 + 7 * Z.of_nat k) * 8) by ring.
      apply Z_mod_mult. }
    unfold RRS_PHI, SB, SHADOW_OFF, AENT in *. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
  + cbn [rrs_facts f_alias alias_ok]. split; [|split; [|exact I]].
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 11 0) (SOff 19 0)) = U E (SOff 32 0)).
      rewrite U_SAlu, (U_atom E 11 _ E11), (U_atom E 19 _ E19), (U_atom E 32 _ E32) by (unfold AENT; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). reflexivity.
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 19 0) (SOff 11 0)) = U E (SOff 32 0)).
      rewrite U_SAlu, (U_atom E 11 _ E11), (U_atom E 19 _ E19), (U_atom E 32 _ E32) by (unfold AENT; lia).
      cbn [zalu_raw]. unfold zcanon, M64. rewrite Z.mod_small by (unfold AENT; lia). lia. }
clear HE.
assert (HBx : U E BxS = SHADOW_OFF) by (unfold BxS; rewrite (U_atom E 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxS rrs_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE
      (rxG0 cx + AENT * Z.of_nat k) 8 HAR RIn);
    [unfold AENT; lia | change (req_size ATABLE) with 896; unfold AENT; lia].
  + exact HBx.
  + rewrite (U_atom E 32 _ E32) by (unfold AENT; lia). reflexivity.
  + lia.
  + unfold AENT; lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rr_scan)) with (Z_to_bv 64 (BASE + A_rr_scan)).
(* 0x8426c add a0,a1,s3 (the alias: a0 = X), to the first trap edge *)
paj_run_tok_x RUNG HS HJ SHOK rrs_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rrs_mem Em1.
(* TRAP EDGE 1, 0x84270 bltu a0,a1 -> unimp (WRAP): never taken, G0 + 56 k does not wrap *)
psrr_branch_tok RUNG BRR HS SHOK rrs_Bspan.
{ exfalso. rewrite (trap_ptr_wrap_atom E 32 11 (rxG0 cx) (AENT * Z.of_nat k) E32 E11) in Hc by (unfold AENT; lia).
  discriminate. }
(* the runner folds seqz a0 to 0 (atom 32 >= 4096); TRAP EDGE 2, 0x8427c beqz (a3 xor 0) -> unimp: never taken, a3 = 1 *)
paj_run_tok_x RUNG HS HJ SHOK rrs_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rrs_mem Em2.
psrr_branch_tok RUNG BRR HS SHOK rrs_Bspan.
{ exfalso. rewrite (trap_null_xor_folded E 13 E13) in Hc0. discriminate. }
(* TRAP EDGE 3, 0x84280 beqz a4 -> unimp: the runner decides it from a4's seat fact mkAF 1 1 0; then the shadow check of
   the fd field (fast path: the report call 0x842b4 is never reached), the fd load, to the match test 0x84298 *)
paj_run_tok_x RUNG HS HJ SHOK rrs_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rrs_mem Em3.
psrr_branch_tok RUNG BRR HS SHOK rrs_Bspan.
- (* entry k has fd: to 0x842d8, RRM k *)
  rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 8 _ E8) in Hc1 by lia.
  apply Z.eqb_eq in Hc1.
  paj_run_to_tok_x RUNTOG HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0xdc).
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrs_mem Em4.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    prreg HS (10%bv : bv 5) N10; prreg HS (19%bv : bv 5) N19;
    pmkst HS; rewrite Em4, Em3, Em2, Em1 in HJ |- *; apply KM; unfold RRM_xR;
    eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1 end.
  split; [reflexivity|].
  split; [rrs_held HK HRBq Hsp H3 H4 H8 H9 H18 H20|].
  split; [rewrite N10, E32; reflexivity|].
  split; [rewrite N19, E19; reflexivity|].
  split; [exact HFD0|]. split; [exact Hk|]. split; [exact Hc1|].
  split; [split; [exact HJ | exact HLVr] | exact (proj2 HH)].
- (* entry k has not fd: the step s3 += 56 and the bound test 0x842a0 *)
  rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 8 _ E8) in Hc1 by lia.
  apply Z.eqb_neq in Hc1.
  paj_run_tok_x RUNG HS HJ SHOK rrs_Bspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rrs_mem Em4.
  psrr_branch_tok RUNG BRR HS SHOK rrs_Bspan.
  + (* s3 = 56 |es|: entry k was the last; to the unlock tail 0x843c0, RRU None *)
    rewrite branch_eq_U, (U_atom E 12 _ E12), (U_atom_off E 19 _ 56 E19) in Hc2 by (unfold rN, AENT; lia).
    apply Z.eqb_eq in Hc2.
    assert (Hlast : S k = length (rxes cx)) by (unfold rN, AENT in Hc2; lia).
    paj_run_to_tok_x RUNTOG HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x1c4).
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rrs_mem Em5.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
      cbn [ms_regs restrict] in HK;
      pmkst HS; rewrite Em5, Em4, Em3, Em2, Em1 in HJ |- *; apply KU; unfold RRU_xR;
      eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1 end.
    split; [reflexivity|].
    split; [rrs_base HK HRBq Hsp H3 H4|].
    split; [exact HFD0|].
    split; [split; [split; [exact HJ | exact HLVr] | exact (proj2 HH)]|].
    (* no entry has fd (the lane's In_nth argument, relay_remove_p_bc.v:1586-1589) *)
    intros e He. destruct (In_nth (rxes cx) e relay_remove_b_c.no_entry He) as (i & Hi & <-).
    destruct (Nat.lt_ge_cases i k) as [L|L]; [exact (Hpre i L)|].
    replace i with k by lia. exact Hc1.
  + (* entries left: back to the loop head 0x8426c, RRL (S k) *)
    rewrite branch_eq_U, (U_atom E 12 _ E12), (U_atom_off E 19 _ 56 E19) in Hc2 by (unfold rN, AENT; lia).
    apply Z.eqb_neq in Hc2.
    assert (Hk1 : (S k < length (rxes cx))%nat) by (unfold rN, AENT in Hc2; lia).
    paj_run_to_tok_x RUNTOG HS HJ SHOK rrs_Bspan (AF_fr_relay_remove + 0x70).
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    rrs_mem Em5.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RRS_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK;
      cbn [ms_regs restrict] in HK;
      prreg HS (19%bv : bv 5) N19;
      pmkst HS; rewrite Em5, Em4, Em3, Em2, Em1 in HJ |- *; apply KL; unfold RRL_xR;
      eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1 end.
    rewrite E19, unsigned_lit_small in N19 by (unfold AENT; lia).
    split; [reflexivity|].
    split; [rrs_held HK HRBq Hsp H3 H4 H8 H9 H18 H20|].
    split; [rewrite (HK 11%bv) by (cbv; tauto); exact H11|].
    split; [rewrite (HK 12%bv) by (cbv; tauto); exact H12|].
    split; [rewrite (HK 13%bv) by (cbv; tauto); exact H13|].
    split; [rewrite (HK 14%bv) by (cbv; tauto); exact H14|].
    split; [rewrite N19; unfold w64, AENT; f_equal; lia|].
    split; [exact HFD0|]. split; [exact Hk1|].
    split; [intros i Hi; destruct (Nat.eq_dec i k) as [->|Hne]; [exact Hc1 | apply Hpre; lia]|].
    split; [split; [exact HJ | exact HLVr] | exact (proj2 HH)].
Qed.
End wR.
(* the strict texts below are the R section's at R := wle (route R's rule: one walk text): the twins read no law of
   R and no R premise, so they hold at wle as they stand *)
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* SCANS: the loop by induction on |es| - k (the lane's rrA_scan_fuel). *)
Theorem rr_scans : rr_scans_stmt B PST ARx MT RP MMAX RG.
Proof. eapply (rr_scans_xR (@wle SEGS)); wle_inst. Qed.

Theorem rr_scan : rr_scan_stmt B PST ARx MT RP MMAX RG.
Proof. eapply (rr_scan_xR (@wle SEGS)); wle_inst. Qed.

End c.
End b.
End a.
