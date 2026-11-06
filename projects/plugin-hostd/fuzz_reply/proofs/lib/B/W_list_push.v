(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (asan-ubsan) walk of plugin-hostd/fuzz_reply's list_push
   (0x85324, 223 instructions, frame 96), proving lib/B/W_contract.v's lp_spec / lp_spec_g at
   BASE + AF_fr_list_push (lib/B/W_listing.v:23, 0x2fe0).  Written in the shape of the image-A walk
   (a working branch ff4c06b2f3a, lib/A/W_list_push.v + lib/A/W_lp_tail.v + lib/A/W_list_push_tail.v, Qed),
   over lib/B's own listing: image B is NOT a relocation of image A (UBSan runs in trap mode here, so every
   check is an inline branch to `unimp`, which changes the register allocation and inserts 19 trap branches in
   this function).  The A tail files are inlined here as one lemma (lp_tail_seg), as the lane gets one new file.

   The walk: list_push(l, s, n) reads l->n and l->cap; when the list is full it grows the vector with realloc
   (8 entries, then doubling), copies the n source bytes into a fresh malloc'd block of n + 1 bytes with
   __asan_memcpy, NUL-terminates it and appends (block, n) to the vector.  Four cuts:
     SEG1  0x85324 .. the realloc call 0x853e0 (grow) or the malloc call 0x85404 (room),
     SEG2  the realloc return 0x853e4 .. the malloc call 0x85404   (lp_grow_seg),
     SEG3  the malloc return 0x85408 .. the __asan_memcpy call 0x8547c,
     SEG4  the memcpy return 0x85480 .. the ret 0x855bc            (SEG3/SEG4: lp_tail_seg).
   realloc goes through ARE (arealloc_cf_rule_c_x at CTX_R), malloc through AMA (amalloc_cf_rule_c_x at CTX_M), __asan_memcpy through
   AMEMCPY (aintrin_realizes_x OCpy); the forced-success posts refute the NULL arms (0x853e4, 0x85470 /
   __asan_handle_no_return; abort).

   The 19 UBSan trap branches to the `unimp` at 0x855c0 (census: TRAPS-CENSUS.md (sha256 b33c2b52103e; internal record)).
   Seven of them stop the runner and are closed with lib/B/W_traps.v (a Theorem Labs lane), the other twelve the runner
   decides itself from this walk's facts:
     0x85360  ALIGN8 LA              trap_align8      (lp_spec's LA mod 8 = 0)
     0x853bc  INT32 DOUBLING         runner           (fact atom 34: cap <= 2 ^ 30 - 1, from alist_at)
     0x85434  NULL-CONS (beq)        trap_br_eq + trap_U_seqz   (v + 16 n >= 4096; snez v folded to 1)
     0x85448  PTR-OVF (signed index) trap_ptr_sovf + trap_U_sltu_ge  (v <= v + 16 n; slti n,0 folded to 0)
     0x8544c  NON-NULL v             runner           (fact atom 44: 4096 <= v)
     0x85454  ALIGN8 v + 16 n        trap_align8      (v is 16-aligned: al_blocks)
     0x8546c  NON-NULL v + 16 n      trap_nonnull
     0x854a8  NULL-CONS (beq)        runner           (the same condition, already assumed at 0x85434)
     0x854bc  PTR-OVF                runner           (assumed at 0x85448)
     0x854c0  NON-NULL v             runner           (fact atom 44)
     0x854c8  ALIGN8 v + 16 n        runner           (assumed at 0x85454)
     0x854e4  PTR-OVF (bltu) d + n   trap_ptr_bltu
     0x854f4  NULL-CONS (xor)        trap_br_eq + trap_U_seqz   (d + n >= 4096; snez d folded to 1)
     0x854f8  NON-NULL d             runner           (fact atom 52: 4096 <= d)
     0x85538  NULL-CONS (beq)        runner           (assumed at 0x85434)
     0x8554c  PTR-OVF                runner           (assumed at 0x85448)
     0x85550  NON-NULL v             runner           (fact atom 44)
     0x85558  ALIGN8 v + 16 n        runner           (assumed at 0x85454)
     0x85578  INT32 +1 (n + 1)       runner           (fact atom 45: n <= 2 ^ 30 - 1)
   B's frame is 96 bytes (0x85324 `addi sp,sp,-96`, ra at 88, s0 .. s10 at 80 .. 0), so LP_STK = 96 + ASTACK
   holds unchanged from image A.  Registers differ from A only in s5 / s6: B keeps the shadow base SB in s6
   (atom 22) and the shadow address of l->n in s5 (atom 21); A has them the other way round.

   The room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record) and C3, as image A's F1b (lib/A/W_list_push.v / W_lp_tail.v at
   e32cc1247c0): the Sections take the room record RP; lp_spec_x's live bytes are C3's peak over list_push's trace
   (lp_peak_grow / lp_peak_nogrow give each call's own premise), its room budget 3 (grow) or 1 (lp_rk_eq) is spent as
   realloc's 2 and the tail malloc's 1, and its peak-form counts give each call's count premise (lp_cnt_at at S; at the
   tail after realloc, S's counts plus the new vector, the old one gone).  lp_tail_pre_x (local here; image A's is
   lib/A/W_list_push_tail.v's text) takes kr and carries the tail malloc's rp_RM RP Sc (1 + kr) and cnt_ok at Sc,
   word for word as image A's; the malloc's stack room comes from the call's journal (W_journal_x.aj_stack_room_x). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00 YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_frame W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_kit_xb W_journal_x W_contract_x W_sites_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
(* the lib/B sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) step 3): no sink instance is a hint after this *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* Reuse search (the three-clause script; its report reuse-list_push.txt (sha256 ff5e5e65ae5f; internal record)):
   no released proof of list_push at either entry and none of image B's W_contract lp_spec;
   of the unreleased hits it lists on 0x85324, fuzz_reply's are lib/B/Prog plain-model files (another statement) and the others are another unit's equal number (libreac/fuzz_disco YI12.v:210).
*)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_list_push : Z := AF_fr_list_push.
Definition A_list_pushP : Z := BASE + A_list_push.
(* the malloc call: 0x85404 = list_push + 0xe0 *)
Definition A_lp_mcall : Z := AF_fr_list_push + 0xe0.
(* list_push's frame: ra at 88, s0 .. s10 at 80 .. 0 (image B's prologue 0x85328 .. 0x85354) *)
Definition lp_saved : list (Z * Z) :=
[(88, 1); (80, 8); (72, 9); (64, 18); (56, 19); (48, 20); (40, 21); (32, 22); (24, 23); (16, 24); (8, 25); (0, 26)].
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                      | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
(* a UBSan trap edge of the runner (Hc : branch_taken c a b = true) closed by a lib/B/W_traps.v lemma *)
(* image-band facts: lib/B's YCbq (IMG_TOP_B = 0x5fc000) and Reusable's (IMG_TOP_A) are two constants, and a
   bare `unfold off_img` reaches only one of them *)
Ltac unf_imgband := repeat first
[ progress unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.zone2 in *
| progress unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.zone2 in *
| progress unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in *
| progress unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.off_img in * ].
Ltac lp_clearbr := repeat match goal with H : branch_taken _ _ _ = false |- _ => clear H end.
Ltac lp_trap L := exfalso;
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rewrite L in H; discriminate end.
(* ---- the symbolic state at the call (lane W2's walk of the segment) ----
   Atoms: 0 .. 31 the registers at the call; 32 .. 43 the caller's ra, s0 .. s10 as list_push saved them (the
   frame's slots 88 .. 0); 44 / 45 / 46 the list's v / n / cap; 47 the slot address v + 16 n.  The engine reads
   v + (n << 4) as atom 47 through the alias of lpt_facts, so the slot needs no fresh atom. *)
Definition lpt_Bx : sv := SOff 22 0.
Definition lpt_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lpt_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 96 0 0
[YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 8 (SOff 34 0));
 YP09.mkChunk 64 (CVal 8 (SOff 35 0)); YP09.mkChunk 56 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 37 0));
 YP09.mkChunk 40 (CVal 8 (SOff 38 0)); YP09.mkChunk 32 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 40 0));
 YP09.mkChunk 16 (CVal 8 (SOff 41 0)); YP09.mkChunk 8 (CVal 8 (SOff 42 0)); YP09.mkChunk 0 (CVal 8 (SOff 43 0))].
Definition lpt_lregion : YP09.region :=
YP09.mkRegion (Some 18%nat) 0 16 0 16
[YP09.mkChunk 0 (CVal 8 (SOff 44 0)); YP09.mkChunk 8 (CVal 4 (SOff 45 0)); YP09.mkChunk 12 (CVal 4 (SOff 46 0))].
Definition lpt_slot : YP09.region := YP09.mkRegion (Some 47%nat) 0 16 0 16 [].
Definition lpt_regions : smem := [lpt_stack; lpt_lregion; lpt_slot].
Definition lpt_alias : sv * sv := (SAlu ALU_ADD (SOff 44 0) (SAlu ALU_SLL (SOff 45 0) (SLit 4)), SOff 47 0).
Definition HEAPF : afact := mkAF 0 0x7fffff800000 0.
Definition lpt_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0 (2 ^ 16) 0); (18%nat, mkAF 0x10000 0x5fc000 0);
(22%nat, mkAF SB SB 0); (44%nat, mkAF 4096 0x7fffff800000 4); (45%nat, mkAF 0 (2 ^ 30 - 1) 0);
(46%nat, mkAF 0 (2 ^ 30 - 1) 0); (47%nat, HEAPF) ] [] [lpt_alias].
Definition lpt_regs : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 18 8)) 20%bv (SOff 18 12))
21%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 8) (SLit 3)) (SOff 22 0)))
23%bv (SAlu ALU_SRL (SOff 18 0) (SLit 3)))
24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 12) (SLit 3)) (SOff 22 0)).
Definition ss_lpt : sstate := mkSS A_lp_mcall lpt_regs lpt_regions None lpt_facts.
Definition lpt_SH : list shent := [ mkSHE 18 0 16; mkSHE 47 0 16 ].
Definition lpt_extra (regs : bvmap 5 word) (v N cap : Z) : list word :=
map (fun p => getr regs (Z_to_bv 5 (snd p))) lp_saved ++ map (Z_to_bv 64) [v; N; cap; v + 16 * N].
(* After __asan_memcpy: the byte d + n (d the new block, atom 52; n atom 9) as atom 80, and its one-byte region. *)
Definition lpt_aE : YP09.region := YP09.mkRegion (Some 80%nat) 0 1 0 1 [].
Definition lpt_SH3 : list shent := lpt_SH ++ [mkSHE 80 0 1].
Lemma lpt_regs_ok_set : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hv r'. unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r'). unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma lpt_nth_le_bytes : forall n z k, (k < n)%nat ->
nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|]. destruct k as [|k]; cbn [Z_to_le_bytes nth].
- replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
(* an 8-byte value in memory is the garr8 of its little-endian bytes *)
Lemma lpt_garr8_of_val8 : forall m a v, 0 <= v < 2 ^ 64 ->
val_mem SEGS m a 8 v -> garr8 SEGS m a (bzs (Mem.le8 (Z_to_bv 64 v))).
Proof.
intros m a v Hv H j Hj.
assert (Hj8 : (j < 8)%nat) by (unfold bzs in Hj; rewrite length_map, Mem.length_le8 in Hj; exact Hj).
assert (Hn : nth j (bzs (Mem.le8 (Z_to_bv 64 v))) 0 = YO0f.le_byte v 8 j).
{ unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, Mem.length_le8; exact Hj8).
  rewrite map_nth. unfold Mem.le8, word_to_le_bytes, bz. rewrite lpt_nth_le_bytes by exact Hj8.
  rewrite unsigned_lit_small by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. replace (8 * Z.of_nat 8) with 64 by lia. rewrite (Z.mod_small v (2 ^ 64)) by lia. reflexivity. }
rewrite Hn. set (b := YO0f.le_byte v 8 j).
assert (Hr : 0 <= b < 256) by (unfold b, YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr]. intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (H j Hj8). fold b. do 2 f_equal. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small b 256) by lia. rewrite (Z.mod_small b 256) by lia. reflexivity.
Qed.
(* garr8 carried over unchanged bytes *)
Lemma lp_mod8_of_16 : forall v n, v mod 16 = 0 -> 0 <= n -> (v + 16 * n) mod 8 = 0.
Proof.
intros v n Hv Hn. apply Z.mod_divide in Hv as [k Hk]; [|lia]. subst v.
replace (k * 16 + 16 * n) with ((2 * k + 2 * n) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma lpt_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (a + j) = aview SEGS H m (a + j)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS H H' m m' (a + Z.of_nat j) 1); [|exact Hv].
intros k Hk. rewrite <- !Z.add_assoc. apply HK. lia.
Qed.
(* ---- the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record) and C3's peak premise: list_push's room budget, live bytes, counts ---- *)
(* lp_spec_x's room budget Z.to_nat (lp_cost MT_rk ..): 3 when the vector grows (realloc, then malloc), else 1 *)
Lemma lp_rk_eq : forall l n, Z.to_nat (lp_cost MT_rk l n) = ((if lp_grow l then 2 else 0) + 1)%nat.
Proof. intros l n. unfold lp_cost. destruct (lp_grow l); reflexivity. Qed.
(* C3's peak premise (lp_spec_x: blocks_bytes S + tr_peak (lp_tr l n) <= LIVE_MAX), when the list has room: the one
   request is the text's block *)
Lemma lp_peak_nogrow : forall bb l n, lp_grow l = false -> 0 <= n ->
  bb + tr_peak (lp_tr l n) <= LIVE_MAX -> bb + (n + 1) <= LIVE_MAX.
Proof.
  intros bb l n Hg Hn. revert Hg. unfold lp_tr, lp_grow, ListTr.list_push_tra.
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; [intros Hg; discriminate Hg|].
  intros _ H. cbv beta iota in H; cbn [app tr_peak fold_right] in H. lia.
Qed.
(* ... and when the vector grows: realloc's own premise at the entry, and the tail malloc's at the state after it (the
   new vector counted, the old one, if any, gone) *)
Lemma lp_peak_grow : forall bb l n, lp_grow l = true -> 0 <= n ->
  bb + tr_peak (lp_tr l n) <= LIVE_MAX ->
  bb + lp_vbytes l <= LIVE_MAX /\
  bb - (if hl_cap l =? 0 then 0 else AREC * hl_cap l) + lp_vbytes l + (n + 1) <= LIVE_MAX.
Proof.
  intros bb l n Hg Hn. revert Hg. unfold lp_tr, lp_grow, lp_vbytes, ListTr.list_push_tra, grow_cap, AREC.
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; [|intros Hg; discriminate Hg].
  intros _. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]; intros H; cbv beta iota in H |- *;
    cbn [app tr_peak fold_right] in H; split; lia.
Qed.
(* the count premise of one allocator call (cnt_ok) from a spec's peak form: the peak is not negative *)
Lemma lp_cnt_at : forall RP0 pk l, cnt_ok_pk RP0 pk l -> cnt_ok RP0 l.
Proof.
  intros RP0 pk l H. unfold cnt_ok.
  apply (cnt_ok_pk_mono RP0 pk (fun _ => 0%nat) l l); [intros Pq; cbv beta; lia | exact H].
Qed.
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): list_push over any allocator relation ARx with
   its laws, stated as W_contract_x.lp_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the
   generic relation), HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: YCbqG.ARx_shadow_law's premise at
   every state), IMGC / BLKN (lib/B/W_kit_xb.v, for blk_off_imgB_x, image B's top 0x5fc000), and the allocator rules
   in their caller-context form, each at its own table with its closed trace fact: realloc (arealloc_cf_rule_c_x at
   CTX_R; the realloc call hands the rule the chain [], so its trace is the singleton [its return address 0x853e4 =
   list_push + 0xc0], HCTX_lp_realloc) and malloc (amalloc_cf_rule_c_x at CTX_M; [0x85408 = list_push + 0xe4],
   HCTX_lp_malloc); AMEMCPY is W_sites_x.aintrin_realizes_x OCpy.  Image A's second segment is its own files
   (lib/A/W_list_push_tail.v, W_lp_tail.v); here it is lp_tail_seg below, converted in place with A's delta. ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the room invariant and the live counts, as W_contract_x.v Section w2 *)
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
(* the request bound of the allocator rules; at most 2 ^ 30, so that 2 * cap stays inside slliw's 32 bits *)
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
(* G misses errno and the runtime's two static cells the walk reads (the GOT slot of the shadow base and the
   cell); at PB_fr this is a vm_compute over G *)
Hypothesis HGR : gx_rt B G.
Lemma GX_RT : forall a, inG G a -> ~ (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) /\ ~ (VAL (A_OBJ 30) <= a < VAL (A_OBJ 30) + 8).
Proof. intros a Ha. exact (proj2 (HGR a Ha)). Qed.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xc0] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M.
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xe4] CTX_M.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* What holds at the malloc call, on both paths.
   - (W ly S regs mem md) is list_push's entry, with the spec's arguments LA SRC l lines x q k;
   - (Wc lyc Sc memc mdc kc regsc) is the state at the call, and lc the list as it is there: the same texts as l,
     the vector grown when l was full (its capacity is grow_cap N CAP > N), the count still N;
   - the registers hold what the code put there (s0 = LA+8, s1 = n, s2 = LA, s3 = SRC, s4 = LA+12, s5 = the shadow
     base SB, s6 / s8 the shadow addresses of LA+8 / LA+12, s7 = LA >> 3, a0 = n + 1; s9 / s10 are scratch), and
     the frame holds the caller's ra and s0 .. s10;
   - the blocks: the old vector replaced by the new one when l was full; the source still a live block other than
     the vector, holding x; the meter has paid the growth;
   - the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record), as image A's lib/A/W_list_push_tail.v lp_tail_pre_x: the tail's malloc at its
     own pre state Sc, with the room budget 1 + kr and the live counts. *)
Definition lp_tail_pre_x (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kc : Z) (lc : hlist)
(kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B lyc Sc Wc memc LA lc lines /\
hl_recs lc = hl_recs l /\ hl_cap lc = grow_cap (hl_n l) (hl_cap l) /\ hl_n lc < hl_cap lc /\
(lp_grow l = false -> hl_v lc = hl_v l) /\
(lp_grow l = true -> ~ In (hl_v lc, AREC * hl_cap lc) (ablocks B ly S)) /\
(forall rest,
 Permutation (ablocks B ly S) ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
 Permutation (ablocks B lyc Sc) ((if lp_grow l then [(hl_v lc, AREC * hl_cap lc)] else []) ++ rest)) /\
frames Sc = frames S /\
mo_le MT S Sc (if lp_grow l then mo_malloc MT (lp_vbytes l) + mo_free MT else 0) /\
mo_ok MT S (lp_cost MT l n) /\
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the tail's malloc at its own pre state Sc *)
rp_RM RP Sc (1 + kr) /\ cnt_ok RP (ablocks B lyc Sc) /\
blocks_bytes Sc + (n + 1) <= LIVE_MAX /\ n < 2 ^ 16 /\
garr8 SEGS (mrestrict (w_H Wc) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\
(lines = false -> (1 <= length x)%nat) /\
getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 22 = w64 SB /\
getr regsc 21 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (n + 1) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 96 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
Lemma lpt_inG_img : forall a, inG G a -> 0x10000 <= a < 0x5fc000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HG a Ha))). Qed.
(* the new block of an allocator call is disjoint from every block before it *)
Lemma lpt_new_disj : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 lyc Sc res n b m,
ARx ly2 S2 Hp2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> In (b, m) (ablocks B lyc Sc) ->
b + req_size m <= res \/ res + req_size n <= b.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 lyc Sc res n b m HAR2 Ebl Hin. apply in_split in Hin as (l1 & l2 & E1).
pose proof (sep_blocks_pos_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (b, m) (res, n) l1 l2 [] HAR2) as Hd.
rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.
(* a byte of the vector is one the journal lets list_push write: the vector of l (in lp_FP l) or the grown one *)
Lemma lpt_vec_awr : forall ly S l lc STK sp0 blc lyq ownq a,
hl_recs lc = hl_recs l -> hl_cap lc = grow_cap (hl_n l) (hl_cap l) -> hl_n lc < hl_cap lc ->
(lp_grow l = false -> hl_v lc = hl_v l) ->
(lp_grow l = true -> ~ In (hl_v lc, AREC * hl_cap lc) (ablocks B ly S)) ->
In (hl_v lc, AREC * hl_cap lc) blc -> hl_v lc <= a < hl_v lc + AREC * hl_cap lc ->
awr_byte STK sp0 (lp_FP l) (ablocks B ly S) blc lyq ownq a.
Proof.
intros ly S l lc STK sp0 blc lyq ownq a Hrecs Hcap Hnc Hv1 Hv2 Hin Ha.
assert (Hn0 : 0 <= hl_n lc) by (unfold hl_n; lia).
assert (Hreq : req_size (AREC * hl_cap lc) = AREC * hl_cap lc)
by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap lc) 0); lia).
destruct (lp_grow l) eqn:Hg.
- right; right; left. exists (hl_v lc), (AREC * hl_cap lc). split; [exact Hin|]. split; [exact (Hv2 eq_refl)|].
  rewrite Hreq. exact Ha.
- right; left. unfold lp_grow in Hg.
  assert (Hc : hl_cap lc = hl_cap l) by (rewrite Hcap; unfold grow_cap; rewrite Hg; reflexivity).
  split.
  + unfold lp_FP. destruct (Z.eqb_spec (hl_cap l) 0) as [H0|H0]; [lia|].
    exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity|]. cbn [fst snd].
    rewrite <- (Hv1 eq_refl), <- Hc. exact Ha.
  + exists (hl_v lc), (AREC * hl_cap lc). split; [exact Hin|]. rewrite Hreq. exact Ha.
Qed.
(* ---- the entry: the symbolic state at the call ---- *)
Lemma lpt_entry : forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
lp_tail_pre_x W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) ss_lpt
(restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)))
/\ sh_ok SEGS lpt_Bx lpt_SH (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) (mrestrict (w_H Wc) memc).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr HPRE.
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Hrecs & Hcap & Hnc & Hv1 & Hv2 & Hperm & Hfr & Hmle & Hmok & _ & _ & Hbb &
Hn16 & Hx & Hlin1 & Hlin2 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R22 & R21 & R23 & R24 & R10 & Hsaved & Hapk).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc HJ) as HAR.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc' & Hvec & _).
assert (Rn0 : 0 <= hl_n lc) by (unfold hl_n; lia).
destruct Hvec as [[Hc0 _] | (Hc0 & Hin & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hin) as (Hv16 & Hv4096 & Hvceil & Hvapp & Hvpres & _).
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc _ _ HAR Hin) as Hoff.
assert (Hreq : req_size (AREC * hl_cap lc) = 16 * hl_cap lc)
by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap lc) 0); lia).
rewrite Hreq in Hvceil, Hvapp, Hvpres, Hoff.
pose proof (lpt_inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (lpt_inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
assert (Hsp16 : (spZ regs - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 LA)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact R18).
assert (E22 : ew E 22 = w64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 22 22%bv eq_refl); exact R22).
assert (E44 : ew E 44 = Z_to_bv 64 (hl_v lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 (hl_n lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 13)).
assert (E46 : ew E 46 = Z_to_bv 64 (hl_cap lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 14)).
assert (E47 : ew E 47 = Z_to_bv 64 (hl_v lc + 16 * hl_n lc))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 15)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (CK : forall off j r, nth_error lp_saved j = Some (off, r) -> ew E (32 + j) = getr regs (Z_to_bv 5 r) ->
YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 96) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j r Hj Hew.
  apply (chunk_ok_val SEGS E _ (spZ regs - 96) off 8 _ (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite Hew, Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. zside.
  - zside.
  - rewrite Forall_forall in Hsaved. exact (Hsaved (off, r) (nth_error_In _ _ Hj)). }
split.
- unfold ss_lpt. apply pa_entry_st_ok_full.
  + unfold lpt_regs. repeat apply lpt_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg| ..].
    all: cbn [sv_denot]; rewrite ?E18, ?E22; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
    first [rewrite R8 | rewrite R20 | rewrite R21 | rewrite R23 | rewrite R24]; reflexivity.
  + vm_compute. reflexivity.
  + unfold lpt_regions, lpt_stack, lpt_lregion, lpt_slot.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [unfold spZ in *; lia|]. split; [unfold spZ in *; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
        apply (CK o (a - 32)%nat _ eq_refl); reflexivity end.
    * rewrite (VB 18%nat LA E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HwL; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ LA 0 8 _ (hl_v lc)); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mv.
      -- apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n lc)); [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
      -- apply (chunk_ok_val SEGS E _ LA 12 4 _ (hl_cap lc)); [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mc].
    * rewrite (VB 47%nat _ E47) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hvpres (hl_v lc + 16 * hl_n lc + o) ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold lpt_regions, lpt_stack, lpt_lregion, lpt_slot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 18%nat LA E18) by lia. rewrite (VB 47%nat _ E47) by lia.
    cbn [base_val]. rewrite Usp. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold spZ in *. unf_imgband. repeat split; lia.
  + split; [|split; [exact I | split; [|exact I]]].
    * cbn [lpt_facts f_atoms atoms_ok]. unfold afact_ok, HEAPF. cbn [af_lo af_hi af_al2].
      rewrite Usp, E9, E18, E22, E44, E45, E46, E47. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hsp16, Hv16.
      unfold spZ in *. repeat match goal with |- _ /\ _ => split end; lia.
    * cbn [lpt_facts f_alias alias_ok lpt_alias sv_denot]. rewrite E44, E45, E47. rewrite !unsigned_lit_small by lia.
      assert (S1 : zalu64 ALU_SLL (hl_n lc) 4 = hl_n lc * 2 ^ 4).
      { unfold zalu64. cbn [zalu_raw]. change (Z.land (zcanon 4) 63) with 4. unfold zcanon, M64.
        rewrite (Z.mod_small (hl_n lc)) by lia. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. }
      assert (S2 : zalu64 ALU_ADD (hl_v lc) (hl_n lc * 2 ^ 4) = hl_v lc + 16 * hl_n lc).
      { unfold zalu64. cbn [zalu_raw]. unfold zcanon, M64.
        rewrite (Z.mod_small (hl_v lc)), (Z.mod_small (hl_n lc * 2 ^ 4)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite !Z.add_0_r, !zalu64_sound, S1, S2. reflexivity.
- unfold sh_ok, lpt_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E lpt_Bx 18 LA 16 LA 0 16).
    * exact (azs_range_addressable_x B ARx LAWS lyc Sc Hpc Wc memc mdc LA 16 HAR HZ).
    * unfold U, lpt_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros y Hy. unfold SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E lpt_Bx 47 (hl_v lc + 16 * hl_n lc) 16 (hl_v lc + 16 * hl_n lc) 0 16).
    * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc Wc memc mdc (hl_v lc) (AREC * hl_cap lc)); [exact HAR | exact Hin | lia |].
      rewrite Hreq. lia.
    * unfold U, lpt_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hvapp. unfold SHADOW_OFF. lia.
Qed.
(* ---- the list's memory after the push ---- *)
Lemma lpt_len_text_recs : forall l, length (concat (map text_rec l)) = (16 * length l)%nat.
Proof.
induction l as [|r l IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
Lemma lpt_garr8_moved : forall H H' (m m' : word -> option byte) a b l,
(forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (b + j) = aview SEGS H m (a + j)) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') b l.
Proof.
intros H H' m m' a b l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (b + Z.of_nat j) 1); [|exact Hv].
intros k Hk. rewrite <- !Z.add_assoc. apply HK. lia.
Qed.
(* the vector: the old prefix, the new slot (block, length), the rest of the old junk *)
Lemma lpt_vec_garr8 : forall H H' (mc mf : word -> option byte) v recs junk d x,
(16 <= length junk)%nat ->
garr8 SEGS (mrestrict H mc) v (bzs (concat (map text_rec recs) ++ junk)) ->
(forall a, v <= a < v + 16 * Z.of_nat (length recs) \/
  v + 16 * Z.of_nat (length recs) + 16 <= a < v + 16 * Z.of_nat (length recs) + Z.of_nat (length junk) ->
  aview SEGS H' mf a = aview SEGS H mc a) ->
0 <= d < 2 ^ 64 -> Z.of_nat (length x) < 2 ^ 64 ->
val_mem SEGS (mrestrict H' mf) (v + 16 * Z.of_nat (length recs)) 8 d ->
val_mem SEGS (mrestrict H' mf) (v + 16 * Z.of_nat (length recs) + 8) 8 (Z.of_nat (length x)) ->
garr8 SEGS (mrestrict H' mf) v (bzs (concat (map text_rec (recs ++ [(d, x)])) ++ skipn 16 junk)).
Proof.
intros H H' mc mf v recs junk d x Hj16 Hold HK Hd Hn V0 V8.
assert (LP : Z.of_nat (length (bzs (concat (map text_rec recs)))) = 16 * Z.of_nat (length recs))
by (unfold bzs; rewrite length_map, lpt_len_text_recs; lia).
unfold bzs in Hold. rewrite map_app in Hold. apply garr8_app in Hold as [Hp Hj]. fold (bzs (concat (map text_rec recs))) in Hp, Hj.
rewrite LP in Hj.
rewrite <- (firstn_skipn 16 junk) in Hj. rewrite map_app in Hj. apply garr8_app in Hj as [_ Hj].
rewrite length_map, length_firstn in Hj. replace (Init.Nat.min 16 (length junk)) with 16%nat in Hj by lia.
rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
unfold bzs. rewrite <- app_assoc, !map_app. apply garr8_app. split.
- apply (lpt_garr8_kept H H' mc mf v); [|exact Hp].
  intros j Hjj. apply HK. left. fold (bzs (concat (map text_rec recs))) in Hjj. lia.
- fold (bzs (concat (map text_rec recs))). rewrite LP. apply garr8_app. split.
  + unfold text_rec. cbn [fst snd]. rewrite map_app. apply garr8_app. split.
    * fold (bzs (Mem.le8 (Z_to_bv 64 d))). apply lpt_garr8_of_val8; [exact Hd | exact V0].
    * rewrite length_map, Mem.length_le8. fold (bzs (Mem.le8 (Z_to_bv 64 (Z.of_nat (length x))))).
      replace (v + 16 * Z.of_nat (length recs) + Z.of_nat 8) with (v + 16 * Z.of_nat (length recs) + 8) by lia.
      apply lpt_garr8_of_val8; [lia | exact V8].
  + replace (Z.of_nat (length (map bz (text_rec (d, x))))) with 16
    by (rewrite length_map; unfold text_rec; rewrite length_app, !Mem.length_le8; reflexivity).
    apply (lpt_garr8_kept H H' mc mf _); [|replace (v + 16 * Z.of_nat (length recs) + 16) with
      (v + 16 * Z.of_nat (length recs) + Z.of_nat 16) by lia; exact Hj].
    intros j Hjj. apply HK. right. rewrite length_map, length_skipn in Hjj. lia.
Qed.
(* ---- frame helpers ---- *)
Lemma lpt_not_wrange : forall E rs a,
Forall (fun r => ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r)) rs ->
~ in_wrange E rs a.
Proof. intros E rs a HF (r & Hin & Hr). rewrite Forall_forall in HF. exact (HF r Hin Hr). Qed.
(* the bytes SEG3 / SEG4 may write: the list struct (atom 18), the vector slot (atom 47), the NUL (atom 80) *)
Ltac lp_nowr U18x U47x := apply lpt_not_wrange;
lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18x, ?U47x; lia.
Ltac lp_nowr3 U80x U18x U47x := apply lpt_not_wrange;
lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end;
repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U80x, ?U18x, ?U47x; lia.
(* SEG3's write permission: the frame, the list struct in G, the slot of the vector *)
Ltac lp_awr_mid U18x U47x HGLx HSLOTx Hvx :=
lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|];
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18x in Ha;
  right; left; apply HGLx; lia|];
apply awr_ok_x_cons; [|apply awr_ok_x_nil]; intros a Ha;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
rewrite U47x in Ha; left; split; [apply HSLOTx; [exact Hvx | lia] | lia].
(* SEG4's write permission: the NUL byte of the new block, then SEG3's three *)
Ltac lp_awr_end U80x U18x U47x HGLx HSLOTx Hvx AWRDx :=
lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U80x in Ha;
  left; split; [apply AWRDx; lia | lia]|];
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|];
apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18x in Ha;
  right; left; apply HGLx; lia|];
apply awr_ok_x_cons; [|apply awr_ok_x_nil]; intros a Ha;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
rewrite U47x in Ha; left; split; [apply HSLOTx; [exact Hvx | lia] | lia].
Lemma lpt_apresent_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
assert (Hx : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
specialize (Hg _ Hx). unfold mrestrict in Hg. rewrite Hh in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; reflexivity].
Qed.
(* an image byte stays writable when its presence is kept *)
Lemma lpt_writable_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (mrestrict (w_H Wa) m) a -> writable_at SEGS (mrestrict (w_H Wb) m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, mrestrict in *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma lpt_inG_not_owned : forall ly S Hp (W : world SEGS) m md a, ARx ly S Hp W m md -> inG G a -> ~ aowned B ly S a.
Proof.
intros ly S Hp W m md a HAR Ha Ho.
exact (proj1 (proj2 (HG a Ha)) (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W m md a HAR (proj1 (HG a Ha))) Ho)).
Qed.
(* the shadow entries of the list struct and of the slot, at any AR state that still has the vector *)
Lemma lpt_shok : forall Ex ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 LA v N cap,
ARx ly2 S2 Hp2 W2 mem2 md2 -> azs B LA 16 -> 0x10000 <= LA -> LA + 16 <= 0x5fc000 ->
In (v, AREC * cap) (ablocks B ly2 S2) -> 0 <= N < cap ->
ew Ex 18 = w64 LA -> ew Ex 22 = w64 SB -> ew Ex 47 = Z_to_bv 64 (v + 16 * N) ->
sh_ok SEGS lpt_Bx lpt_SH Ex (mrestrict (w_H W2) mem2).
Proof.
intros Ex ly2 S2 Hp2 W2 mem2 md2 LA v N cap HAR HZ HL0 HL1 Hin HN X18 X21 X47.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR Hin) as (_ & Hv4096 & Hvceil & Hvapp & _).
assert (Hreq : req_size (AREC * cap) = 16 * cap) by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * cap) 0); lia).
rewrite Hreq in Hvceil, Hvapp.
assert (UB : U Ex lpt_Bx = SHADOW_OFF).
{ unfold U, lpt_Bx. cbn [sv_denot]. rewrite X21, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SB; lia). reflexivity. }
unfold sh_ok, lpt_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W2) mem2 Ex lpt_Bx 18 LA 16 LA 0 16).
  + exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 LA 16 HAR HZ).
  + exact UB.
  + unfold U. cbn [sv_denot]. rewrite X18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros y Hy. unfold SHADOW_OFF in *. lia.
- apply (shent_ok_of_range SEGS (w_H W2) mem2 Ex lpt_Bx 47 (v + 16 * N) 16 (v + 16 * N) 0 16).
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 mem2 md2 v (AREC * cap)); [exact HAR | exact Hin | lia |].
    rewrite Hreq. lia.
  + exact UB.
  + unfold U. cbn [sv_denot]. rewrite X47, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hvapp. unfold SHADOW_OFF. lia.
Qed.
(* ---- SEG3 and SEG4: the malloc call 0x85404 to the ret ---- *)
Lemma lp_tail_seg : forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
In (q, k) (ablocks B lyc Sc) -> q <> hl_v lc -> q <= SRC -> SRC + Z.of_nat (length x) <= q + req_size k ->
lp_tail_pre_x W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)) mdc)
(lp_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines x kr).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr Hq Hqv HqS HqE HPRE.
destruct (lpt_entry W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr HPRE) as [HS SHOK].
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Hrecs & Hcap & Hnc & Hv1 & Hv2 & Hperm & Hfrm & Hmle & Hmok & HRM & Hcnt & Hbb &
Hn16 & Hx & Hlin1 & Hlin2 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R22 & R21 & R23 & R24 & R10 & Hsaved & Hapk & Herrc).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc HJ) as HARc.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc' & Hvec & HND & HVR & HRECS).
assert (Rn0 : 0 <= hl_n lc) by (unfold hl_n; lia).
destruct Hvec as [[Hc0 _] | (Hc0 & Hin & Hjunk & Hgarr)]; [lia|].
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as (Hv16 & Hv4096 & Hvceil & Hvapp & Hvpres & _).
assert (Hreq : req_size (AREC * hl_cap lc) = 16 * hl_cap lc)
by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap lc) 0); lia).
rewrite Hreq in Hvceil, Hvapp, Hvpres.
pose proof (lpt_inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (lpt_inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as Hoff. rewrite Hreq in Hoff. unf_imgband.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hq) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _).
assert (Hn0 : 0 <= Z.of_nat (length x)) by lia.
assert (Hsp : alloc_ceiling + 16384 <= spZ regs - 96 /\ spZ regs <= 2 ^ 47) by (unfold spZ in *; lia).
(* errno's four bytes: image bytes, outside the list struct (gx_rt) *)
pose proof (pal_env B TL) as (_ & HeImg & _).
assert (HER : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i) /\ 0x10000 <= as_errno B + i < 0x5fc000 /\
  ~ (LA <= as_errno B + i < LA + 16)).
{ intros i Hi. assert (HI : in_img SEGS (as_errno B + i)) by (apply HeImg; clear - Hi; lia).
  split; [exact HI|]. split; [exact (pa_img_range _ HI)|].
  intros Hc. exact (proj1 (HGR _ (HGL _ Hc)) ltac:(clear - Hi; lia)). }
remember (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regsc (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
clear HE.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E3 : ew E 3 = getr regs 3) by exact (eq_trans (EA 3%nat ltac:(lia)) R3).
assert (E4 : ew E 4 = getr regs 4) by exact (eq_trans (EA 4%nat ltac:(lia)) R4).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x))) by exact (eq_trans (EA 9%nat ltac:(lia)) R9).
assert (E10 : ew E 10 = w64 (Z.of_nat (length x) + 1)) by exact (eq_trans (EA 10%nat ltac:(lia)) R10).
assert (E18 : ew E 18 = w64 LA) by exact (eq_trans (EA 18%nat ltac:(lia)) R18).
assert (E19 : ew E 19 = w64 SRC) by exact (eq_trans (EA 19%nat ltac:(lia)) R19).
assert (E22 : ew E 22 = w64 SB) by exact (eq_trans (EA 22%nat ltac:(lia)) R22).
assert (E27 : ew E 27 = getr regs 27) by exact (eq_trans (EA 27%nat ltac:(lia)) R27).
assert (E47 : ew E 47 = Z_to_bv 64 (hl_v lc + 16 * hl_n lc)) by exact (EX 15%nat ltac:(lia)).
assert (U18 : bv_unsigned (ew E 18) = LA) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U47 : bv_unsigned (ew E 47) = hl_v lc + 16 * hl_n lc) by (rewrite E47; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HSLOT : forall blc lyq a, In (hl_v lc, AREC * hl_cap lc) blc -> hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16 ->
awr_byte LP_STK (spZ regs) (lp_FP l) (ablocks B ly S) blc lyq [] a)
by (intros blc lyq a Hb Ha; apply (lpt_vec_awr ly S l lc); try assumption; unfold AREC; lia).
unfold cfg_at.
(* R1: the jal to malloc *)
paj_run_tok_x RUN HS HJ SHOK lpt_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    right; left; apply HGL; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite U47 in Ha. left. split; [apply HSLOT; [exact Hin | lia] | lia]. }
rename HFr into HFr1, HG0 into HGr1. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H Wc) (ms_mem ms1) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha H1 H2. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms1) HFr1 a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18, ?U47; lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 96) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; unfold spZ in *; lia).
destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
(* malloc(n + 1) *)
eapply SRr_bind.
{ rewrite (pal_malloc B TL).
  eapply (AMA Wc (ms_regs ms1) (ms_mem ms1) LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] lyc Sc Hpc _ kc
    (Z.of_nat (length x) + 1) (-96) _ [] kr HJi).
  - rewrite Q10, E10. reflexivity.
  - lia.
  - exact Hbb.
  - exact Hcnt.
  - rewrite Usp1. lia.
  - reflexivity.
  - lia.
  - lia.
  - eapply aj_stack_room_x with (o := -96); [exact HJi | rewrite Usp1; lia | lia].
  - rewrite Q3, E3. exact Hgp.
  - rewrite Q4, E4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre lyc _ (spZ regs - 96) (LA + 8) [] (ms_regs ms1)).
    + apply achain_low. lia.
    + rewrite Usp1. lia.
    + unfold s0Z. rewrite Q8, E18. unfold w64. rewrite (unsigned_lit_small LA) by lia. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - cbn [spine]. replace (raZ (ms_regs ms1)) with (BASE + AF_fr_list_push + 0xe4); [exact HCTX_lp_malloc|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    first [lia | (unfold A_lp_mcall in *; lia) | (unfold A_lp_mcall, AF_fr_list_push in *; lia) |
           (idtac "LPT-CTX-RA"; match goal with |- ?g => idtac g end; fail)].
  - exact HRM.
  - apply (mok_station MT S Sc (lp_cost MT l (Z.of_nat (length x))) _ _ MLAW Hmok Hmle).
    + apply (mo_malloc_nonneg MT MLAW). lia.
    + unfold lp_cost. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & d & -> & HJ2i & HP2 & Hd10 & Hfr2 & Hd4096 & Hbl2 & Hkept2 &
Hmle2 & HRM2 & Herr2 & Hpres2).
(* ---- after malloc: d (atom 52) is a new block of n + 1 bytes ---- *)
pose proof (proj1 HJ2i) as HAR2.
assert (Hreqd : req_size (Z.of_nat (length x) + 1) = Z.of_nat (length x) + 1)
by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length x) + 1) 0); lia).
assert (Hdn : In (d, Z.of_nat (length x) + 1) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Hvin2 : In (hl_v lc, AREC * hl_cap lc) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hin).
assert (Hqin2 : In (q, k) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hq).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hdn) as (Hd16 & _ & Hdceil & Hdapp & Hdpres & _).
rewrite Hreqd in Hdceil, Hdapp, Hdpres.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hvin2) as (_ & _ & _ & _ & Hvpres2 & _).
rewrite Hreq in Hvpres2.
pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hin) as Ddv. rewrite Hreq, Hreqd in Ddv.
pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hq) as Ddq. rewrite Hreqd in Ddq.
assert (Hne : (q, k) <> (hl_v lc, AREC * hl_cap lc)) by (intros He; injection He as He1 _; exact (Hqv He1)).
pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc q k _ _ HARc Hq Hin Hne) as Dqv.
rewrite Hreq in Dqv. unfold zdisjoint in Dqv. cbn [fst snd] in Dqv.
assert (NOTLA : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (LA <= a < LA + 16)).
{ intros b m a Hbm Ha HLa. apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc b m a HARc Hbm Ha). exact (proj1 (HG a (HGL a HLa))). }
assert (KM : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
~ (d <= a < d + (Z.of_nat (length x) + 1)) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms1) a).
{ intros b m a Hbm Ha Hnd. destruct Hkept2 as (_ & K2 & _). replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hbm); [lia|]. cbv beta. rewrite Hreqd. replace (b + (a - b)) with a by lia. exact Hnd. }
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18, ?U47.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 Hkept2); [lia | lia].
  - intros a Ha. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct Hkept2 as (_ & _ & K3 & _). apply K3.
    + exact (proj1 (HG a (HGL a ltac:(lia)))).
    + exact (proj1 (proj2 (HG a (HGL a ltac:(lia))))).
    + exact (proj1 (HGR a (HGL a ltac:(lia)))).
  - intros a Ha Hw. apply (lpt_writable_img Wc W2 (ms_mem ms1) mem2 a); [exact (proj1 (HG a (HGL a ltac:(lia)))) | | exact Hw].
    intros Hpa. apply Hpres2; [exact (proj1 (HG a (HGL a ltac:(lia))))
    | exact (lpt_inG_not_owned lyc Sc Hpc Wc _ _ a (proj1 HJi) (HGL a ltac:(lia)))
    | exact (lpt_inG_not_owned ly2 S2 Hp2 W2 mem2 md2 a HAR2 (HGL a ltac:(lia)))
    | exact (proj1 (HGR a (HGL a ltac:(lia))))
    | rewrite Hreqd; intros Hb; apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ a HAR2 Hdn); [rewrite Hreqd; lia|];
      exact (proj1 (HG a (HGL a ltac:(lia))))
    | exact Hpa].
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (KM (hl_v lc) (AREC * hl_cap lc) a Hin); [rewrite Hreq; unfold AREC in *; lia | lia].
  - intros a Ha _. apply (apresent_writable SEGS). exact (proj1 (Hvpres2 a ltac:(lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea52 : ew Ea 52 = w64 d) by (rewrite HEa; exact Hd10).
clear HEa.
assert (HFa : afact_ok Ea 52 (mkAF 4096 0x7fffff800000 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea52. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite Hd16. lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 52%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ2 : ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (kc + 1)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (kc + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | apply out_none]. }
assert (U18a : bv_unsigned (ew Ea 18) = LA) by (rewrite OLDa by lia; exact U18).
assert (U47a : bv_unsigned (ew Ea 47) = hl_v lc + 16 * hl_n lc) by (rewrite OLDa by lia; exact U47).
assert (SHOK2 : sh_ok SEGS lpt_Bx lpt_SH Ea (mrestrict (w_H W2) mem2)).
{ apply (lpt_shok Ea ly2 S2 Hp2 W2 mem2 md2 LA (hl_v lc) (hl_n lc) (hl_cap lc) HAR2 HZ ltac:(lia) ltac:(lia) Hvin2 ltac:(lia));
  rewrite OLDa by lia; [exact E18 | exact E22 | exact E47]. }
(* R2: 0x85408 .. the jal to __asan_memcpy (0x8547c), through four UBSan trap branches *)
assert (EV44 : ew E 44 = Z_to_bv 64 (hl_v lc)) by exact (EX 12%nat ltac:(lia)).
assert (Ea44 : ew Ea 44 = Z_to_bv 64 (hl_v lc)) by (rewrite OLDa by lia; exact EV44).
assert (Ea47 : ew Ea 47 = Z_to_bv 64 (hl_v lc + 16 * hl_n lc)) by (rewrite OLDa by lia; exact E47).
assert (UA44 : U Ea (SOff 44 0) = hl_v lc) by (apply (U_atom Ea 44 _ Ea44); lia).
assert (UA47 : U Ea (SOff 47 0) = hl_v lc + 16 * hl_n lc) by (apply (U_atom Ea 47 _ Ea47); lia).
assert (Hsl8 : (hl_v lc + 16 * hl_n lc) mod 8 = 0) by (apply lp_mod8_of_16; [exact Hv16 | lia]).
paj_run_tok_x RUN HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrA, HG0 into HGrA. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msA end.
assert (Kw1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msA) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem msA) HFrA a Ha); lp_nowr U18a U47a).
(* 0x85434 NULL-CONSISTENCY of v and the slot v + 16 N: the runner folded `snez v` to 1 (fact atom 44), so the
   trap edge is `1 =? seqz (v + 16 N)` and W_traps' trap_U_seqz gives the second as 0 *)
psrr_branch_tok RUN BR HS SHOK2 lpt_Bspan.
{ exfalso. lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
  rewrite trap_br_eq, (U_lit Ea 1 ltac:(lia)), (trap_U_seqz Ea (SOff 47 0) _ UA47 ltac:(lia)) in H; discriminate end. }
paj_run_tok_x RUN HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrB, HG0 into HGrB. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msB end.
assert (Kw2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msA) (ms_mem msB) HFrB a Ha ltac:(lp_nowr U18a U47a));
    apply Kw1; assumption).
(* 0x85448 POINTER OVERFLOW with a signed index: slti N,0 is 0 (fact atom 45) and sltu (v + 16 N) v is 0 *)
psrr_branch_tok RUN BR HS SHOK2 lpt_Bspan.
{ lp_trap (trap_ptr_sovf Ea (SAlu ALU_SLTU (SOff 47 0) (SOff 44 0)) (SLit 0) 0
    (trap_U_sltu_ge Ea (SOff 44 0) (SOff 47 0) (hl_v lc) (hl_v lc + 16 * hl_n lc) UA44 UA47 ltac:(lia))
    (U_lit Ea 0 ltac:(lia))). }
paj_run_tok_x RUN HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrC, HG0 into HGrC. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msC end.
assert (Kw3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msB) (ms_mem msC) HFrC a Ha ltac:(lp_nowr U18a U47a));
    apply Kw2; assumption).
(* 0x85454 ALIGN8 of the slot: v is 16-aligned (al_blocks), so v + 16 N is 8-aligned *)
psrr_branch_tok RUN BR HS SHOK2 lpt_Bspan.
{ lp_trap (trap_align8 Ea (SOff 47 0) (hl_v lc + 16 * hl_n lc) UA47 Hsl8). }
paj_run_tok_x RUN HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrD, HG0 into HGrD. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msD end.
assert (Kw4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msD) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msC) (ms_mem msD) HFrD a Ha ltac:(lp_nowr U18a U47a));
    apply Kw3; assumption).
(* 0x8546c NON-NULL of the slot *)
psrr_branch_tok RUN BR HS SHOK2 lpt_Bspan.
{ lp_trap (trap_nonnull Ea (SOff 47 0) (hl_v lc + 16 * hl_n lc) UA47 ltac:(lia)). }
paj_run_tok_x RUN HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFr2, HG0 into HGrE. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msD) (ms_mem ms2) HFr2 a Ha ltac:(lp_nowr U18a U47a));
    apply Kw4; assumption).
pose proof (mem_grows_trans _ _ _ HGrA (mem_grows_trans _ _ _ HGrB
  (mem_grows_trans _ _ _ HGrC (mem_grows_trans _ _ _ HGrD HGrE)))) as HGr2.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (Usp2 : spZ (ms_regs ms2) = spZ regs - 96).
{ unfold spZ. rewrite P2. rewrite OLDa by lia. rewrite E2. apply unsigned_lit_small. unfold spZ in *. lia. }
pose proof (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2m.
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hdn) as Hdoff. rewrite Hreqd in Hdoff. unf_imgband.
(* the source bytes at the call are the ones at the malloc call *)
assert (KS : forall i, 0 <= i < Z.of_nat (length x) ->
aview SEGS (w_H W2) (ms_mem ms2) (SRC + i) = aview SEGS (w_H Wc) memc (SRC + i)).
{ intros i Hi. assert (Hb : q <= SRC + i < q + req_size k) by lia.
  rewrite K2 by (first [exact (NOTLA q k (SRC + i) Hq Hb) | unfold AREC in *; lia]).
  rewrite (KM q k (SRC + i) Hq Hb) by lia.
  apply K1; [lia | exact (NOTLA q k (SRC + i) Hq Hb) | unfold AREC in *; lia]. }
destruct HJ2 as (HSTK2 & HXO2 & (memS2 & HJi2 & HAG2) & HOUT2). rewrite !Z.add_0_r in HJi2.
(* __asan_memcpy(d, SRC, n) *)
eapply SRr_bind.
{ eapply (aj_intrin_at_x B PST ARx LAWS OCpy (SIGMA WS_asan_memcpy) AMEMCPY W2 (ms_regs ms2) (ms_mem ms2) LP_STK (spZ regs)
    (lp_FP l) ly S Hp W memS2 md [] ly2 S2 Hp2 _ (kc + 1) d SRC (Z.of_nat (length x)) (-96) _ HJi2).
  - rewrite P10, Ea52. reflexivity.
  - rewrite P11. rewrite OLDa by lia. exact E19.
  - rewrite P12. rewrite OLDa by lia. exact E9.
  - lia.
  - lia.
  - lia.
  - rewrite Usp2. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite P3. rewrite OLDa by lia. rewrite E3. exact Hgp.
  - rewrite P4. rewrite OLDa by lia. rewrite E4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia].
    replace a with (d + (a - d)) by lia.
    eapply (awr_new_block_any_x SEGS B PST ARx LAWS LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] lyc Sc Hpc Wc (ms_mem ms1) _ kc
      ly2 S2 Hp2 W2 mem2 md2 d (Z.of_nat (length x) + 1) (ablocks B ly2 S2) (a - d) ly2 [] HJi HAR2 Hbl2);
    [lia | exact Hdn | rewrite Hreqd; lia].
  - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ d (Z.of_nat (length x) + 1));
    [exact HAR2m | exact Hdn | lia | rewrite Hreqd; lia].
  - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ d (Z.of_nat (length x) + 1));
    [exact HAR2m | exact Hdn | lia | rewrite Hreqd; lia].
  - intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ d (Z.of_nat (length x) + 1));
    [exact HAR2m | exact Hdn | lia | rewrite Hreqd; lia | exact Hpos].
  - split; [lia|]. split; [lia|]. split; [|split; [lia|]].
    + intros a Ha. split; [|rewrite Usp2; lia].
      replace a with (SRC + Z.of_nat (Z.to_nat (a - SRC))) by lia. rewrite KS by lia.
      unfold aview. rewrite (garr8_mbyte SEGS _ SRC _ (Z.to_nat (a - SRC)) Hx) by (unfold bzs; rewrite length_map; lia).
      discriminate.
    + split; [eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ q k); [exact HAR2m | exact Hqin2 | lia | lia]|].
      split; [eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ q k); [exact HAR2m | exact Hqin2 | lia | lia]|].
      intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ q k);
      [exact HAR2m | exact Hqin2 | lia | lia | exact Hpos]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3i & HP3 & Hd10b & Hcpy & Hfr3 & Hpres3).
(* ---- after __asan_memcpy ---- *)
assert (Usp2a : bv_unsigned (ew Ea 2) = spZ regs - 96) by (rewrite OLDa by lia; exact Usp).
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 2 (spZ regs - 96)); [exact Usp2a | | exact Hpres3].
    intros a Ha. apply Hfr3; lia.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 18 LA); [exact U18a | | exact Hpres3].
    intros a Ha. apply Hfr3; lia.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 47 (hl_v lc + 16 * hl_n lc)); [exact U47a | | exact Hpres3].
    intros a Ha. apply Hfr3; unfold AREC in *; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 64 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 64)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
(* the byte d + n: atom 80, its fact, its alias, its region *)
pose proof (st_ok_pi_havoc 80 Eb _ _ [w64 (d + Z.of_nat (length x))] HS ltac:(vm_compute; reflexivity) ltac:(cbv; lia)) as HSc.
clear HS. rename HSc into HS.
remember (havoc Eb 80 [w64 (d + Z.of_nat (length x))]) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 80)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (Ec80 : ew Ec 80 = w64 (d + Z.of_nat (length x))) by (rewrite HEc; reflexivity).
clear HEc.
assert (Ec52 : ew Ec 52 = w64 d) by (rewrite OLDc, OLDb by lia; exact Ea52).
assert (Ec9 : ew Ec 9 = w64 (Z.of_nat (length x))) by (rewrite OLDc, OLDb, OLDa by lia; exact E9).
assert (U80 : bv_unsigned (ew Ec 80) = d + Z.of_nat (length x)) by (rewrite Ec80; apply unsigned_lit_small; lia).
assert (U18c : bv_unsigned (ew Ec 18) = LA) by (rewrite OLDc, OLDb by lia; exact U18a).
assert (U47c : bv_unsigned (ew Ec 47) = hl_v lc + 16 * hl_n lc) by (rewrite OLDc, OLDb by lia; exact U47a).
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs - 96) by (rewrite OLDc, OLDb by lia; exact Usp2a).
assert (HFc : afact_ok Ec 80 HEAPF) by (unfold afact_ok, HEAPF; cbn [af_lo af_hi af_al2]; rewrite U80; rewrite Z.pow_0_r, Z.mod_1_r; lia).
pose proof (st_ok_pi_add_fact Ec _ _ 80%nat _ HS HFc) as HSc. clear HS HFc. rename HSc into HS.
assert (HAc : sv_denot Ec (SAlu ALU_ADD (SOff 52 0) (SOff 9 0)) = sv_denot Ec (SOff 80 0)).
{ cbn [sv_denot]. rewrite Ec52, Ec9, Ec80. unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r, zalu64_sound.
  apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
  rewrite (Z.mod_small d), (Z.mod_small (Z.of_nat (length x))) by lia. apply Z.mod_mod. lia. }
pose proof (st_ok_pi_add_alias Ec _ _ _ _ HS HAc) as HSc. clear HS HAc. rename HSc into HS.
assert (Hpd : forall i, 0 <= i <= Z.of_nat (length x) -> apresent (w_H W2) mem3 (d + i)).
{ intros i Hi. apply Hpres3. apply (lpt_apresent_grows _ mem2 _ _ HGr2). exact (proj1 (Hdpres (d + i) ltac:(lia))). }
pose proof (st_ok_pi_add_region Ec _ _ lpt_aE HS ltac:(vm_compute; reflexivity)) as HSc.
match type of HSc with ?ty -> _ => assert (HRG : ty); [|specialize (HSc HRG); clear HRG] end.
{ unfold lpt_aE, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite U80. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). replace (d + Z.of_nat (length x) + o) with (d + Z.of_nat (length x)) by lia.
  apply Hpd. lia. }
match type of HSc with ?ty -> _ => assert (HRD : ty); [|specialize (HSc HRD); clear HRD] end.
{ lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  unfold lpt_aE. cbn [all_disjoint]. unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U80, Uspc, U18c, U47c. unfold spZ in *. unfold AREC in *. repeat split; lia. }
clear HS. rename HSc into HS.
assert (HJ3 : ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem3 md3 (kc + 1)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem3 md3 (kc + 1) memS2);
  [lia | lia | rewrite !Z.add_0_r; exact HJ3i | exact HAG2 | apply out_none]. }
pose proof (proj1 HJ3i) as HAR3.
assert (SHOK3 : sh_ok SEGS lpt_Bx lpt_SH3 Ec (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, lpt_SH3. apply Forall_app. split.
  - apply (lpt_shok Ec ly2 S2 Hp2 W2 mem3 md3 LA (hl_v lc) (hl_n lc) (hl_cap lc) HAR3 HZ ltac:(lia) ltac:(lia) Hvin2 ltac:(lia));
    rewrite OLDc, OLDb, OLDa by lia; [exact E18 | exact E22 | exact E47].
  - constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W2) mem3 Ec lpt_Bx 80 (d + Z.of_nat (length x)) 1 (d + Z.of_nat (length x)) 0 1).
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 mem3 md3 d (Z.of_nat (length x) + 1)); [exact HAR3 | exact Hdn | lia |].
      rewrite Hreqd. lia.
    + unfold U, lpt_Bx. cbn [sv_denot]. rewrite OLDc, OLDb, OLDa by lia. rewrite E22, Z.add_0_r. unfold w64.
      rewrite Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Ec80, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hdapp. unfold SHADOW_OFF. lia. }
(* R3: 0x85480 .. the ret, through two UBSan trap branches: the NUL at d + n, the slot length,
   l->n = n + 1, the epilogue *)
assert (UC52 : U Ec (SOff 52 0) = d) by (apply (U_atom Ec 52 _ Ec52); lia).
assert (UC80 : U Ec (SOff 80 0) = d + Z.of_nat (length x)) by (apply (U_atom Ec 80 _ Ec80); lia).
assert (AWRD : forall a, d <= a < d + (Z.of_nat (length x) + 1) ->
awr_byte LP_STK (spZ regs) (lp_FP l) (ablocks B ly S) (ablocks B ly2 S2) ly2 [] a).
{ intros a Ha. replace a with (d + (a - d)) by lia.
  eapply (awr_new_block_any_x SEGS B PST ARx LAWS LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] lyc Sc Hpc Wc (ms_mem ms1) _ kc
    ly2 S2 Hp2 W2 mem2 md2 d (Z.of_nat (length x) + 1) (ablocks B ly2 S2) (a - d) ly2 [] HJi HAR2 Hbl2);
  [lia | exact Hdn | rewrite Hreqd; lia]. }
paj_run_tok_x RUN HS HJ3 SHOK3 lpt_Bspan.
{ lp_awr_end U80 U18c U47c HGL HSLOT Hvin2 AWRD. }
lp_clearbr.
rename HFr into HFrF, HG0 into HGrF. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msF end.
assert (Kw5 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
~ (d + Z.of_nat (length x) <= a < d + Z.of_nat (length x) + 1) ->
aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem3 a)
by (intros a Ha H1 H2 H3; apply (aview_kept_out _ _ (w_H W2) mem3 (ms_mem msF) HFrF a Ha); lp_nowr3 U80 U18c U47c).
(* 0x854e4 POINTER OVERFLOW of d + n: no unsigned wrap, d <= d + n *)
psrr_branch_tok RUN BR HS SHOK3 lpt_Bspan.
{ lp_trap (trap_ptr_bltu Ec (SOff 52 0) (SOff 80 0) d (d + Z.of_nat (length x)) UC52 UC80 ltac:(lia)). }
paj_run_tok_x RUN HS HJ3 SHOK3 lpt_Bspan.
{ lp_awr_end U80 U18c U47c HGL HSLOT Hvin2 AWRD. }
lp_clearbr.
rename HFr into HFrG, HG0 into HGrG. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msG end.
assert (Kw6 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
~ (d + Z.of_nat (length x) <= a < d + Z.of_nat (length x) + 1) ->
aview SEGS (w_H W2) (ms_mem msG) a = aview SEGS (w_H W2) mem3 a)
by (intros a Ha H1 H2 H3;
    rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msF) (ms_mem msG) HFrG a Ha ltac:(lp_nowr3 U80 U18c U47c));
    apply Kw5; assumption).
(* 0x854f4 NULL-CONSISTENCY of d and d + n: the runner folded `snez d` to 1 (fact atom 52) *)
psrr_branch_tok RUN BR HS SHOK3 lpt_Bspan.
{ exfalso. lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
  rewrite trap_br_eq, U_SAlu, (U_lit Ec 1 ltac:(lia)), (trap_U_seqz Ec (SOff 80 0) _ UC80 ltac:(lia)),
          (U_lit Ec 0 ltac:(lia)) in H; vm_compute in H; discriminate end. }
paj_run_tok_x RUN HS HJ3 SHOK3 lpt_Bspan.
{ lp_awr_end U80 U18c U47c HGL HSLOT Hvin2 AWRD. }
lp_clearbr.
rename HFr into HFr3, HG0 into HGrH. clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
pose proof (mem_grows_trans _ _ _ HGrF (mem_grows_trans _ _ _ HGrG HGrH)) as HGr3.
(* ---- at the ret ---- *)
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (22%bv : bv 5) F22. prreg HS (21%bv : bv 5) F21. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (OLDE : forall m, (m < 48)%nat -> ew Ec m = ew E m) by (intros m Hm; rewrite OLDc, OLDb, OLDa by lia; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msf)).
{ apply aregs_preserved_eqs.
  - rewrite F2, Uspc. replace (spZ regs - 96 + 96) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite F3, OLDE by lia. exact E3.
  - rewrite F4, OLDE by lia. exact E4.
  - rewrite F8, OLDE by lia. exact (EX 1%nat ltac:(lia)).
  - rewrite F9, OLDE by lia. exact (EX 2%nat ltac:(lia)).
  - rewrite F18, OLDE by lia. exact (EX 3%nat ltac:(lia)).
  - rewrite F19, OLDE by lia. exact (EX 4%nat ltac:(lia)).
  - rewrite F20, OLDE by lia. exact (EX 5%nat ltac:(lia)).
  - rewrite F21, OLDE by lia. exact (EX 6%nat ltac:(lia)).
  - rewrite F22, OLDE by lia. exact (EX 7%nat ltac:(lia)).
  - rewrite F23, OLDE by lia. exact (EX 8%nat ltac:(lia)).
  - rewrite F24, OLDE by lia. exact (EX 9%nat ltac:(lia)).
  - rewrite F25, OLDE by lia. exact (EX 10%nat ltac:(lia)).
  - rewrite F26, OLDE by lia. exact (EX 11%nat ltac:(lia)).
  - rewrite F27, OLDE by lia. exact E27. }
assert (ER1 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
(* the memory at the ret *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 80)%nat -> ew Ef m = ew Ec m) by (intros m Hm; subst Ef; rewrite !ew_ewset_other by lia; reflexivity).
assert (E44 : ew E 44 = Z_to_bv 64 (hl_v lc)) by exact (EX 12%nat ltac:(lia)).
assert (E45 : ew E 45 = Z_to_bv 64 (hl_n lc)) by exact (EX 13%nat ltac:(lia)).
assert (E46 : ew E 46 = Z_to_bv 64 (hl_cap lc)) by exact (EX 14%nat ltac:(lia)).
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RL.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RE.
cbn [ms_mem restrict] in RL, RS, RE.
assert (UFL : bv_unsigned (ew Ef 18) = LA) by (rewrite UF by lia; exact U18c).
assert (UFS : bv_unsigned (ew Ef 47) = hl_v lc + 16 * hl_n lc) by (rewrite UF by lia; exact U47c).
assert (UFE : bv_unsigned (ew Ef 80) = d + Z.of_nat (length x)).
{ subst Ef. rewrite !ew_ewset_other by lia. exact U80. }
assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v lc)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDE by lia. rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n lc + 1)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDE by lia. rewrite E45. rewrite unsigned_lit_small by lia. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap lc)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDE by lia. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (hl_v lc + 16 * hl_n lc + 0) (N.to_nat 8) d).
{ eapply (field_of_region Ef _ 47 _); [exact RS | exact UFS | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite Ec52. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VS8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (hl_v lc + 16 * hl_n lc + 8) (N.to_nat 8) (Z.of_nat (length x))).
{ eapply (field_of_region Ef _ 47 _); [exact RS | exact UFS | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite Ec9. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VE : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (d + Z.of_nat (length x) + 0) (N.to_nat 1) 0).
{ eapply (field_of_region Ef _ 80 _); [exact RE | exact UFE | cbn [In]; left; reflexivity | reflexivity | zside | zside]. }
rewrite Z.add_0_r in VL0, VS0, VE.
assert (HAWR : awr W2 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite UFL in RLw. exact (RLw i Hi). }
(* every old block byte outside the slot is the byte at the call *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) -> ~ (d + Z.of_nat (length x) <= a < d + Z.of_nat (length x) + 1) ->
aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha H1 H2 H3.
  rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msG) (ms_mem msf) HFr3 a Ha ltac:(lp_nowr3 U80 U18c U47c)).
  apply Kw6; assumption. }
assert (KB : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H Wc) memc a).
{ intros b m a Hbm Ha Hns.
  pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hbm) as Dn. rewrite Hreqd in Dn.
  pose proof (NOTLA b m a Hbm Ha) as Hla.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hbm) as (_ & Hb4096 & Hbc & _).
  rewrite K3 by lia. rewrite Hfr3 by lia. rewrite K2 by lia. rewrite (KM b m a Hbm Ha) by lia. apply K1; lia. }
assert (KD : forall i, 0 <= i < Z.of_nat (length x) ->
aview SEGS (w_H W2) (ms_mem msf) (d + i) = aview SEGS (w_H Wc) memc (SRC + i)).
{ intros i Hi. rewrite K3.
  - rewrite (Hcpy i Hi). apply KS. exact Hi.
  - lia.
  - intros HLa. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ (d + i) HAR2 Hdn); [rewrite Hreqd; lia|].
    exact (proj1 (HG _ (HGL _ HLa))).
  - unfold AREC in *. lia.
  - lia. }
(* the new text *)
assert (GD : garr8 SEGS (arm W2 (ms_mem msf)) d (bzs (x ++ [Z_to_bv 8 0]))).
{ unfold bzs, arm. rewrite map_app. apply garr8_app. split.
  - fold (bzs x). apply (lpt_garr8_moved (w_H Wc) (w_H W2) memc (ms_mem msf) SRC d); [|exact Hx].
    intros j Hj. unfold bzs in Hj. rewrite length_map in Hj. apply KD. lia.
  - rewrite length_map. intros j Hj. cbn [length map] in Hj. assert (j = 0%nat) as -> by lia. cbn [nth map].
    change (bz (Z_to_bv 8 0)) with 0. split; [|lia]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact VE. }
(* the old texts *)
assert (RECS : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly2 S2) /\
garr8 SEGS (arm W2 (ms_mem msf)) (fst r) (bzs (snd r ++ [Z_to_bv 8 0])) /\
(lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= APARTIAL) /\
(lines = false -> (1 <= length (snd r))%nat)) (hl_recs lc)).
{ rewrite Forall_forall in HRECS |- *. intros r Hr. destruct (HRECS r Hr) as (Hb & Hg & Hl1 & Hl2).
  split; [rewrite Hbl2; apply in_or_app; left; exact Hb|]. split; [|split; assumption].
  assert (Hne' : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v lc, AREC * hl_cap lc)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hb Hin Hne') as Dr.
  rewrite Hreq in Dr. unfold zdisjoint in Dr. cbn [fst snd] in Dr.
  assert (Hreqr : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
  rewrite Hreqr in Dr.
  apply (lpt_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem msf)); [|exact Hg].
  intros j Hj. unfold bzs in Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  apply (KB _ _ _ Hb); [rewrite Hreqr; lia | unfold AREC in *; lia]. }
(* the vector *)
assert (Hj16 : (16 <= length (hl_junk lc))%nat) by (unfold AREC in *; lia).
assert (GV : garr8 SEGS (arm W2 (ms_mem msf)) (hl_v lc)
  (bzs (concat (map text_rec (hl_recs lc ++ [(d, x)])) ++ skipn 16 (hl_junk lc)))).
{ apply (lpt_vec_garr8 (w_H Wc) (w_H W2) memc (ms_mem msf) (hl_v lc) (hl_recs lc) (hl_junk lc) d x Hj16 Hgarr).
  - intros a Ha. apply (KB (hl_v lc) (AREC * hl_cap lc) a Hin); unfold hl_n, AREC in *; rewrite ?Hreq; lia.
  - lia.
  - lia.
  - exact VS0.
  - exact VS8. }
assert (HN' : hl_n (HL (hl_v lc) (hl_cap lc) (hl_recs lc ++ [(d, x)]) (skipn 16 (hl_junk lc))) = hl_n lc + 1)
by (unfold hl_n; cbn [hl_recs]; rewrite length_app; cbn [length]; lia).
(* ---- the return ---- *)
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold lp_post_x.
exists ly2, S2, Hp2, (ms_regs msf), (ms_mem msf). eexists.
exists (kc + 1), (HL (hl_v lc) (hl_cap lc) (hl_recs lc ++ [(d, x)]) (skipn 16 (hl_junk lc))), d.
split; [rewrite F1, OLDE by lia; rewrite ER1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ3|].
split; [exact HPF|].
split.
{ unfold alist_at. cbn [hl_v hl_cap hl_recs hl_junk]. rewrite HN'.
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [lia|].
  split; [right; split; [lia|]; split; [exact Hvin2|]; split; [rewrite length_skipn; unfold AREC in *; lia | exact GV]|].
  split.
  { rewrite map_app. cbn [map fst]. apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_cons_append _ _)).
    constructor; [|exact (proj1 (NoDup_ListNoDup _) HND)].
    intros Hd'. apply in_map_iff in Hd' as (r & Hrd & Hr). rewrite Forall_forall in HRECS. destruct (HRECS r Hr) as (Hb & _).
    pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hb) as Dn. rewrite Hreqd in Dn.
    unfold req_size in Dn. destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia. }
  split.
  { rewrite map_app. cbn [map fst]. intros Hv'. apply in_app_or in Hv' as [Hv' | [Hv' | []]]; [exact (HVR Hv')|].
    unfold AREC in *. lia. }
  apply Forall_app. split; [exact RECS|]. constructor; [|constructor].
  split; [exact Hdn|]. split; [exact GD|]. split; [exact Hlin1 | exact Hlin2]. }
split; [cbn [hl_recs]; rewrite Hrecs; reflexivity|].
split; [cbn [hl_cap]; exact Hcap|].
split; [intros Hg; cbn [hl_v]; exact (Hv1 Hg)|].
split.
{ intros rest Hpm. rewrite Hbl2. cbn [hl_v hl_cap].
  eapply Permutation_trans; [apply Permutation_app_tail; exact (Hperm rest Hpm)|].
  apply Permutation_sym. apply Permutation_cons_append. }
split.
{ intros a Hi Hno Herr Hpa.
  assert (Hnot : forall ly0 S0 Hq0 (W0 : world SEGS) m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hq0 W0 m0 md0 HA Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HA Hi) Ho)).
  pose proof (lpt_apresent_grows _ _ _ _ HGr1 (Hapk a Hi Hno Herr Hpa)) as AP2.
  assert (AP3 : apresent (w_H W2) mem2 a).
  { apply (Hpres2 a Hi (Hnot _ _ _ _ _ _ (proj1 HJi)) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact AP2].
    intros Hb. exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ a HAR2 Hdn Hb Hi). }
  exact (lpt_apresent_grows _ _ _ _ HGr3 (Hpres3 a (lpt_apresent_grows _ _ _ _ HGr2 AP3))). }
(* errno: no run writes it (image, outside the struct, the slot and the NUL byte), malloc keeps its view, and
   __asan_memcpy writes only [d, d + n) and its stack band *)
split.
{ intros i Hi. destruct (HER i Hi) as (HI & HR & HnL).
  assert (HnS : ~ (hl_v lc + 16 * hl_n lc <= as_errno B + i < hl_v lc + 16 * hl_n lc + 16)).
  { intros Hc. apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ (as_errno B + i) HARc Hin); [|exact HI].
    rewrite Hreq. clear - Hc Hnc Rn0. lia. }
  assert (HnD : ~ (d <= as_errno B + i < d + (Z.of_nat (length x) + 1))).
  { intros Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ (as_errno B + i) HAR2 Hdn); [|exact HI].
    rewrite Hreqd. exact Hc. }
  rewrite K3 by (clear - HR HnL HnS HnD; lia).
  rewrite Hfr3 by (clear - HR HnD Hsp Hes C1; lia).
  rewrite K2 by (clear - HR HnL HnS; lia).
  rewrite (Herr2 i Hi).
  rewrite K1 by (clear - HR HnL HnS; lia).
  exact (Herrc i Hi). }
split; [rewrite Hfr2; exact Hfrm|].
split; [unfold lp_cost; exact (mle_station MT S Sc S2 _ _ MLAW Hmle Hmle2)|].
(* the room round: the malloc's post keeps the room invariant at the return's allocator state S2 *)
exact HRM2.
Qed.
Definition Bx : sv := SOff 35 0.
Definition LP_FRAME : Z := 96.
Definition lp_lregion : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 12 (CVal 4 (SOff 34 0))].
Definition lp_regions : smem := [ stack_region LP_FRAME; got_regionP; bcell_regionP 35; lp_lregion ].
Definition lp_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 0x5fc000 0);
(33%nat, mkAF 0 (2 ^ 30 - 1) 0); (34%nat, mkAF 0 (2 ^ 30 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_lp : sstate := mkSS A_list_push sr_atoms lp_regions None lp_facts.
Definition lp_SH : list shent := [ mkSHE 10 0 16 ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lp_extra (v n c : Z) : list word := map (Z_to_bv 64) [v; n; c; SB].
Lemma inG_img : forall a, inG G a -> 0x10000 <= a < 0x5fc000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HG a Ha))). Qed.
Lemma lp_entry : forall W ly S Hp regs mem md ch LA (l : hlist) lines,
afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA ->
alist_at B ly S W mem LA l lines ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))) ss_lp
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_list_pushP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx lp_SH (Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HL HGL HZ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity.
pose proof HL as (Mv & Mn & Mc & HwL & Hnc & Hvec & _).
pose proof (inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
pose proof (GX_RT LA (HGL LA ltac:(lia))) as [HR0 HR1]. pose proof (GX_RT (LA + 15) (HGL (LA + 15) ltac:(lia))) as [HR2 HR3].
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Rv : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0); lia).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_lp, A_list_pushP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold lp_regions, lp_lregion, stack_region, got_regionP, bcell_regionP, LP_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E273) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat LA E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HwL; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ LA 0 8 _ (hl_v l)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
   rewrite Z.add_0_r. exact Mv.
-- apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n l)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
-- apply (chunk_ok_val SEGS E _ LA 12 4 _ (hl_cap l)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mc].
+ apply pairwise_disjoint_of_extents. unfold lp_regions, lp_lregion, stack_region, got_regionP, bcell_regionP, extent_of_region, LP_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat LA E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E273) by (pose proof (pa_val_range (A_OBJ 30)); lia). cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (HR4 : ~ (LA <= VAL (A_OBJ 0) < LA + 16)) by (intros Hc; destruct (GX_RT _ (HGL _ Hc)) as [X _]; apply X; lia).
assert (HR5 : ~ (LA <= VAL (A_OBJ 30) < LA + 16)) by (intros Hc; destruct (GX_RT _ (HGL _ Hc)) as [_ X]; apply X; lia).
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HLA0 HLA1 HR0 HR1 HR2 HR3 HR4 HR5. clear.
unf_imgband; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [lp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hnc HLA0 Rn0. clear.
unf_imgband; unfold SB, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lp_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bx 10 LA 16 LA 0 16).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md LA 16 HAR HZ).
+ unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
Lemma lp_blks_in : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W mem LA l lines HL b Hb. destruct HL as (_ & _ & _ & _ & _ & H6 & _ & _ & H9).
unfold alist_blks in Hb. apply in_app_iff in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<-|[]].
  destruct H6 as [(Hc & _) | (_ & Hin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.
Lemma lp_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
(* the bytes a list's predicate reads outside its struct lie in its blocks *)
Lemma lp_fp_blk : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall r a, In r (alist_fp LA l) -> fst r <= a < snd r -> ~ (LA <= a < LA + 16) ->
exists b, In b (ablocks B ly S) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W mem LA l lines HL r a Hr Ha Hn. pose proof HL as (_ & _ & _ & _ & Hnc & H6 & _ & _ & H9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [cbn in Ha; lia|]. apply in_app_iff in Hr as [Hr|Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<-|[]].
  destruct H6 as [(Hc & _) | (Hc0 & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  exists (hl_v l, AREC * hl_cap l). split; [exact Hin|]. unfold gfp in Ha. cbn [fst snd] in *.
  unfold bzs in Ha. rewrite length_map, length_app, lp_concat_len in Ha. unfold req_size, AREC, hl_n in *.
  destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia|].
  lia.
- apply in_map_iff in Hr as (t & <- & Ht). rewrite Forall_forall in H9. destruct (H9 t Ht) as (Hin & _).
  exists (fst t, Z.of_nat (length (snd t)) + 1). split; [exact Hin|]. unfold gfp in Ha. cbn [fst snd] in *.
  unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. unfold req_size.
  destruct (Z.of_nat (length (snd t)) + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.
Lemma lp_inG_not_owned : forall ly S Hp (W : world SEGS) m md a, ARx ly S Hp W m md -> inG G a -> ~ aowned B ly S a.
Proof.
intros ly S Hp W m md a HAR Ha Ho.
exact (proj1 (proj2 (HG a Ha)) (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W m md a HAR (proj1 (HG a Ha))) Ho)).
Qed.
(* errno's four bytes are image bytes outside the list struct (gx_rt keeps errno out of G) *)
Lemma lp_errno_out : forall LA a, (forall b, LA <= b < LA + 16 -> inG G b) -> as_errno B <= a < as_errno B + 4 ->
0x10000 <= a < 0x5fc000 /\ ~ (LA <= a < LA + 16).
Proof.
intros LA a HGL Ha. pose proof (pal_env B TL) as (_ & HeImg & _).
split; [exact (pa_img_range a (HeImg a Ha))|].
intros Hc. exact (proj1 (HGR a (HGL a Hc)) Ha).
Qed.
(* ---- the growth arm (N = CAP): realloc, the stores of v and cap, to the malloc call ---- *)
(* the realloc call returns to 0x853e4 = list_push + 0xc0 *)
Definition A_lp_rret : Z := AF_fr_list_push + 0xc0.
Lemma lp_sll : forall a s, 0 <= s < 64 -> 0 <= a -> a * 2 ^ s < 2 ^ 64 ->
alu64 ALU_SLL (Z_to_bv 64 a) (Z_to_bv 64 s) = Z_to_bv 64 (a * 2 ^ s).
Proof.
intros a s Hs Ha Hr. rewrite zalu64_sound. f_equal. unfold zalu64. cbn [zalu_raw].
assert (Hl : Z.land (zcanon s) 63 = s).
{ unfold zcanon, M64. rewrite (Z.mod_small s) by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 6) with 64. lia. }
rewrite Hl. unfold zcanon, M64. rewrite (Z.mod_small a) by lia. rewrite Z.shiftl_mul_pow2 by lia.
assert (0 <= a * 2 ^ s) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
apply Z.mod_small. lia.
Qed.
(* the blocks of an allocator state are pairwise disjoint, so no block occurs twice *)
Lemma lp_nodup : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (HN : Forall (fun b => 0 <= snd b) (ablocks B ly S)).
{ rewrite Forall_forall. intros [p n] Hb. cbn [snd]. exact (BLKN ly S Hp W mem md p n HAR Hb). }
assert (HP : ablocks B ly S = [] \/ pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S))).
{ destruct (ablocks B ly S) as [|[p0 n0] L] eqn:EL; [left; reflexivity|right].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p0 n0 HAR ltac:(rewrite EL; left; reflexivity)) as (_ & _ & _ & _ & _ & HP).
  rewrite EL in HP. exact HP. }
clear HAR. revert HN HP. generalize (ablocks B ly S) as L0. intros L0.
induction L0 as [|b L IH]; intros HN HP; [constructor|].
destruct HP as [HP|HP]; [discriminate|]. apply Forall_cons_iff in HN as [Hb HN].
cbn [map pairwise] in HP. destruct HP as [HF HP]. constructor.
- intros Hin. assert (Hd : zdisjoint (fst b, req_size (snd b)) (fst b, req_size (snd b))).
  { first [rewrite Forall_forall in HF; apply HF | apply HF]. apply (in_map (fun b => (fst b, req_size (snd b))) L b Hin). }
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. revert Hd Hb. clear. unfold req_size.
  destruct (Z.eqb_spec (snd b) 0); intros; lia.
- apply IH; [exact HN | right; exact HP].
Qed.
Lemma lp_bzs_map : forall jz : list Z, Forall (fun b => 0 <= b < 256) jz -> bzs (map (Z_to_bv 8) jz) = jz.
Proof.
induction jz as [|b jz IH]; intros HF; [reflexivity|]. apply Forall_cons_iff in HF as [Hb HF].
unfold bzs in *. cbn [map]. rewrite (IH HF). f_equal. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. exact Hb.
Qed.
Lemma lp_present_of : forall H (m : word -> option byte) a, apresent H m a -> YO0d.present (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. exists b. unfold mrestrict. rewrite Hh. exact Hb. Qed.
(* What holds at the realloc call of the growth arm (0x853e0, the jal to the realloc trampoline), in values:
   the list is still l (full: N = CAP), s9 = grow_cap N CAP, a0 = v, a1 = 16 * s9, s10 the shadow address of
   LA; the frame holds the caller's ra and s0 .. s10.  The live bytes are lp_spec_x's (C3's peak over list_push's
   trace); the room budget is lp_spec_x's at a growing list (realloc 2, then the tail's malloc 1) and the counts are
   lp_spec_x's peak form, all at the entry's allocator state S (the walk to the call allocates nothing). *)
Definition lp_rcall_pre (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B ly S W memc LA l lines /\ hl_n l = hl_cap l /\ lp_vbytes l < MMAX /\
blocks_bytes S + tr_peak (lp_tr l n) <= LIVE_MAX /\ n < 2 ^ 16 /\
In (q, k) (ablocks B ly S) /\ q <> hl_v l /\ q <= SRC /\ SRC + n <= q + req_size k /\
garr8 SEGS (mrestrict (w_H W) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\ (lines = false -> (1 <= length x)%nat) /\
mo_ok MT S (lp_cost MT l n) /\
rp_RM RP S (3 + kr)%nat /\ cnt_ok_pk RP (lp_peak l n) (ablocks B ly S) /\
getr regsc 1 = Z_to_bv 64 (BASE + A_lp_rret) /\ getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 22 = w64 SB /\
getr regsc 21 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\
getr regsc 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (hl_v l) /\ getr regsc 11 = w64 (lp_vbytes l) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H W) memc) (spZ regs - 96 + fst p) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem W memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* the state seated at the realloc's return: registers are atoms except s4 = LA + 12 and the shadow addresses
   s8 / s10 of LA + 12 / LA (atom 18 = LA, 22 = SB, 10 = the new vector, 9 = n); the list struct with its n field
   (atom 32); no frame (the segment does not touch it) *)
Definition lpr_lregion : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 0 16 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))].
Definition lpr_regs : list sv :=
sr_set (sr_set (sr_set sr_atoms 20%bv (SOff 18 12))
24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 12) (SLit 3)) (SOff 22 0)))
26%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 22 0)).
Definition lpr_facts : facts :=
mkFacts [ (9%nat, mkAF 0 (2 ^ 16) 0); (10%nat, mkAF 4096 0x7fffff800000 4); (18%nat, mkAF 0x10000 0x5fc000 0);
(22%nat, mkAF SB SB 0) ] [] [].
Definition ss_lpr : sstate := mkSS A_lp_rret lpr_regs [lpr_lregion] None lpr_facts.
Definition lpr_SH : list shent := [ mkSHE 18 0 16 ].
Lemma lp_grow_seg : forall W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr,
lp_rcall_pre W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA WS_realloc)) memc (seg_rom SEGS)) mdc)
(lp_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines x kr).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr HPRE.
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Heq & Hvb & Hlive & Hx16 & Hq & Hqv & HqS & HqE & HSRC &
Hlin1 & Hlin2 & HMOK & HRM & HCNT & R1 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R22 & R21 & R23 & R24 & R25 & R26 &
R10 & R11 & HSAVED & HAPK & HERRC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 HJ) as HARc.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc & Hvec & HND & HVR & HRECS).
pose proof (proj1 (Forall_forall _ _) HRECS) as HRECS'.
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hgr : lp_grow l = true) by (unfold lp_grow; rewrite Heq; apply Z.eqb_refl).
assert (Hgc : grow_cap (hl_n l) (hl_cap l) = if hl_cap l =? 0 then 8 else 2 * hl_cap l)
by (unfold grow_cap; rewrite Heq, Z.eqb_refl; reflexivity).
assert (Hvb16 : lp_vbytes l = 16 * grow_cap (hl_n l) (hl_cap l)) by reflexivity.
assert (Hgb : hl_cap l < grow_cap (hl_n l) (hl_cap l) /\ 16 * grow_cap (hl_n l) (hl_cap l) < 2 ^ 30)
by (rewrite Hgc in *; destruct (Z.eqb_spec (hl_cap l) 0); lia).
(* C3's peak: realloc's live bytes at S, and the tail malloc's after it *)
destruct (lp_peak_grow (blocks_bytes S) l (Z.of_nat (length x)) Hgr ltac:(lia) Hlive) as [Hlv1 Hlv2].
pose proof (inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
assert (Usp : spZ regsc = spZ regs - 96) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
destruct HJ as (HSTK0 & HXO0 & (memS & HJi & HAG) & HOUT0). rewrite !Z.add_0_r in HJi.
(* realloc(v, 16 * s9) *)
eapply SRr_bind.
{ eapply (ARE W regsc memc LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] ly S Hp mdc 0 (hl_v l) (AREC * hl_cap l)
    (lp_vbytes l) (-96) _ [] (1 + kr)%nat HJi).
  - destruct Hvec as [[_ ->] | (_ & Hin & _)]; [left; reflexivity | right; exact Hin].
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - exact (lp_cnt_at RP _ _ HCNT).
  - rewrite Usp. lia.
  - reflexivity.
  - lia.
  - lia.
  - eapply aj_stack_room_x with (o := -96); [exact HJi | rewrite Usp; lia | lia].
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold A_lp_rret, AF_fr_list_push; lia | reflexivity].
  - apply (achain_chain_pre ly _ (spZ regs - 96) (LA + 8) [] regsc).
    + apply achain_low. lia.
    + rewrite Usp. lia.
    + unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite R1. rewrite unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
      unfold A_lp_rret, AF_fr_list_push. lia.
  - cbn [spine]. replace (raZ regsc) with (BASE + AF_fr_list_push + 0xc0); [exact HCTX_lp_realloc|].
    unfold raZ. rewrite R1, unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
    unfold A_lp_rret. lia.
  - exact HRM.
  - intros Hp0 Hin i Hi. unfold lp_FP. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0].
    + destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact (False_ind _ (Hp0 Hv0)) | lia].
    + exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity|]. cbn [fst snd].
      unfold req_size, AREC in Hi. destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; unfold AREC; lia.
  - apply (mok_station MT S S (lp_cost MT l (Z.of_nat (length x))) 0 _ MLAW HMOK (mle_start MT S MLAW)).
    + pose proof (mo_free_nonneg MT MLAW). pose proof (mo_malloc_nonneg MT MLAW (lp_vbytes l) ltac:(lia)). lia.
    + unfold lp_cost. rewrite Hgr. pose proof (mo_malloc_nonneg MT MLAW (Z.of_nat (length x) + 1) ltac:(lia)). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres & Hfr2 & H4096 & Hp0 & Hpn &
Hcpy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
(* ---- after realloc: res (atom 10) is the new vector; the old one went ---- *)
pose proof (proj1 HJ2i) as HAR2.
assert (HPM : exists L, Permutation (ablocks B ly2 S2) ((res, lp_vbytes l) :: L) /\
  (forall b, In b (ablocks B ly S) -> b <> (hl_v l, AREC * hl_cap l) -> In b L) /\
  (forall rest, Permutation (ablocks B ly S) ((if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) ++ rest) ->
    Permutation L rest) /\
  bsum L + (if hl_cap l =? 0 then 0 else AREC * hl_cap l) = bsum (ablocks B ly S) /\
  (forall Pq, (acnt Pq L <= acnt Pq (ablocks B ly S))%nat)).
{ destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0].
  - assert (Hv0 : hl_v l = 0) by (destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact Hv0 | lia]).
    exists (ablocks B ly S). split; [exact (Hp0 Hv0)|]. split; [intros b Hb _; exact Hb|].
    split; [intros rest Hpr; exact Hpr|]. split; [cbv beta iota; lia | intros Pq; lia].
  - destruct Hvec as [[Hc _] | (_ & Hin & _)]; [lia|].
    assert (Hv0 : hl_v l <> 0)
    by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
    destruct (Hpn Hv0) as (l1 & l2 & El & Hpq).
    exists (l1 ++ l2). split; [exact Hpq|]. split.
    + intros b Hb Hne. rewrite El in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]];
      [apply in_or_app; left; exact Hb | exfalso; apply Hne; symmetry; exact Hb | apply in_or_app; right; exact Hb].
    + split.
      * intros rest Hpr. rewrite El in Hpr.
        exact (Permutation_app_inv l1 l2 [] rest (hl_v l, AREC * hl_cap l) Hpr).
      * split; [rewrite El, !bsum_app, bsum_cons; cbn [snd]; cbv beta iota; unfold AREC; lia|].
        intros Pq. rewrite El. apply acnt_del_le. }
destruct HPM as (L & HPL & HinL & HpermL & HbsL & HcL).
assert (HND2 : List.NoDup ((res, lp_vbytes l) :: L)) by exact (Permutation_NoDup HPL (lp_nodup ly2 S2 Hp2 W2 mem2 md2 HAR2)).
apply NoDup_cons_iff in HND2 as [HnotL HNDL].
assert (Hvin2 : In (res, lp_vbytes l) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
assert (HL2 : forall b, In b L -> In b (ablocks B ly2 S2)) by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); right; exact Hb).
assert (DL : forall b m, In (b, m) L -> b + req_size m <= res \/ res + req_size (lp_vbytes l) <= b).
{ intros b m Hb. assert (Hne : (b, m) <> (res, lp_vbytes l)) by (intros He; rewrite He in Hb; exact (HnotL Hb)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m res (lp_vbytes l) HAR2 (HL2 _ Hb) Hvin2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hvin2) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _).
assert (Hreqv : req_size (lp_vbytes l) = lp_vbytes l) by (unfold req_size; destruct (Z.eqb_spec (lp_vbytes l) 0); lia).
rewrite Hreqv in Hrceil, Hrapp, Hrpres, DL.
destruct Hkept2 as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
(* a byte of an old block other than the old vector is the byte at the call *)
assert (KB : forall b m a, In (b, m) (ablocks B ly S) -> (b, m) <> (hl_v l, AREC * hl_cap l) -> b <= a < b + req_size m ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros b m a Hb Hne Ha. pose proof (DL b m (HinL _ Hb Hne)) as D1.
  assert (D2 : hl_v l <> 0 -> b + req_size m <= hl_v l \/ hl_v l + req_size (AREC * hl_cap l) <= b).
  { intros Hv0. destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exfalso; exact (Hv0 Hv)|].
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W memc mdc b m _ _ HARc Hb Hin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
  replace a with (b + (a - b)) by lia. apply (KA2 b m (a - b) Hb); [lia|]. cbv beta.
  intros [Hx | (Hv0 & Hx)]; [lia | specialize (D2 Hv0); lia]. }
(* the list struct's bytes are image bytes: kept, and still writable *)
assert (KL : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply KA3; [exact (proj1 (HG a (HGL a Ha))) | exact (proj1 (proj2 (HG a (HGL a Ha)))) | exact (proj1 (HGR a (HGL a Ha)))]. }
assert (WL2 : forall o, 0 <= o < 16 -> writable_at SEGS (mrestrict (w_H W2) mem2) (LA + o)).
{ intros o Ho. assert (Ha : LA <= LA + o < LA + 16) by lia.
  apply (lpt_writable_img W W2 memc mem2 (LA + o)); [exact (proj1 (HG _ (HGL _ Ha))) | | exact (HwL o Ho)].
  intros Hpa. apply Hpres2; [exact (proj1 (HG _ (HGL _ Ha)))
  | exact (lp_inG_not_owned ly S Hp W _ _ (LA + o) HARc (HGL _ Ha))
  | exact (lp_inG_not_owned ly2 S2 Hp2 W2 mem2 md2 (LA + o) HAR2 (HGL _ Ha))
  | exact (proj1 (HGR _ (HGL _ Ha)))
  | | exact Hpa].
  intros [Hb | (Hv0 & Hb)].
  - apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (LA + o) HAR2 Hvin2); [rewrite Hreqv; lia|].
    exact (proj1 (HG _ (HGL _ Ha))).
  - destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (LA + o) HARc Hin Hb (proj1 (HG _ (HGL _ Ha)))). }
assert (MN2 : val_mem SEGS (mrestrict (w_H W2) mem2) (LA + 8) 4 (hl_n l)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W2) memc mem2); [|exact Mn]. intros k0 Hk0. apply KL. cbn in Hk0. lia. }
(* ---- the state at the realloc's return ---- *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (hl_n l)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs2 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (PS : forall i, (i < 32)%nat -> acallee_saved (Z.of_nat i) -> ew E i = getr regsc (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi Hs. rewrite (EA i Hi). exact (HP2 (Z.of_nat i) Hs). }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96)) by exact (eq_trans (PS 2%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R2).
assert (E3 : ew E 3 = getr regs 3) by exact (eq_trans (PS 3%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R3).
assert (E4 : ew E 4 = getr regs 4) by exact (eq_trans (PS 4%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R4).
assert (E8 : ew E 8 = w64 (LA + 8)) by exact (eq_trans (PS 8%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R8).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x))) by exact (eq_trans (PS 9%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R9).
assert (E10 : ew E 10 = w64 res) by exact (eq_trans (EA 10%nat ltac:(lia)) Hres).
assert (E18 : ew E 18 = w64 LA) by exact (eq_trans (PS 18%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R18).
assert (E19 : ew E 19 = w64 SRC) by exact (eq_trans (PS 19%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R19).
assert (E22 : ew E 22 = w64 SB) by exact (eq_trans (PS 22%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R22).
assert (E21 : ew E 21 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (PS 21%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R21).
assert (E23 : ew E 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3))
by exact (eq_trans (PS 23%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R23).
assert (E25 : ew E 25 = w64 (grow_cap (hl_n l) (hl_cap l)))
by exact (eq_trans (PS 25%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R25).
assert (E27 : ew E 27 = getr regs 27) by exact (eq_trans (PS 27%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (P20 : getr regs2 20 = w64 (LA + 12)) by exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) R20).
assert (P24 : getr regs2 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) R24).
assert (P26 : getr regs2 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) R26).
assert (U18 : bv_unsigned (ew E 18) = LA) by (rewrite E18; apply unsigned_lit_small; lia).
assert (Usp2 : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (HS : st_ok_pi SEGS VAL E ss_lpr (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_lp_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lpr. apply pa_entry_st_ok_full.
  - unfold lpr_regs. repeat apply lpt_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg| ..].
    all: cbn [sv_denot]; rewrite ?E18, ?E22; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
    first [rewrite P20 | rewrite P24 | rewrite P26]; reflexivity.
  - vm_compute. reflexivity.
  - unfold lpr_lregion. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 18%nat LA E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply WL2; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n l)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MN2].
  - apply pairwise_disjoint_of_extents. unfold lpr_lregion. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [lpr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E10, E18, E22. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hr16.
    repeat match goal with |- _ /\ _ => split end; unfold SB; lia. }
assert (SHOK : sh_ok SEGS lpt_Bx lpr_SH E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, lpr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E lpt_Bx 18 LA 16 LA 0 16).
  + exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 LA 16 HAR2 HZ).
  + unfold U, lpt_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros y Hy. unfold SHADOW_OFF in *. lia. }
assert (HJ2 : ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | apply out_none]. }
clear HE.
(* R: beqz (refuted by 4096 <= res), the shadow checks, l->v = res, l->cap = s9, a0 = n + 1, to the malloc call *)
paj_run_to_tok_x RUNTO HS HJ2 SHOK lpt_Bspan A_lp_mcall.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite U18 in Ha. apply HGL. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
rename HFr into HFrR, HG0 into HGrR.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (22%bv : bv 5) F22. prreg HS (21%bv : bv 5) F21. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (27%bv : bv 5) F27.
(* ---- the memory at the malloc call ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 64)%nat -> ew Ef m = ew E m) by (intros m Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RL. cbn [ms_mem restrict] in RL.
assert (UFL : bv_unsigned (ew Ef 18) = LA) by (rewrite UF by lia; exact U18).
assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) res).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E10. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (grow_cap (hl_n l) (hl_cap l))).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E25. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W2 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite UFL in RLw. exact (RLw i Hi). }
(* off the list struct the run wrote nothing *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem msf) HFrR a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18; lia. }
(* the vector: the copied records, then the rest of the new block as junk *)
assert (HPJ : forall a, res + 16 * hl_cap l <= a < res + 16 * hl_cap l + Z.of_nat (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) ->
  YO0d.present (mrestrict (w_H W2) (ms_mem msf)) a).
{ intros a Ha. apply lp_present_of. apply (apresent_grows _ _ _ a HGrR). apply (proj1 (Hrpres a ltac:(rewrite Hvb16; lia))). }
destruct (garr8_of_present SEGS (mrestrict (w_H W2) (ms_mem msf)) (res + 16 * hl_cap l)
  (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) HPJ) as (jz & Hjl & Hjg).
assert (HjF : Forall (fun b => 0 <= b < 256) jz).
{ apply Forall_forall. intros b Hb. apply (In_nth _ _ 0) in Hb as (j & Hj & <-). exact (proj2 (Hjg j Hj)). }
assert (GV : garr8 SEGS (arm W2 (ms_mem msf)) res (bzs (concat (map text_rec (hl_recs l)) ++ map (Z_to_bv 8) jz))).
{ unfold bzs, arm. rewrite map_app. apply garr8_app. split.
  - destruct Hvec as [[Hc0 Hv0] | (Hc0 & Hin & Hjk & Hgv)].
    + assert (Hr0 : hl_recs l = []) by (apply length_zero_iff_nil; unfold hl_n in *; lia).
      rewrite Hr0. cbn [map concat]. apply garr8_nil.
    + assert (Hj0 : hl_junk l = []) by (apply length_zero_iff_nil; unfold AREC, hl_n in *; lia).
      rewrite Hj0, app_nil_r in Hgv. unfold arm in Hgv.
      apply (lpt_garr8_moved (w_H W) (w_H W2) memc (ms_mem msf) (hl_v l) res); [|exact Hgv].
      intros j Hj. rewrite length_map, lp_concat_len in Hj.
      assert (Hv0 : hl_v l <> 0) by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
      rewrite KR.
      * apply (Hcpy Hv0 j). unfold AREC, hl_n in *. lia.
      * unfold hl_n in *. lia.
      * intros HLa. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (res + j) HAR2 Hvin2); [rewrite Hreqv; unfold AREC, hl_n in *; lia|].
        exact (proj1 (HG _ (HGL _ HLa))).
  - rewrite length_map, lp_concat_len.
    replace (res + Z.of_nat (16 * length (hl_recs l))) with (res + 16 * hl_cap l) by (unfold hl_n in *; lia).
    change (map bz (map (Z_to_bv 8) jz)) with (bzs (map (Z_to_bv 8) jz)). rewrite (lp_bzs_map jz HjF). exact Hjg. }
(* the texts: their blocks stay, untouched *)
assert (RECS : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly2 S2) /\
  garr8 SEGS (arm W2 (ms_mem msf)) (fst r) (bzs (snd r ++ [Z_to_bv 8 0])) /\
  (lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= APARTIAL) /\
  (lines = false -> (1 <= length (snd r))%nat)) (hl_recs l)).
{ apply Forall_forall. intros r Hr. destruct (HRECS' r Hr) as (Hb & Hg & Hl1 & Hl2).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  split; [exact (HL2 _ (HinL _ Hb Hne))|]. split; [|split; assumption].
  assert (Hreqr : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hb) as (_ & H4096r & Hce & _). rewrite Hreqr in Hce.
  unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf)); [|exact Hg].
  intros j Hj. unfold bzs in Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  rewrite KR; [apply (KB _ _ _ Hb Hne); rewrite Hreqr; lia | lia |].
  intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (fst r + j) HARc Hb ltac:(rewrite Hreqr; lia) (proj1 (HG _ (HGL _ HLa)))). }
assert (HNR : ~ In res (map fst (hl_recs l))).
{ intros Hin. apply in_map_iff in Hin as (r & Hrr & Hr). destruct (HRECS' r Hr) as (Hb & _).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  pose proof (DL _ _ (HinL _ Hb Hne)) as D. rewrite Hrr in D. revert D. clear - Hvb16 Hgb Hnc Rn0. unfold req_size.
  destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); intros; lia. }
assert (HLC : alist_at B ly2 S2 W2 (ms_mem msf) LA (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) lines).
{ unfold alist_at. cbn [hl_v hl_cap hl_recs hl_junk].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [unfold hl_n in *; cbn [hl_recs]; lia|].
  split; [right; split; [lia|]; split; [exact Hvin2|]; split;
    [rewrite length_map, Hjl, Z2Nat.id by lia; unfold AREC, hl_n in *; cbn [hl_recs]; lia | exact GV]|].
  split; [exact HND|]. split; [exact HNR | exact RECS]. }
(* ---- the malloc call: SEG3 / SEG4 (lp_tail_seg above) ---- *)
eapply (lp_tail_seg W ly S Hp regs mem md LA SRC l lines x q k W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (0 + 3)
  (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) kr).
- apply HL2, HinL; [exact Hq | intros He; injection He as He1 _; exact (Hqv He1)].
- cbn [hl_v]. intros Hqr.
  assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
  pose proof (BLKN ly S Hp W memc mdc q k HARc Hq) as Hk0.
  pose proof (DL _ _ (HinL _ Hq Hne)) as D. rewrite Hqr in D. revert D. clear - Hvb16 Hgb Hnc Rn0 Hk0. unfold req_size.
  destruct (Z.eqb_spec k 0); intros; lia.
- exact HqS.
- exact HqE.
- unfold lp_tail_pre_x. cbv zeta. cbn [hl_v hl_cap hl_recs hl_junk]. rewrite Hgr. cbn [andb negb app].
  split; [exact HJ2|]. split; [exists ch; exact HAF|]. split; [exact HGL|]. split; [exact HZ|].
  split; [exact HLC|]. split; [reflexivity|]. split; [reflexivity|].
  split; [change (hl_n l < grow_cap (hl_n l) (hl_cap l)); lia|].
  split; [intros Hf; discriminate|].
  split; [intros _ Hin; apply HnotL; apply HinL; [exact Hin | intros He; injection He as _ He2; unfold lp_vbytes, AREC in He2; lia]|].
  split; [intros rest Hpr; eapply Permutation_trans; [exact HPL|]; apply perm_skip; apply HpermL;
    revert Hpr; destruct (hl_cap l =? 0); intros Hpr; exact Hpr|].
  split; [exact Hfr2|]. split; [exact Hmle2|]. split; [exact HMOK|].
  (* the room round: realloc's post leaves the tail's budget; the counts at S2 are S's plus the new vector, within
     lp_spec_x's peak (the old vector, if any, is gone) *)
  split; [exact HRM2|].
  split.
  { unfold cnt_ok. apply (cnt_ok_pk_mono RP (lp_peak l (Z.of_nat (length x))) (fun _ => 0%nat) (ablocks B ly S) (ablocks B ly2 S2));
      [|exact HCNT].
    intros Pq. unfold lp_peak. cbv beta. rewrite (acnt_perm Pq _ _ HPL), acnt_cons. cbn [snd]. rewrite Hgr, andb_true_r.
    specialize (HcL Pq). lia. }
  split; [rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPL), bsum_cons; cbn [snd];
    rewrite (blocks_bytes_bsum B ly S) in Hlv2; lia|].
  split; [exact Hx16|].
  split.
  { unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf) SRC (bzs x)); [|exact HSRC].
    intros j Hj. unfold bzs in Hj. rewrite length_map in Hj.
    assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hq) as (_ & Hq4096 & Hqce & _).
    rewrite KR; [apply (KB q k (SRC + j) Hq Hne); lia | lia |].
    intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc q k (SRC + j) HARc Hq ltac:(lia) (proj1 (HG _ (HGL _ HLa)))). }
  split; [exact Hlin1|]. split; [exact Hlin2|].
  split; [rewrite F2, E2; reflexivity|].
  split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|]. split; [rewrite F27, E27; reflexivity|].
  split; [rewrite F8, E8; reflexivity|]. split; [rewrite F9, E9; reflexivity|]. split; [rewrite F18, E18; reflexivity|].
  split; [rewrite F19, E19; reflexivity|].
  split; [rewrite F20, E18; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F22, E22; reflexivity|]. split; [rewrite F21, E21; reflexivity|]. split; [rewrite F23, E23; reflexivity|].
  split; [rewrite F24, E18, E22; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F10, E9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split.
  { apply Forall_forall. intros p Hpp. rewrite Forall_forall in HSAVED.
    apply (val_mem_kept SEGS (w_H W) (w_H W2) memc (ms_mem msf)); [|exact (HSAVED p Hpp)].
    assert (Hfp : 0 <= fst p <= 88)
    by (unfold lp_saved in Hpp; cbn [In] in Hpp; repeat destruct Hpp as [<- | Hpp]; try destruct Hpp; cbn [fst]; lia).
    intros k0 Hk0. cbn in Hk0. rewrite KR by lia. apply KA1; lia. }
  split.
  2: { intros i Hi. destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL].
       rewrite KR by (clear - HeR HeL; lia). rewrite (Herr2 i Hi). exact (HERRC i Hi). }
  intros a Hi Hno Herr Hpa.
  assert (Hnot : forall ly0 S0 Hq0 (W0 : world SEGS) m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hq0 W0 m0 md0 HA Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HA Hi) Ho)).
  apply (apresent_grows _ _ _ a HGrR).
  apply (Hpres2 a Hi (Hnot _ _ _ _ _ _ HARc) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact (HAPK a Hi Hno Herr Hpa)].
  intros [Hb | (Hv0 & Hb)].
  + exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ a HAR2 Hvin2 Hb Hi).
  + destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ a HARc Hin Hb Hi).
Qed.
Theorem pb_list_push_x : lp_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_list_push).
Proof.
change (BASE + AF_fr_list_push) with A_list_pushP.
intros W ly S Hp regs mem md ch LA SRC l lines x q k HPRE H10 H11 H12 HLA8 HL HGL HZ Hcap25 Hx16 Hlive Hq Hqv Hq1 Hq2 Hsrc
Hlines1 Hlines2 HMOK kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (lp_entry W ly S Hp regs mem md ch LA l lines HPRE H10 HL HGL HZ) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HL as (Mv & Mn & Mc & HwL & Hnc & Hvec & HND & HVR & HRECS).
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Rv : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
assert (HJ : ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W mem md 0).
{ apply (ajournal_gx_init_x SEGS B PST ARx G 0 [] LP_STK (lp_FP l) ly S Hp W regs mem md ch HPRE); [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 SRC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (Z.of_nat (length x))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_list_pushP) with (Z_to_bv 64 A_list_pushP). unfold A_list_pushP, A_list_push.
paj_run_tok_x RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
(* 0x85360: the UBSan ALIGN8 trap on LA, refuted by lp_spec's LA mod 8 = 0 (W_traps trap_align8) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ lp_trap (trap_align8 E (SOff 10 0) LA (U_atom E 10 LA E10 ltac:(pose proof (inG_img LA (HGL LA ltac:(lia))); lia)) HLA8). }
paj_run_tok_x RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
(* 0x853ac bne a0,a1: N <> CAP (the list has room) or N = CAP (the vector grows) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* the list has room: N < CAP; straight to the malloc call *)
assert (Hlt : hl_n l < hl_cap l).
{ rewrite branch_ne_U in Hc0. rewrite (U_atom _ 33 (hl_n l)), (U_atom _ 34 (hl_cap l)) in Hc0;
  [| rewrite !ew_ewset_other by lia; exact E34 | lia | rewrite !ew_ewset_other by lia; exact E33 | lia].
  apply Bool.negb_true_iff, Z.eqb_neq in Hc0. lia. }
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (A_lp_mcall).
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (10%bv : bv 5) Q10.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (27%bv : bv 5) Q27.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
assert (HLAr : 0x10000 <= LA /\ LA + 16 <= 0x5fc000)
by (pose proof (inG_img LA (HGL LA ltac:(lia))); pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))); lia).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (proj1 HAE 27%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
(* the chunks of the frame and of the list region, read back at the call *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (CK : forall i r c, nth_error (ss_mem ssv) i = Some r -> In c (YP09.r_chunks r) ->
    YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (YP09.r_base r)) c)
  by (intros i r c Hi0 Hcc; exact (st_ok_chunk SEGS Ev (abs_ss VAL ssv) (restrict (w_H W) msv) i r c HS Hi0 Hcc)) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 0) with Some ?r0 =>
    assert (CK0 : forall c, In c (YP09.r_chunks r0) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 2%nat)) c)
    by (intros c Hcc; exact (CK 0%nat r0 c ltac:(vm_compute; reflexivity) Hcc)) end;
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 3) with Some ?r3 =>
    assert (CK3 : forall c, In c (YP09.r_chunks r3) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 10%nat)) c)
    by (intros c Hcc; exact (CK 3%nat r3 c ltac:(vm_compute; reflexivity) Hcc)) end end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (EV2 : base_val Ev (Some 2%nat) = spZ regs)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); exact Usp);
  assert (EV10 : base_val Ev (Some 10%nat) = LA)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); rewrite E10;
        apply unsigned_lit_small; clear - HLAr; lia);
  assert (EVr : forall r, (r < 32)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (EVx : forall r, (32 <= r < 36)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  (* the frame holds the caller's ra and s0 .. s10 *)
  assert (SAVED : Forall (fun p => val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (spZ regs - 96 + fst p) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved);
  [ unfold lp_saved; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (spZ regs - 96 + ?o) 8 (bv_unsigned (getr regs (Z_to_bv 5 ?r))) =>
      let c := eval vm_compute in (o - 96) in
      let rn := eval vm_compute in (Z.to_nat r) in
      replace (spZ regs - 96 + o) with (base_val Ev (Some 2%nat) + c) by (rewrite EV2; clear; lia);
      apply (val_of_chunk_ok SEGS Ev _ _ c 8 (SOff rn 0));
      [ exact (CK0 (YP09.mkChunk c (CVal 8 (SOff rn 0))) ltac:(clear; cbn; tauto))
      | cbn [sv_denot]; rewrite Z.add_0_r, EVr by (clear; cbv; lia);
        rewrite (proj1 HAE rn ltac:(clear; cbv; lia)), (ew_Ereg_nat regs _ rn (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HR; lia
      | clear; vm_compute; discriminate ] end |];
  assert (MV' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) LA 8 (hl_v l));
  [ replace LA with (base_val Ev (Some 10%nat) + 0) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 0 8 (SOff 32 0));
    [ exact (CK3 (YP09.mkChunk 0 (CVal 8 (SOff 32 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E32, unsigned_lit_small by (clear - Rv; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Rv; lia | clear; vm_compute; discriminate ] |];
  assert (MN' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 8) 4 (hl_n l));
  [ replace (LA + 8) with (base_val Ev (Some 10%nat) + 8) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 8 4 (SOff 33 0));
    [ exact (CK3 (YP09.mkChunk 8 (CVal 4 (SOff 33 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E33, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  assert (MC' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 12) 4 (hl_cap l));
  [ replace (LA + 12) with (base_val Ev (Some 10%nat) + 12) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 12 4 (SOff 34 0));
    [ exact (CK3 (YP09.mkChunk 12 (CVal 4 (SOff 34 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E34, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  idtac
end.
(* heap and low bytes off the image were not written by the two runs *)
assert (KEEP : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x5fc000 <= a \/ ~ (LA <= a < LA + 16)) ->
  mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hoi.
  lazymatch type of HFr1 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr1 end.
  lazymatch type of HFr0 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr0 end.
  lazymatch type of HFr with frame_of ?Ev1 ?rs1 _ _ => let r1 := eval vm_compute in rs1 in change rs1 with r1 in HFr end.
  rewrite HFr1, HFr0, HFr; [reflexivity | | |];
  rewrite unsigned_lit_small by (clear - Ha C1; unfold alloc_ceiling in *; lia);
  intros (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]); try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (clear; discriminate);
  try rewrite Usp in Hr; try (rewrite E10, unsigned_lit_small in Hr by (clear - HLAr; lia));
  clear - Hr Hoi Ha Hceil Hslo Hstk0 HLAr WS C1; unfold LP_STK, ASTACK in *; lia. }
assert (HGT : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms1)))
by exact (mem_grows_trans _ _ _ HG0 (mem_grows_trans _ _ _ HG1 HG2)).
(* the list as it is at the call: the same as at entry *)
assert (HLc : alist_at B ly S W (ms_mem ms1) LA l lines).
{ apply (alist_at_kept B ly S W mem ly S W (ms_mem ms1) LA l lines HL); [|exact (lp_blks_in ly S W mem LA l lines HL)].
  intros r Hr a Ha.
  assert (HWg : writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a)
  by (intros Hw; eapply writable_at_grows; [exact HGT | exact Hw]).
  destruct (Z.le_gt_cases LA a) as [Hlo | Hlo]; [destruct (Z.lt_ge_cases a (LA + 16)) as [Hhi | Hhi]|].
  - (* the struct: its three fields hold the same values, and it stays writable *)
    split; [| intros _; apply HWg; replace a with (LA + (a - LA)) by ring; apply HwL; clear - Hlo Hhi; lia].
    unfold aview. f_equal. unfold arm in Mv, Mn, Mc.
    destruct (Z.lt_ge_cases a (LA + 8)) as [Hz8 | Hz8]; [|destruct (Z.lt_ge_cases a (LA + 12)) as [Hz12 | Hz12]].
    + replace a with (LA + (a - LA)) by ring.
      exact (val_mem_agree SEGS _ _ LA 8 (hl_v l) Mv MV' (a - LA) ltac:(clear - Hlo Hz8; cbn; lia)).
    + replace a with ((LA + 8) + (a - (LA + 8))) by ring.
      exact (val_mem_agree SEGS _ _ (LA + 8) 4 (hl_n l) Mn MN' (a - (LA + 8)) ltac:(clear - Hz8 Hz12; cbn; lia)).
    + replace a with ((LA + 12) + (a - (LA + 12))) by ring.
      exact (val_mem_agree SEGS _ _ (LA + 12) 4 (hl_cap l) Mc MC' (a - (LA + 12)) ltac:(clear - Hz12 Hhi; cbn; lia)).
  - destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hhi; lia)) as ([p nb] & Hb & Hab).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _).
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff. unf_imgband. cbn [fst snd] in Hab.
    assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia).
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)].
  - destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hlo; lia)) as ([p nb] & Hb & Hab).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _).
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff. unf_imgband. cbn [fst snd] in Hab.
    assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia).
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]. }
assert (Hng : lp_grow l = false) by (unfold lp_grow; apply Z.eqb_neq; clear - Hlt; lia).
assert (HSRC : garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) SRC (bzs x)).
{ destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q k HAR Hq) as (_ & H4096 & Hceilq & _).
  pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ q k HAR Hq) as Hoff. unf_imgband.
  apply (akept_garr8 W mem W (ms_mem ms1)); [|exact Hsrc].
  intros a Ha. unfold bzs in Ha. rewrite length_map in Ha.
  assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (apply KEEP; clear - Ha Hq1 Hq2 H4096 Hceilq Hoff; lia).
  split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]. }
eapply (lp_tail_seg W ly S Hp regs mem md LA SRC l lines x q k W ly S Hp (ms_regs ms1) (ms_mem ms1) _ 0 l kr Hq Hqv Hq1 Hq2).
unfold lp_tail_pre_x. cbv zeta. rewrite Hng. cbn [andb negb app].
split; [exact HJ|]. split; [exists ch; exact HPRE|]. split; [exact HGL|]. split; [exact HZ|].
split; [exact HLc|]. split; [reflexivity|].
split; [unfold grow_cap; destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [Heq|_]; [clear - Hlt Heq; lia | reflexivity]|].
split; [unfold grow_cap; destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [Heq|_]; [clear - Hlt Heq; lia | clear - Hlt; lia]|].
split; [intros _; reflexivity|]. split; [intros Hg; discriminate|].
split; [intros rest Hpr; exact Hpr|]. split; [reflexivity|]. split; [exact (mle_start MT S MLAW)|].
split; [exact HMOK|].
(* the room round: the list has room, so the tail's malloc is list_push's only call, at the entry's state S *)
split; [rewrite lp_rk_eq, Hng in HRM; exact HRM|]. split; [exact (lp_cnt_at RP _ _ HCNT)|].
split; [pose proof (lp_peak_nogrow (blocks_bytes S) l (Z.of_nat (length x)) Hng ltac:(lia) Hlive); lia|].
split; [exact Hx16|].
split; [exact HSRC|]. split; [exact Hlines1|]. split; [exact Hlines2|].
split; [rewrite Q2, Usp; f_equal; clear; ring|].
split; [rewrite Q3, E3; reflexivity|]. split; [rewrite Q4, E4; reflexivity|]. split; [rewrite Q27, E27; reflexivity|].
split; [rewrite Q8, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q9, E12; reflexivity|]. split; [rewrite Q18, E10; reflexivity|]. split; [rewrite Q19, E11; reflexivity|].
split; [rewrite Q20, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|]. split; [rewrite Q22, E35; reflexivity|].
split; [rewrite Q21, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q23, E10; reflexivity|].
split; [rewrite Q24, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q10, E12, unsigned_lit_small by (clear - Hx16; lia); reflexivity|].
split; [exact SAVED|].
split.
2: { intros i Hi. destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL].
     apply aview_eq_of. apply KEEP; [clear - HeR C1; lia | right; right; exact HeL]. }
intros a _ _ _ Hpa. exact (apresent_grows _ _ _ a HGT Hpa).
-
(* the list is full: N = CAP; the vector grows with realloc *)
assert (Heq : hl_n l = hl_cap l).
{ rewrite branch_ne_U in Hc0. rewrite (U_atom _ 33 (hl_n l)), (U_atom _ 34 (hl_cap l)) in Hc0;
  [| rewrite !ew_ewset_other by lia; exact E34 | lia | rewrite !ew_ewset_other by lia; exact E33 | lia].
  apply Bool.negb_false_iff, Z.eqb_eq in Hc0. lia. }
(* the room round: lp_spec_x's budget at a growing list is 3 (realloc, then the tail's malloc) *)
assert (HRM3 : rp_RM RP S (3 + kr)%nat).
{ assert (Hgr : lp_grow l = true) by (unfold lp_grow; rewrite Heq; apply Z.eqb_refl).
  rewrite lp_rk_eq, Hgr in HRM. exact HRM. }
paj_run_tok_x RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
(* beqz a0 at 0x853b0: N = 0, so CAP = 0 (s9 := 8), or CAP <> 0 (s9 := 2 CAP, slliw); both reach the realloc call *)
psrr_branch_tok RUN BR HS SHOK Bspan.
all: paj_run_tok_x RUN HS HJ SHOK Bspan.
all: try (lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|];
  apply awr_ok_x_cons_awr0; [awr_any|];
  apply awr_ok_x_cons_awr0; [awr_any|];
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
  intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia;
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia); apply HGL; lia).
(* s9 and a1 = s9 << 4, per arm *)
all: prreg HS (25%bv : bv 5) Q25.
all: prreg HS (11%bv : bv 5) Q11.
1: assert (R25 : getr (ms_regs ms2) 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\ getr (ms_regs ms2) 11 = w64 (lp_vbytes l)).
1: { assert (Hc00 : hl_cap l = 0).
     { rewrite branch_eq_U in Hc1. rewrite (U_atom _ 33 (hl_n l)) in Hc1 by first [rewrite !ew_ewset_other by lia; exact E33 | lia].
       rewrite U_lit in Hc1 by lia. apply Z.eqb_eq in Hc1. lia. }
     unfold lp_vbytes, grow_cap, AREC. rewrite Heq, Z.eqb_refl, Hc00. cbn [Z.eqb]. rewrite Q25, Q11. split; reflexivity. }
2: assert (R25 : getr (ms_regs ms2) 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\ getr (ms_regs ms2) 11 = w64 (lp_vbytes l)).
2: { assert (Hn0 : hl_n l <> 0).
     { rewrite branch_eq_U in Hc1. rewrite (U_atom _ 33 (hl_n l)) in Hc1 by first [rewrite !ew_ewset_other by lia; exact E33 | lia].
       rewrite U_lit in Hc1 by lia. apply Z.eqb_neq in Hc1. exact Hc1. }
     unfold lp_vbytes, grow_cap, AREC. rewrite Heq, Z.eqb_refl. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]; [lia|].
     rewrite Q25, Q11, E33. unfold w64. rewrite !lp_sll by lia. split; f_equal; lia. }
(* the rest is the same in both arms *)
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1.
all: prreg HS (2%bv : bv 5) Q2.
all: prreg HS (3%bv : bv 5) Q3.
all: prreg HS (4%bv : bv 5) Q4.
all: prreg HS (8%bv : bv 5) Q8.
all: prreg HS (9%bv : bv 5) Q9.
all: prreg HS (10%bv : bv 5) Q10.
all: prreg HS (18%bv : bv 5) Q18.
all: prreg HS (19%bv : bv 5) Q19.
all: prreg HS (20%bv : bv 5) Q20.
all: prreg HS (22%bv : bv 5) Q22.
all: prreg HS (21%bv : bv 5) Q21.
all: prreg HS (23%bv : bv 5) Q23.
all: prreg HS (24%bv : bv 5) Q24.
all: prreg HS (26%bv : bv 5) Q26.
all: prreg HS (27%bv : bv 5) Q27.
all: assert (HLAr : 0x10000 <= LA /\ LA + 16 <= 0x5fc000)
  by (pose proof (inG_img LA (HGL LA ltac:(lia))); pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))); lia).
all: assert (E27 : ew E 27 = getr regs 27) by (rewrite (proj1 HAE 27%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (CK : forall i r c, nth_error (ss_mem ssv) i = Some r -> In c (YP09.r_chunks r) ->
    YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (YP09.r_base r)) c)
  by (intros i r c Hi1 Hcc; exact (st_ok_chunk SEGS Ev ssv (restrict (w_H W) msv) i r c HS Hi1 Hcc)) end.
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 0) with Some ?r0 =>
    assert (CK0 : forall c, In c (YP09.r_chunks r0) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 2%nat)) c)
    by (intros c Hcc; exact (CK 0%nat r0 c ltac:(vm_compute; reflexivity) Hcc)) end;
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 3) with Some ?r3 =>
    assert (CK3 : forall c, In c (YP09.r_chunks r3) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 10%nat)) c)
    by (intros c Hcc; exact (CK 3%nat r3 c ltac:(vm_compute; reflexivity) Hcc)) end end.
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (EV2 : base_val Ev (Some 2%nat) = spZ regs)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); exact Usp);
  assert (EV10 : base_val Ev (Some 10%nat) = LA)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); rewrite E10;
        apply unsigned_lit_small; clear - HLAr; lia);
  assert (EVr : forall r, (r < 32)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (EVx : forall r, (32 <= r < 36)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (SAVED : Forall (fun p => val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (spZ regs - 96 + fst p) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved);
  [ unfold lp_saved; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (spZ ?rg - 96 + ?o) 8 (bv_unsigned (getr ?rg (Z_to_bv 5 ?r))) =>
      let c := eval vm_compute in (o - 96) in
      let rn := eval vm_compute in (Z.to_nat r) in
      replace (spZ rg - 96 + o) with (base_val Ev (Some 2%nat) + c) by (rewrite EV2; clear; lia);
      apply (val_of_chunk_ok SEGS Ev _ _ c 8 (SOff rn 0));
      [ exact (CK0 (YP09.mkChunk c (CVal 8 (SOff rn 0))) ltac:(clear; cbn; tauto))
      | cbn [sv_denot]; rewrite Z.add_0_r, EVr by (clear; cbv; lia);
        rewrite (proj1 HAE rn ltac:(clear; cbv; lia)), (ew_Ereg_nat regs _ rn (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HR; lia
      | clear; vm_compute; discriminate ] end |];
  assert (MV' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) LA 8 (hl_v l));
  [ replace LA with (base_val Ev (Some 10%nat) + 0) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 0 8 (SOff 32 0));
    [ exact (CK3 (YP09.mkChunk 0 (CVal 8 (SOff 32 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E32, unsigned_lit_small by (clear - Rv; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Rv; lia | clear; vm_compute; discriminate ] |];
  assert (MN' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 8) 4 (hl_n l));
  [ replace (LA + 8) with (base_val Ev (Some 10%nat) + 8) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 8 4 (SOff 33 0));
    [ exact (CK3 (YP09.mkChunk 8 (CVal 4 (SOff 33 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E33, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  assert (MC' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 12) 4 (hl_cap l));
  [ replace (LA + 12) with (base_val Ev (Some 10%nat) + 12) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 12 4 (SOff 34 0));
    [ exact (CK3 (YP09.mkChunk 12 (CVal 4 (SOff 34 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E34, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  idtac
end.
(* the three runs wrote only the frame and the list struct *)
all: assert (HGT : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms2)))
  by exact (mem_grows_trans _ _ _ HG0 (mem_grows_trans _ _ _ HG1 (mem_grows_trans _ _ _ HG2 HG3))).
all: assert (KEEP : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x5fc000 <= a \/ ~ (LA <= a < LA + 16)) ->
  mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha Hoi;
  lazymatch type of HFr2 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr2 end;
  lazymatch type of HFr1 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr1 end;
  lazymatch type of HFr0 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr0 end;
  lazymatch type of HFr with frame_of ?Ev1 ?rs1 _ _ => let r1 := eval vm_compute in rs1 in change rs1 with r1 in HFr end;
  rewrite HFr2, HFr1, HFr0, HFr; [reflexivity | | | |];
  rewrite unsigned_lit_small by (clear - Ha C1; unfold alloc_ceiling in *; lia);
  intros (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]); try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (clear; discriminate);
  try rewrite Usp in Hr; try (rewrite E10, unsigned_lit_small in Hr by (clear - HLAr; lia));
  clear - Hr Hoi Ha Hceil Hslo Hstk0 HLAr WS C1; unfold LP_STK, ASTACK in *; lia).
(* the list as it is at the realloc call: the same as at entry *)
all: assert (HLc : alist_at B ly S W (ms_mem ms2) LA l lines)
  by (apply (alist_at_kept B ly S W mem ly S W (ms_mem ms2) LA l lines HL); [|exact (lp_blks_in ly S W mem LA l lines HL)];
  intros r Hr a Ha;
  assert (HWg : writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms2)) a)
    by (intros Hw; eapply writable_at_grows; [exact HGT | exact Hw]);
  destruct (Z.le_gt_cases LA a) as [Hlo | Hlo]; [destruct (Z.lt_ge_cases a (LA + 16)) as [Hhi | Hhi]|];
  [ split; [| intros _; apply HWg; replace a with (LA + (a - LA)) by ring; apply HwL; clear - Hlo Hhi; lia];
    unfold aview; f_equal; unfold arm in Mv, Mn, Mc;
    destruct (Z.lt_ge_cases a (LA + 8)) as [Hz8 | Hz8]; [|destruct (Z.lt_ge_cases a (LA + 12)) as [Hz12 | Hz12]];
    [ replace a with (LA + (a - LA)) by ring;
      exact (val_mem_agree SEGS _ _ LA 8 (hl_v l) Mv MV' (a - LA) ltac:(clear - Hlo Hz8; cbn; lia))
    | replace a with ((LA + 8) + (a - (LA + 8))) by ring;
      exact (val_mem_agree SEGS _ _ (LA + 8) 4 (hl_n l) Mn MN' (a - (LA + 8)) ltac:(clear - Hz8 Hz12; cbn; lia))
    | replace a with ((LA + 12) + (a - (LA + 12))) by ring;
      exact (val_mem_agree SEGS _ _ (LA + 12) 4 (hl_cap l) Mc MC' (a - (LA + 12)) ltac:(clear - Hz12 Hhi; cbn; lia)) ]
  | destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hhi; lia)) as ([p nb] & Hb & Hab);
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _);
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff; unf_imgband; cbn [fst snd] in Hab;
    assert (Hk : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia);
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]
  | destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hlo; lia)) as ([p nb] & Hb & Hab);
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _);
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff; unf_imgband; cbn [fst snd] in Hab;
    assert (Hk : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia);
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)] ]).
all: assert (HSRC : garr8 SEGS (mrestrict (w_H W) (ms_mem ms2)) SRC (bzs x))
  by (destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q k HAR Hq) as (_ & H4096 & Hceilq & _);
  pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ q k HAR Hq) as Hoff; unf_imgband;
  apply (akept_garr8 W mem W (ms_mem ms2)); [|exact Hsrc];
  intros a Ha; unfold bzs in Ha; rewrite length_map in Ha;
  assert (Hk : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Ha Hq1 Hq2 H4096 Hceilq Hoff; lia);
  split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]).
(* the realloc call: the growth segment *)
all: eapply (lp_grow_seg W ly S Hp regs mem md LA SRC l lines x q k (ms_regs ms2) (ms_mem ms2) _ kr).
all: unfold lp_rcall_pre; cbv zeta.
all: split; [exact HJ|].
all: split; [exists ch; exact HPRE|].
all: split; [exact HGL|].
all: split; [exact HZ|].
all: split; [exact HLc|].
all: split; [exact Heq|].
all: split; [apply Hcap25; unfold lp_grow; rewrite Heq; apply Z.eqb_refl|].
all: split; [exact Hlive|].
all: split; [exact Hx16|].
all: split; [exact Hq|].
all: split; [exact Hqv|].
all: split; [exact Hq1|].
all: split; [exact Hq2|].
all: split; [exact HSRC|].
all: split; [exact Hlines1|].
all: split; [exact Hlines2|].
all: split; [exact HMOK|].
all: split; [exact HRM3|].
all: split; [exact HCNT|].
all: split; [rewrite Q1; reflexivity|].
all: split; [rewrite Q2, Usp; f_equal; clear; ring|].
all: split; [rewrite Q3, E3; reflexivity|].
all: split; [rewrite Q4, E4; reflexivity|].
all: split; [rewrite Q27, E27; reflexivity|].
all: split; [rewrite Q8, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q9, E12; reflexivity|].
all: split; [rewrite Q18, E10; reflexivity|].
all: split; [rewrite Q19, E11; reflexivity|].
all: split; [rewrite Q20, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q22, E35; reflexivity|].
all: split; [rewrite Q21, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q23, E10; reflexivity|].
all: split; [rewrite Q24, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [exact (proj1 R25)|].
all: split; [rewrite Q26, E10, E35; reflexivity|].
all: split; [rewrite Q10, E32; reflexivity|].
all: split; [exact (proj2 R25)|].
all: split; [exact SAVED|].
all: split; [intros a _ _ _ Hpa; exact (apresent_grows _ _ _ a HGT Hpa)|].
all: intros i Hi; destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL];
  apply aview_eq_of; apply KEEP; [clear - HeR C1; lia | right; right; exact HeL].
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, 3, 4): list_push at a world relation R, stated as W_contract_xR.lp_spec_xR
   (journal ajournal_gx_xR R, step relation SRrG SEGS R, post W_contract_xR.lp_post_xR R); image B's twin of image A's
   lib/A/W_list_push.v Section c wR with lib/A/W_lp_tail.v (pb_lp_tail_xR) and lib/A/W_list_push_tail.v
   (lp_tail_pre_xR), whose tail segment image B has here (lp_tail_seg).  The runs are the G runs
   (W_journal_x.paj_run_x_xG / paj_run_to_x_xG), the branches paj_branch_xR; the realloc call goes through the realloc
   rule at R at CTX_R (ARE_R) and the tail's malloc through the malloc rule at R at CTX_M (AMA_R), their call-boundary
   premise RO at the call memory from the call state's ARx (RO_ARx; part 3c removed their memnorm premise) and
   realloc's hull admission from HA_call at the meter fact of the call; __asan_memcpy stays the strict AMEMCPY
   (W_sites_x.aj_intrin_at_xR); the ret is a strict step lifted by SRr_SRrG (WLE_R).  lpt_entry, lp_tail_seg,
   lp_grow_seg and pb_list_push_x above keep their strict proofs. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis ARE_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Hypothesis AMA_R : amalloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO CTX_M R.
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRG := paj_branch_xR (PI := PI) (R := R).
(* :403 lp_tail_pre_x at R: the journal is ajournal_gx_xR R; every other conjunct is verbatim (image A's
   W_list_push_tail.lp_tail_pre_xR) *)
Definition lp_tail_pre_xR (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(Wc : world SEGS) lyc Sc (Hpc : list Z) (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kc : Z) (lc : hlist)
(kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B lyc Sc Wc memc LA lc lines /\
hl_recs lc = hl_recs l /\ hl_cap lc = grow_cap (hl_n l) (hl_cap l) /\ hl_n lc < hl_cap lc /\
(lp_grow l = false -> hl_v lc = hl_v l) /\
(lp_grow l = true -> ~ In (hl_v lc, AREC * hl_cap lc) (ablocks B ly S)) /\
(forall rest,
 Permutation (ablocks B ly S) ((if lp_grow l && negb (hl_cap l =? 0) then [(hl_v l, AREC * hl_cap l)] else []) ++ rest) ->
 Permutation (ablocks B lyc Sc) ((if lp_grow l then [(hl_v lc, AREC * hl_cap lc)] else []) ++ rest)) /\
frames Sc = frames S /\
mo_le MT S Sc (if lp_grow l then mo_malloc MT (lp_vbytes l) + mo_free MT else 0) /\
mo_ok MT S (lp_cost MT l n) /\
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) v3): the tail's malloc at its own pre state Sc *)
rp_RM RP Sc (1 + kr) /\ cnt_ok RP (ablocks B lyc Sc) /\
blocks_bytes Sc + (n + 1) <= LIVE_MAX /\ n < 2 ^ 16 /\
garr8 SEGS (mrestrict (w_H Wc) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\
(lines = false -> (1 <= length x)%nat) /\
getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 22 = w64 SB /\
getr regsc 21 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (n + 1) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 96 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem Wc memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H Wc) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* :474 lpt_entry: the entry reads only the call state's ARx (ajournal_gx_AR_xR), so the proof is the strict one *)
Lemma lpt_entry_xR : forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
lp_tail_pre_xR W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) ss_lpt
(restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)))
/\ sh_ok SEGS lpt_Bx lpt_SH (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) (mrestrict (w_H Wc) memc).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr HPRE.
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Hrecs & Hcap & Hnc & Hv1 & Hv2 & Hperm & Hfr & Hmle & Hmok & _ & _ & Hbb &
Hn16 & Hx & Hlin1 & Hlin2 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R22 & R21 & R23 & R24 & R10 & Hsaved & Hapk).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc HJ) as HAR.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc' & Hvec & _).
assert (Rn0 : 0 <= hl_n lc) by (unfold hl_n; lia).
destruct Hvec as [[Hc0 _] | (Hc0 & Hin & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hin) as (Hv16 & Hv4096 & Hvceil & Hvapp & Hvpres & _).
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc _ _ HAR Hin) as Hoff.
assert (Hreq : req_size (AREC * hl_cap lc) = 16 * hl_cap lc)
by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap lc) 0); lia).
rewrite Hreq in Hvceil, Hvapp, Hvpres, Hoff.
pose proof (lpt_inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (lpt_inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
assert (Hsp16 : (spZ regs - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 LA)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact R18).
assert (E22 : ew E 22 = w64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 22 22%bv eq_refl); exact R22).
assert (E44 : ew E 44 = Z_to_bv 64 (hl_v lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 (hl_n lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 13)).
assert (E46 : ew E 46 = Z_to_bv 64 (hl_cap lc)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 14)).
assert (E47 : ew E 47 = Z_to_bv 64 (hl_v lc + 16 * hl_n lc))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 15)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (CK : forall off j r, nth_error lp_saved j = Some (off, r) -> ew E (32 + j) = getr regs (Z_to_bv 5 r) ->
YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 96) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j r Hj Hew.
  apply (chunk_ok_val SEGS E _ (spZ regs - 96) off 8 _ (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite Hew, Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. zside.
  - zside.
  - rewrite Forall_forall in Hsaved. exact (Hsaved (off, r) (nth_error_In _ _ Hj)). }
split.
- unfold ss_lpt. apply pa_entry_st_ok_full.
  + unfold lpt_regs. repeat apply lpt_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg| ..].
    all: cbn [sv_denot]; rewrite ?E18, ?E22; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
    first [rewrite R8 | rewrite R20 | rewrite R21 | rewrite R23 | rewrite R24]; reflexivity.
  + vm_compute. reflexivity.
  + unfold lpt_regions, lpt_stack, lpt_lregion, lpt_slot.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [unfold spZ in *; lia|]. split; [unfold spZ in *; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?a 0))) =>
        apply (CK o (a - 32)%nat _ eq_refl); reflexivity end.
    * rewrite (VB 18%nat LA E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HwL; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ LA 0 8 _ (hl_v lc)); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Mv.
      -- apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n lc)); [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
      -- apply (chunk_ok_val SEGS E _ LA 12 4 _ (hl_cap lc)); [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mc].
    * rewrite (VB 47%nat _ E47) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hvpres (hl_v lc + 16 * hl_n lc + o) ltac:(lia))).
  + apply pairwise_disjoint_of_extents. unfold lpt_regions, lpt_stack, lpt_lregion, lpt_slot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 18%nat LA E18) by lia. rewrite (VB 47%nat _ E47) by lia.
    cbn [base_val]. rewrite Usp. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold spZ in *. unf_imgband. repeat split; lia.
  + split; [|split; [exact I | split; [|exact I]]].
    * cbn [lpt_facts f_atoms atoms_ok]. unfold afact_ok, HEAPF. cbn [af_lo af_hi af_al2].
      rewrite Usp, E9, E18, E22, E44, E45, E46, E47. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hsp16, Hv16.
      unfold spZ in *. repeat match goal with |- _ /\ _ => split end; lia.
    * cbn [lpt_facts f_alias alias_ok lpt_alias sv_denot]. rewrite E44, E45, E47. rewrite !unsigned_lit_small by lia.
      assert (S1 : zalu64 ALU_SLL (hl_n lc) 4 = hl_n lc * 2 ^ 4).
      { unfold zalu64. cbn [zalu_raw]. change (Z.land (zcanon 4) 63) with 4. unfold zcanon, M64.
        rewrite (Z.mod_small (hl_n lc)) by lia. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. }
      assert (S2 : zalu64 ALU_ADD (hl_v lc) (hl_n lc * 2 ^ 4) = hl_v lc + 16 * hl_n lc).
      { unfold zalu64. cbn [zalu_raw]. unfold zcanon, M64.
        rewrite (Z.mod_small (hl_v lc)), (Z.mod_small (hl_n lc * 2 ^ 4)) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite !Z.add_0_r, !zalu64_sound, S1, S2. reflexivity.
- unfold sh_ok, lpt_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E lpt_Bx 18 LA 16 LA 0 16).
    * exact (azs_range_addressable_x B ARx LAWS lyc Sc Hpc Wc memc mdc LA 16 HAR HZ).
    * unfold U, lpt_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros y Hy. unfold SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E lpt_Bx 47 (hl_v lc + 16 * hl_n lc) 16 (hl_v lc + 16 * hl_n lc) 0 16).
    * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc Wc memc mdc (hl_v lc) (AREC * hl_cap lc)); [exact HAR | exact Hin | lia |].
      rewrite Hreq. lia.
    * unfold U, lpt_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hvapp. unfold SHADOW_OFF. lia.
Qed.
(* :725 lp_tail_seg *)
Lemma lp_tail_seg_xR : forall W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr,
In (q, k) (ablocks B lyc Sc) -> q <> hl_v lc -> q <= SRC -> SRC + Z.of_nat (length x) <= q + req_size k ->
lp_tail_pre_xR W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr ->
SRrG SEGS R Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_lp_mcall)) memc (seg_rom SEGS)) mdc)
(lp_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines x kr).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr Hq Hqv HqS HqE HPRE.
destruct (lpt_entry_xR W ly S Hp regs mem md LA SRC l lines x q k Wc lyc Sc Hpc regsc memc mdc kc lc kr HPRE) as [HS SHOK].
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Hrecs & Hcap & Hnc & Hv1 & Hv2 & Hperm & Hfrm & Hmle & Hmok & HRM & Hcnt & Hbb &
Hn16 & Hx & Hlin1 & Hlin2 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R22 & R21 & R23 & R24 & R10 & Hsaved & Hapk & Herrc).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] lyc Sc Hpc Wc memc mdc kc HJ) as HARc.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc' & Hvec & HND & HVR & HRECS).
assert (Rn0 : 0 <= hl_n lc) by (unfold hl_n; lia).
destruct Hvec as [[Hc0 _] | (Hc0 & Hin & Hjunk & Hgarr)]; [lia|].
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as (Hv16 & Hv4096 & Hvceil & Hvapp & Hvpres & _).
assert (Hreq : req_size (AREC * hl_cap lc) = 16 * hl_cap lc)
by (unfold req_size, AREC; destruct (Z.eqb_spec (16 * hl_cap lc) 0); lia).
rewrite Hreq in Hvceil, Hvapp, Hvpres.
pose proof (lpt_inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (lpt_inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as Hoff. rewrite Hreq in Hoff. unf_imgband.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hq) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _).
assert (Hn0 : 0 <= Z.of_nat (length x)) by lia.
assert (Hsp : alloc_ceiling + 16384 <= spZ regs - 96 /\ spZ regs <= 2 ^ 47) by (unfold spZ in *; lia).
(* errno's four bytes: image bytes, outside the list struct (gx_rt) *)
pose proof (pal_env B TL) as (_ & HeImg & _).
assert (HER : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i) /\ 0x10000 <= as_errno B + i < 0x5fc000 /\
  ~ (LA <= as_errno B + i < LA + 16)).
{ intros i Hi. assert (HI : in_img SEGS (as_errno B + i)) by (apply HeImg; clear - Hi; lia).
  split; [exact HI|]. split; [exact (pa_img_range _ HI)|].
  intros Hc. exact (proj1 (HGR _ (HGL _ Hc)) ltac:(clear - Hi; lia)). }
remember (Eimg (Ereg regsc (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regsc (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j (lpt_extra regs (hl_v lc) (hl_n lc) (hl_cap lc)) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
clear HE.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E3 : ew E 3 = getr regs 3) by exact (eq_trans (EA 3%nat ltac:(lia)) R3).
assert (E4 : ew E 4 = getr regs 4) by exact (eq_trans (EA 4%nat ltac:(lia)) R4).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x))) by exact (eq_trans (EA 9%nat ltac:(lia)) R9).
assert (E10 : ew E 10 = w64 (Z.of_nat (length x) + 1)) by exact (eq_trans (EA 10%nat ltac:(lia)) R10).
assert (E18 : ew E 18 = w64 LA) by exact (eq_trans (EA 18%nat ltac:(lia)) R18).
assert (E19 : ew E 19 = w64 SRC) by exact (eq_trans (EA 19%nat ltac:(lia)) R19).
assert (E22 : ew E 22 = w64 SB) by exact (eq_trans (EA 22%nat ltac:(lia)) R22).
assert (E27 : ew E 27 = getr regs 27) by exact (eq_trans (EA 27%nat ltac:(lia)) R27).
assert (E47 : ew E 47 = Z_to_bv 64 (hl_v lc + 16 * hl_n lc)) by exact (EX 15%nat ltac:(lia)).
assert (U18 : bv_unsigned (ew E 18) = LA) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U47 : bv_unsigned (ew E 47) = hl_v lc + 16 * hl_n lc) by (rewrite E47; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HSLOT : forall blc lyq a, In (hl_v lc, AREC * hl_cap lc) blc -> hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16 ->
awr_byte LP_STK (spZ regs) (lp_FP l) (ablocks B ly S) blc lyq [] a)
by (intros blc lyq a Hb Ha; apply (lpt_vec_awr ly S l lc); try assumption; unfold AREC; lia).
unfold cfg_at.
(* R1: the jal to malloc *)
paj_run_tok_xR RUNG HS HJ SHOK lpt_Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    right; left; apply HGL; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite U47 in Ha. left. split; [apply HSLOT; [exact Hin | lia] | lia]. }
rename HFr into HFr1, HG0 into HGr1. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H Wc) (ms_mem ms1) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha H1 H2. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms1) HFr1 a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18, ?U47; lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 96) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; unfold spZ in *; lia).
destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
(* the malloc rule's call-boundary premise at the call memory, from the call state's ARx *)
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
(* malloc(n + 1) *)
eapply (SRrG_bind SEGS R R_trans).
{ rewrite (pal_malloc B TL).
  eapply (AMA_R Wc (ms_regs ms1) (ms_mem ms1) LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] lyc Sc Hpc _ kc
    (Z.of_nat (length x) + 1) (-96) _ [] kr HJi).
  - rewrite Q10, E10. reflexivity.
  - lia.
  - exact Hbb.
  - exact Hcnt.
  - rewrite Usp1. lia.
  - reflexivity.
  - lia.
  - lia.
  - eapply aj_stack_room_xR with (o := -96); [exact HJi | rewrite Usp1; lia | lia].
  - rewrite Q3, E3. exact Hgp.
  - rewrite Q4, E4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre lyc _ (spZ regs - 96) (LA + 8) [] (ms_regs ms1)).
    + apply achain_low. lia.
    + rewrite Usp1. lia.
    + unfold s0Z. rewrite Q8, E18. unfold w64. rewrite (unsigned_lit_small LA) by lia. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - exact HRO.
  - cbn [spine]. replace (raZ (ms_regs ms1)) with (BASE + AF_fr_list_push + 0xe4); [exact HCTX_lp_malloc|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    first [lia | (unfold A_lp_mcall in *; lia) | (unfold A_lp_mcall, AF_fr_list_push in *; lia) |
           (idtac "LPT-CTX-RA"; match goal with |- ?g => idtac g end; fail)].
  - exact HRM.
  - apply (mok_station MT S Sc (lp_cost MT l (Z.of_nat (length x))) _ _ MLAW Hmok Hmle).
    + apply (mo_malloc_nonneg MT MLAW). lia.
    + unfold lp_cost. lia. }
cbv beta. intros W2 c2 HRw2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & d & -> & HJ2i & HP2 & Hd10 & Hfr2 & Hd4096 & Hbl2 & Hkept2 &
Hmle2 & HRM2 & Herr2 & Hpres2).
(* ---- after malloc: d (atom 52) is a new block of n + 1 bytes ---- *)
pose proof (proj1 HJ2i) as HAR2.
assert (Hreqd : req_size (Z.of_nat (length x) + 1) = Z.of_nat (length x) + 1)
by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length x) + 1) 0); lia).
assert (Hdn : In (d, Z.of_nat (length x) + 1) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Hvin2 : In (hl_v lc, AREC * hl_cap lc) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hin).
assert (Hqin2 : In (q, k) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hq).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hdn) as (Hd16 & _ & Hdceil & Hdapp & Hdpres & _).
rewrite Hreqd in Hdceil, Hdapp, Hdpres.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hvin2) as (_ & _ & _ & _ & Hvpres2 & _).
rewrite Hreq in Hvpres2.
pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hin) as Ddv. rewrite Hreq, Hreqd in Ddv.
pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hq) as Ddq. rewrite Hreqd in Ddq.
assert (Hne : (q, k) <> (hl_v lc, AREC * hl_cap lc)) by (intros He; injection He as He1 _; exact (Hqv He1)).
pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc q k _ _ HARc Hq Hin Hne) as Dqv.
rewrite Hreq in Dqv. unfold zdisjoint in Dqv. cbn [fst snd] in Dqv.
assert (NOTLA : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ (LA <= a < LA + 16)).
{ intros b m a Hbm Ha HLa. apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc b m a HARc Hbm Ha). exact (proj1 (HG a (HGL a HLa))). }
assert (KM : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
~ (d <= a < d + (Z.of_nat (length x) + 1)) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms1) a).
{ intros b m a Hbm Ha Hnd. destruct Hkept2 as (_ & K2 & _). replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hbm); [lia|]. cbv beta. rewrite Hreqd. replace (b + (a - b)) with a by lia. exact Hnd. }
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U18, ?U47.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 Hkept2); [lia | lia].
  - intros a Ha. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct Hkept2 as (_ & _ & K3 & _). apply K3.
    + exact (proj1 (HG a (HGL a ltac:(lia)))).
    + exact (proj1 (proj2 (HG a (HGL a ltac:(lia))))).
    + exact (proj1 (HGR a (HGL a ltac:(lia)))).
  - intros a Ha Hw. apply (lpt_writable_img Wc W2 (ms_mem ms1) mem2 a); [exact (proj1 (HG a (HGL a ltac:(lia)))) | | exact Hw].
    intros Hpa. apply Hpres2; [exact (proj1 (HG a (HGL a ltac:(lia))))
    | exact (lpt_inG_not_owned lyc Sc Hpc Wc _ _ a (proj1 HJi) (HGL a ltac:(lia)))
    | exact (lpt_inG_not_owned ly2 S2 Hp2 W2 mem2 md2 a HAR2 (HGL a ltac:(lia)))
    | exact (proj1 (HGR a (HGL a ltac:(lia))))
    | rewrite Hreqd; intros Hb; apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ a HAR2 Hdn); [rewrite Hreqd; lia|];
      exact (proj1 (HG a (HGL a ltac:(lia))))
    | exact Hpa].
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (KM (hl_v lc) (AREC * hl_cap lc) a Hin); [rewrite Hreq; unfold AREC in *; lia | lia].
  - intros a Ha _. apply (apresent_writable SEGS). exact (proj1 (Hvpres2 a ltac:(lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea52 : ew Ea 52 = w64 d) by (rewrite HEa; exact Hd10).
clear HEa.
assert (HFa : afact_ok Ea 52 (mkAF 4096 0x7fffff800000 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea52. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite Hd16. lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 52%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ2 : ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (kc + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (kc + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | apply out_none]. }
assert (U18a : bv_unsigned (ew Ea 18) = LA) by (rewrite OLDa by lia; exact U18).
assert (U47a : bv_unsigned (ew Ea 47) = hl_v lc + 16 * hl_n lc) by (rewrite OLDa by lia; exact U47).
assert (SHOK2 : sh_ok SEGS lpt_Bx lpt_SH Ea (mrestrict (w_H W2) mem2)).
{ apply (lpt_shok Ea ly2 S2 Hp2 W2 mem2 md2 LA (hl_v lc) (hl_n lc) (hl_cap lc) HAR2 HZ ltac:(lia) ltac:(lia) Hvin2 ltac:(lia));
  rewrite OLDa by lia; [exact E18 | exact E22 | exact E47]. }
(* R2: 0x85408 .. the jal to __asan_memcpy (0x8547c), through four UBSan trap branches *)
assert (EV44 : ew E 44 = Z_to_bv 64 (hl_v lc)) by exact (EX 12%nat ltac:(lia)).
assert (Ea44 : ew Ea 44 = Z_to_bv 64 (hl_v lc)) by (rewrite OLDa by lia; exact EV44).
assert (Ea47 : ew Ea 47 = Z_to_bv 64 (hl_v lc + 16 * hl_n lc)) by (rewrite OLDa by lia; exact E47).
assert (UA44 : U Ea (SOff 44 0) = hl_v lc) by (apply (U_atom Ea 44 _ Ea44); lia).
assert (UA47 : U Ea (SOff 47 0) = hl_v lc + 16 * hl_n lc) by (apply (U_atom Ea 47 _ Ea47); lia).
assert (Hsl8 : (hl_v lc + 16 * hl_n lc) mod 8 = 0) by (apply lp_mod8_of_16; [exact Hv16 | lia]).
paj_run_tok_xR RUNG HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrA, HG0 into HGrA. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msA end.
assert (Kw1 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msA) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem msA) HFrA a Ha); lp_nowr U18a U47a).
(* 0x85434 NULL-CONSISTENCY of v and the slot v + 16 N: the runner folded `snez v` to 1 (fact atom 44), so the
   trap edge is `1 =? seqz (v + 16 N)` and W_traps' trap_U_seqz gives the second as 0 *)
psrr_branch_tok RUNG BRG HS SHOK2 lpt_Bspan.
{ exfalso. lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
  rewrite trap_br_eq, (U_lit Ea 1 ltac:(lia)), (trap_U_seqz Ea (SOff 47 0) _ UA47 ltac:(lia)) in H; discriminate end. }
paj_run_tok_xR RUNG HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrB, HG0 into HGrB. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msB end.
assert (Kw2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msA) (ms_mem msB) HFrB a Ha ltac:(lp_nowr U18a U47a));
    apply Kw1; assumption).
(* 0x85448 POINTER OVERFLOW with a signed index: slti N,0 is 0 (fact atom 45) and sltu (v + 16 N) v is 0 *)
psrr_branch_tok RUNG BRG HS SHOK2 lpt_Bspan.
{ lp_trap (trap_ptr_sovf Ea (SAlu ALU_SLTU (SOff 47 0) (SOff 44 0)) (SLit 0) 0
    (trap_U_sltu_ge Ea (SOff 44 0) (SOff 47 0) (hl_v lc) (hl_v lc + 16 * hl_n lc) UA44 UA47 ltac:(lia))
    (U_lit Ea 0 ltac:(lia))). }
paj_run_tok_xR RUNG HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrC, HG0 into HGrC. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msC end.
assert (Kw3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msB) (ms_mem msC) HFrC a Ha ltac:(lp_nowr U18a U47a));
    apply Kw2; assumption).
(* 0x85454 ALIGN8 of the slot: v is 16-aligned (al_blocks), so v + 16 N is 8-aligned *)
psrr_branch_tok RUNG BRG HS SHOK2 lpt_Bspan.
{ lp_trap (trap_align8 Ea (SOff 47 0) (hl_v lc + 16 * hl_n lc) UA47 Hsl8). }
paj_run_tok_xR RUNG HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFrD, HG0 into HGrD. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msD end.
assert (Kw4 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msD) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msC) (ms_mem msD) HFrD a Ha ltac:(lp_nowr U18a U47a));
    apply Kw3; assumption).
(* 0x8546c NON-NULL of the slot *)
psrr_branch_tok RUNG BRG HS SHOK2 lpt_Bspan.
{ lp_trap (trap_nonnull Ea (SOff 47 0) (hl_v lc + 16 * hl_n lc) UA47 ltac:(lia)). }
paj_run_tok_xR RUNG HS HJ2 SHOK2 lpt_Bspan.
{ lp_awr_mid U18a U47a HGL HSLOT Hvin2. }
lp_clearbr.
rename HFr into HFr2, HG0 into HGrE. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into ms2 end.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> ~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha H1 H2; rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msD) (ms_mem ms2) HFr2 a Ha ltac:(lp_nowr U18a U47a));
    apply Kw4; assumption).
pose proof (mem_grows_trans _ _ _ HGrA (mem_grows_trans _ _ _ HGrB
  (mem_grows_trans _ _ _ HGrC (mem_grows_trans _ _ _ HGrD HGrE)))) as HGr2.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (Usp2 : spZ (ms_regs ms2) = spZ regs - 96).
{ unfold spZ. rewrite P2. rewrite OLDa by lia. rewrite E2. apply unsigned_lit_small. unfold spZ in *. lia. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2m.
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hdn) as Hdoff. rewrite Hreqd in Hdoff. unf_imgband.
(* the source bytes at the call are the ones at the malloc call *)
assert (KS : forall i, 0 <= i < Z.of_nat (length x) ->
aview SEGS (w_H W2) (ms_mem ms2) (SRC + i) = aview SEGS (w_H Wc) memc (SRC + i)).
{ intros i Hi. assert (Hb : q <= SRC + i < q + req_size k) by lia.
  rewrite K2 by (first [exact (NOTLA q k (SRC + i) Hq Hb) | unfold AREC in *; lia]).
  rewrite (KM q k (SRC + i) Hq Hb) by lia.
  apply K1; [lia | exact (NOTLA q k (SRC + i) Hq Hb) | unfold AREC in *; lia]. }
destruct HJ2 as (HSTK2 & HXO2 & (memS2 & HJi2 & HAG2) & HOUT2). rewrite !Z.add_0_r in HJi2.
(* __asan_memcpy(d, SRC, n) *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_intrin_at_xR B PST ARx LAWS R_trans WLE_R OCpy (SIGMA WS_asan_memcpy) AMEMCPY W2 (ms_regs ms2) (ms_mem ms2) LP_STK (spZ regs)
    (lp_FP l) ly S Hp W memS2 md [] ly2 S2 Hp2 _ (kc + 1) d SRC (Z.of_nat (length x)) (-96) _ HJi2).
  - rewrite P10, Ea52. reflexivity.
  - rewrite P11. rewrite OLDa by lia. exact E19.
  - rewrite P12. rewrite OLDa by lia. exact E9.
  - lia.
  - lia.
  - lia.
  - rewrite Usp2. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite P3. rewrite OLDa by lia. rewrite E3. exact Hgp.
  - rewrite P4. rewrite OLDa by lia. rewrite E4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia].
    replace a with (d + (a - d)) by lia.
    eapply (awr_new_block_any_xR SEGS B PST ARx LAWS (R := R) LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] lyc Sc Hpc Wc (ms_mem ms1) _ kc
      ly2 S2 Hp2 W2 mem2 md2 d (Z.of_nat (length x) + 1) (ablocks B ly2 S2) (a - d) ly2 [] HJi HAR2 Hbl2);
    [lia | exact Hdn | rewrite Hreqd; lia].
  - eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ d (Z.of_nat (length x) + 1));
    [exact HAR2m | exact Hdn | lia | rewrite Hreqd; lia].
  - eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ d (Z.of_nat (length x) + 1));
    [exact HAR2m | exact Hdn | lia | rewrite Hreqd; lia].
  - intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ d (Z.of_nat (length x) + 1));
    [exact HAR2m | exact Hdn | lia | rewrite Hreqd; lia | exact Hpos].
  - split; [lia|]. split; [lia|]. split; [|split; [lia|]].
    + intros a Ha. split; [|rewrite Usp2; lia].
      replace a with (SRC + Z.of_nat (Z.to_nat (a - SRC))) by lia. rewrite KS by lia.
      unfold aview. rewrite (garr8_mbyte SEGS _ SRC _ (Z.to_nat (a - SRC)) Hx) by (unfold bzs; rewrite length_map; lia).
      discriminate.
    + split; [eapply (YCe5x.amem_range_of_block_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem ms2) _ q k); [exact HAR2m | exact Hqin2 | lia | lia]|].
      split; [eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ q k); [exact HAR2m | exact Hqin2 | lia | lia]|].
      intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem ms2) _ q k);
      [exact HAR2m | exact Hqin2 | lia | lia | exact Hpos]. }
cbv beta. intros W3 c3 HRw3 (-> & regs3 & mem3 & md3 & -> & HJ3i & HP3 & Hd10b & Hcpy & Hfr3 & Hpres3).
(* ---- after __asan_memcpy ---- *)
assert (Usp2a : bv_unsigned (ew Ea 2) = spZ regs - 96) by (rewrite OLDa by lia; exact Usp).
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 2 (spZ regs - 96)); [exact Usp2a | | exact Hpres3].
    intros a Ha. apply Hfr3; lia.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 18 LA); [exact U18a | | exact Hpres3].
    intros a Ha. apply Hfr3; lia.
  - apply (region_kept_aview Ea (w_H W2) (ms_mem ms2) mem3 47 (hl_v lc + 16 * hl_n lc)); [exact U47a | | exact Hpres3].
    intros a Ha. apply Hfr3; unfold AREC in *; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 64 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 64)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
(* the byte d + n: atom 80, its fact, its alias, its region *)
pose proof (st_ok_pi_havoc 80 Eb _ _ [w64 (d + Z.of_nat (length x))] HS ltac:(vm_compute; reflexivity) ltac:(cbv; lia)) as HSc.
clear HS. rename HSc into HS.
remember (havoc Eb 80 [w64 (d + Z.of_nat (length x))]) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 80)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (Ec80 : ew Ec 80 = w64 (d + Z.of_nat (length x))) by (rewrite HEc; reflexivity).
clear HEc.
assert (Ec52 : ew Ec 52 = w64 d) by (rewrite OLDc, OLDb by lia; exact Ea52).
assert (Ec9 : ew Ec 9 = w64 (Z.of_nat (length x))) by (rewrite OLDc, OLDb, OLDa by lia; exact E9).
assert (U80 : bv_unsigned (ew Ec 80) = d + Z.of_nat (length x)) by (rewrite Ec80; apply unsigned_lit_small; lia).
assert (U18c : bv_unsigned (ew Ec 18) = LA) by (rewrite OLDc, OLDb by lia; exact U18a).
assert (U47c : bv_unsigned (ew Ec 47) = hl_v lc + 16 * hl_n lc) by (rewrite OLDc, OLDb by lia; exact U47a).
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs - 96) by (rewrite OLDc, OLDb by lia; exact Usp2a).
assert (HFc : afact_ok Ec 80 HEAPF) by (unfold afact_ok, HEAPF; cbn [af_lo af_hi af_al2]; rewrite U80; rewrite Z.pow_0_r, Z.mod_1_r; lia).
pose proof (st_ok_pi_add_fact Ec _ _ 80%nat _ HS HFc) as HSc. clear HS HFc. rename HSc into HS.
assert (HAc : sv_denot Ec (SAlu ALU_ADD (SOff 52 0) (SOff 9 0)) = sv_denot Ec (SOff 80 0)).
{ cbn [sv_denot]. rewrite Ec52, Ec9, Ec80. unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r, zalu64_sound.
  apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
  rewrite (Z.mod_small d), (Z.mod_small (Z.of_nat (length x))) by lia. apply Z.mod_mod. lia. }
pose proof (st_ok_pi_add_alias Ec _ _ _ _ HS HAc) as HSc. clear HS HAc. rename HSc into HS.
assert (Hpd : forall i, 0 <= i <= Z.of_nat (length x) -> apresent (w_H W2) mem3 (d + i)).
{ intros i Hi. apply Hpres3. apply (lpt_apresent_grows _ mem2 _ _ HGr2). exact (proj1 (Hdpres (d + i) ltac:(lia))). }
pose proof (st_ok_pi_add_region Ec _ _ lpt_aE HS ltac:(vm_compute; reflexivity)) as HSc.
match type of HSc with ?ty -> _ => assert (HRG : ty); [|specialize (HSc HRG); clear HRG] end.
{ unfold lpt_aE, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite U80. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). replace (d + Z.of_nat (length x) + o) with (d + Z.of_nat (length x)) by lia.
  apply Hpd. lia. }
match type of HSc with ?ty -> _ => assert (HRD : ty); [|specialize (HSc HRD); clear HRD] end.
{ lazymatch goal with |- all_disjoint _ _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  unfold lpt_aE. cbn [all_disjoint]. unfold YP09.extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U80, Uspc, U18c, U47c. unfold spZ in *. unfold AREC in *. repeat split; lia. }
clear HS. rename HSc into HS.
assert (HJ3 : ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem3 md3 (kc + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem3 md3 (kc + 1) memS2);
  [lia | lia | rewrite !Z.add_0_r; exact HJ3i | exact HAG2 | apply out_none]. }
pose proof (proj1 HJ3i) as HAR3.
assert (SHOK3 : sh_ok SEGS lpt_Bx lpt_SH3 Ec (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, lpt_SH3. apply Forall_app. split.
  - apply (lpt_shok Ec ly2 S2 Hp2 W2 mem3 md3 LA (hl_v lc) (hl_n lc) (hl_cap lc) HAR3 HZ ltac:(lia) ltac:(lia) Hvin2 ltac:(lia));
    rewrite OLDc, OLDb, OLDa by lia; [exact E18 | exact E22 | exact E47].
  - constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W2) mem3 Ec lpt_Bx 80 (d + Z.of_nat (length x)) 1 (d + Z.of_nat (length x)) 0 1).
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 mem3 md3 d (Z.of_nat (length x) + 1)); [exact HAR3 | exact Hdn | lia |].
      rewrite Hreqd. lia.
    + unfold U, lpt_Bx. cbn [sv_denot]. rewrite OLDc, OLDb, OLDa by lia. rewrite E22, Z.add_0_r. unfold w64.
      rewrite Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Ec80, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hdapp. unfold SHADOW_OFF. lia. }
(* R3: 0x85480 .. the ret, through two UBSan trap branches: the NUL at d + n, the slot length,
   l->n = n + 1, the epilogue *)
assert (UC52 : U Ec (SOff 52 0) = d) by (apply (U_atom Ec 52 _ Ec52); lia).
assert (UC80 : U Ec (SOff 80 0) = d + Z.of_nat (length x)) by (apply (U_atom Ec 80 _ Ec80); lia).
assert (AWRD : forall a, d <= a < d + (Z.of_nat (length x) + 1) ->
awr_byte LP_STK (spZ regs) (lp_FP l) (ablocks B ly S) (ablocks B ly2 S2) ly2 [] a).
{ intros a Ha. replace a with (d + (a - d)) by lia.
  eapply (awr_new_block_any_xR SEGS B PST ARx LAWS (R := R) LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] lyc Sc Hpc Wc (ms_mem ms1) _ kc
    ly2 S2 Hp2 W2 mem2 md2 d (Z.of_nat (length x) + 1) (ablocks B ly2 S2) (a - d) ly2 [] HJi HAR2 Hbl2);
  [lia | exact Hdn | rewrite Hreqd; lia]. }
paj_run_tok_xR RUNG HS HJ3 SHOK3 lpt_Bspan.
{ lp_awr_end U80 U18c U47c HGL HSLOT Hvin2 AWRD. }
lp_clearbr.
rename HFr into HFrF, HG0 into HGrF. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msF end.
assert (Kw5 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
~ (d + Z.of_nat (length x) <= a < d + Z.of_nat (length x) + 1) ->
aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem3 a)
by (intros a Ha H1 H2 H3; apply (aview_kept_out _ _ (w_H W2) mem3 (ms_mem msF) HFrF a Ha); lp_nowr3 U80 U18c U47c).
(* 0x854e4 POINTER OVERFLOW of d + n: no unsigned wrap, d <= d + n *)
psrr_branch_tok RUNG BRG HS SHOK3 lpt_Bspan.
{ lp_trap (trap_ptr_bltu Ec (SOff 52 0) (SOff 80 0) d (d + Z.of_nat (length x)) UC52 UC80 ltac:(lia)). }
paj_run_tok_xR RUNG HS HJ3 SHOK3 lpt_Bspan.
{ lp_awr_end U80 U18c U47c HGL HSLOT Hvin2 AWRD. }
lp_clearbr.
rename HFr into HFrG, HG0 into HGrG. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msG end.
assert (Kw6 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
~ (d + Z.of_nat (length x) <= a < d + Z.of_nat (length x) + 1) ->
aview SEGS (w_H W2) (ms_mem msG) a = aview SEGS (w_H W2) mem3 a)
by (intros a Ha H1 H2 H3;
    rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msF) (ms_mem msG) HFrG a Ha ltac:(lp_nowr3 U80 U18c U47c));
    apply Kw5; assumption).
(* 0x854f4 NULL-CONSISTENCY of d and d + n: the runner folded `snez d` to 1 (fact atom 52) *)
psrr_branch_tok RUNG BRG HS SHOK3 lpt_Bspan.
{ exfalso. lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
  rewrite trap_br_eq, U_SAlu, (U_lit Ec 1 ltac:(lia)), (trap_U_seqz Ec (SOff 80 0) _ UC80 ltac:(lia)),
          (U_lit Ec 0 ltac:(lia)) in H; vm_compute in H; discriminate end. }
paj_run_tok_xR RUNG HS HJ3 SHOK3 lpt_Bspan.
{ lp_awr_end U80 U18c U47c HGL HSLOT Hvin2 AWRD. }
lp_clearbr.
rename HFr into HFr3, HG0 into HGrH. clear HF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
pose proof (mem_grows_trans _ _ _ HGrF (mem_grows_trans _ _ _ HGrG HGrH)) as HGr3.
(* ---- at the ret ---- *)
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (22%bv : bv 5) F22. prreg HS (21%bv : bv 5) F21. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (OLDE : forall m, (m < 48)%nat -> ew Ec m = ew E m) by (intros m Hm; rewrite OLDc, OLDb, OLDa by lia; reflexivity).
assert (HPF : aregs_preserved regs (ms_regs msf)).
{ apply aregs_preserved_eqs.
  - rewrite F2, Uspc. replace (spZ regs - 96 + 96) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite F3, OLDE by lia. exact E3.
  - rewrite F4, OLDE by lia. exact E4.
  - rewrite F8, OLDE by lia. exact (EX 1%nat ltac:(lia)).
  - rewrite F9, OLDE by lia. exact (EX 2%nat ltac:(lia)).
  - rewrite F18, OLDE by lia. exact (EX 3%nat ltac:(lia)).
  - rewrite F19, OLDE by lia. exact (EX 4%nat ltac:(lia)).
  - rewrite F20, OLDE by lia. exact (EX 5%nat ltac:(lia)).
  - rewrite F21, OLDE by lia. exact (EX 6%nat ltac:(lia)).
  - rewrite F22, OLDE by lia. exact (EX 7%nat ltac:(lia)).
  - rewrite F23, OLDE by lia. exact (EX 8%nat ltac:(lia)).
  - rewrite F24, OLDE by lia. exact (EX 9%nat ltac:(lia)).
  - rewrite F25, OLDE by lia. exact (EX 10%nat ltac:(lia)).
  - rewrite F26, OLDE by lia. exact (EX 11%nat ltac:(lia)).
  - rewrite F27, OLDE by lia. exact E27. }
assert (ER1 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
(* the memory at the ret *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 80)%nat -> ew Ef m = ew Ec m) by (intros m Hm; subst Ef; rewrite !ew_ewset_other by lia; reflexivity).
assert (E44 : ew E 44 = Z_to_bv 64 (hl_v lc)) by exact (EX 12%nat ltac:(lia)).
assert (E45 : ew E 45 = Z_to_bv 64 (hl_n lc)) by exact (EX 13%nat ltac:(lia)).
assert (E46 : ew E 46 = Z_to_bv 64 (hl_cap lc)) by exact (EX 14%nat ltac:(lia)).
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RL.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RS.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RE.
cbn [ms_mem restrict] in RL, RS, RE.
assert (UFL : bv_unsigned (ew Ef 18) = LA) by (rewrite UF by lia; exact U18c).
assert (UFS : bv_unsigned (ew Ef 47) = hl_v lc + 16 * hl_n lc) by (rewrite UF by lia; exact U47c).
assert (UFE : bv_unsigned (ew Ef 80) = d + Z.of_nat (length x)).
{ subst Ef. rewrite !ew_ewset_other by lia. exact U80. }
assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) (hl_v lc)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDE by lia. rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n lc + 1)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDE by lia. rewrite E45. rewrite unsigned_lit_small by lia. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (hl_cap lc)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF, OLDE by lia. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (hl_v lc + 16 * hl_n lc + 0) (N.to_nat 8) d).
{ eapply (field_of_region Ef _ 47 _); [exact RS | exact UFS | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite Ec52. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VS8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (hl_v lc + 16 * hl_n lc + 8) (N.to_nat 8) (Z.of_nat (length x))).
{ eapply (field_of_region Ef _ 47 _); [exact RS | exact UFS | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite Ec9. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VE : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (d + Z.of_nat (length x) + 0) (N.to_nat 1) 0).
{ eapply (field_of_region Ef _ 80 _); [exact RE | exact UFE | cbn [In]; left; reflexivity | reflexivity | zside | zside]. }
rewrite Z.add_0_r in VL0, VS0, VE.
assert (HAWR : awr W2 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite UFL in RLw. exact (RLw i Hi). }
(* every old block byte outside the slot is the byte at the call *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) -> ~ (d + Z.of_nat (length x) <= a < d + Z.of_nat (length x) + 1) ->
aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha H1 H2 H3.
  rewrite (aview_kept_out _ _ (w_H W2) (ms_mem msG) (ms_mem msf) HFr3 a Ha ltac:(lp_nowr3 U80 U18c U47c)).
  apply Kw6; assumption. }
assert (KB : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
~ (hl_v lc + 16 * hl_n lc <= a < hl_v lc + 16 * hl_n lc + 16) ->
aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H Wc) memc a).
{ intros b m a Hbm Ha Hns.
  pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hbm) as Dn. rewrite Hreqd in Dn.
  pose proof (NOTLA b m a Hbm Ha) as Hla.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hbm) as (_ & Hb4096 & Hbc & _).
  rewrite K3 by lia. rewrite Hfr3 by lia. rewrite K2 by lia. rewrite (KM b m a Hbm Ha) by lia. apply K1; lia. }
assert (KD : forall i, 0 <= i < Z.of_nat (length x) ->
aview SEGS (w_H W2) (ms_mem msf) (d + i) = aview SEGS (w_H Wc) memc (SRC + i)).
{ intros i Hi. rewrite K3.
  - rewrite (Hcpy i Hi). apply KS. exact Hi.
  - lia.
  - intros HLa. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ (d + i) HAR2 Hdn); [rewrite Hreqd; lia|].
    exact (proj1 (HG _ (HGL _ HLa))).
  - unfold AREC in *. lia.
  - lia. }
(* the new text *)
assert (GD : garr8 SEGS (arm W2 (ms_mem msf)) d (bzs (x ++ [Z_to_bv 8 0]))).
{ unfold bzs, arm. rewrite map_app. apply garr8_app. split.
  - fold (bzs x). apply (lpt_garr8_moved (w_H Wc) (w_H W2) memc (ms_mem msf) SRC d); [|exact Hx].
    intros j Hj. unfold bzs in Hj. rewrite length_map in Hj. apply KD. lia.
  - rewrite length_map. intros j Hj. cbn [length map] in Hj. assert (j = 0%nat) as -> by lia. cbn [nth map].
    change (bz (Z_to_bv 8 0)) with 0. split; [|lia]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact VE. }
(* the old texts *)
assert (RECS : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly2 S2) /\
garr8 SEGS (arm W2 (ms_mem msf)) (fst r) (bzs (snd r ++ [Z_to_bv 8 0])) /\
(lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= APARTIAL) /\
(lines = false -> (1 <= length (snd r))%nat)) (hl_recs lc)).
{ rewrite Forall_forall in HRECS |- *. intros r Hr. destruct (HRECS r Hr) as (Hb & Hg & Hl1 & Hl2).
  split; [rewrite Hbl2; apply in_or_app; left; exact Hb|]. split; [|split; assumption].
  assert (Hne' : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v lc, AREC * hl_cap lc)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hb Hin Hne') as Dr.
  rewrite Hreq in Dr. unfold zdisjoint in Dr. cbn [fst snd] in Dr.
  assert (Hreqr : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
  rewrite Hreqr in Dr.
  apply (lpt_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem msf)); [|exact Hg].
  intros j Hj. unfold bzs in Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  apply (KB _ _ _ Hb); [rewrite Hreqr; lia | unfold AREC in *; lia]. }
(* the vector *)
assert (Hj16 : (16 <= length (hl_junk lc))%nat) by (unfold AREC in *; lia).
assert (GV : garr8 SEGS (arm W2 (ms_mem msf)) (hl_v lc)
  (bzs (concat (map text_rec (hl_recs lc ++ [(d, x)])) ++ skipn 16 (hl_junk lc)))).
{ apply (lpt_vec_garr8 (w_H Wc) (w_H W2) memc (ms_mem msf) (hl_v lc) (hl_recs lc) (hl_junk lc) d x Hj16 Hgarr).
  - intros a Ha. apply (KB (hl_v lc) (AREC * hl_cap lc) a Hin); unfold hl_n, AREC in *; rewrite ?Hreq; lia.
  - lia.
  - lia.
  - exact VS0.
  - exact VS8. }
assert (HN' : hl_n (HL (hl_v lc) (hl_cap lc) (hl_recs lc ++ [(d, x)]) (skipn 16 (hl_junk lc))) = hl_n lc + 1)
by (unfold hl_n; cbn [hl_recs]; rewrite length_app; cbn [length]; lia).
(* ---- the return ---- *)
(* the rest is the ret: a strict step lifted to R *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold lp_post_xR.
exists ly2, S2, Hp2, (ms_regs msf), (ms_mem msf). eexists.
exists (kc + 1), (HL (hl_v lc) (hl_cap lc) (hl_recs lc ++ [(d, x)]) (skipn 16 (hl_junk lc))), d.
split; [rewrite F1, OLDE by lia; rewrite ER1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ3|].
split; [exact HPF|].
split.
{ unfold alist_at. cbn [hl_v hl_cap hl_recs hl_junk]. rewrite HN'.
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [lia|].
  split; [right; split; [lia|]; split; [exact Hvin2|]; split; [rewrite length_skipn; unfold AREC in *; lia | exact GV]|].
  split.
  { rewrite map_app. cbn [map fst]. apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_cons_append _ _)).
    constructor; [|exact (proj1 (NoDup_ListNoDup _) HND)].
    intros Hd'. apply in_map_iff in Hd' as (r & Hrd & Hr). rewrite Forall_forall in HRECS. destruct (HRECS r Hr) as (Hb & _).
    pose proof (lpt_new_disj ly2 S2 Hp2 W2 mem2 md2 lyc Sc d _ _ _ HAR2 Hbl2 Hb) as Dn. rewrite Hreqd in Dn.
    unfold req_size in Dn. destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia. }
  split.
  { rewrite map_app. cbn [map fst]. intros Hv'. apply in_app_or in Hv' as [Hv' | [Hv' | []]]; [exact (HVR Hv')|].
    unfold AREC in *. lia. }
  apply Forall_app. split; [exact RECS|]. constructor; [|constructor].
  split; [exact Hdn|]. split; [exact GD|]. split; [exact Hlin1 | exact Hlin2]. }
split; [cbn [hl_recs]; rewrite Hrecs; reflexivity|].
split; [cbn [hl_cap]; exact Hcap|].
split; [intros Hg; cbn [hl_v]; exact (Hv1 Hg)|].
split.
{ intros rest Hpm. rewrite Hbl2. cbn [hl_v hl_cap].
  eapply Permutation_trans; [apply Permutation_app_tail; exact (Hperm rest Hpm)|].
  apply Permutation_sym. apply Permutation_cons_append. }
split.
{ intros a Hi Hno Herr Hpa.
  assert (Hnot : forall ly0 S0 Hq0 (W0 : world SEGS) m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hq0 W0 m0 md0 HAx Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HAx Hi) Ho)).
  pose proof (lpt_apresent_grows _ _ _ _ HGr1 (Hapk a Hi Hno Herr Hpa)) as AP2.
  assert (AP3 : apresent (w_H W2) mem2 a).
  { apply (Hpres2 a Hi (Hnot _ _ _ _ _ _ (proj1 HJi)) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact AP2].
    intros Hb. exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ a HAR2 Hdn Hb Hi). }
  exact (lpt_apresent_grows _ _ _ _ HGr3 (Hpres3 a (lpt_apresent_grows _ _ _ _ HGr2 AP3))). }
(* errno: no run writes it (image, outside the struct, the slot and the NUL byte), malloc keeps its view, and
   __asan_memcpy writes only [d, d + n) and its stack band *)
split.
{ intros i Hi. destruct (HER i Hi) as (HI & HR & HnL).
  assert (HnS : ~ (hl_v lc + 16 * hl_n lc <= as_errno B + i < hl_v lc + 16 * hl_n lc + 16)).
  { intros Hc. apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ (as_errno B + i) HARc Hin); [|exact HI].
    rewrite Hreq. clear - Hc Hnc Rn0. lia. }
  assert (HnD : ~ (d <= as_errno B + i < d + (Z.of_nat (length x) + 1))).
  { intros Hc. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 d _ (as_errno B + i) HAR2 Hdn); [|exact HI].
    rewrite Hreqd. exact Hc. }
  rewrite K3 by (clear - HR HnL HnS HnD; lia).
  rewrite Hfr3 by (clear - HR HnD Hsp Hes C1; lia).
  rewrite K2 by (clear - HR HnL HnS; lia).
  rewrite (Herr2 i Hi).
  rewrite K1 by (clear - HR HnL HnS; lia).
  exact (Herrc i Hi). }
split; [rewrite Hfr2; exact Hfrm|].
split; [unfold lp_cost; exact (mle_station MT S Sc S2 _ _ MLAW Hmle Hmle2)|].
(* the room round: the malloc's post keeps the room invariant at the return's allocator state S2 *)
exact HRM2.
Qed.
(* :1510 lp_rcall_pre *)
Definition lp_rcall_pre_xR (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B ly S W memc LA l lines /\ hl_n l = hl_cap l /\ lp_vbytes l < MMAX /\
blocks_bytes S + tr_peak (lp_tr l n) <= LIVE_MAX /\ n < 2 ^ 16 /\
In (q, k) (ablocks B ly S) /\ q <> hl_v l /\ q <= SRC /\ SRC + n <= q + req_size k /\
garr8 SEGS (mrestrict (w_H W) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\ (lines = false -> (1 <= length x)%nat) /\
mo_ok MT S (lp_cost MT l n) /\
rp_RM RP S (3 + kr)%nat /\ cnt_ok_pk RP (lp_peak l n) (ablocks B ly S) /\
getr regsc 1 = Z_to_bv 64 (BASE + A_lp_rret) /\ getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 22 = w64 SB /\
getr regsc 21 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\
getr regsc 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (hl_v l) /\ getr regsc 11 = w64 (lp_vbytes l) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H W) memc) (spZ regs - 96 + fst p) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem W memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* :1551 lp_grow_seg *)
Lemma lp_grow_seg_xR : forall W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr,
lp_rcall_pre_xR W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA WS_realloc)) memc (seg_rom SEGS)) mdc)
(lp_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines x kr).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr HPRE.
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Heq & Hvb & Hlive & Hx16 & Hq & Hqv & HqS & HqE & HSRC &
Hlin1 & Hlin2 & HMOK & HRM & HCNT & R1 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R22 & R21 & R23 & R24 & R25 & R26 &
R10 & R11 & HSAVED & HAPK & HERRC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 HJ) as HARc.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc & Hvec & HND & HVR & HRECS).
pose proof (proj1 (Forall_forall _ _) HRECS) as HRECS'.
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hgr : lp_grow l = true) by (unfold lp_grow; rewrite Heq; apply Z.eqb_refl).
assert (Hgc : grow_cap (hl_n l) (hl_cap l) = if hl_cap l =? 0 then 8 else 2 * hl_cap l)
by (unfold grow_cap; rewrite Heq, Z.eqb_refl; reflexivity).
assert (Hvb16 : lp_vbytes l = 16 * grow_cap (hl_n l) (hl_cap l)) by reflexivity.
assert (Hgb : hl_cap l < grow_cap (hl_n l) (hl_cap l) /\ 16 * grow_cap (hl_n l) (hl_cap l) < 2 ^ 30)
by (rewrite Hgc in *; destruct (Z.eqb_spec (hl_cap l) 0); lia).
(* C3's peak: realloc's live bytes at S, and the tail malloc's after it *)
destruct (lp_peak_grow (blocks_bytes S) l (Z.of_nat (length x)) Hgr ltac:(lia) Hlive) as [Hlv1 Hlv2].
pose proof (inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
assert (Usp : spZ regsc = spZ regs - 96) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
destruct HJ as (HSTK0 & HXO0 & (memS & HJi & HAG) & HOUT0). rewrite !Z.add_0_r in HJi.
(* the realloc rule's call-boundary premise at the call memory, from the call state's ARx, and its hull admission
   from the meter fact at the call *)
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
assert (HMOKc : mo_ok MT S (mo_malloc MT (lp_vbytes l) + mo_free MT)).
{ apply (mok_station MT S S (lp_cost MT l (Z.of_nat (length x))) 0 _ MLAW HMOK (mle_start MT S MLAW)).
  + pose proof (mo_free_nonneg MT MLAW). pose proof (mo_malloc_nonneg MT MLAW (lp_vbytes l) ltac:(lia)). lia.
  + unfold lp_cost. rewrite Hgr. pose proof (mo_malloc_nonneg MT MLAW (Z.of_nat (length x) + 1) ltac:(lia)). lia. }
(* realloc(v, 16 * s9) *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (ARE_R W regsc memc LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] ly S Hp mdc 0 (hl_v l) (AREC * hl_cap l)
    (lp_vbytes l) (-96) _ [] (1 + kr)%nat HJi).
  - destruct Hvec as [[_ ->] | (_ & Hin & _)]; [left; reflexivity | right; exact Hin].
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - exact (lp_cnt_at RP _ _ HCNT).
  - rewrite Usp. lia.
  - reflexivity.
  - lia.
  - lia.
  - eapply aj_stack_room_xR with (o := -96); [exact HJi | rewrite Usp; lia | lia].
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold A_lp_rret, AF_fr_list_push; lia | reflexivity].
  - apply (achain_chain_pre ly _ (spZ regs - 96) (LA + 8) [] regsc).
    + apply achain_low. lia.
    + rewrite Usp. lia.
    + unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite R1. rewrite unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
      unfold A_lp_rret, AF_fr_list_push. lia.
  - exact HRO.
  - apply HA_call. exact HMOKc.
  - cbn [spine]. replace (raZ regsc) with (BASE + AF_fr_list_push + 0xc0); [exact HCTX_lp_realloc|].
    unfold raZ. rewrite R1, unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
    unfold A_lp_rret. lia.
  - exact HRM.
  - intros Hp0 Hin i Hi. unfold lp_FP. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0].
    + destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact (False_ind _ (Hp0 Hv0)) | lia].
    + exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity|]. cbn [fst snd].
      unfold req_size, AREC in Hi. destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; unfold AREC; lia.
  - exact HMOKc. }
cbv beta. intros W2 c2 HRw2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres & Hfr2 & H4096 & Hp0 & Hpn &
Hcpy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
(* ---- after realloc: res (atom 10) is the new vector; the old one went ---- *)
pose proof (proj1 HJ2i) as HAR2.
assert (HPM : exists L, Permutation (ablocks B ly2 S2) ((res, lp_vbytes l) :: L) /\
  (forall b, In b (ablocks B ly S) -> b <> (hl_v l, AREC * hl_cap l) -> In b L) /\
  (forall rest, Permutation (ablocks B ly S) ((if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) ++ rest) ->
    Permutation L rest) /\
  bsum L + (if hl_cap l =? 0 then 0 else AREC * hl_cap l) = bsum (ablocks B ly S) /\
  (forall Pq, (acnt Pq L <= acnt Pq (ablocks B ly S))%nat)).
{ destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0].
  - assert (Hv0 : hl_v l = 0) by (destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact Hv0 | lia]).
    exists (ablocks B ly S). split; [exact (Hp0 Hv0)|]. split; [intros b Hb _; exact Hb|].
    split; [intros rest Hpr; exact Hpr|]. split; [cbv beta iota; lia | intros Pq; lia].
  - destruct Hvec as [[Hc _] | (_ & Hin & _)]; [lia|].
    assert (Hv0 : hl_v l <> 0)
    by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
    destruct (Hpn Hv0) as (l1 & l2 & El & Hpq).
    exists (l1 ++ l2). split; [exact Hpq|]. split.
    + intros b Hb Hne. rewrite El in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]];
      [apply in_or_app; left; exact Hb | exfalso; apply Hne; symmetry; exact Hb | apply in_or_app; right; exact Hb].
    + split.
      * intros rest Hpr. rewrite El in Hpr.
        exact (Permutation_app_inv l1 l2 [] rest (hl_v l, AREC * hl_cap l) Hpr).
      * split; [rewrite El, !bsum_app, bsum_cons; cbn [snd]; cbv beta iota; unfold AREC; lia|].
        intros Pq. rewrite El. apply acnt_del_le. }
destruct HPM as (L & HPL & HinL & HpermL & HbsL & HcL).
assert (HND2 : List.NoDup ((res, lp_vbytes l) :: L)) by exact (Permutation_NoDup HPL (lp_nodup ly2 S2 Hp2 W2 mem2 md2 HAR2)).
apply NoDup_cons_iff in HND2 as [HnotL HNDL].
assert (Hvin2 : In (res, lp_vbytes l) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
assert (HL2 : forall b, In b L -> In b (ablocks B ly2 S2)) by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); right; exact Hb).
assert (DL : forall b m, In (b, m) L -> b + req_size m <= res \/ res + req_size (lp_vbytes l) <= b).
{ intros b m Hb. assert (Hne : (b, m) <> (res, lp_vbytes l)) by (intros He; rewrite He in Hb; exact (HnotL Hb)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m res (lp_vbytes l) HAR2 (HL2 _ Hb) Hvin2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hvin2) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _).
assert (Hreqv : req_size (lp_vbytes l) = lp_vbytes l) by (unfold req_size; destruct (Z.eqb_spec (lp_vbytes l) 0); lia).
rewrite Hreqv in Hrceil, Hrapp, Hrpres, DL.
destruct Hkept2 as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
(* a byte of an old block other than the old vector is the byte at the call *)
assert (KB : forall b m a, In (b, m) (ablocks B ly S) -> (b, m) <> (hl_v l, AREC * hl_cap l) -> b <= a < b + req_size m ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros b m a Hb Hne Ha. pose proof (DL b m (HinL _ Hb Hne)) as D1.
  assert (D2 : hl_v l <> 0 -> b + req_size m <= hl_v l \/ hl_v l + req_size (AREC * hl_cap l) <= b).
  { intros Hv0. destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exfalso; exact (Hv0 Hv)|].
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W memc mdc b m _ _ HARc Hb Hin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
  replace a with (b + (a - b)) by lia. apply (KA2 b m (a - b) Hb); [lia|]. cbv beta.
  intros [Hx | (Hv0 & Hx)]; [lia | specialize (D2 Hv0); lia]. }
(* the list struct's bytes are image bytes: kept, and still writable *)
assert (KL : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply KA3; [exact (proj1 (HG a (HGL a Ha))) | exact (proj1 (proj2 (HG a (HGL a Ha)))) | exact (proj1 (HGR a (HGL a Ha)))]. }
assert (WL2 : forall o, 0 <= o < 16 -> writable_at SEGS (mrestrict (w_H W2) mem2) (LA + o)).
{ intros o Ho. assert (Ha : LA <= LA + o < LA + 16) by lia.
  apply (lpt_writable_img W W2 memc mem2 (LA + o)); [exact (proj1 (HG _ (HGL _ Ha))) | | exact (HwL o Ho)].
  intros Hpa. apply Hpres2; [exact (proj1 (HG _ (HGL _ Ha)))
  | exact (lp_inG_not_owned ly S Hp W _ _ (LA + o) HARc (HGL _ Ha))
  | exact (lp_inG_not_owned ly2 S2 Hp2 W2 mem2 md2 (LA + o) HAR2 (HGL _ Ha))
  | exact (proj1 (HGR _ (HGL _ Ha)))
  | | exact Hpa].
  intros [Hb | (Hv0 & Hb)].
  - apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (LA + o) HAR2 Hvin2); [rewrite Hreqv; lia|].
    exact (proj1 (HG _ (HGL _ Ha))).
  - destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (LA + o) HARc Hin Hb (proj1 (HG _ (HGL _ Ha)))). }
assert (MN2 : val_mem SEGS (mrestrict (w_H W2) mem2) (LA + 8) 4 (hl_n l)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W2) memc mem2); [|exact Mn]. intros k0 Hk0. apply KL. cbn in Hk0. lia. }
(* ---- the state at the realloc's return ---- *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (hl_n l)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs2 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (PS : forall i, (i < 32)%nat -> acallee_saved (Z.of_nat i) -> ew E i = getr regsc (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi Hs. rewrite (EA i Hi). exact (HP2 (Z.of_nat i) Hs). }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96)) by exact (eq_trans (PS 2%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R2).
assert (E3 : ew E 3 = getr regs 3) by exact (eq_trans (PS 3%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R3).
assert (E4 : ew E 4 = getr regs 4) by exact (eq_trans (PS 4%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R4).
assert (E8 : ew E 8 = w64 (LA + 8)) by exact (eq_trans (PS 8%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R8).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x))) by exact (eq_trans (PS 9%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R9).
assert (E10 : ew E 10 = w64 res) by exact (eq_trans (EA 10%nat ltac:(lia)) Hres).
assert (E18 : ew E 18 = w64 LA) by exact (eq_trans (PS 18%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R18).
assert (E19 : ew E 19 = w64 SRC) by exact (eq_trans (PS 19%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R19).
assert (E22 : ew E 22 = w64 SB) by exact (eq_trans (PS 22%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R22).
assert (E21 : ew E 21 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (PS 21%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R21).
assert (E23 : ew E 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3))
by exact (eq_trans (PS 23%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R23).
assert (E25 : ew E 25 = w64 (grow_cap (hl_n l) (hl_cap l)))
by exact (eq_trans (PS 25%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R25).
assert (E27 : ew E 27 = getr regs 27) by exact (eq_trans (PS 27%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (P20 : getr regs2 20 = w64 (LA + 12)) by exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) R20).
assert (P24 : getr regs2 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) R24).
assert (P26 : getr regs2 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) R26).
assert (U18 : bv_unsigned (ew E 18) = LA) by (rewrite E18; apply unsigned_lit_small; lia).
assert (Usp2 : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (HS : st_ok_pi SEGS VAL E ss_lpr (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_lp_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lpr. apply pa_entry_st_ok_full.
  - unfold lpr_regs. repeat apply lpt_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg| ..].
    all: cbn [sv_denot]; rewrite ?E18, ?E22; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
    first [rewrite P20 | rewrite P24 | rewrite P26]; reflexivity.
  - vm_compute. reflexivity.
  - unfold lpr_lregion. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 18%nat LA E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply WL2; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n l)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MN2].
  - apply pairwise_disjoint_of_extents. unfold lpr_lregion. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [lpr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E10, E18, E22. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hr16.
    repeat match goal with |- _ /\ _ => split end; unfold SB; lia. }
assert (SHOK : sh_ok SEGS lpt_Bx lpr_SH E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, lpr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E lpt_Bx 18 LA 16 LA 0 16).
  + exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 LA 16 HAR2 HZ).
  + unfold U, lpt_Bx. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros y Hy. unfold SHADOW_OFF in *. lia. }
assert (HJ2 : ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | apply out_none]. }
clear HE.
(* R: beqz (refuted by 4096 <= res), the shadow checks, l->v = res, l->cap = s9, a0 = n + 1, to the malloc call *)
paj_run_to_tok_xR RUNTOG HS HJ2 SHOK lpt_Bspan A_lp_mcall.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite U18 in Ha. apply HGL. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
rename HFr into HFrR, HG0 into HGrR.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (22%bv : bv 5) F22. prreg HS (21%bv : bv 5) F21. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (27%bv : bv 5) F27.
(* ---- the memory at the malloc call ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 64)%nat -> ew Ef m = ew E m) by (intros m Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RL. cbn [ms_mem restrict] in RL.
assert (UFL : bv_unsigned (ew Ef 18) = LA) by (rewrite UF by lia; exact U18).
assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) res).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E10. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (grow_cap (hl_n l) (hl_cap l))).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E25. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W2 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite UFL in RLw. exact (RLw i Hi). }
(* off the list struct the run wrote nothing *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem msf) HFrR a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18; lia. }
(* the vector: the copied records, then the rest of the new block as junk *)
assert (HPJ : forall a, res + 16 * hl_cap l <= a < res + 16 * hl_cap l + Z.of_nat (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) ->
  YO0d.present (mrestrict (w_H W2) (ms_mem msf)) a).
{ intros a Ha. apply lp_present_of. apply (apresent_grows _ _ _ a HGrR). apply (proj1 (Hrpres a ltac:(rewrite Hvb16; lia))). }
destruct (garr8_of_present SEGS (mrestrict (w_H W2) (ms_mem msf)) (res + 16 * hl_cap l)
  (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) HPJ) as (jz & Hjl & Hjg).
assert (HjF : Forall (fun b => 0 <= b < 256) jz).
{ apply Forall_forall. intros b Hb. apply (In_nth _ _ 0) in Hb as (j & Hj & <-). exact (proj2 (Hjg j Hj)). }
assert (GV : garr8 SEGS (arm W2 (ms_mem msf)) res (bzs (concat (map text_rec (hl_recs l)) ++ map (Z_to_bv 8) jz))).
{ unfold bzs, arm. rewrite map_app. apply garr8_app. split.
  - destruct Hvec as [[Hc0 Hv0] | (Hc0 & Hin & Hjk & Hgv)].
    + assert (Hr0 : hl_recs l = []) by (apply length_zero_iff_nil; unfold hl_n in *; lia).
      rewrite Hr0. cbn [map concat]. apply garr8_nil.
    + assert (Hj0 : hl_junk l = []) by (apply length_zero_iff_nil; unfold AREC, hl_n in *; lia).
      rewrite Hj0, app_nil_r in Hgv. unfold arm in Hgv.
      apply (lpt_garr8_moved (w_H W) (w_H W2) memc (ms_mem msf) (hl_v l) res); [|exact Hgv].
      intros j Hj. rewrite length_map, lp_concat_len in Hj.
      assert (Hv0 : hl_v l <> 0) by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
      rewrite KR.
      * apply (Hcpy Hv0 j). unfold AREC, hl_n in *. lia.
      * unfold hl_n in *. lia.
      * intros HLa. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (res + j) HAR2 Hvin2); [rewrite Hreqv; unfold AREC, hl_n in *; lia|].
        exact (proj1 (HG _ (HGL _ HLa))).
  - rewrite length_map, lp_concat_len.
    replace (res + Z.of_nat (16 * length (hl_recs l))) with (res + 16 * hl_cap l) by (unfold hl_n in *; lia).
    change (map bz (map (Z_to_bv 8) jz)) with (bzs (map (Z_to_bv 8) jz)). rewrite (lp_bzs_map jz HjF). exact Hjg. }
(* the texts: their blocks stay, untouched *)
assert (RECS : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly2 S2) /\
  garr8 SEGS (arm W2 (ms_mem msf)) (fst r) (bzs (snd r ++ [Z_to_bv 8 0])) /\
  (lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= APARTIAL) /\
  (lines = false -> (1 <= length (snd r))%nat)) (hl_recs l)).
{ apply Forall_forall. intros r Hr. destruct (HRECS' r Hr) as (Hb & Hg & Hl1 & Hl2).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  split; [exact (HL2 _ (HinL _ Hb Hne))|]. split; [|split; assumption].
  assert (Hreqr : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hb) as (_ & H4096r & Hce & _). rewrite Hreqr in Hce.
  unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf)); [|exact Hg].
  intros j Hj. unfold bzs in Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  rewrite KR; [apply (KB _ _ _ Hb Hne); rewrite Hreqr; lia | lia |].
  intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (fst r + j) HARc Hb ltac:(rewrite Hreqr; lia) (proj1 (HG _ (HGL _ HLa)))). }
assert (HNR : ~ In res (map fst (hl_recs l))).
{ intros Hin. apply in_map_iff in Hin as (r & Hrr & Hr). destruct (HRECS' r Hr) as (Hb & _).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  pose proof (DL _ _ (HinL _ Hb Hne)) as D. rewrite Hrr in D. revert D. clear - Hvb16 Hgb Hnc Rn0. unfold req_size.
  destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); intros; lia. }
assert (HLC : alist_at B ly2 S2 W2 (ms_mem msf) LA (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) lines).
{ unfold alist_at. cbn [hl_v hl_cap hl_recs hl_junk].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [unfold hl_n in *; cbn [hl_recs]; lia|].
  split; [right; split; [lia|]; split; [exact Hvin2|]; split;
    [rewrite length_map, Hjl, Z2Nat.id by lia; unfold AREC, hl_n in *; cbn [hl_recs]; lia | exact GV]|].
  split; [exact HND|]. split; [exact HNR | exact RECS]. }
(* ---- the malloc call: SEG3 / SEG4 (lp_tail_seg_xR above) ---- *)
eapply (lp_tail_seg_xR W ly S Hp regs mem md LA SRC l lines x q k W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (0 + 3)
  (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) kr).
- apply HL2, HinL; [exact Hq | intros He; injection He as He1 _; exact (Hqv He1)].
- cbn [hl_v]. intros Hqr.
  assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
  pose proof (BLKN ly S Hp W memc mdc q k HARc Hq) as Hk0.
  pose proof (DL _ _ (HinL _ Hq Hne)) as D. rewrite Hqr in D. revert D. clear - Hvb16 Hgb Hnc Rn0 Hk0. unfold req_size.
  destruct (Z.eqb_spec k 0); intros; lia.
- exact HqS.
- exact HqE.
- unfold lp_tail_pre_xR. cbv zeta. cbn [hl_v hl_cap hl_recs hl_junk]. rewrite Hgr. cbn [andb negb app].
  split; [exact HJ2|]. split; [exists ch; exact HAF|]. split; [exact HGL|]. split; [exact HZ|].
  split; [exact HLC|]. split; [reflexivity|]. split; [reflexivity|].
  split; [change (hl_n l < grow_cap (hl_n l) (hl_cap l)); lia|].
  split; [intros Hf; discriminate|].
  split; [intros _ Hin; apply HnotL; apply HinL; [exact Hin | intros He; injection He as _ He2; unfold lp_vbytes, AREC in He2; lia]|].
  split; [intros rest Hpr; eapply Permutation_trans; [exact HPL|]; apply perm_skip; apply HpermL;
    revert Hpr; destruct (hl_cap l =? 0); intros Hpr; exact Hpr|].
  split; [exact Hfr2|]. split; [exact Hmle2|]. split; [exact HMOK|].
  (* the room round: realloc's post leaves the tail's budget; the counts at S2 are S's plus the new vector, within
     lp_spec_x's peak (the old vector, if any, is gone) *)
  split; [exact HRM2|].
  split.
  { unfold cnt_ok. apply (cnt_ok_pk_mono RP (lp_peak l (Z.of_nat (length x))) (fun _ => 0%nat) (ablocks B ly S) (ablocks B ly2 S2));
      [|exact HCNT].
    intros Pq. unfold lp_peak. cbv beta. rewrite (acnt_perm Pq _ _ HPL), acnt_cons. cbn [snd]. rewrite Hgr, andb_true_r.
    specialize (HcL Pq). lia. }
  split; [rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPL), bsum_cons; cbn [snd];
    rewrite (blocks_bytes_bsum B ly S) in Hlv2; lia|].
  split; [exact Hx16|].
  split.
  { unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf) SRC (bzs x)); [|exact HSRC].
    intros j Hj. unfold bzs in Hj. rewrite length_map in Hj.
    assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hq) as (_ & Hq4096 & Hqce & _).
    rewrite KR; [apply (KB q k (SRC + j) Hq Hne); lia | lia |].
    intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc q k (SRC + j) HARc Hq ltac:(lia) (proj1 (HG _ (HGL _ HLa)))). }
  split; [exact Hlin1|]. split; [exact Hlin2|].
  split; [rewrite F2, E2; reflexivity|].
  split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|]. split; [rewrite F27, E27; reflexivity|].
  split; [rewrite F8, E8; reflexivity|]. split; [rewrite F9, E9; reflexivity|]. split; [rewrite F18, E18; reflexivity|].
  split; [rewrite F19, E19; reflexivity|].
  split; [rewrite F20, E18; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F22, E22; reflexivity|]. split; [rewrite F21, E21; reflexivity|]. split; [rewrite F23, E23; reflexivity|].
  split; [rewrite F24, E18, E22; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F10, E9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split.
  { apply Forall_forall. intros p Hpp. rewrite Forall_forall in HSAVED.
    apply (val_mem_kept SEGS (w_H W) (w_H W2) memc (ms_mem msf)); [|exact (HSAVED p Hpp)].
    assert (Hfp : 0 <= fst p <= 88)
    by (unfold lp_saved in Hpp; cbn [In] in Hpp; repeat destruct Hpp as [<- | Hpp]; try destruct Hpp; cbn [fst]; lia).
    intros k0 Hk0. cbn in Hk0. rewrite KR by lia. apply KA1; lia. }
  split.
  2: { intros i Hi. destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL].
       rewrite KR by (clear - HeR HeL; lia). rewrite (Herr2 i Hi). exact (HERRC i Hi). }
  intros a Hi Hno Herr Hpa.
  assert (Hnot : forall ly0 S0 Hq0 (W0 : world SEGS) m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hq0 W0 m0 md0 HAx Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HAx Hi) Ho)).
  apply (apresent_grows _ _ _ a HGrR).
  apply (Hpres2 a Hi (Hnot _ _ _ _ _ _ HARc) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact (HAPK a Hi Hno Herr Hpa)].
  intros [Hb | (Hv0 & Hb)].
  + exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ a HAR2 Hvin2 Hb Hi).
  + destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ a HARc Hin Hb Hi).
Qed.
(* :1908 pb_list_push_x *)
Theorem pb_list_push_xR : lp_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_list_push).
Proof.
change (BASE + AF_fr_list_push) with A_list_pushP.
intros W ly S Hp regs mem md ch LA SRC l lines x q k HPRE H10 H11 H12 HLA8 HL HGL HZ Hcap25 Hx16 Hlive Hq Hqv Hq1 Hq2 Hsrc
Hlines1 Hlines2 HMOK kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (lp_entry W ly S Hp regs mem md ch LA l lines HPRE H10 HL HGL HZ) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HL as (Mv & Mn & Mc & HwL & Hnc & Hvec & HND & HVR & HRECS).
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Rv : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
assert (HJ : ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W mem md 0).
{ apply (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] LP_STK (lp_FP l) ly S Hp W regs mem md ch HPRE); [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 SRC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (Z.of_nat (length x))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_list_pushP) with (Z_to_bv 64 A_list_pushP). unfold A_list_pushP, A_list_push.
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
(* 0x85360: the UBSan ALIGN8 trap on LA, refuted by lp_spec's LA mod 8 = 0 (W_traps trap_align8) *)
psrr_branch_tok RUNG BRG HS SHOK Bspan.
{ lp_trap (trap_align8 E (SOff 10 0) LA (U_atom E 10 LA E10 ltac:(pose proof (inG_img LA (HGL LA ltac:(lia))); lia)) HLA8). }
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
(* 0x853ac bne a0,a1: N <> CAP (the list has room) or N = CAP (the vector grows) *)
psrr_branch_tok RUNG BRG HS SHOK Bspan.
-
(* the list has room: N < CAP; straight to the malloc call *)
assert (Hlt : hl_n l < hl_cap l).
{ rewrite branch_ne_U in Hc0. rewrite (U_atom _ 33 (hl_n l)), (U_atom _ 34 (hl_cap l)) in Hc0;
  [| rewrite !ew_ewset_other by lia; exact E34 | lia | rewrite !ew_ewset_other by lia; exact E33 | lia].
  apply Bool.negb_true_iff, Z.eqb_neq in Hc0. lia. }
paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan (A_lp_mcall).
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (21%bv : bv 5) Q21. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (10%bv : bv 5) Q10.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (27%bv : bv 5) Q27.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
assert (HLAr : 0x10000 <= LA /\ LA + 16 <= 0x5fc000)
by (pose proof (inG_img LA (HGL LA ltac:(lia))); pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))); lia).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (proj1 HAE 27%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
(* the chunks of the frame and of the list region, read back at the call *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (CK : forall i r c, nth_error (ss_mem ssv) i = Some r -> In c (YP09.r_chunks r) ->
    YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (YP09.r_base r)) c)
  by (intros i r c Hi0 Hcc; exact (st_ok_chunk SEGS Ev (abs_ss VAL ssv) (restrict (w_H W) msv) i r c HS Hi0 Hcc)) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 0) with Some ?r0 =>
    assert (CK0 : forall c, In c (YP09.r_chunks r0) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 2%nat)) c)
    by (intros c Hcc; exact (CK 0%nat r0 c ltac:(vm_compute; reflexivity) Hcc)) end;
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 3) with Some ?r3 =>
    assert (CK3 : forall c, In c (YP09.r_chunks r3) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 10%nat)) c)
    by (intros c Hcc; exact (CK 3%nat r3 c ltac:(vm_compute; reflexivity) Hcc)) end end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (EV2 : base_val Ev (Some 2%nat) = spZ regs)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); exact Usp);
  assert (EV10 : base_val Ev (Some 10%nat) = LA)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); rewrite E10;
        apply unsigned_lit_small; clear - HLAr; lia);
  assert (EVr : forall r, (r < 32)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (EVx : forall r, (32 <= r < 36)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  (* the frame holds the caller's ra and s0 .. s10 *)
  assert (SAVED : Forall (fun p => val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (spZ regs - 96 + fst p) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved);
  [ unfold lp_saved; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (spZ regs - 96 + ?o) 8 (bv_unsigned (getr regs (Z_to_bv 5 ?r))) =>
      let c := eval vm_compute in (o - 96) in
      let rn := eval vm_compute in (Z.to_nat r) in
      replace (spZ regs - 96 + o) with (base_val Ev (Some 2%nat) + c) by (rewrite EV2; clear; lia);
      apply (val_of_chunk_ok SEGS Ev _ _ c 8 (SOff rn 0));
      [ exact (CK0 (YP09.mkChunk c (CVal 8 (SOff rn 0))) ltac:(clear; cbn; tauto))
      | cbn [sv_denot]; rewrite Z.add_0_r, EVr by (clear; cbv; lia);
        rewrite (proj1 HAE rn ltac:(clear; cbv; lia)), (ew_Ereg_nat regs _ rn (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HR; lia
      | clear; vm_compute; discriminate ] end |];
  assert (MV' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) LA 8 (hl_v l));
  [ replace LA with (base_val Ev (Some 10%nat) + 0) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 0 8 (SOff 32 0));
    [ exact (CK3 (YP09.mkChunk 0 (CVal 8 (SOff 32 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E32, unsigned_lit_small by (clear - Rv; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Rv; lia | clear; vm_compute; discriminate ] |];
  assert (MN' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 8) 4 (hl_n l));
  [ replace (LA + 8) with (base_val Ev (Some 10%nat) + 8) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 8 4 (SOff 33 0));
    [ exact (CK3 (YP09.mkChunk 8 (CVal 4 (SOff 33 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E33, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  assert (MC' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 12) 4 (hl_cap l));
  [ replace (LA + 12) with (base_val Ev (Some 10%nat) + 12) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 12 4 (SOff 34 0));
    [ exact (CK3 (YP09.mkChunk 12 (CVal 4 (SOff 34 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E34, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  idtac
end.
(* heap and low bytes off the image were not written by the two runs *)
assert (KEEP : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x5fc000 <= a \/ ~ (LA <= a < LA + 16)) ->
  mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hoi.
  lazymatch type of HFr1 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr1 end.
  lazymatch type of HFr0 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr0 end.
  lazymatch type of HFr with frame_of ?Ev1 ?rs1 _ _ => let r1 := eval vm_compute in rs1 in change rs1 with r1 in HFr end.
  rewrite HFr1, HFr0, HFr; [reflexivity | | |];
  rewrite unsigned_lit_small by (clear - Ha C1; unfold alloc_ceiling in *; lia);
  intros (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]); try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (clear; discriminate);
  try rewrite Usp in Hr; try (rewrite E10, unsigned_lit_small in Hr by (clear - HLAr; lia));
  clear - Hr Hoi Ha Hceil Hslo Hstk0 HLAr WS C1; unfold LP_STK, ASTACK in *; lia. }
assert (HGT : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms1)))
by exact (mem_grows_trans _ _ _ HG0 (mem_grows_trans _ _ _ HG1 HG2)).
(* the list as it is at the call: the same as at entry *)
assert (HLc : alist_at B ly S W (ms_mem ms1) LA l lines).
{ apply (alist_at_kept B ly S W mem ly S W (ms_mem ms1) LA l lines HL); [|exact (lp_blks_in ly S W mem LA l lines HL)].
  intros r Hr a Ha.
  assert (HWg : writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a)
  by (intros Hw; eapply writable_at_grows; [exact HGT | exact Hw]).
  destruct (Z.le_gt_cases LA a) as [Hlo | Hlo]; [destruct (Z.lt_ge_cases a (LA + 16)) as [Hhi | Hhi]|].
  - (* the struct: its three fields hold the same values, and it stays writable *)
    split; [| intros _; apply HWg; replace a with (LA + (a - LA)) by ring; apply HwL; clear - Hlo Hhi; lia].
    unfold aview. f_equal. unfold arm in Mv, Mn, Mc.
    destruct (Z.lt_ge_cases a (LA + 8)) as [Hz8 | Hz8]; [|destruct (Z.lt_ge_cases a (LA + 12)) as [Hz12 | Hz12]].
    + replace a with (LA + (a - LA)) by ring.
      exact (val_mem_agree SEGS _ _ LA 8 (hl_v l) Mv MV' (a - LA) ltac:(clear - Hlo Hz8; cbn; lia)).
    + replace a with ((LA + 8) + (a - (LA + 8))) by ring.
      exact (val_mem_agree SEGS _ _ (LA + 8) 4 (hl_n l) Mn MN' (a - (LA + 8)) ltac:(clear - Hz8 Hz12; cbn; lia)).
    + replace a with ((LA + 12) + (a - (LA + 12))) by ring.
      exact (val_mem_agree SEGS _ _ (LA + 12) 4 (hl_cap l) Mc MC' (a - (LA + 12)) ltac:(clear - Hz12 Hhi; cbn; lia)).
  - destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hhi; lia)) as ([p nb] & Hb & Hab).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _).
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff. unf_imgband. cbn [fst snd] in Hab.
    assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia).
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)].
  - destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hlo; lia)) as ([p nb] & Hb & Hab).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _).
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff. unf_imgband. cbn [fst snd] in Hab.
    assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia).
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]. }
assert (Hng : lp_grow l = false) by (unfold lp_grow; apply Z.eqb_neq; clear - Hlt; lia).
assert (HSRC : garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) SRC (bzs x)).
{ destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q k HAR Hq) as (_ & H4096 & Hceilq & _).
  pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ q k HAR Hq) as Hoff. unf_imgband.
  apply (akept_garr8 W mem W (ms_mem ms1)); [|exact Hsrc].
  intros a Ha. unfold bzs in Ha. rewrite length_map in Ha.
  assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (apply KEEP; clear - Ha Hq1 Hq2 H4096 Hceilq Hoff; lia).
  split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]. }
eapply (lp_tail_seg_xR W ly S Hp regs mem md LA SRC l lines x q k W ly S Hp (ms_regs ms1) (ms_mem ms1) _ 0 l kr Hq Hqv Hq1 Hq2).
unfold lp_tail_pre_xR. cbv zeta. rewrite Hng. cbn [andb negb app].
split; [exact HJ|]. split; [exists ch; exact HPRE|]. split; [exact HGL|]. split; [exact HZ|].
split; [exact HLc|]. split; [reflexivity|].
split; [unfold grow_cap; destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [Heq|_]; [clear - Hlt Heq; lia | reflexivity]|].
split; [unfold grow_cap; destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [Heq|_]; [clear - Hlt Heq; lia | clear - Hlt; lia]|].
split; [intros _; reflexivity|]. split; [intros Hg; discriminate|].
split; [intros rest Hpr; exact Hpr|]. split; [reflexivity|]. split; [exact (mle_start MT S MLAW)|].
split; [exact HMOK|].
(* the room round: the list has room, so the tail's malloc is list_push's only call, at the entry's state S *)
split; [rewrite lp_rk_eq, Hng in HRM; exact HRM|]. split; [exact (lp_cnt_at RP _ _ HCNT)|].
split; [pose proof (lp_peak_nogrow (blocks_bytes S) l (Z.of_nat (length x)) Hng ltac:(lia) Hlive); lia|].
split; [exact Hx16|].
split; [exact HSRC|]. split; [exact Hlines1|]. split; [exact Hlines2|].
split; [rewrite Q2, Usp; f_equal; clear; ring|].
split; [rewrite Q3, E3; reflexivity|]. split; [rewrite Q4, E4; reflexivity|]. split; [rewrite Q27, E27; reflexivity|].
split; [rewrite Q8, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q9, E12; reflexivity|]. split; [rewrite Q18, E10; reflexivity|]. split; [rewrite Q19, E11; reflexivity|].
split; [rewrite Q20, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|]. split; [rewrite Q22, E35; reflexivity|].
split; [rewrite Q21, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q23, E10; reflexivity|].
split; [rewrite Q24, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q10, E12, unsigned_lit_small by (clear - Hx16; lia); reflexivity|].
split; [exact SAVED|].
split.
2: { intros i Hi. destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL].
     apply aview_eq_of. apply KEEP; [clear - HeR C1; lia | right; right; exact HeL]. }
intros a _ _ _ Hpa. exact (apresent_grows _ _ _ a HGT Hpa).
-
(* the list is full: N = CAP; the vector grows with realloc *)
assert (Heq : hl_n l = hl_cap l).
{ rewrite branch_ne_U in Hc0. rewrite (U_atom _ 33 (hl_n l)), (U_atom _ 34 (hl_cap l)) in Hc0;
  [| rewrite !ew_ewset_other by lia; exact E34 | lia | rewrite !ew_ewset_other by lia; exact E33 | lia].
  apply Bool.negb_false_iff, Z.eqb_eq in Hc0. lia. }
(* the room round: lp_spec_x's budget at a growing list is 3 (realloc, then the tail's malloc) *)
assert (HRM3 : rp_RM RP S (3 + kr)%nat).
{ assert (Hgr : lp_grow l = true) by (unfold lp_grow; rewrite Heq; apply Z.eqb_refl).
  rewrite lp_rk_eq, Hgr in HRM. exact HRM. }
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_awr0; [awr_any|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
(* beqz a0 at 0x853b0: N = 0, so CAP = 0 (s9 := 8), or CAP <> 0 (s9 := 2 CAP, slliw); both reach the realloc call *)
psrr_branch_tok RUNG BRG HS SHOK Bspan.
all: paj_run_tok_xR RUNG HS HJ SHOK Bspan.
all: try (lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons_awr0; [awr_any; rewrite ?ew_ewset_other by lia; exact Usp|];
  apply awr_ok_x_cons_awr0; [awr_any|];
  apply awr_ok_x_cons_awr0; [awr_any|];
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
  intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia;
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia); apply HGL; lia).
(* s9 and a1 = s9 << 4, per arm *)
all: prreg HS (25%bv : bv 5) Q25.
all: prreg HS (11%bv : bv 5) Q11.
1: assert (R25 : getr (ms_regs ms2) 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\ getr (ms_regs ms2) 11 = w64 (lp_vbytes l)).
1: { assert (Hc00 : hl_cap l = 0).
     { rewrite branch_eq_U in Hc1. rewrite (U_atom _ 33 (hl_n l)) in Hc1 by first [rewrite !ew_ewset_other by lia; exact E33 | lia].
       rewrite U_lit in Hc1 by lia. apply Z.eqb_eq in Hc1. lia. }
     unfold lp_vbytes, grow_cap, AREC. rewrite Heq, Z.eqb_refl, Hc00. cbn [Z.eqb]. rewrite Q25, Q11. split; reflexivity. }
2: assert (R25 : getr (ms_regs ms2) 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\ getr (ms_regs ms2) 11 = w64 (lp_vbytes l)).
2: { assert (Hn0 : hl_n l <> 0).
     { rewrite branch_eq_U in Hc1. rewrite (U_atom _ 33 (hl_n l)) in Hc1 by first [rewrite !ew_ewset_other by lia; exact E33 | lia].
       rewrite U_lit in Hc1 by lia. apply Z.eqb_neq in Hc1. exact Hc1. }
     unfold lp_vbytes, grow_cap, AREC. rewrite Heq, Z.eqb_refl. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]; [lia|].
     rewrite Q25, Q11, E33. unfold w64. rewrite !lp_sll by lia. split; f_equal; lia. }
(* the rest is the same in both arms *)
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1.
all: prreg HS (2%bv : bv 5) Q2.
all: prreg HS (3%bv : bv 5) Q3.
all: prreg HS (4%bv : bv 5) Q4.
all: prreg HS (8%bv : bv 5) Q8.
all: prreg HS (9%bv : bv 5) Q9.
all: prreg HS (10%bv : bv 5) Q10.
all: prreg HS (18%bv : bv 5) Q18.
all: prreg HS (19%bv : bv 5) Q19.
all: prreg HS (20%bv : bv 5) Q20.
all: prreg HS (22%bv : bv 5) Q22.
all: prreg HS (21%bv : bv 5) Q21.
all: prreg HS (23%bv : bv 5) Q23.
all: prreg HS (24%bv : bv 5) Q24.
all: prreg HS (26%bv : bv 5) Q26.
all: prreg HS (27%bv : bv 5) Q27.
all: assert (HLAr : 0x10000 <= LA /\ LA + 16 <= 0x5fc000)
  by (pose proof (inG_img LA (HGL LA ltac:(lia))); pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))); lia).
all: assert (E27 : ew E 27 = getr regs 27) by (rewrite (proj1 HAE 27%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (CK : forall i r c, nth_error (ss_mem ssv) i = Some r -> In c (YP09.r_chunks r) ->
    YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (YP09.r_base r)) c)
  by (intros i r c Hi1 Hcc; exact (st_ok_chunk SEGS Ev ssv (restrict (w_H W) msv) i r c HS Hi1 Hcc)) end.
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 0) with Some ?r0 =>
    assert (CK0 : forall c, In c (YP09.r_chunks r0) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 2%nat)) c)
    by (intros c Hcc; exact (CK 0%nat r0 c ltac:(vm_compute; reflexivity) Hcc)) end;
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 3) with Some ?r3 =>
    assert (CK3 : forall c, In c (YP09.r_chunks r3) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 10%nat)) c)
    by (intros c Hcc; exact (CK 3%nat r3 c ltac:(vm_compute; reflexivity) Hcc)) end end.
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (EV2 : base_val Ev (Some 2%nat) = spZ regs)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); exact Usp);
  assert (EV10 : base_val Ev (Some 10%nat) = LA)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); rewrite E10;
        apply unsigned_lit_small; clear - HLAr; lia);
  assert (EVr : forall r, (r < 32)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (EVx : forall r, (32 <= r < 36)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (SAVED : Forall (fun p => val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (spZ regs - 96 + fst p) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved);
  [ unfold lp_saved; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (spZ ?rg - 96 + ?o) 8 (bv_unsigned (getr ?rg (Z_to_bv 5 ?r))) =>
      let c := eval vm_compute in (o - 96) in
      let rn := eval vm_compute in (Z.to_nat r) in
      replace (spZ rg - 96 + o) with (base_val Ev (Some 2%nat) + c) by (rewrite EV2; clear; lia);
      apply (val_of_chunk_ok SEGS Ev _ _ c 8 (SOff rn 0));
      [ exact (CK0 (YP09.mkChunk c (CVal 8 (SOff rn 0))) ltac:(clear; cbn; tauto))
      | cbn [sv_denot]; rewrite Z.add_0_r, EVr by (clear; cbv; lia);
        rewrite (proj1 HAE rn ltac:(clear; cbv; lia)), (ew_Ereg_nat regs _ rn (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HR; lia
      | clear; vm_compute; discriminate ] end |];
  assert (MV' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) LA 8 (hl_v l));
  [ replace LA with (base_val Ev (Some 10%nat) + 0) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 0 8 (SOff 32 0));
    [ exact (CK3 (YP09.mkChunk 0 (CVal 8 (SOff 32 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E32, unsigned_lit_small by (clear - Rv; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Rv; lia | clear; vm_compute; discriminate ] |];
  assert (MN' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 8) 4 (hl_n l));
  [ replace (LA + 8) with (base_val Ev (Some 10%nat) + 8) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 8 4 (SOff 33 0));
    [ exact (CK3 (YP09.mkChunk 8 (CVal 4 (SOff 33 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E33, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  assert (MC' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 12) 4 (hl_cap l));
  [ replace (LA + 12) with (base_val Ev (Some 10%nat) + 12) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 12 4 (SOff 34 0));
    [ exact (CK3 (YP09.mkChunk 12 (CVal 4 (SOff 34 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E34, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  idtac
end.
(* the three runs wrote only the frame and the list struct *)
all: assert (HGT : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms2)))
  by exact (mem_grows_trans _ _ _ HG0 (mem_grows_trans _ _ _ HG1 (mem_grows_trans _ _ _ HG2 HG3))).
all: assert (KEEP : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x5fc000 <= a \/ ~ (LA <= a < LA + 16)) ->
  mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha Hoi;
  lazymatch type of HFr2 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr2 end;
  lazymatch type of HFr1 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr1 end;
  lazymatch type of HFr0 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr0 end;
  lazymatch type of HFr with frame_of ?Ev1 ?rs1 _ _ => let r1 := eval vm_compute in rs1 in change rs1 with r1 in HFr end;
  rewrite HFr2, HFr1, HFr0, HFr; [reflexivity | | | |];
  rewrite unsigned_lit_small by (clear - Ha C1; unfold alloc_ceiling in *; lia);
  intros (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]); try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (clear; discriminate);
  try rewrite Usp in Hr; try (rewrite E10, unsigned_lit_small in Hr by (clear - HLAr; lia));
  clear - Hr Hoi Ha Hceil Hslo Hstk0 HLAr WS C1; unfold LP_STK, ASTACK in *; lia).
(* the list as it is at the realloc call: the same as at entry *)
all: assert (HLc : alist_at B ly S W (ms_mem ms2) LA l lines)
  by (apply (alist_at_kept B ly S W mem ly S W (ms_mem ms2) LA l lines HL); [|exact (lp_blks_in ly S W mem LA l lines HL)];
  intros r Hr a Ha;
  assert (HWg : writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms2)) a)
    by (intros Hw; eapply writable_at_grows; [exact HGT | exact Hw]);
  destruct (Z.le_gt_cases LA a) as [Hlo | Hlo]; [destruct (Z.lt_ge_cases a (LA + 16)) as [Hhi | Hhi]|];
  [ split; [| intros _; apply HWg; replace a with (LA + (a - LA)) by ring; apply HwL; clear - Hlo Hhi; lia];
    unfold aview; f_equal; unfold arm in Mv, Mn, Mc;
    destruct (Z.lt_ge_cases a (LA + 8)) as [Hz8 | Hz8]; [|destruct (Z.lt_ge_cases a (LA + 12)) as [Hz12 | Hz12]];
    [ replace a with (LA + (a - LA)) by ring;
      exact (val_mem_agree SEGS _ _ LA 8 (hl_v l) Mv MV' (a - LA) ltac:(clear - Hlo Hz8; cbn; lia))
    | replace a with ((LA + 8) + (a - (LA + 8))) by ring;
      exact (val_mem_agree SEGS _ _ (LA + 8) 4 (hl_n l) Mn MN' (a - (LA + 8)) ltac:(clear - Hz8 Hz12; cbn; lia))
    | replace a with ((LA + 12) + (a - (LA + 12))) by ring;
      exact (val_mem_agree SEGS _ _ (LA + 12) 4 (hl_cap l) Mc MC' (a - (LA + 12)) ltac:(clear - Hz12 Hhi; cbn; lia)) ]
  | destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hhi; lia)) as ([p nb] & Hb & Hab);
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _);
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff; unf_imgband; cbn [fst snd] in Hab;
    assert (Hk : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia);
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]
  | destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hlo; lia)) as ([p nb] & Hb & Hab);
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _);
    pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff; unf_imgband; cbn [fst snd] in Hab;
    assert (Hk : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia);
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)] ]).
all: assert (HSRC : garr8 SEGS (mrestrict (w_H W) (ms_mem ms2)) SRC (bzs x))
  by (destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q k HAR Hq) as (_ & H4096 & Hceilq & _);
  pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ q k HAR Hq) as Hoff; unf_imgband;
  apply (akept_garr8 W mem W (ms_mem ms2)); [|exact Hsrc];
  intros a Ha; unfold bzs in Ha; rewrite length_map in Ha;
  assert (Hk : mrestrict (w_H W) (ms_mem ms2) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Ha Hq1 Hq2 H4096 Hceilq Hoff; lia);
  split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]).
(* the realloc call: the growth segment *)
all: eapply (lp_grow_seg_xR W ly S Hp regs mem md LA SRC l lines x q k (ms_regs ms2) (ms_mem ms2) _ kr).
all: unfold lp_rcall_pre_xR; cbv zeta.
all: split; [exact HJ|].
all: split; [exists ch; exact HPRE|].
all: split; [exact HGL|].
all: split; [exact HZ|].
all: split; [exact HLc|].
all: split; [exact Heq|].
all: split; [apply Hcap25; unfold lp_grow; rewrite Heq; apply Z.eqb_refl|].
all: split; [exact Hlive|].
all: split; [exact Hx16|].
all: split; [exact Hq|].
all: split; [exact Hqv|].
all: split; [exact Hq1|].
all: split; [exact Hq2|].
all: split; [exact HSRC|].
all: split; [exact Hlines1|].
all: split; [exact Hlines2|].
all: split; [exact HMOK|].
all: split; [exact HRM3|].
all: split; [exact HCNT|].
all: split; [rewrite Q1; reflexivity|].
all: split; [rewrite Q2, Usp; f_equal; clear; ring|].
all: split; [rewrite Q3, E3; reflexivity|].
all: split; [rewrite Q4, E4; reflexivity|].
all: split; [rewrite Q27, E27; reflexivity|].
all: split; [rewrite Q8, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q9, E12; reflexivity|].
all: split; [rewrite Q18, E10; reflexivity|].
all: split; [rewrite Q19, E11; reflexivity|].
all: split; [rewrite Q20, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q22, E35; reflexivity|].
all: split; [rewrite Q21, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q23, E10; reflexivity|].
all: split; [rewrite Q24, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [exact (proj1 R25)|].
all: split; [rewrite Q26, E10, E35; reflexivity|].
all: split; [rewrite Q10, E32; reflexivity|].
all: split; [exact (proj2 R25)|].
all: split; [exact SAVED|].
all: split; [intros a _ _ _ Hpa; exact (apresent_grows _ _ _ a HGT Hpa)|].
all: intros i Hi; destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL];
  apply aview_eq_of; apply KEEP; [clear - HeR C1; lia | right; right; exact HeL].
Qed.
End wR.
(* the two pre texts at R := wle are the strict ones *)
Lemma lp_tail_pre_x_wle : lp_tail_pre_x = lp_tail_pre_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma lp_rcall_pre_wle : lp_rcall_pre = lp_rcall_pre_xR (@wle SEGS). Proof. reflexivity. Qed.
End c.
(* list_push's G-generic form (W_contract_x.v lp_spec_g_x): the Section hypotheses on G are lp_spec_g_x's premises
   gx_ok / gx_rt; the allocator rules stay hypotheses, each at its own caller-context table with its closed trace fact
   (realloc at CTX_R, malloc at CTX_M). *)
Section g.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
(* the room round: lp_spec_g_x passes RP through (W_contract_x.v Section w2g) *)
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xc0] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M.
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xe4] CTX_M.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Theorem pb_list_push_g_x : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Proof.
intros G HG HGR.
eapply pb_list_push_x; eassumption.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, 4): list_push's G-generic form at a world relation R (W_contract_xR.lp_spec_g_xR),
   image B's twin of image A's lib/A/W_list_push.v Section g wR: pb_list_push_xR (Section c wR) with the realloc rule at
   R at CTX_R and the malloc rule at R at CTX_M, their call-boundary premise from RO_ARx and realloc's hull
   admission from HA_call; __asan_memcpy stays the strict AMEMCPY.  pb_list_push_g_x keeps its strict proof. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis ARE_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Hypothesis AMA_R : amalloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO CTX_M R.
(* :2378 pb_list_push_g_x *)
Theorem pb_list_push_g_xR : lp_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_list_push).
Proof.
intros G HG HGR.
eapply pb_list_push_xR with (R := R) (RO := RO) (HA := HA); eassumption.
Qed.
End wR.
End g.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_list_push's and pb_list_push_g's
   statements are the AR walk's, byte-identical, now corollaries of pb_list_push_x / pb_list_push_g_x at
   ARx := ARi0 (cgif's AR with the head set empty), PST := [].  As in image A's template (lib/A/W_list_push.v and
   W_lp_tail.v Sections cAR / gAR), their Sections take LX0 (the laws at ARi0, a Theorem Labs lane's rulings (a) and HP0) in
   place of LAWS, and the allocator rules in their caller-context forms (W_journal.v Section hc: realloc at CTX_R,
   malloc at CTX_M) with the closed trace facts HCTX_lp_realloc / HCTX_lp_malloc in place of arealloc_cf_rule /
   amalloc_cf_rule.  The bridges: W_contract_x.lp_spec_x_AR0 / lp_spec_g_x_AR0,
   W_journal_x.arealloc_cf_rule_c_x_of_AR0 / amalloc_cf_rule_c_x_of_AR0 / ARi0_hp0,
   W_sites_x.aintrin_realizes_x_of_AR0, W_kit_x.AR_imgc / AR_blkn (image B's top). ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xc0] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c SEGS B MT MMAX CTX_M.
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xe4] CTX_M.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Theorem pb_list_push : lp_spec B MT G MMAX (BASE + AF_fr_list_push).
Proof.
apply lp_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (arealloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX_R (SIGMA WS_realloc) ARE) as AREx.
pose proof (amalloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX_M AMA) as AMAx.
pose proof (aintrin_realizes_x_of_AR0 SEGS B OCpy (SIGMA WS_asan_memcpy) AMEMCPY) as AMEMCPYx.
exact (pb_list_push_x B [] (ARi0 SEGS B) LX0 HP0 TL MT RP_AR MLAW MMAX HMMAX G HG HGR IMGC BLKN CTX_R AREx HCTX_lp_realloc
  CTX_M AMAx HCTX_lp_malloc AMEMCPYx).
Qed.
End cAR.
Section gAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xc0] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c SEGS B MT MMAX CTX_M.
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xe4] CTX_M.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Theorem pb_list_push_g : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Proof.
apply lp_spec_g_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (arealloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX_R (SIGMA WS_realloc) ARE) as AREx.
pose proof (amalloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX_M AMA) as AMAx.
pose proof (aintrin_realizes_x_of_AR0 SEGS B OCpy (SIGMA WS_asan_memcpy) AMEMCPY) as AMEMCPYx.
exact (pb_list_push_g_x B [] (ARi0 SEGS B) LX0 HP0 TL MT RP_AR MLAW MMAX HMMAX IMGC BLKN CTX_R AREx HCTX_lp_realloc
  CTX_M AMAx HCTX_lp_malloc AMEMCPYx).
Qed.
End gAR.
End b.
End a.
